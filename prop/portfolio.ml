(* Race N z3 subprocesses per query and take the first definite verdict. z3 emits
   its few bytes of output just before exiting, so we wait for each to exit and
   read the temp files rather than streaming. *)

(* [Unknown] carries z3's `:reason-unknown`, present only when the query appended
   [(get-info :reason-unknown)]; [None] when no reason line was emitted. *)
type smt_result = SmtSat | SmtUnsat | Unknown of string option
type entry = { label : string; query : string }

(* z3 prints the reason as `(:reason-unknown "<text>")`; "" after sat/unsat. *)
let parse_reason_unknown (lines : string list) : string option =
  List.find_map
    (fun line ->
      if not (String.starts_with ~prefix:"(:reason-unknown" line) then None
      else
        match (String.index_opt line '"', String.rindex_opt line '"') with
        | Some i, Some j when j > i ->
            let s = String.sub line (i + 1) (j - i - 1) in
            if s = "" then None else Some s
        | _ -> None)
    lines

(* z3 misbehaving (stderr output, `(error ...)`, empty/unrecognized output) is
   raised, not collapsed to a verdict; only a genuine `unknown` line is [Unknown]. *)
let classify ~(stdout : string) ~(stderr : string) : smt_result =
  let fail what =
    failwith
    @@ Printf.sprintf "z3 subprocess %s\n--- stdout ---\n%s\n--- stderr ---\n%s"
         what stdout stderr
  in
  if String.trim stderr <> "" then fail "wrote to stderr";
  let lines = List.map String.trim (String.split_on_char '\n' stdout) in
  if List.exists (String.starts_with ~prefix:"(error ") lines then
    fail "emitted error on stdout";
  match List.find_opt (fun s -> s <> "") lines with
  | None -> fail "produced no output"
  | Some "unsat" -> SmtUnsat
  | Some "sat" -> SmtSat
  | Some "unknown" -> Unknown (parse_reason_unknown lines)
  | Some other -> fail (Printf.sprintf "unrecognized first line %S" other)

let remove_tmp tmp = try Sys.remove tmp with Sys_error _ -> ()

let log_retained ~label tmp =
  Printf.eprintf "Portfolio: retained failing query (%s) at %s\n%!" label tmp

let write_query_tmp (e : entry) : string =
  let tmp = Filename.temp_file "zutils_z3_" ".smt2" in
  Out_channel.with_open_text tmp (fun oc -> output_string oc e.query);
  tmp

let read_file path = In_channel.with_open_bin path In_channel.input_all

(* waitpid each killed pid so it doesn't linger as a zombie. *)
let reap_killed (pids : int list) : unit =
  List.iter
    (fun pid -> try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ())
    pids;
  List.iter
    (fun pid ->
      try ignore (Unix.waitpid [] pid)
      with Unix.Unix_error (Unix.ECHILD, _, _) -> ())
    pids

(* Raises [Failure] on any z3 misbehavior — [classify]'s own checks, plus a verdict
   from a process that did not exit cleanly. *)
let classify_outcome ~stdout ~stderr ~(status : Unix.process_status) :
    smt_result =
  match classify ~stdout ~stderr with
  | Unknown _ as t -> t
  | (SmtSat | SmtUnsat) as r -> (
      match status with
      | Unix.WEXITED 0 -> r
      | _ -> failwith "z3 emitted a verdict but did not exit cleanly")

type solver = {
  label : string;
  query_tmp : string;
  stdout_tmp : string;
  stderr_tmp : string;
  pid : int;
}

let spawn_one (devnull : Unix.file_descr) (entry : entry) : solver =
  let query_tmp = write_query_tmp entry in
  let stdout_tmp = Filename.temp_file "zutils_z3_out_" ".txt" in
  let stderr_tmp = Filename.temp_file "zutils_z3_err_" ".txt" in
  let out_fd = Unix.openfile stdout_tmp [ Unix.O_WRONLY; Unix.O_TRUNC ] 0o600 in
  let err_fd = Unix.openfile stderr_tmp [ Unix.O_WRONLY; Unix.O_TRUNC ] 0o600 in
  match
    Unix.create_process "z3"
      [| "z3"; "-smt2"; query_tmp |]
      devnull out_fd err_fd
  with
  | pid ->
      Unix.close out_fd;
      Unix.close err_fd;
      { label = entry.label; query_tmp; stdout_tmp; stderr_tmp; pid }
  | exception exn ->
      List.iter
        (fun fd -> try Unix.close fd with Unix.Unix_error _ -> ())
        [ out_fd; err_fd ];
      remove_tmp stdout_tmp;
      remove_tmp stderr_tmp;
      remove_tmp query_tmp;
      raise exn

let solve (entries : entry list) : smt_result * string option =
  match entries with
  | [] -> failwith "Portfolio.solve: no entries"
  | _ ->
      let live = ref [] in
      let devnull = Unix.openfile "/dev/null" [ Unix.O_RDONLY ] 0 in
      Fun.protect
        ~finally:(fun () ->
          (try Unix.close devnull with Unix.Unix_error _ -> ());
          (* The loop drops each solver from [live] the instant the poll reaps it,
             so [live] holds only un-reaped pids. *)
          reap_killed (List.map (fun c -> c.pid) !live);
          List.iter
            (fun c ->
              remove_tmp c.query_tmp;
              remove_tmp c.stdout_tmp;
              remove_tmp c.stderr_tmp)
            !live)
        (fun () ->
          List.iter (fun e -> live := spawn_one devnull e :: !live) entries;
          (* Poll only our own pids with [WNOHANG]; [Unix.wait ()] would reap — and
             steal the status of — any child of the host process, not just our z3s.
             Each z3 self-exits on its [:timeout], so some pid always finishes and
             the loop drains. *)
          let rec loop reason =
            match !live with
            | [] -> (Unknown reason, None)
            | cs -> (
                let finished =
                  List.find_map
                    (fun c ->
                      match Unix.waitpid [ Unix.WNOHANG ] c.pid with
                      | 0, _ -> None
                      | _, status -> Some (c, status))
                    cs
                in
                match finished with
                | None ->
                    Unix.sleepf 0.005;
                    loop reason
                | Some (c, status) -> (
                    live := List.filter (fun c' -> c'.pid <> c.pid) !live;
                    let stdout = read_file c.stdout_tmp
                    and stderr = read_file c.stderr_tmp in
                    remove_tmp c.stdout_tmp;
                    remove_tmp c.stderr_tmp;
                    match classify_outcome ~stdout ~stderr ~status with
                    | exception Failure m ->
                        log_retained ~label:c.label c.query_tmp;
                        failwith
                          (Printf.sprintf "Portfolio: z3 error (%s): %s" c.label
                             m)
                    | (SmtSat | SmtUnsat) as r ->
                        remove_tmp c.query_tmp;
                        (r, Some c.label)
                    | Unknown r ->
                        remove_tmp c.query_tmp;
                        (* keep the first non-None reason; a later [unknown] may carry none *)
                        loop (if Option.is_none reason then r else reason)))
          in
          loop None)

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

let layout_smt_result = function
  | SmtSat -> "sat"
  | SmtUnsat -> "unsat"
  | Unknown None -> "unknown"
  | Unknown (Some r) -> Printf.sprintf "unknown(%s)" r

let classify ~(status : Unix.process_status) ~(stdout : string)
    ~(stderr : string) : (smt_result, string) result =
  let fail what =
    Error
      (Printf.sprintf "z3 subprocess %s\n--- stdout ---\n%s\n--- stderr ---\n%s"
         what stdout stderr)
  in
  match status with
  | Unix.WEXITED n when n <> 0 -> fail (Printf.sprintf "exited %d" n)
  | Unix.WSIGNALED n -> fail (Printf.sprintf "killed by signal %d" n)
  | Unix.WSTOPPED n -> fail (Printf.sprintf "stopped by signal %d" n)
  | Unix.WEXITED _ -> (
      let lines =
        String.split_on_char '\n' stdout
        |> List.map String.trim
        |> List.filter (fun s -> s <> "")
      in
      if String.trim stderr <> "" then fail "wrote to stderr"
      else
        match List.find_opt (String.starts_with ~prefix:"(error ") lines with
        | Some e -> fail (Printf.sprintf "emitted %s on stdout" e)
        | None -> (
            match lines with
            | [] -> fail "produced no output"
            | "unsat" :: _ -> Ok SmtUnsat
            | "sat" :: _ -> Ok SmtSat
            | "unknown" :: rest -> Ok (Unknown (parse_reason_unknown rest))
            | other :: _ ->
                fail (Printf.sprintf "unrecognized first line %S" other)))

let remove_tmp tmp = try Sys.remove tmp with Sys_error _ -> ()

let log_retained ~label tmp =
  Printf.eprintf "Portfolio: retained failing query (%s) at %s\n%!" label tmp

let write_query_tmp (e : entry) : string =
  let tmp = Filename.temp_file "zutils_z3_" ".smt2" in
  Out_channel.with_open_text tmp (fun oc -> output_string oc e.query);
  tmp

let read_file path = In_channel.with_open_bin path In_channel.input_all

let kill_and_reap (pids : int list) : unit =
  List.iter
    (fun pid ->
      try Unix.kill pid Sys.sigkill
      with Unix.Unix_error (Unix.ESRCH, _, _) -> ())
    pids;
  List.iter
    (fun pid ->
      try ignore (Unix.waitpid [] pid)
      with Unix.Unix_error (Unix.ECHILD, _, _) -> ())
    pids

type solver = {
  label : string;
  query_tmp : string;
  stdout_tmp : string;
  stderr_tmp : string;
  pid : int;
}

let spawn_one (entry : entry) : solver =
  let query_tmp = write_query_tmp entry in
  let stdout_tmp = Filename.temp_file "zutils_z3_out_" ".txt" in
  let stderr_tmp = Filename.temp_file "zutils_z3_err_" ".txt" in
  let devnull = Unix.openfile "/dev/null" [ Unix.O_RDONLY ] 0 in
  let out_fd = Unix.openfile stdout_tmp [ Unix.O_WRONLY; Unix.O_TRUNC ] 0o600 in
  let err_fd = Unix.openfile stderr_tmp [ Unix.O_WRONLY; Unix.O_TRUNC ] 0o600 in
  let close_fds () = List.iter Unix.close [ devnull; out_fd; err_fd ] in
  match
    Unix.create_process "z3"
      [| "z3"; "-smt2"; query_tmp |]
      devnull out_fd err_fd
  with
  | pid ->
      close_fds ();
      { label = entry.label; query_tmp; stdout_tmp; stderr_tmp; pid }
  | exception exn ->
      close_fds ();
      remove_tmp stdout_tmp;
      remove_tmp stderr_tmp;
      remove_tmp query_tmp;
      raise exn

let solve (entries : entry list) : smt_result * string option =
  match entries with
  | [] -> failwith "Portfolio.solve: no entries"
  | _ ->
      let live = ref [] in
      Fun.protect
        ~finally:(fun () ->
          (* The loop drops each solver from [live] the instant the poll reaps it,
             so [live] holds only un-reaped pids. *)
          kill_and_reap (List.map (fun c -> c.pid) !live);
          List.iter
            (fun c ->
              remove_tmp c.query_tmp;
              remove_tmp c.stdout_tmp;
              remove_tmp c.stderr_tmp)
            !live)
        (fun () ->
          List.iter (fun e -> live := spawn_one e :: !live) entries;
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
                    match classify ~status ~stdout ~stderr with
                    | Error m ->
                        log_retained ~label:c.label c.query_tmp;
                        failwith
                          (Printf.sprintf "Portfolio: z3 error (%s): %s" c.label
                             m)
                    | Ok ((SmtSat | SmtUnsat) as r) ->
                        remove_tmp c.query_tmp;
                        (r, Some c.label)
                    | Ok (Unknown r) ->
                        remove_tmp c.query_tmp;
                        (* keep the first non-None reason; a later [unknown] may carry none *)
                        loop (if Option.is_none reason then r else reason)))
          in
          loop None)

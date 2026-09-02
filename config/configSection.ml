(* Strictness is per-section: the root stays an untyped [string -> json] map, so
   an unknown top-level key is never read. *)
let parse root name of_yojson =
  match Yojson.Safe.Util.member name root with
  | `Null -> failwith (Printf.sprintf "meta-config: missing section %S" name)
  | j -> (
      match of_yojson j with
      | Ok c -> c
      | Error e -> failwith (Printf.sprintf "meta-config section %S: %s" name e)
      )

module type SECTION = sig
  type t

  val name : string
  val of_yojson : Yojson.Safe.t -> (t, string) result
end

module Make (S : SECTION) : sig
  val of_meta_config : Yojson.Safe.t -> S.t
  val set : S.t -> unit
  val get : unit -> S.t
end = struct
  let of_meta_config root = parse root S.name S.of_yojson
  let cur : S.t option ref = ref None
  let set c = cur := Some c

  let get () =
    match !cur with
    | Some c -> c
    | None -> failwith (Printf.sprintf "%s config read before set" S.name)
end

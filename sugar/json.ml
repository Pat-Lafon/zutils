open Yojson.Basic.Util

let load_json fname =
  try Yojson.Basic.from_file fname
  with _ ->
    raise @@ failwith (Printf.sprintf "cannot find json file(%s)" fname)

let load_string j field = j |> member field |> to_string

let load_int j field = j |> member field |> to_int

let load_list j field = j |> member field |> to_list

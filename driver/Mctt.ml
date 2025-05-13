open McttLib.Main

let () =
  if Array.length Sys.argv <> 2
  then begin
    Printf.fprintf stderr
      "Missing <input-file> argument.\nUsage: %s <input-file>\n" Sys.argv.(0);
    exit 7
  end;
  let filename = Sys.argv.(1) in
  let code = main_of_filename filename in
  exit code

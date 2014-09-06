
let main () =
    let cin =
      if Array.length Sys.argv > 1
      then open_in Sys.argv.(1)
      else stdin
    in
try
    let lexbuf = Lexing.from_channel cin in
    while true do
Parser.input Lexer.token lexbuf
done
with End_of_file -> exit 0
  let _ = Printexc.print main ()

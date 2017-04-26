open QuickChickToolLexer
open QuickChickToolParser
open QuickChickToolTypes


let main = 
  Parsing.set_trace true;
  let lexbuf = Lexing.from_channel stdin in
  let result = program lexer lexbuf in
  print_endline (String.concat "" (List.map node_to_string result));

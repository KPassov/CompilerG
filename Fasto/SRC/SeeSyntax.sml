load "Lexing";
load "Nonstdio";
load "Parser";
load "Lexer";
load "OS";

fun createLexerStream ( is : BasicIO.instream ) =
      Lexing.createLexer ( fn buff => fn n => Nonstdio.buff_input is buff 0 n);

fun errorMess s = let val () = TextIO.output (TextIO.stdErr,s ^ "\n");
                  in []
                  end

fun showsyntax f =
  let
    val lexbuf = createLexerStream (BasicIO.open_in f)
  in let val result = Parser.Prog Lexer.Token lexbuf
     in result
     end
     handle Parsing.yyexit x => errorMess "Parser exit"
          | Parsing.ParseError x =>
            let val (line,col) = Lexer.getPos lexbuf
            in errorMess ("Parse error at line " ^ makestring line
                          ^ ", column " ^ makestring col  ^ ".")
            end
          | Lexer.LexicalError (msg,(line,col)) 
            => errorMess ("Lexical error " ^ msg ^ " at line " ^ makestring line
                          ^ ", column " ^ makestring col  ^ ".")
  end
  handle SysErr (action,err) => let val msg = case err of
                                                  SOME e => OS.errorMsg e
                                                | NONE   => "NONE" 
                                in errorMess ("SysErr in "^action ^": " ^ msg)
                                end

fun ppsyntax f =
  let
    val lexbuf = createLexerStream (BasicIO.open_in f)
  in let val result = Parser.Prog Lexer.Token lexbuf
     in print (Fasto.prettyPrint result);()
     end
     handle Parsing.yyexit x => (errorMess "Parser exit";())
          | Parsing.ParseError x =>
            let val (line,col) = Lexer.getPos lexbuf
            in (errorMess ("Parse error at line " ^ makestring line
                          ^ ", column " ^ makestring col  ^ "."));()
            end
  end
  handle SysErr (action,err) => let val msg = case err of
                                                  SOME e => OS.errorMsg e
                                                | NONE   => "NONE" 
                                 in (errorMess ("SysErr in "^action ^": " ^ msg));()
                                end


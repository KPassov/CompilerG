(* does this work?? *)
load "Lexing";
load "Nonstdio";
load "OS";

load "Parser";
load "Lexer";
load "Type";
load "Mips";
load "Compiler";

open Compiler (* compileExp *)
open Type     (* expType    *)

fun createLexerStream ( is : BasicIO.instream ) =
      Lexing.createLexer ( fn buff => fn n => Nonstdio.buff_input is buff 0 n)


fun errorMess s = (TextIO.output (TextIO.stdErr,s ^ "\n"); 
                   Lexer.resetPos ();
                   Parsing.clearParser())

fun showsyntax f =
  let
    val lexbuf = createLexerStream (BasicIO.open_in f)
  in let val result = Parser.Prog Lexer.Token lexbuf
     in result
     end
     handle Parsing.yyexit x => (errorMess "Parser exit";[])
          | Parsing.ParseError x =>
            let val (line,col) = Lexer.getPos lexbuf
            in (errorMess ("Parse error at line " ^ makestring line
                           ^ ", column " ^ makestring col  ^ ".");[])
            end
          | Lexer.LexicalError (msg,(line,col)) 
            => (errorMess ("Lexical error " ^ msg ^ " at line " ^ makestring line
                          ^ ", column " ^ makestring col  ^ ".");[])
  end
  handle SysErr (action,err) 
         => let val msg = case err of
                              SOME e => OS.errorMsg e
                            | NONE   => "NONE" 
            in (errorMess ("SysErr in "^action ^": " ^ msg);[])
            end

fun ppsyntax f =
  let
    val lexbuf = createLexerStream (BasicIO.open_in f)
  in let val result = Parser.Prog Lexer.Token lexbuf
     in (print (Fasto.prettyPrint result);())
     end
     handle Parsing.yyexit x => (errorMess "Parser exit";())
          | Parsing.ParseError x =>
            let val (line,col) = Lexer.getPos lexbuf
            in (errorMess ("Parse error at line " ^ makestring line
                           ^ ", column " ^ makestring col  ^ ".");())
            end
  end
  handle SysErr (action,err) 
         => let val msg = case err of
                              SOME e => OS.errorMsg e
                            | NONE   => "NONE" 
            in (errorMess ("SysErr in "^action ^": " ^ msg);())
            end

exception MyError of string

fun parseExp s =
    let val dummyprog =     "fun int dummy()=\n" ^ s 
                        ^ "\nfun int main() = read(int)\n"
        val lexbuf  = Lexing.createLexerString dummyprog
        val default = [Fasto.Var ("ERROR",(0,0))]
    in let val ts = Parser.Prog Lexer.Token lexbuf
       in case ts of 
              [] => raise MyError ("not understood: " ^ s)
            | (("dummy",_,_,exp,_)::_) => [exp]
            | other => raise MyError ("understood: " ^ Fasto.prettyPrint other)
       end
     handle MyError msg => (errorMess msg; default)
          | Parsing.yyexit x => (errorMess "Parser exit";default)
          | Parsing.ParseError x
            => let val (line,col) = Lexer.getPos lexbuf
               in (errorMess ("Parse error at line " ^ makestring line
                              ^ ", column " ^ makestring col  ^ "."));default
               end
          | Lexer.LexicalError (mess,(lin,col))
            => (errorMess ("Lexical error: " ^mess^ " at line "
                           ^ makestring lin ^ ", column " 
                           ^ makestring col); default)
    end

fun typeOf exp = Type.expType [("ERROR",Fasto.UNKNOWN)] exp
(*  | typeOf _     = (Fasto.UNKNOWN, Fasto.Var ("ERROR",(0,0))) *)
    handle Type.Error (mess,(lin,col)) =>
           let val () = errorMess ("Type error: " ^mess^ " at line "
                         ^ makestring lin ^ ", column " ^ makestring col)
           in (Fasto.UNKNOWN, Fasto.Var ("ERROR",(0,0)))
           end

val typeOfExp = typeOf o List.hd o parseExp 

fun compile exp = Compiler.compileExp exp [] "RESULT"

val compileExp = compile o #2 o typeOf o List.hd o parseExp

fun expInfo str = let val (tp, exp) = typeOfExp str
                      val code = compile exp
                  in print ("Expression: " ^ str 
                            ^ ", type " ^ Fasto.pp_type tp
                            ^ "\ncompiles to: \n" ^ Mips.pp_mips_list code)
                  end

fun roundtrip file
  = let val parsed = showsyntax file
        val pretty = Fasto.prettyPrint parsed
        val lexbuf = Lexing.createLexerString pretty
    in let val second = Parser.Prog Lexer.Token lexbuf
           val secondPretty = Fasto.prettyPrint second
       in if secondPretty = pretty
          then ()
          else raise MyError (file ^ ": second parse different:\n"
                              ^ pretty ^ "\n vs. \n" 
                              ^ secondPretty)
       end
       handle MyError msg => (errorMess msg) 
            | Parsing.yyexit x => (errorMess "(2)Parser exit")
            | Parsing.ParseError x =>
              let val (line,col) = Lexer.getPos lexbuf
              in (errorMess ("(2)Parse error at line " ^ makestring line
                             ^ ", column " ^ makestring col  ^ "."))
              end
            | Lexer.LexicalError (msg,(line,col)) 
              => (errorMess ("(2)Lexical error " ^ msg ^ " at line " 
                             ^ makestring line 
                             ^ ", column " ^ makestring col  ^ "."))
    end


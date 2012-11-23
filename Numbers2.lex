{
  (* Above the rules, there is a section for SML code. 

     Helper functions, declarations, and necessary "open" statements
     go here.
   *)

   open Lexing (* getLexemeStart, lexbuf, ... see documentation *)

   exception LexicalError of string * int (* position *)

   fun lexerError lexbuf s = 
       raise LexicalError (s, getLexemeStart lexbuf);

   (* Token type, often defined by the next phase *)
   datatype TokenType 
     = Decimal of int | Octal of int | Hex of int
     | Float of real | Scientific of real
     | Symbol of string
     | EOF

   (* helper functions *)
   fun decodeInt lexbuf 
     = let val s = getLexeme lexbuf 
       in case Int.fromString s of 
              NONE   => lexerError lexbuf ( s ^ ": not an int.")
            | SOME n => n
       end

   fun decodeFloat lexbuf
     = let val s = getLexeme lexbuf 
       in case Real.fromString s of 
              NONE   => lexerError lexbuf ( s ^ ": not a float.")
            | SOME x => x
       end

   (* octal and hex need more involved helper functions *)

   fun value (c : char) : int (* return digit value, assume correct input *)
     = let val v = Char.ord c
       in if v >= 48 andalso v <= 57 (* 0 - 9 *) then v - 48
          else if v >= 65 andalso v <= 70 (* A - F *) then v - 55
          else if v >= 97 andalso v <= 102 (* a - f *) then v - 87
          else raise LexicalError ("Illegal digit in conversion", 0)
       end

   fun decodeInBase (base : int) (s : string) : int
     = let fun acc ( c : char, acc : int) : int = acc*base + value c
       in List.foldl acc 0 (String.explode s)
       end

   (* "lex" will later be the generated function "Token" *)
   fun repeat lex b = let val res = lex b
                      in res :: (if res = EOF then [] else repeat lex b)
                      end

   fun Scan lex s = let val buf = createLexerString s
                    in repeat lex buf
                    end
        handle LexicalError (msg,pos) 
           => (TextIO.output (TextIO.stdErr, msg ^ makestring pos ^"\n");[])

   (* what follows is the set of token definitions and actions. Format:

   regular_expression      { returned token, probably using "lexbuf" }

    *)
}

(* SML comments can be anywhere *)

(* these are shortcuts that can be used later *)
let nonzero = [`1`-`9`]
let digit   = `0` | nonzero

(* 
let not_allowed = digit not_allowed | "recursion not allowed" 
*)

rule Token = parse
    [` ` `\t` `\n` `\r`]       (* ignore white space (make a recursive call) *)
                               { Token lexbuf }

  | `0` | nonzero digit*       { Decimal (decodeInt lexbuf) }
  | `0`[`0`-`7`]+              { Octal (decodeInBase 8 (getLexeme lexbuf)) }

  | `0` (`x`|`X`)              (* call a different scanner (start code) *)
                               { hexToken lexbuf }

  | `+` | `-` | `*` | `/`      { Symbol (getLexeme lexbuf) }

  | digit* `.` digit+ | digit+ `.`
                               { Float (decodeFloat lexbuf) }

  | (digit* `.` digit+ | digit+ `.`?) (`e`|`E`) (`+`|`-`)? digit+
                               { Scientific (decodeFloat lexbuf) }

  | eof                        { EOF }
  | _ { lexerError lexbuf ("Lexical error at input `"^getLexeme lexbuf^ "`") }

and hexToken = parse 
    (digit | [`A`-`F``a`-`f`])+ { Hex (decodeInBase 16 (getLexeme lexbuf))  }
  | _  {lexerError lexbuf ("Hex digit expected, found " ^ getLexeme lexbuf) }
;
(* Do not forget this semicolon. Noone will tell you where the error is *)

(* Fasto Compiler Driver *)

(* To interpret an input program located at ../DATA/filename.fo, run
 * 
 * $ FastoC -i ../DATA/filename
 *
 * To compile the same program with optimizations enabled, run
 *
 * $ FastoC -o ../DATA/filename
 *
 * To compile the same program without optimizations enabled, run
 *
 * $ FastoC -c ../DATA/filename
 *
 * or simply,
 *
 * $ FastoC ../DATA/filename
 *
 *)

structure FastoC =
struct

  fun createLexerStream ( is : BasicIO.instream ) =
      Lexing.createLexer ( fn buff => fn n => Nonstdio.buff_input is buff 0 n )

  fun errorMsg s = TextIO.output (TextIO.stdErr,s ^ "\n")

  fun errorMsgAt s (line, column) = errorMsg
    (s ^ "\nLine " ^ makestring line ^ ", column " ^ makestring column ^ ".")

  fun interpret pgm =
    let val absyn_str = Fasto.prettyPrint pgm
      val () = print
        ("Program is:\n\n" ^ absyn_str ^ "\n\nInput/Output:\n")
      val resultStr = Fasto.pp_exp 0 (Interpret.evalPgm pgm)
    in
      print "\n\nRESULT: ";
      print resultStr;
      print "\n"
    end

  fun applyAll fs x = foldr (fn (f, y) => f y) x fs

  fun compileAux opts pgm outpath =
    let val pgmDecorated = Type.checkProgram pgm
        val opt_pgm = applyAll opts pgmDecorated
        val code = Compiler.compile opt_pgm
        val outfile = TextIO.openOut outpath
    in
      TextIO.output (outfile, Mips.pp_mips_list code);
      TextIO.closeOut outfile
    end

  fun compile arg path =
    let
      val inpath = path ^ ".fo"
      val outpath = path ^ ".asm"
      val lexbuf = createLexerStream (BasicIO.open_in inpath)
    in
      let val pgm = Parser.Prog Lexer.Token lexbuf
      in case arg of
        "-i" => interpret pgm
      | "-o" => compileAux [Optimization.opt_pgm] pgm outpath
      | _ => compileAux [] pgm outpath
      end
      handle
        Parsing.yyexit ob => errorMsg "Parser-exit\n"
      | Parsing.ParseError ob =>
          errorMsgAt "Parsing error" (Lexer.getPos lexbuf)

      | Lexer.LexicalError (mess, pos) =>
          errorMsgAt ("Lexing error: "  ^ mess) pos

      | Interpret.Error (mess, pos) =>
          errorMsgAt ("Interpreter error: " ^ mess) pos

      | SymTab.Duplicate (mess) =>
          errorMsg ("Symbol table error: " ^ mess)

      | Optimization.NotInSymTab (id) =>
          errorMsg ("Optimization error: Id not found in symbol table " ^ id)

      | Optimization.Error (mess, pos) =>
          errorMsgAt ("Optimization error: " ^ mess) pos

      | Compiler.Error (mess, pos) =>
          errorMsgAt ("Compilation error: " ^ mess) pos

      | Type.Error (mess, pos) =>
          errorMsgAt ("Type error: " ^ mess) pos

      | SysErr (s,_) => errorMsg ("Exception: " ^ s)
    end
  val _ =
    let
      val argv = Mosml.argv()
    in
      case argv of
        [_, arg, path] => compile arg path
      | [_, path] => compile "-c" path
      | _ => print "Please supply a path to a Fasto program.\n"
    end
end

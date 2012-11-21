signature Compiler =
sig

  exception Error of string*(int*int)

  val compile : Fasto.Prog -> Mips.mips list

  (* for debugging *)
  val compileExp : Fasto.Exp 
                   -> (string * string) list
                   -> string
                   -> Mips.mips list

end

signature Interpret = sig
    type e = Fasto.Exp
    type f = Fasto.FunDec

    exception Error of string*(int*int)

    val buildFtab: f list -> (string * f) list

    val evalExp : e * (string * e) list * (string * f) list -> e
    val callFun : f * e list * (string * f) list * (int*int)-> e

    val evalPgm : f list -> e
end


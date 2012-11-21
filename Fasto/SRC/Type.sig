signature Type =
sig

  exception Error of string*(int*int)

  (* build static function table and export it *)
  val functionTable : (string * (Fasto.Type list * Fasto.Type)) list ref

  val checkProgram : Fasto.Prog -> Fasto.Prog

(* The type checker function exported here returns a modified syntax tree
  where all UNKNOWN types are replaced by inferred types (with the location
  that implied this type inference). The types introduced by the type checker
  are needed for array allocation in the compiler (to know array memory size).

  If a type error is detected, the exception will be raised. It is up to the
  implementation whether all type errors are collected in the string (ignoring
  the position) or the exception is raised immediately.
*)

(* for debugging... *)
  val expType : (string * Fasto.Type) list
                -> Fasto.Exp 
                -> Fasto.Type * Fasto.Exp

end

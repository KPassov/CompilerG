(* Symbol Table: Polymorphic for Values and Functions *)
structure SymTab = struct

    exception Duplicate of string (* passing duplicate key to caller *)

    fun empty()                 = []

    fun lookup n []             = NONE
      | lookup n ((n1,i1)::tab) = if (n=n1) then SOME i1 else lookup n tab

    (* (re-)binding names (shadowing possible earlier definitions *)
    fun bind n i stab = (n,i)::stab

    (* binding with a duplicate check (shadowing disallowed) *)
    fun insert n i stab           
      = case lookup n stab of
            NONE       => (n,i)::stab
          | SOME thing => raise Duplicate n

end

(* 

Fasto er et funktionelt array-sprog til oversættelse, F-A-S-T-O.
Fasto er også et spansk ord, der betyder "pomp" eller "pragt".
Derfor skal vi programmere en "pragtfuld" oversætter for Fasto.

*)
structure  Fasto =
struct

  (* types for abstract syntax for Fasto *)

  type pos = int * int  (* position: (line, column) *)

  datatype Type
    = Int of pos
    | Bool of pos
    | Char of pos
    | Array of Type * pos
    | UNKNOWN (* filled by type checker *)

  and Exp
    = Num of int * pos                     
    | Log of bool * pos                    
    | CharLit of char * pos
    | StringLit of string * pos            (* e.g., "Hello World!\n"       *)
    | ArrayLit of Exp list * Type * pos    (* e.g., { {1+x, 3}, {2, {1+4}} *)
                                             (* Type is the array's element type *) 
    | Var of string * pos                  (* e.g., x}    *)
    | Plus of Exp * Exp * pos              (* e.g., x + 3 *)
    | Minus of Exp * Exp * pos             (* e.g., x - 3 *)
    | Equal of Exp * Exp * pos             (* e.g., x = 3 *)
    | Less of Exp * Exp * pos              
    | If of Exp * Exp * Exp * pos         
    | Apply of string * Exp list * pos     (* e.g., f(1, 3+x) *)
    | Let of Dec * Exp * pos               (* e.g., let x = 1 + y in x + y *)

    (* arrays *)
    | Index of string * Exp * Type * pos         (* arr[3]            *)
                                                   (* Type is the input-array element type *)
    | Iota of Exp * pos                          (* iota(n)           *)
    | Map of string * Exp * Type * Type * pos    (* map(f, lst)       *)
                                                   (* The first type  is the input-array  element type *)
                                                   (* The second type is the output-array element type *)
    | Reduce of string * Exp * Exp * Type * pos  (* reduce(f, 0, lst) *)
                                                   (* Type is the input-array element type *) 
    | Replicate of Exp * Exp * Type * pos        (* replicate(n, 0)   *)
                                                   (* Type is the output-array element type *) 

    | Read of Type * pos                         (* e.g., read(int) *)
                                                   (* Type is the type of the to-be-read element *)
    | Write of Exp * Type * pos                  (* e.g., write(map(f, replicate(3,x))) *)
                                                   (* Type is the type of the to-be-written element *)

    | Times of Exp * Exp * pos
    | Divide of Exp * Exp * pos
    | And of Exp * Exp * pos
    | Or of Exp * Exp * pos
    | Not of Exp * pos
    | Negate of Exp * pos

    | MapOP of Operator * Exp * Type * Type * pos    
    | ReduceOP of Operator * Exp * Exp * Type * pos  

    
    (* second-order-array combinators *)
    | Scan of string * Exp * Exp * Type * Type* pos                   (* scan plus 0 { 1, 2, 3 } = { 0, 1, 3, 6 } *)
                                                                   (* Types same as Map. Type is the input-array element type *)
    | Length of Exp * Type * pos                       (* length({1,2,3}) = 3 *) 
                                                                   (* Type is the output Integer *)

  and Dec = Dec of string * Exp * pos

  and Operator = NegOP of pos 
               | NotOP of pos 
               | TimOP of pos 
               | DivOP of pos 
               | PluOP of pos 
               | MinOP of pos 

  type Binding = (string * Type)

  type FunDec = (string * Type * Binding list * Exp * pos)

  type Prog = FunDec list

(****************************************************)
(********** Pretty-Printing Functionality ***********)
(****************************************************)

  fun makeDepth 0 = ""
    | makeDepth n = "  " ^ (makeDepth (n-1))

  (* pretty printing an expression *)
  fun pp_exp d (Num   (n,  pos))        = Int.toString n
    | pp_exp d (Log   (b,  pos))        = Bool.toString b
    | pp_exp d (CharLit (c,  pos))      = "'" ^ Char.toCString c ^ "'"
    | pp_exp d (StringLit (s,  pos))    = "\"" ^ String.toCString s ^ "\""
    | pp_exp d (ArrayLit (lst, t, pos)) = 
        ( case lst of
            [ ]    => " { } "
          | (a::l) => " { "^pp_exp d a^concat (map (fn x => ", "^pp_exp d x) l) ^ " } "
        )
    | pp_exp d (Var    (id, pos))     = id
    | pp_exp d (Plus   (e1, e2, pos))    = " ( " ^ pp_exp d e1 ^ " + " ^ pp_exp d e2 ^ " ) "
    | pp_exp d (Minus  (e1, e2, pos))    = " ( " ^ pp_exp d e1 ^ " - " ^ pp_exp d e2 ^ " ) "
    | pp_exp d (Divide (e1, e2, pos))    = " ( " ^ pp_exp d e1 ^ " / " ^ pp_exp d e2 ^ " ) "
    | pp_exp d (Times  (e1, e2, pos))    = " ( " ^ pp_exp d e1 ^ " * " ^ pp_exp d e2 ^ " ) "
    | pp_exp d (Not   (e, pos))         = pp_exp d e
    | pp_exp d (Equal  (e1, e2, pos))    = " ( " ^ pp_exp d e1 ^ " = " ^ pp_exp d e2 ^ " ) "
    | pp_exp d (Less   (e1, e2, pos))    = " ( " ^ pp_exp d e1 ^ " < " ^ pp_exp d e2 ^ " ) "
    | pp_exp d (Or     (e1, e2, pos))    = " ( " ^ pp_exp d e1 ^ " | " ^ pp_exp d e2 ^ " ) "
    | pp_exp d (And    (e1, e2, pos))    = " ( " ^ pp_exp d e1 ^ " & " ^ pp_exp d e2 ^ " ) "
    | pp_exp d (If     (e1, e2, e3, pos))  = "\n" ^
                makeDepth (d+1) ^ "if( " ^ pp_exp d e1 ^ " )\n" ^
		makeDepth (d+2) ^ "then " ^ pp_exp (d+2) e2 ^ "\n" ^
                makeDepth (d+2) ^ "else " ^ pp_exp (d+2) e3 ^ "\n" ^
                makeDepth d 
    | pp_exp d (Apply (id, args, pos))    = 
                ( case args of
                    []     => id ^ "() "
                  | (a::l) => id ^ "( " ^ pp_exp d a ^ concat (map (fn x => ", "^pp_exp d x) l) ^ " ) " 
                )
    | pp_exp d (Let   (Dec(id, e1, pos1), e2, pos2)) = 
                "\n"^makeDepth(d+1)^"let " ^ id ^ " = " ^ pp_exp (d+2) e1 ^ 
                " in  " ^ pp_exp (d+2) e2
    | pp_exp d (Index (id, e, t, pos))       = id ^ "[ " ^ pp_exp d e ^ " ]"
    (* Array Constructs *)
    | pp_exp d (Iota (e, pos))         = "iota ( " ^ pp_exp d e ^ " ) "
    | pp_exp d (Map(id, e, _,_, pos))    = "map ( " ^ id ^ ", " ^ pp_exp d e ^ " ) "
    | pp_exp d (Length(e, t, pos))    = "length ( " ^ pp_exp d e ^ " ) "
    | pp_exp d (Reduce(id, el, lst, t, pos)) = "reduce ( "^id^", "^pp_exp d el^", "^pp_exp d lst^" ) " 
    | pp_exp d (Replicate(e, el, t, pos)) = "replicate ( "^pp_exp d e^", "^pp_exp d el^" ) " 
    | pp_exp d (Read (t,p)) = "read(" ^pp_type t ^") "
    | pp_exp d (Write (e,t,p)) = "write(" ^pp_exp d e ^") "
    | pp_exp d (MapOP(oper, e, _,_, pos))    = "mapop ( " ^ pp_operator oper ^ ", " ^ pp_exp d e ^ " ) "
    | pp_exp d (ReduceOP(oper, el, lst, t, pos)) = "reduceop ( "^ pp_operator oper ^", "^pp_exp d el^", "^pp_exp d lst^" ) " 
    | pp_exp d (_) = "Error unknown input from Parser.sml" 

  (* pretty printing a type *)
  and pp_type (Int  pos) = "int "
    | pp_type (Bool pos) = "bool "
    | pp_type (Char pos) = "char "
    | pp_type (Array (tp, pos)) = "[ " ^ pp_type tp ^ " ] "
    | pp_type UNKNOWN = "UNKNOWN "

  (*pretty printing of operators*)
  and pp_operator (NegOP pos) = " ~ "
    | pp_operator (NotOP pos) = " not  "
    | pp_operator (TimOP pos) = " * "
    | pp_operator (DivOP pos) = " / "
    | pp_operator (PluOP pos) = " + "
    | pp_operator (MinOP pos) = " - "
  
  (* pretty printing a function declaration *)
  fun pp_fun d (id, ret_tp, args, body, pos) =
    let (* pretty printing a list of bindings separated by commas *)
        fun pp_bd  (id : string, tp : Type) = pp_type tp ^ " " ^ id
        fun pp_cbd (bd : (string * Type)) = ", " ^ pp_bd bd
        fun pp_bindings []      = ""
          | pp_bindings [bd]    = pp_bd bd
          | pp_bindings (bd::l) = pp_bd bd ^ concat (map pp_cbd l)

    in "\n\nfun " ^ pp_type ret_tp ^ id ^ 
       "( " ^ pp_bindings args ^ ") = \n" ^ 
       makeDepth (d+1) ^ pp_exp (d+1) body 
    end

  (* pretty printing a PROGRAM *)
  fun prettyPrint (p : Prog) = concat (map (pp_fun 0) p) ^ "\n"

end

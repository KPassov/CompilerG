(*************************************************************)
(********************* Interpreter ***************************)
(*************************************************************)

structure Interpret :> Interpret = struct
    open Fasto

    type e = Fasto.Exp
    type f = Fasto.FunDec
    type position = (int*int)
    exception Error of string*(position)

(****************************)
(***   HELPER FUNCTIONS   ***) 
(****************************)

(****************************************************************)
(*** Accessing the fields of a function's declaration:        ***)
(*** A Function Declaration is a tuple of: (i) function name, ***)
(***  (ii) return type, (iii) formal arguments names & types, ***)
(***  (iv) function's body, (v) position. See Fasto.FunDec.   ***)
(****************************************************************)

fun getFunName(fid,_,_,_,_)= fid
fun getFunRTP (_,rtp,_,_,_)= rtp
fun getFunArgs(_,_,arg,_,_)= arg
fun getFunBody(_,_,_,bdy,_)= bdy
fun getFunPos (_,_,_,_,pos)= pos


(*************************************************)
(*** Function table associates a function name ***)
(***   its declaration, i.e. Fasto.FunDec      ***) 
(*************************************************)

fun buildFtab [] =  (** first the built-in functions **)
        let val p  = (0,0) 
            val ch = #"a"
        in  [( "chr", ("chr", Char(p), [("n", Int(p))], Num(1,p),      p) ), 
             ( "ord", ("ord", Int(p) , [("c",Char(p))], CharLit(ch,p), p) ) ] @  SymTab.empty()
        end
                    (** regular functions, i.e., defined inside the program **)
  | buildFtab ( fdcl::fs ) =
        let val fid   = getFunName(fdcl)
            val pos   = getFunPos (fdcl)
            val ftab  = buildFtab fs
            val flook = SymTab.lookup fid ftab
        in  case flook of 
              NONE   => SymTab.bind fid fdcl ftab 
            | SOME f => raise Error ("Already defined function: "^fid, pos) 
        end


(*************************************************)
(*** checking whether a value matches a type   ***)
(***   1. basic type values match their        ***)
(***          corresponding types              ***)
(***   2. arrays are treated recursively       ***)
(*************************************************)
fun typeMatch ( Int (p), Num    (i,  pos) ) = true
  | typeMatch ( Bool(p), Log    (i,  pos) ) = true
  | typeMatch ( Char(p), CharLit(ch, pos) ) = true
  | typeMatch ( Array(t, p), ArrayLit(exp_lst, tp, pos) ) = 
        foldl (fn(x,y)=>x andalso y) true (map (fn x => typeMatch(t, x)) exp_lst)
  | typeMatch (_, _) = false



(**************************************************)
(*** Evaluating (i) binary operators +, -, etc. ***)
(***            (ii)equality operator           ***)
(***           (iii)relational operator <,>     ***)
(**************************************************)
fun evalBinop ( bop, Num(n1,p1), Num(n2, p2), pos ) = Num(bop(n1, n2),pos)
  | evalBinop ( bop, e1, e2, pos ) =
        raise Error("Arguments of + Are Not Integers! Arg1: " ^ 
                    pp_exp 0 e1 ^ " Arg2: " ^ pp_exp 0 e2, pos )

fun evalEq ( Num(n1,p1),     Num(n2,p2),     pos ) = Log(n1=n2,pos)
  | evalEq ( Log(b1,p1),     Log(b2,p2),     pos ) = Log(b1=b2,pos)
  | evalEq ( CharLit(c1,p1), CharLit(c2,p2), pos ) = Log(c1=c2,pos)
  | evalEq ( e1, e2, pos ) = raise Error("Argument Types Do Not Match! Arg1: " ^
                                          pp_exp 0 e1 ^ " Arg2: " ^ pp_exp 0 e2, pos )

fun evalRelop ( bop, Num(n1,p1),     Num(n2,p2),     pos ) = Log(bop(n1,n2),pos)
  | evalRelop ( bop, CharLit(n1,p1), CharLit(n2,p2), pos ) = Log(bop(Char.ord(n1),Char.ord(n2)),pos)
  | evalRelop ( bop, Log(n1,p1),     Log(n2,p2),     pos ) =
        let val i1 = if n1 then 1 else 0
            val i2 = if n2 then 1 else 0
        in  Log(bop(i1,i2),pos)
        end
  | evalRelop ( bop, e1, e2, pos ) = raise Error("Argument Types Do Not Match! Arg1: " ^ 
                                                 pp_exp 0 e1 ^ " Arg2: " ^ pp_exp 0 e2, pos)

(***********************************************)
(*** Checking Correctness of Array Indexing, ***)
(***   i.e., index witing legal array bounds ***)
(***********************************************)
fun applyIndexing( ArrayLit(lst, tp, p1), Num(ind, p2), pos ) =
        let val len = List.length(lst)
        in  List.nth(lst,ind)
        end
  | applyIndexing( arr, ind, pos ) =
        raise Error("Indexing Error: Arg Is Not A Matrix " ^ 
                    pp_exp 0 arr ^ " or Index Is Not A NUM " ^
                    pp_exp 0 ind, pos )  

(*******************************************************)
(*** Creates a new value-symbol table (vtable) that  ***)
(***   binds the name of the formal parameter to the ***)
(***   value of the corresponding actual parameter   ***)
(*******************************************************)
fun bindTypeIds ([], [], fid, pd, pc) = SymTab.empty()
  | bindTypeIds ([], a,  fid, pd, pc) = 
        raise Error("Number of formal and actual params do not match! In call to "^fid, pc)
  | bindTypeIds (b,  [], fid, pd, pc) = 
        raise Error("Number of formal and actual params do not match! In call to "^fid, pc)
  | bindTypeIds ( (faid, fatp)::fargs, a::aargs, fid, pd, pc ) = 
        let val vtab   = bindTypeIds( fargs, aargs, fid, pd, pc )
        in  if( typeMatch(fatp, a) ) 
              then case SymTab.lookup faid vtab of
                     NONE   => SymTab.bind faid a vtab
                   | SOME m => raise Error("Formal Argument Is Already In Symbol Table!"^
                                           " In function: "^fid^" formal argument: "^faid, pd)
              else raise Error("Actual and Formal Argument Type Do Not Match!"^
                               " In function: "^fid^" formal argument: "^faid^
                               " of type: "^pp_type(fatp)^
                               " does not matches actual argument: "^
                               pp_exp 0 a, pc)
        end
        

(********************************************************************)
(********************************************************************)
(*** INTERPRETER FOR EXP case analysis after expression's shape:  ***)
(***   1. vtab holds the binding between the variable name        ***)
(***      and its interpreted value. The value can be an integer, ***)
(***      a character, a boolean, or an arbitrary array, i.e.,    ***)
(***      AbSyn values.                                           ***)
(***   2. ftab holds the binding between the function name        ***)
(***      and its declaration, i.e., Fasto.FunDec                 ***)
(***   3. the result is the interpreted value of the expression   ***)
(********************************************************************)
(********************************************************************)

fun evalExp ( Num      (n,    pos), vtab, ftab ) = Num     (n,pos)
  | evalExp ( Log      (b,    pos), vtab, ftab ) = Log     (b,pos)
  | evalExp ( CharLit  (c,    pos), vtab, ftab ) = CharLit (c,pos)
  | evalExp ( ArrayLit (l, t, pos), vtab, ftab ) =    (* ArrayLit(l, t, pos) *)
        let val els = (map (fn x => evalExp(x, vtab, ftab)) l)
        in  ArrayLit(els, t, pos)
        end

  | evalExp ( StringLit(s, pos), vtab, ftab ) =
        let val str  = String.explode s
            val exps = map (fn c => CharLit(c,pos)) str 
        in ArrayLit(exps, Char(pos), pos)
        end

  | evalExp ( Var(id, pos), vtab, ftab ) =
        let val res = SymTab.lookup id vtab
        in case res of 
             NONE   => raise Error("Symbol "^id^" Is Not In Symbol Table!\n", pos)
           | SOME m => m
        end

  | evalExp ( Plus(e1, e2, pos), vtab, ftab ) =
        let val res1   = evalExp(e1, vtab, ftab)
            val res2   = evalExp(e2, vtab, ftab)
        in  evalBinop(op +, res1, res2, pos)
        end

  | evalExp ( Minus(e1, e2, pos), vtab, ftab ) =
        let val res1   = evalExp(e1, vtab, ftab)
            val res2   = evalExp(e2, vtab, ftab)
        in  evalBinop(op -, res1, res2, pos)
        end

  | evalExp ( Times(e1, e2, pos), vtab, ftab ) =
        let val res1   = evalExp(e1, vtab, ftab)
            val res2   = evalExp(e2, vtab, ftab)
        in  evalBinop(op *, res1, res2, pos)
        end

  | evalExp ( Divide(e1, e2, pos), vtab, ftab ) =
        let val res1   = evalExp(e1, vtab, ftab)
            val res2   = evalExp(e2, vtab, ftab)
        in  evalBinop(op div, res1, res2, pos)
        end

  | evalExp ( Equal(e1, e2, pos), vtab, ftab ) =
        let val r1 = evalExp(e1, vtab, ftab)
            val r2 = evalExp(e2, vtab, ftab)
	in evalEq(r1, r2, pos)
	end

  | evalExp ( Less(e1, e2, pos), vtab, ftab ) =
        let val r1 = evalExp(e1, vtab, ftab)
            val r2 = evalExp(e2, vtab, ftab)
	in  evalRelop(op <, r1, r2, pos)   (* > *)
	end

  | evalExp ( If ( Log (true,_),e2,_,pos), vtab, ftab) = evalExp(e2, vtab, ftab)
  | evalExp ( If ( Log (false,_),_,e3,pos), vtab, ftab) = evalExp(e3, vtab, ftab)
  | evalExp ( If(e1, e2, e3, pos), vtab, ftab ) =
        let val cond = evalExp(e1, vtab, ftab)
        in case cond of 
	      Log (true,_) => evalExp(e2, vtab, ftab)
           |  Log (false,_)=> evalExp(e3, vtab, ftab)
           |  other        => raise Error("If Condition is Not Logical Value!", pos)
        end

  (************************************************************************)
  (** application of regular functions, i.e., defined in the program     **)
  (** special built-in functions "ord" and "chr" are handled in callFun **)
  (************************************************************************)
  | evalExp ( Apply(fid, args, pos), vtab, ftab ) =
        let val evargs = map (fn e => evalExp(e, vtab, ftab)) args
        in  if(fid = "ord" orelse fid = "chr") 
                 (***********************************************************)
                 (** dirty trick to handle the built in functions :        **)
                 (** just send the (valid) function id and the evaluated   **)
                 (** actual arguments and 'callFun' will handle the rest  **)
                 (***********************************************************)
            then callFun( (fid, Int(0,0),[],Num(1,(0,0)),(0,0)), evargs, ftab, pos)
  
                 (***********************************************************)  
                 (** we take the regular-function declaration from ftable  **)
                 (***********************************************************)
            else case  ( SymTab.lookup fid ftab ) of
                   SOME f => callFun(f, evargs, ftab, pos)
                 | NONE   => raise Error("Function "^fid^" Is Not In Symbol Table! Called At: ", pos)
        end

  | evalExp ( Let(Dec(id,e,p), exp, pos), vtab, ftab ) =
        let val res   = evalExp(e, vtab, ftab)
            val nvtab = SymTab.bind id res vtab 
        in  evalExp(exp, nvtab, ftab)
        end

  | evalExp ( Index(id, e, tp, pos), vtab, ftab ) =
        let val ind = evalExp(e, vtab, ftab)
            val arr = SymTab.lookup id vtab
        in case arr of
             NONE   => raise Error("Array Id "^id^" Is Not In SymTab!", pos)
           | SOME m => applyIndexing(m, ind, pos)
        end

  (**********************************************)
  (*** Second-Order-Function-Array Constructs ***)
  (**********************************************)
  | evalExp ( Iota (e, pos), vtab, ftab ) =
        let val sz = evalExp(e, vtab, ftab)
        in case sz of
             Num(size, pos) =>
                if(size > 0) then ArrayLit(List.tabulate(size, (fn x => Num(x,pos))), Int(pos), pos)
                             else raise Error("Error: In iota call, size is less or equal to 0: "^
                                                Int.toString(size), pos)
           | _ => raise Error("Iota Arg Is Not A Number: "^pp_exp 0 sz, pos)
        end

  | evalExp ( Replicate (n, e, tp, pos), vtab, ftab ) =
        let val sz  = evalExp(n, vtab, ftab)
            val el  = evalExp(e, vtab, ftab)
        in case sz of
             Num(size, pos) =>
               let val els = if(size > 0) then List.tabulate(size, (fn x => el))
                             else raise Error("Error: In call to replicate, size is less or equal to 0: "^
                                               Int.toString(size), pos)
               in case el of
                    Num     (i,  pos) => ArrayLit(els, Int (pos),    pos)
                  | Log     (b,  pos) => ArrayLit(els, Bool(pos),    pos)
                  | CharLit (c,  pos) => ArrayLit(els, Char(pos),    pos)
                  | ArrayLit(a,t,pos) => ArrayLit(els, Array(t,pos), pos)
                  | _                 => raise Error("Unevaluated Element in Replicate "^pp_exp 0 el, pos)
               end
           | _ => raise Error("Replicate First Arg (Array Size) "^
                              "Was Not Evaluated To A Number: "^pp_exp 0 sz, pos)
        end

  | evalExp ( Map (fid, arrexp, _, _, pos), vtab, ftab ) =
        let val fexp = SymTab.lookup fid ftab
            val arr  = evalExp(arrexp, vtab, ftab)
        in case fexp of
             NONE   => raise Error("Function "^fid^" Is Not In SymTab!", pos)
           | SOME f => let val (fid, rtp, fargs, body, pdecl) = f
                       in case rtp of
                            UNKNOWN => raise Error("The Return Type of Function "^fid^
                                                   " Is UNKNOWN: "^pp_type rtp, pos )
                          | otherwise =>
                              ( case arr of
                                  ArrayLit(lst,tp1,p) =>
                                      let val mlst = map (fn x => callFun(f, [x], ftab, pos) ) lst
                                      in  ArrayLit(mlst, rtp, pos)
                                      end
                                | otherwise => raise Error("Second Argument of Map Is Not An Array: "
                                                            ^pp_exp 0 arr, pos)   )
                       end
        end

  | evalExp ( Reduce (fid, ne, arrexp, tp, pos), vtab, ftab ) =
        let val fexp = SymTab.lookup fid ftab
            val arr  = evalExp(arrexp, vtab, ftab)
            val nel  = evalExp(ne, vtab, ftab)
        in  case fexp of
              NONE => raise Error("Function "^fid^" Is Not In SymTab!", pos)
            | SOME f => let val (fid, rtp, fargs, body, pdecl) = f
                        in case rtp of
                            UNKNOWN => raise Error("The Return Type of Function "^fid^
                                                   " Is UNKNOWN: "^pp_type rtp, pos )
                          | otherwise =>
                              ( case arr of 
                                  ArrayLit(lst,tp1,p) =>
                                    foldl (fn (x,y) => callFun(f, [x,y], ftab, pos) ) nel lst 
                                | otherwise => raise Error("Third Argument of Reduce Is Not An Array: "^
                                                             pp_exp 0 arr, pos)   
                              )
                        end
        end

  | evalExp ( Read (t,p), vtab, ftab ) =
        let val str = TextIO.inputLine(TextIO.stdIn)
        in case t of
             Int p1  => let val v = Int.fromString(str)
                        in case v of
                             SOME n    => Num(n,p)
                           | otherwise => raise Error("read(int) Failed! ", p)
                        end
           | Bool p1 => let val v = Int.fromString(str) (* Bool.fromString(str) *)
                        in case v of
                             SOME b    => if( b=0 ) then Log(false,p) else Log(true,p)
                           | otherwise => raise Error("read(bool) Failed; 0==false, 1==true! ", p)
                        end
           | Char p1 => let val v = Char.fromCString(str)
                        in case v of
                             SOME c    => CharLit(c,p)
                           | otherwise => raise Error("read(char) Failed!  ", p)
                        end
           | otherwise => raise Error("Read Operation is Valid Only on Basic Types ", p)
        end

  | evalExp ( Write(exp,t,p), vtab, ftab ) =
        let val e  = evalExp(exp, vtab, ftab)
            val () =
            case e of
              Num     (n,pos) => print( (Int.toString n) ^ " " )
            | Log     (b,pos) => let val res = if(b) then "1 " else "0 " in print( res ) end
            | CharLit (c,pos) => print( (Char.toCString c)^" " )
            | ArrayLit(a,t,pos) => (
                  case t of
                    Char(pos) => 
                        let fun mapfun e = 
                                case e of
                                  CharLit(c,p1) => c
                                | otherwise     => raise Error("Expression "^pp_exp 0 e^
                                                               " Should Have Been Evaluated To CharLit ", pos)
                        in print( String.implode (map mapfun a)^" " )
                        end
                  | otherwise => raise Error("Write Can Be Called Only on Basic and Array(Char) Types ", p)
              )
            | otherwise => raise Error("Write Can Be Called Only on Basic and Array(Char) Types ", p)
        in e
        end
  | evalExp _  = raise Error("Unimplemented!", (0,0)) 


(*************************************************************)
(*** INTERPRETER FOR FUNCTION CALLS:                       ***)
(***  1st arg is the function's declaration (Fasto.FunDec) ***)
(***  2nd arg is a list of the evaluated actual arguments  ***)
(***  3rd arg is the function's symbol table, which        ***)
(***          associates a function name with its FunDec   ***)
(***  4th arg is the position where the call occurred      ***)
(***  The result is the value resulted from interpreting   ***)
(***      the function call, i.e., by evaluating he body   ***)
(***      of the function on the given actual parameters   ***)
(*************************************************************)

and callFun ( (fid, rtp, fargs, body, pdcl), aargs, ftab, pcall ) =
    case fid of
      (* treating "special" functions such as ord/chr *)
      "ord" => (  case aargs of
                    [Fasto.CharLit(c,p)] => Fasto.Num(ord(c), pcall)
                  | otherwise => raise Error("Argument of \"ord\" Does Not Evaluate to Char: "^
                                              String.concat(map (pp_exp 0) aargs), pcall)
               )
    | "chr" => (  case aargs of
                    [Fasto.Num(n,p)] => Fasto.CharLit(chr(n), pcall)
                  | otherwise => raise Error("Argument of \"chr\" Does Not Evaluate to Num: "^
                                              String.concat(map (pp_exp 0) aargs), pcall)
               )

      (* treating "normal" functions, which have a definition in the program *)
    | _     =>
        let val vtab = bindTypeIds(fargs, aargs, fid, pdcl, pcall)
            val res  = evalExp( body, vtab, ftab )

        in  if( typeMatch(rtp, res) ) 
            then res
            else raise Error("Result Type Does Not Matches The Return Type!"^
                             " In function: "^fid^" Return Type: "^pp_type(rtp)^
                             " Result: "^pp_exp 0 res, pcall)
        end


(*********************************************)
(*** INTERPRETER FOR PRG:                  ***)
(*** 1. builds the functions' symbol table ***)
(*** 2. interprets the body of "main" and  ***)
(*** 3. Returns the interpreted result     ***)
(*********************************************)
and evalPgm funlst =
        let val ftab  = buildFtab funlst
            val mainf = SymTab.lookup "main" ftab
        in  case mainf of
              NONE   => raise Error("Did Not Find Main Fun! Abort! ", (0,0))
            | SOME m => callFun(m, [], ftab, (0,0))
	end

end

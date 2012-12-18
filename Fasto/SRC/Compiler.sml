(* Compiler for Fasto *)
(* Compile by mosmlc -c Compiler.sml *)
(* Then recompile CC by mosmlc CC.sml -o CC *)

structure Compiler :> Compiler =
struct

  (* Use "raise Error (message,position)" for error messages *)
  exception Error of string*(int*int)

  (* Name generator.  Call with, e.g., t1 = "tmp"^newName () *)
  val counter = ref 0

  fun newName () = (counter := !counter + 1;
                  "_" ^ Int.toString (!counter)^ "_")

  (* Number to text with "normal" sign symbol *)
  fun makeConst n = if n>=0 then Int.toString n
                    else "-" ^ Int.toString (~n)

  (* Table storing all string literals, with labels given to them *)
  val stringTable = ref []
  (* could also contain "\n", ",", "Index out of bounds in line ", but the
     format is a bit different (length and dummy pointer come first) *)

  (* Building a string in the heap, including initialisation code *)
  fun buildString (label, str)
    = let val data = [Mips.ALIGN "2"   (* means: word-align *)
                     ,Mips.LABEL label (* pointer *)
                     ,Mips.SPACE "8"   (* size(int) and data pointer (word) *)
                     ,Mips.ASCIIZ str]
          val initR = label^ "_init"
          val addrR = label^ "_addr"
          val initcode = [ Mips.LA(addrR, label)
                         , Mips.LI(initR, makeConst (1 + (String.size str)))
                         , Mips.SW(initR, addrR, makeConst 0 )
                         , Mips.ADDI(initR, addrR, makeConst 8)
                         , Mips.SW(initR, addrR, makeConst 4 )]
      in (initcode, data)
      end

  (* link register *)
  val RA = "31"
  (* Register for stack pointer *)
  val SP = "29"
  (* Register for heap pointer *)
  val HP = "28"

  (* Suggested register division *)
  val minReg = 2       (* lowest usable register *)
  val maxCaller = 15   (* highest caller-saves register *)
  val maxReg = 25      (* highest allocatable register *)

  (* zipWith: did not find it so I implement it here *)
  fun zipWith f (x::xs) (y::ys) = f(x,y) :: (zipWith f xs ys)
    | zipWith _    _       _    = [];

  fun getElSize(tp: Fasto.Type) : int = 
        case tp of Fasto.Char(p) => 1 | Fasto.Bool(p) => 1 | otherwise => 4

  (*********************************************************************)
  (* generates the code to check that the array index is within bounds *)
  (* THIS IS SUPPOSED TO BE PART OF THE PROJECT!!!                     *)
  (*********************************************************************)
   
  
  fun check_bounds(arr_beg, ind_reg, (line,c), arr_szeCB, arr_label1, arr_label2) =[
	Mips.LW(arr_szeCB, arr_beg , "0"), Mips.BGEZ(ind_reg,arr_label2),
	Mips.LABEL(arr_label1), Mips.LI("5",makeConst line), Mips.J "_IndexOutOfBoundsError_", 
	Mips.LABEL(arr_label2), Mips.SUB(arr_szeCB,ind_reg,arr_szeCB), 
	 (*Mips.ADDI(ind_reg,ind_reg,"-1"), ind-length<0 >*)
	Mips.BGEZ(arr_szeCB, arr_label1)]

(*create register to hold the *)

  (****************************************************************************************)
  (* size_reg is the register that stores an int denoting the num of array elements       *)
  (* place    is the register that will store the start address of array                  *)
  (* the result array will have shape: [size,ptr_to_data[0],data[0],..,data[size-1]]      *)
  (* char/bool element is 1 byte, int element is 4 bytes;                                 *)
  (* for Array(Char) we allocate/write an extra NULL element so that we can use putstring *)
  (****************************************************************************************)
  fun dynalloc(size_reg:string, place:string, tp:Fasto.Type) : Mips.MipsProg = 
      let val tmp_reg = "_tmp_reg_"^newName()  
          val is_char = case tp of Fasto.Char(p) => true | otherwise => false
          val is_bool = case tp of Fasto.Bool(p) => true | otherwise => false

          val code1   = case tp of 
                            Fasto.Char _ => [Mips.ADDI(tmp_reg, size_reg, "9")]
                          | Fasto.Bool _ => [Mips.ADDI(tmp_reg, size_reg, "8")]
                          | other        => [Mips.SLL (tmp_reg, size_reg, "2"),
                                             Mips.ADDI(tmp_reg, tmp_reg,  "8")]

          val code2  = if(is_char orelse is_bool) (* align to 4 byte boundary *)
                           then [Mips.ADDI(tmp_reg, tmp_reg, "3")
                                ,Mips.SRA (tmp_reg, tmp_reg, "2")
                                ,Mips.SLL (tmp_reg, tmp_reg, "2")]
                           else []

          val code3   =  [ Mips.MOVE(place,HP) ] @ code1 @ code2 @ 
                         [ Mips.ADD (HP, HP, tmp_reg),
                           Mips.SW(size_reg,place, "0"),
                           Mips.ADDI(tmp_reg,place,"8"),
                           Mips.SW(tmp_reg, place, "4") ]

      in if(is_char) then code3 @ [ Mips.ADD(tmp_reg,size_reg,place), 
                                    Mips.SB("0",tmp_reg,"8") ]
                     else code3
      end

  (**********************************************************************)
  (* Generates code for a do loop:                                      *)
  (*     do i = 0, n-1                                                  *)
  (*        arr[i] = f(i)                                               *)
  (*     enddo                                                          *)
  (* Where: el_sz is size of one element: one or four (bytes)           *)
  (*        i_reg, n_reg, arr_reg, are the registers holding            *)
  (*            i, n, and the array address, respectively.              *)
  (*        addr_reg is initially arr_reg + 8, i.e., the start of       *)
  (*            array-data segment, and is incremented by el_sz within  *)
  (*            the loop in order to populate the array                 *)
  (*        f(i_reg, res_reg) produces the code for computing f(i),     *)
  (*            where the result is stored in res_reg                   *)
  (**********************************************************************)
  fun compileDoLoop( el_sz : int, n_reg : string, arr_reg : string, 
                     f : string*string->Mips.MipsProg, pos ) : Mips.MipsProg = 
        let val i_reg     = "_ind_var_" ^newName()
            val res_reg   = "_res_i_reg"^newName()
            val tmp_reg   = "_tmp_reg_" ^newName()
            val loop_beg  = "_loop_beg_"^newName()
            val loop_end  = "_loop_end_"^newName()
            val addr_reg  = "_arr_loc_" ^newName() 
            val header    = [ Mips.LW(addr_reg, arr_reg, "4"), Mips.MOVE(i_reg, "0"), 
                              Mips.LABEL(loop_beg), Mips.SUB(tmp_reg, i_reg, n_reg), 
                              Mips.BGEZ(tmp_reg, loop_end)
                            ]
            val code_fi   = f(i_reg, res_reg)
            val code_assign  = 
                  case el_sz of
                    4 => [ Mips.SW(res_reg,addr_reg,"0"), Mips.ADDI(addr_reg,addr_reg,"4") ]
                  | 1 => [ Mips.SB(res_reg,addr_reg,"0"), Mips.ADDI(addr_reg,addr_reg,"1") ] 
                  | otherwise => raise Error("The Only Valid Element-Sizes Are 1 and 4. Error",pos)
            val epilog = [ Mips.ADDI(i_reg,i_reg,"1"), Mips.J loop_beg, Mips.LABEL loop_end ]
        in header @ code_fi @ code_assign @ epilog
        end

  (***********************************************************************)
  (*** Generates Code to Call Function fid on the List of Registers args *)
  (***********************************************************************)
  fun ApplyRegs(fid: string, args: string list, place: string, pos) : Mips.MipsProg =
    let val regs_num    = length args
        val () = if (regs_num > maxCaller - minReg) 
                 then raise Error("Num of args of "^fid^" exceeds number of caller registers!", pos)
                 else ()
        val caller_regs = map (makeConst o (fn x => x + minReg)) (List.tabulate(regs_num, fn x => x))
        val move_code : Mips.mips list   = zipWith (fn (x : string, y : string) => Mips.MOVE(x, y)) caller_regs args
    in  move_code @ [ Mips.JAL(fid,caller_regs), Mips.MOVE(place, "2") ]
    end 

  (***********************************************************************)
  (* complieExp evaluates e, the result of e is stored in register place *)
  (*   vtable is the variable's Symbol Table and binds variable names to *)
  (*     the register that stores the value of the corresponding variable*)
  (***********************************************************************)
  fun compileExp e vtable place =
    case e of
      Fasto.Num (n,pos)      =>
        if n<32768 then
	  [Mips.LI (place, makeConst n)]
	else
	  [Mips.LUI (place, makeConst (n div 65536)),
	   Mips.ORI (place, place, makeConst (n mod 65536))]

    | Fasto.Log(b, pos)     => 
        if b = true then
          [Mips.LI (place, makeConst 1)]
        else 
          [Mips.LI (place, makeConst 0)]
    | Fasto.CharLit(c,pos)   => [Mips.LI (place, makeConst (ord c))]
          (* compileExp (Fasto.Num(ord(c),pos)) vtable place *)

(*
    | Fasto.StringLit(str,pos) =>
        let val sz         = size(str) + 1 (* ends in extra null element *)
            val sz_reg     = "_size_reg_"^newName()
            val addr_reg   = "_arr_loc_" ^newName() 
            val tmp_reg    = "_tmp_reg_" ^newName()
            val header     = [ Mips.LI(sz_reg, makeConst sz) ]  @ 
                             dynalloc(sz_reg,place,Fasto.Char(pos)) @
                             [ Mips.LW(addr_reg,place,"4") ]
            fun gench(ch) = [ Mips.LI  ( tmp_reg, makeConst (ord ch) ),
                              Mips.SB  ( tmp_reg, addr_reg, "0" ), 
                              Mips.ADDI( addr_reg,addr_reg, "1" ) 
                            ]
            val epilog     = List.concat ( map gench (explode str) )
                             (* @ [ Mips.SB("0", addr_reg, "0") ] *)
        in  header @ epilog
        end
*)
        (* Alternative, more efficient: create/return a label here, collect
           all string literals of the program (in a ref table), create them
           in the data section before the heap (Mips.ASCIIZ) *)
    | Fasto.StringLit(str,pos) =>
        let val normalChars
              = (List.filter Char.isAlphaNum (String.explode(str)))
                @ String.explode "__str__"
            val label = String.implode(List.take (normalChars,7)) ^newName()
            val ()    = stringTable := (label,str)::(!stringTable)
        in  [Mips.LA (place, label),
             Mips.COMMENT (label^": string \""^ String.toCString str ^ "\"")]
        end
    | Fasto.ArrayLit(elems,tp,pos) =>
        let val is_char = case tp of Fasto.Char(p) => true | otherwise => false
            val is_bool = case tp of Fasto.Bool(p) => true | otherwise => false
            val el_sz   = getElSize tp
            val sz_reg  = "_size_reg_"^newName()
            val addr_reg= "_arr_loc_" ^newName() 
            val tmp_reg = "_tmp_reg_" ^newName()
            val header  = [ Mips.LI(sz_reg, makeConst (length elems)) ]  @ 
                          dynalloc(sz_reg,place,tp) @
                          [ Mips.LW(addr_reg,place,"4") ]
          (*  val () = print("ArrayLit: "^Fasto.pp_exp 0 e ^ " EL_TYPE: " ^ Fasto.pp_type tp) *)

            fun genel(el) = 
                let val codeel= compileExp el vtable tmp_reg
                    val store = if el_sz = 1
                                    then Mips.SB(tmp_reg, addr_reg, "0")
                                    else Mips.SW(tmp_reg, addr_reg, "0") 
                    in codeel @ [store, Mips.ADDI(addr_reg,addr_reg, makeConst el_sz)]
                    end

            val epilog  = List.concat (map genel elems)
                            (*  @ ( if(is_char) then [ Mips.SB("0", addr_reg, "0") ] else [ ] )  *)
        in  header @ epilog
        end
    | Fasto.Var (x,pos) => 
        ( 
            case (SymTab.lookup x vtable) of
              NONE => raise Error ("Name "^x^" not found", pos)
            | SOME reg_name => [Mips.MOVE (place, reg_name)]
        )
    | Fasto.Plus (e1,e2,pos) =>
        let val t1 = "_plus1_"^newName()
            val t2 = "_plus2_"^newName()
            val code1 = compileExp e1 vtable t1
            val code2 = compileExp e2 vtable t2
        in code1 @ code2 @ [Mips.ADD (place,t1,t2)]
        end
    | Fasto.Minus (e1,e2,pos)=>
        let val t1 = "_minus1_"^newName()
            val t2 = "_minus2_"^newName()
            val code1 = compileExp e1 vtable t1
            val code2 = compileExp e2 vtable t2
        in  code1 @ code2 @ [Mips.SUB (place,t1,t2)]
        end
    | Fasto.Times (e1,e2,pos)=>
        let val t1 = "_times1_"^newName()
            val t2 = "_times2_"^newName()
            val code1 = compileExp e1 vtable t1
            val code2 = compileExp e2 vtable t2
        in  code1 @ code2 @ [Mips.MUL (place,t1,t2)]
        end
    | Fasto.Divide (e1,e2,pos)=>
        let val t1 = "_divide1_"^newName()
            val t2 = "_divide2_"^newName()
            val code1 = compileExp e1 vtable t1
            val code2 = compileExp e2 vtable t2
        in  code1 @ code2 @ [Mips.DIV (place,t1,t2)]
        end
    | Fasto.Not (e, pos) =>
        let val truelabel  = "_not1_"^newName()
            val falselabel = "_not2_"^newName()
            val endlabel   = "_endnot_"^newName()
            val code = compileCond e vtable truelabel falselabel
        in  code @ [Mips.LABEL truelabel, Mips.LI (place, makeConst 0),
                   Mips.J endlabel,
                   Mips.LABEL falselabel, Mips.LI (place, makeConst 1),
                   Mips.LABEL endlabel]
        end
    | Fasto.Negate (e, pos) =>
        let val num   = "_neg1_"^newName()
            val code = compileExp e vtable num
            val t1 = "_neg2_"^newName()
        in  code @ [Mips.ADDI(t1, "0","-1"), Mips.MUL(place, num, t1)]
        end
    | Fasto.Or (e1,e2,pos)=>
        let val t1 = "_or1_"^newName()
            val t2 = "_or2_"^newName()
            val code1 = compileExp e1 vtable t1
            val code2 = compileExp e2 vtable t2
        in  code1 @ code2 @ [Mips.OR (place,t1,t2)]
        end
    | Fasto.And (e1,e2,pos)=>
        let val t1 = "_and1_"^newName()
            val t2 = "_and2_"^newName()
            val code1 = compileExp e1 vtable t1
            val code2 = compileExp e2 vtable t2
        in  code1 @ code2 @ [Mips.AND (place,t1,t2)]
        end
    | Fasto.Let (dec,e1,(line,col)) =>
        let val (code1, vtable1) = compileDec dec vtable
            val code2 = compileExp e1 vtable1 place
	    in code1 @ code2
        end
    | Fasto.If (e1,e2,e3,pos) =>
        let val thenLabel = "_then_"^newName()
            val elseLabel = "_else_"^newName()
            val endLabel = "_endif_"^newName()
            val code1 = compileCond e1 vtable thenLabel elseLabel
            val code2 = compileExp e2 vtable place
            val code3 = compileExp e3 vtable place
        in code1 @ [Mips.LABEL thenLabel] @ code2  @ 
           [Mips.J endLabel, Mips.LABEL elseLabel] @ 
           code3 @ [Mips.LABEL endLabel]
        end
    | Fasto.Apply (f, args, pos) =>
        let
            (* Convention: args in regs (2..15), result in reg 2 *)
            val (loadCode,maxreg) = loadArgs args vtable minReg
            val regs = if maxreg > maxCaller 
                       then raise Error ("Too many arguments.", (0,0))
                       else List.tabulate(maxreg - minReg,
                                          makeConst o (fn x => x + minReg))
        in  loadCode @                               (* push args *)
            [Mips.JAL (f,regs),          (* jump to function code *)
             Mips.MOVE (place,"2")]         (* store return value *)
        end

(***************************************************************)
(*** dirty I/O. Read and Write: supported for basic types:   ***)
(*** Int, Char, Boll via SYSCALLS. Write of an Array(Chars)  ***)
(*** is also supported.The others are user's responsibility. ***)
(***************************************************************)
    | Fasto.Read(tp, pos) => (
        case tp of
          Fasto.Int(p)  => [ Mips.JAL ("getint",["2"]),
                             Mips.MOVE(place,"2")  
                           ]
        | Fasto.Char(p) => [ Mips.JAL ("getchar", ["2"]),
                             Mips.MOVE(place, "2") 
                           ]
        | Fasto.Bool(p) => 
            let val tl = "_true_lab_" ^newName()
                val fl = "_false_lab_"^newName()
                val ml = "_merge_lab_"^newName()
                val v  = "_bool_var_"^newName()
            in [ Mips.JAL ("getint", ["2"]),  Mips.MOVE(v, "2"),
                 Mips.BEQ (v,"0",fl),         Mips.J tl,
                 Mips.LABEL fl, Mips.MOVE(place, "0"), Mips.J ml,
                 Mips.LABEL tl, Mips.LI  (place, "1"), Mips.J ml, 
                 Mips.LABEL ml
               ]  
            end
        | _ => raise Error("Read On An Incompatible Type: "^Fasto.pp_type tp, pos)
      )

    | Fasto.Write(e, tp, pos) =>
        let val codeexp = compileExp e vtable place 
        in case tp of
             Fasto.Int(p)  => codeexp @ [ Mips.MOVE("2",place), Mips.JAL("putint", ["2"]) ]
           | Fasto.Bool(p) => codeexp @ [ Mips.MOVE("2",place), Mips.JAL("putint", ["2"]) ]
           | Fasto.Char(p) => codeexp @ [ Mips.MOVE("2",place), Mips.JAL("putchar",["2"]) ]
           | Fasto.Array(Fasto.Char(p1),p2) =>
               let val arr_beg = "_arr_beg_"^newName()
               in  codeexp @ [ Mips.LW(arr_beg, place, "4"), 
                               Mips.MOVE("2", arr_beg), Mips.JAL("putstring", ["2"]) ]
               end

            (*******************************************)
            (*******************************************)
            (** This is supposed to be Project Work!  **)
            (*******************************************)
            (*******************************************)
           | Fasto.Array(eltp, p1) => (* for Array(Int) and Array(Array(Int)) *)
               let val arr_reg   = "_arr_reg_"  ^newName()
                   val sz_reg    = "_size_reg_" ^newName()
                   val tmp_reg   = "_tmp_reg_" ^newName()
                   val i_reg     = "_ind_var_" ^newName()
                   val loop_beg  = "_loop_beg_"^newName()
                   val loop_end  = "_loop_end_"^newName()
 
                   val header1 = [ Mips.LW(sz_reg,place,"0"),      Mips.LW(arr_reg,place,"4"), 
                                   Mips.MOVE(i_reg,"0"),           Mips.LABEL(loop_beg), 
                                   Mips.SUB(tmp_reg,i_reg,sz_reg), Mips.BGEZ(tmp_reg, loop_end)   ]
                   
                   val header2 = if ( (getElSize eltp) = 1 ) 
                                 then [ Mips.LB(tmp_reg,arr_reg,"0"), Mips.ADDI(arr_reg,arr_reg,"1") ]
                                 else [ Mips.LW(tmp_reg,arr_reg,"0"), Mips.ADDI(arr_reg,arr_reg,"4") ]

                   (***************************************************************************)
                   (** create a fake Fasto node corresponding to the array elem              **)
                   (** and call compileExp recursively to generate code to print the element **)
                   (***************************************************************************)
                   val elem_reg  = "ft_elem_reg__"  ^newName()
                   val new_vtab  = SymTab.bind elem_reg tmp_reg vtable
                   val fastoexp : Fasto.Exp = Fasto.Write(Fasto.Var(elem_reg, pos), eltp, pos)
                   val elem_code = compileExp fastoexp new_vtab tmp_reg

               in  codeexp @ header1 @ header2 @ elem_code @ 
                    [ Mips.ADDI(i_reg,i_reg,"1"), Mips.J loop_beg, Mips.LABEL loop_end ]
               end
     
           | _ => raise Error("Write On An Incompatible Type: "^Fasto.pp_type tp, pos)
        end

(*************************************************)
(*** Equal, write similar code for And and Or. ***)
(***   the generated-code pseudocode is:       ***)
(***       place := 0                          ***)
(***         code to compute the values of     ***)
(***         e1 and e2 in t1 and t2            ***)
(***       if( t1 == t2) goto tlab             ***)
(***       goto flab                           ***)
(*** tlab: place := 1                          ***)
(*** flab:                                     ***)
(*************************************************)
    | Fasto.Equal (e1,e2,pos) => 
        let val trueLabel = "_true_"^newName()
            val falseLabel = "_fals_"^newName()
            val endLabel = "_endif_"^newName()
            val code1 = compileCond e vtable trueLabel falseLabel
        in  [Mips.LI (place,"0")] @ code1 @
            [Mips.LABEL trueLabel, Mips.LI (place,"1"), Mips.LABEL falseLabel]
        end

    | Fasto.Less (e1,e2,pos) => 
        let val trueLabel = "_true_"^newName()
            val falseLabel = "_fals_"^newName()
            val endLabel = "_endif_"^newName()
            val code1 = compileCond e vtable trueLabel falseLabel
        in  [Mips.LI (place,"0")] @ code1 @
            [Mips.LABEL trueLabel, Mips.LI (place,"1"), Mips.LABEL falseLabel]
        end



(*********************************************************)
(*** Indexing: 1. generate code to compute the index   ***)
(***           2. check index within bounds (TO DO)    ***)
(***           3. add the start address with the index ***)
(***           4. get the element at that address      ***)
(*********************************************************)
    | Fasto.Index (x,e,tp,pos) => 
            let val ind      = "_arr_ind_"^newName()
                val ind_code = compileExp e vtable ind
                val arr_reg  = "_arr_reg_"^newName()
                    (* store in arr_reg the start of the data segment *)
                val arr_beg = case (SymTab.lookup x vtable) of
                                NONE => raise Error ("Name "^x^" not found", pos)
                              | SOME reg_name => reg_name
                val prolog = [Mips.LW(arr_reg, arr_beg, "4")]
                    (* code to check bounds *)		
		val arr_szeCB = "_arr_szeCB_"^newName()
		val arr_label1 = "_arr_label1CB_"^newName()
		val arr_label2 = "_arr_label2CB_"^newName()
		val arr_label22 = "_arr_label2CB2_"^newName()
                val check_code = check_bounds(arr_beg, ind, pos, arr_szeCB, arr_label1, arr_label2) 
                   (* for INT/ARRAY: ind *= 4 else ind is unchanged *)
                    (* array_var += index; place = *array_var *)
                val epilog = 
                    case tp of
                      Fasto.Char(p) =>[ Mips.ADD(arr_reg,arr_reg,ind), Mips.LB(place,arr_reg,"0") ]
                    | Fasto.Bool(p) =>[ Mips.ADD(arr_reg,arr_reg,ind), Mips.LB(place,arr_reg,"0") ]
                    | oterwise => [ Mips.SLL(ind,ind,"2"), Mips.ADD(arr_reg,arr_reg,ind), 
                                    Mips.LW(place,arr_reg,"0") ]
            in ind_code @ prolog @ check_code @ epilog
            end

(**************************************)
(*** Second Order Functions (SOF)   ***)
(***   iota, replicate, map, reduce ***)
(**************************************)
(*project added scan*)
    | Fasto.Scan  (fid,eExpression, lst, eltp, rtp, pos) => 
        let val lst_reg = "_arr_reg_"  ^newName()
            val inp_addr= "_arr_i_reg_"^newName() 
            val sz_reg  = "_size_reg_" ^newName()
            val e_reg  = "_e_reg_" ^newName()
            val lst_code  = compileExp lst vtable lst_reg
            val e_code  = compileExp eExpression vtable e_reg
	    val last_r = "_last_reg_" ^newName()

            (************************************************************************)
            (* i = loop count, r = the register that stores the computed f(i) value *)
            (* How To Compute?                                                      *)
            (*  1. load the value stored in lst(i) in inp_reg                       *)
            (*  2. apply mapped f with register r as place, i.e.,                   *) 
            (*       call ApplyRegs on fid and inp_reg                              *)
            (************************************************************************)
            fun loopfun(i, r) = if ( getElSize eltp = 1 )
                                then Mips.ADDI(last_r,r,"0")::Mips.LB(r, inp_addr, "0")
                                     :: ApplyRegs(fid, [last_r,r], r, pos) 
                                     @ [Mips.ADDI(inp_addr, inp_addr, "1")]
                                else(Mips.ADDI(last_r,r,"0")::Mips.LW(r, inp_addr, "0")
                                     	:: ApplyRegs(fid, [last_r,r], r, pos)
                                     	@ [Mips.ADDI(inp_addr, inp_addr, "4")] )


	(*Its possible to remove the added items from this compileDoLoop and extract it and use the actual comileloopcfunc*)
	  fun scanDoLoop( el_sz : int, n_reg : string, e_reg : string, arr_reg : string, 
        	             f : string*string->Mips.MipsProg, pos ) : Mips.MipsProg = 
        		let val i_reg     = "_ind_var_" ^newName()
        	    val res_reg   = "_res_i_reg"^newName()
        	    val tmp_reg   = "_tmp_reg_" ^newName()
        	    val loop_beg  = "_loop_beg_"^newName()
        	    val loop_end  = "_loop_end_"^newName()
        	    val addr_reg  = "_arr_loc_" ^newName() 
(*add e to array*)  val code_add_e = case el_sz of
				4 =>[Mips.SW(res_reg, addr_reg, "0"),Mips.ADDI(addr_reg,addr_reg, "4") ] 
			       |1 => [Mips.SB(res_reg, addr_reg, "0"),Mips.ADDI(addr_reg,addr_reg, "1") ]
			       |otherwise => raise Error("The Only Valid Element-Sizes Are 1 and 4. Error",pos)

        	    val header    = [ Mips.LW(addr_reg, arr_reg, "4"), Mips.MOVE(i_reg, "0"), 
				      Mips.ADDI(res_reg, e_reg, "0")(*set last result to e*)
				      ] @ code_add_e @ [
        	                      Mips.LABEL(loop_beg),Mips.SUB(tmp_reg, i_reg, n_reg), 
        	                      Mips.BGEZ(tmp_reg, loop_end)
        	                    ]
        	    val code_fi   = f(i_reg, res_reg)
        	    val code_assign  = 
        	          case el_sz of
        	            4 => [ Mips.SW(res_reg,addr_reg,"0"), Mips.ADDI(addr_reg,addr_reg,"4") ]
        	          | 1 => [ Mips.SB(res_reg,addr_reg,"0"),Mips.ADDI(addr_reg,addr_reg,"1") ] 
        	          | otherwise => raise Error("The Only Valid Element-Sizes Are 1 and 4. Error",pos)
        	    val epilog = [ Mips.ADDI(i_reg,i_reg,"1"), Mips.J loop_beg, Mips.LABEL loop_end ]
        	in header @ code_fi @ code_assign @ epilog
        	end





        (* we use sz_reg to hold the size of the input/output array *)
        in lst_code @ [Mips.LW(sz_reg, lst_reg, "0"), Mips.ADDI(sz_reg, sz_reg, "1")] @ dynalloc(sz_reg, place, rtp) @ 
           [Mips.LW(inp_addr, lst_reg, "4")] @ e_code @
           scanDoLoop( getElSize rtp, sz_reg,e_reg, place, loopfun, pos )
        end
(*project added length*)
    | Fasto.Length(e,t,p) => 
        let val lst_reg = "_arr_reg_"  ^newName()            
            val lst_code  = compileExp e vtable lst_reg
        in lst_code @ [ Mips.LW(place, lst_reg, "0")]
        end
    | Fasto.Iota (e, (line,col)) =>
        let val sz_reg  = "_size_reg_"^newName()
            val code_sz = compileExp e vtable sz_reg

            (******************************************)
            (** code to check that array size, N > 0 **)
            (**   if N-1 >= 0 then JumpTo safe_lab   **)
            (**   JumpTo "_IllegalArrSizeError_"     **)
            (**   safe_lab: ...                      **) 
            (******************************************)
            val safe_lab = "_safe_lab__"^newName()
            val checksize = [ 
                Mips.ADDI(sz_reg,sz_reg,"-1"),  Mips.BGEZ(sz_reg, safe_lab), 
                Mips.LI("5",makeConst line),    Mips.J "_IllegalArrSizeError_",            
                Mips.LABEL(safe_lab),           Mips.ADDI(sz_reg,sz_reg,"1")
              ]
        in  code_sz @ checksize @ dynalloc( sz_reg, place, Fasto.Int((line,col)) ) @ 
            compileDoLoop( 4, sz_reg, place, ( fn(i,r) => [Mips.MOVE(r,i)] ), (line,col) )
        end

    | Fasto.Replicate (n, el, tp, (line,col)) => 
        let val sz_reg  = "_size_reg_"^newName()
            val el_reg  = "_el_reg_"  ^newName() 
            val code_sz = compileExp n  vtable sz_reg
            val code_el = compileExp el vtable el_reg

            (******************************************)
            (** code to check that array size, N > 0 **)
            (** see implementation of iota           **)
            (******************************************)
            val safe_lab = "_safe_lab__"^newName()
            val checksize = [ 
                Mips.ADDI(sz_reg,sz_reg,"-1"),  Mips.BGEZ(sz_reg, safe_lab), 
                Mips.LI("5",makeConst line),    Mips.J "_IllegalArrSizeError_",            
                Mips.LABEL(safe_lab),           Mips.ADDI(sz_reg,sz_reg,"1")
              ]
        in code_sz @ checksize @ code_el @ dynalloc(sz_reg,place,tp) @ 
           compileDoLoop( getElSize tp, sz_reg, place, ( fn(i, r) => [Mips.MOVE(r,el_reg)] ), (line,col) )
        end

    | Fasto.Map  (fid, lst, eltp, rtp, pos) => 
        let val lst_reg = "_arr_reg_"  ^newName()
            val inp_addr= "_arr_i_reg_"^newName() 
            val sz_reg  = "_size_reg_" ^newName()
            val lst_code  = compileExp lst vtable lst_reg

            (************************************************************************)
            (* i = loop count, r = the register that stores the computed f(i) value *)
            (* How To Compute?                                                      *)
            (*  1. load the value stored in lst(i) in inp_reg                       *)
            (*  2. apply mapped f with register r as place, i.e.,                   *) 
            (*       call ApplyRegs on fid and inp_reg                              *)
            (************************************************************************)
            fun loopfun(i, r) = if ( getElSize eltp = 1 )
                                then Mips.LB(r, inp_addr, "0")
                                     :: ApplyRegs(fid, [r], r, pos) 
                                     @ [Mips.ADDI(inp_addr, inp_addr, "1")]
                                else Mips.LW(r, inp_addr, "0")
                                     :: ApplyRegs(fid, [r], r, pos)
                                     @ [Mips.ADDI(inp_addr, inp_addr, "4")]

        (* we use sz_reg to hold the size of the input/output array *)
        in lst_code @ [ Mips.LW(sz_reg, lst_reg, "0")] @ dynalloc(sz_reg, place, rtp) @ 
           [Mips.LW(inp_addr, lst_reg, "4")] @
           compileDoLoop( getElSize rtp, sz_reg, place, loopfun, pos )
        end
(*Operator, List, ElementType, ReturnType, Position*)
    | Fasto.MapOP  (oper, lst, eltp, optp, pos) => 
        (* let  *)
            (* val lst_reg = "_arr_reg_"  ^newName() *)
            (* val inp_addr= "_arr_i_reg_"^newName()  *)
            (* val sz_reg  = "_size_reg_" ^newName() *)
            (* val lst_code  = compileExp lst vtable lst_reg *)

            (* [>**********************************************************************<] *)
            (* [> i = loop count, r = the register that stores the computed f(i) value <] *)
            (* [> How To Compute?                                                      <] *)
            (* [>  1. load the value stored in lst(i) in inp_reg                       <] *)
            (* [>  2. apply mapped f with register r as place, i.e.,                   <]  *)
            (* [>       call ApplyRegs on fid and inp_reg                              <] *)
            (* [>**********************************************************************<] *)
            (* fun loopfun(i, r) = if ( getElSize eltp = 1 ) *)
                                (* then Mips.LB(r, inp_addr, "0") *)
                                     (* :: ApplyRegs(oper, [r], r, pos)  *)
                                     (* @ [Mips.ADDI(inp_addr, inp_addr, "1")] *)
                                (* else Mips.LW(r, inp_addr, "0") *)
                                     (* :: ApplyRegs(oper, [r], r, pos) *)
                                     (* @ [Mips.ADDI(inp_addr, inp_addr, "4")] *)

        (* [> we use sz_reg to hold the size of the input/output array <] *)
        (* in  *)
           if optp = Fasto.Int pos 
            then raise Error("bool", (0,0))
            else raise Error("notbool", (0,0))
           (* lst_code @ [ Mips.LW(sz_reg, lst_reg, "0")] @ dynalloc(sz_reg, place, rtp) @  *)
           (* [Mips.LW(inp_addr, lst_reg, "4")] @ *)
           (* compileDoLoop( getElSize rtp, sz_reg, place, loopfun, pos ) *)
        (* end *)
    (****************************************************)
    (*** CompileDoLoop assumes the result is an array ***)
    (***   so we cannot use it here, instead we write ***)
    (***   the whole assembly and use (only) helper   ***)
    (***   function  ApplyRegs that applies the binary***)
    (***   operator of reduce on the accumulator      ***)
    (***   register, i.e., place, and an element of   ***)
    (***   input array, i.e., tmp_reg                 ***)
    (*** lst_reg iterates over the array              ***)
    (*** i_reg   holds the loop count (i)             ***)
    (*** sz_reg  holds the length of the array        ***)
    (****************************************************) 
    | Fasto.Reduce  (bop,ne,lst,tp,pos) => 
        let val lst_reg   = "_arr_reg_"  ^newName()
            val sz_reg    = "_size_reg_" ^newName()
            val tmp_reg   = "_tmp_reg_" ^newName()
            val i_reg     = "_ind_var_" ^newName()
            val loop_beg  = "_loop_beg_"^newName()
            val loop_end  = "_loop_end_"^newName()
            val is_1      = ((getElSize tp) = 1)
 
            val lst_code  = compileExp lst vtable lst_reg
            val  ne_code  = compileExp ne  vtable tmp_reg             
            val header    = [ Mips.LW(lst_reg,lst_reg,"4"),   Mips.MOVE(i_reg,"0"), 
                              Mips.MOVE(place,tmp_reg),       Mips.LABEL(loop_beg), 
                              Mips.SUB(tmp_reg,i_reg,sz_reg), Mips.BGEZ(tmp_reg, loop_end) ] @
                ( if ( is_1 ) then [ Mips.LB(tmp_reg,lst_reg,"0"), Mips.ADDI(lst_reg,lst_reg,"1") ] 
                              else [ Mips.LW(tmp_reg,lst_reg,"0"), Mips.ADDI(lst_reg,lst_reg,"4") ] )

        in lst_code @ [ Mips.LW(sz_reg,lst_reg,"0")] @ ne_code @ 
           header   @ ApplyRegs(bop,[place,tmp_reg],place,pos) @ 
           [ Mips.ADDI(i_reg,i_reg,"1"), Mips.J loop_beg, Mips.LABEL loop_end ]
        end
    | _ => raise Error("Compiler: Unknown Token from Intepreter", (0,0))

  (**********************************)
  (* pushing arguments on the stack *)
  (**********************************)
  and loadArgs [] vtable reg =
        ([], reg)
    | loadArgs (e::es) vtable reg =
      let
	  val t1 = "_funarg_"^newName()
          val code1 = compileExp e vtable t1
	  val (code2, maxreg) = loadArgs es vtable (reg+1)
      in
          (   code1                             (* compute arg *)
            @ [Mips.MOVE (makeConst reg,t1)] (* store in reg *)
            @ code2, maxreg)
      end

  (* compile condition *)
  and compileCond c vtable tlab flab =
    case c of
      Fasto.Var(nm,pos) => 
        let val reg_var  = ""^newName() 
            val code_var = compileExp c vtable reg_var
        in code_var @ [Mips.BEQ (reg_var, "0",flab), Mips.J tlab]
        end
    | Fasto.Equal (e1,e2,pos) =>
        let
          val t1 = "_eq1_"^newName()
          val t2 = "_eq2_"^newName()
          val code1 = compileExp e1 vtable t1
          val code2 = compileExp e2 vtable t2
	in
	  code1 @ code2 @
	  [Mips.BEQ (t1,t2,tlab), Mips.J flab]
	end

    | Fasto.Less (e1,e2,pos) =>
        let
	  val t1 = "_less1_"^newName()
	  val t2 = "_less2_"^newName()
          val code1 = compileExp e1 vtable t1
          val code2 = compileExp e2 vtable t2
	in
	  code1 @ code2 @
	  [Mips.SLT (t1,t1,t2), Mips.BNE (t1,"0",tlab),Mips.J flab]
	end
(*
    | Fasto.Not (c1,pos) => compileCond c1 vtable flab tlab
    (* jumping code for and and or, Mips instructions unused *)
    | Fasto.And (c1,c2,pos) => 
        let
	  val l1 = "_and_"^newName()
          val code1 = compileCond c1 vtable l1 flab
          val code2 = compileCond c2 vtable tlab flab
	in
	  code1 @ [Mips.LABEL l1] @ code2
	end
    | Fasto.Or (c1,c2,pos) => 
        let
	  val l1 = "_or_"^newName()
          val code1 = compileCond c1 vtable tlab l1
          val code2 = compileCond c2 vtable tlab flab
	in
	  code1 @ [Mips.LABEL l1] @ code2
	end
*)
(* implicit num->bool conversion (all !=0 is true) *)
    | _ =>  let val t1 = "_exp_"^newName()
                val code1 = compileExp c vtable t1
            in  code1 @ [Mips.BNE (t1,"0",tlab), Mips.J flab]
            end

  and compileDec (Fasto.Dec (s,e,pos)) vtable =
        let val t = "_letBind_"^newName()
            val code = compileExp e vtable t
        in (code, SymTab.bind s t vtable)  (* (code, (s,t)::vtable)  *)
        end

  (* code for saving and restoring callee-saves registers *)
  fun stackSave currentReg maxReg savecode restorecode offset =
    if currentReg > maxReg
    then (savecode, restorecode, offset)  (* done *)
    else stackSave (currentReg+1)
                   maxReg
                   (Mips.SW (makeConst currentReg,
                                 SP,
                                 makeConst offset)
                    :: savecode) (* save register *)
                   (Mips.LW (makeConst currentReg,
                                 SP,
                                 makeConst offset)
                    :: restorecode) (* restore register *)
                   (offset-4) (* adjust offset *)

  (* add function arguments to symbol table *)
  and getArgs     []      vtable   _     = ([], vtable) 
    | getArgs ((v,_)::vs) vtable nextReg =
           if nextReg > maxCaller
             then raise Error ("Passing too many arguments!", (0,0))
             else
               let val vname = v ^ "_name_" ^ newName()
                   val vtable1 = SymTab.bind v vname vtable (*   (v,vname)::vtable   *)
                   val (code2,vtable2) = getArgs vs vtable1 (nextReg + 1)
               in ([Mips.MOVE (vname, makeConst nextReg)]
                   @ code2, vtable2)
               end

  (* compile function declaration *)
  and compileFun (fname, resty, args, exp, (line,col)) =
        let (* make a vtable from bound formal parameters,
               then evaluate expression in this context, return it *)
          (* arguments passed in registers, "move" into local vars. *)
          val (argcode, vtable_local) = getArgs args [] minReg
          (* return value in register 2 *)
          val rtmp = fname ^"_res_"^ newName()
          val returncode  = [Mips.MOVE ("2",rtmp)] (* move return val to R2 *)
          val body = compileExp exp vtable_local rtmp (* target expr *)
          val (body1, _, maxr)
                     = RegAlloc.registerAlloc   (* call register allocator *)
                        (argcode @ body @ returncode) 
                        ["2"] 2 maxCaller maxReg
          val (savecode, restorecode, offset) (* save/restore callee-saves *)
              = stackSave (maxCaller+1) maxr [] [] (~8)
        in  [Mips.COMMENT ("Function " ^ fname),
             Mips.LABEL fname,       (* function label *)
             Mips.SW (RA, SP, "-4")] (* save return address *)
          @ savecode                 (* save callee-saves registers *)
          @ [Mips.ADDI (SP,SP,makeConst offset)]   (* SP adjustment *)
          @ body1                    (* code for function body *)
          @ [Mips.ADDI (SP,SP,makeConst (~offset))] (* move SP up *)
          @ restorecode              (* restore callee-saves registers *)
          @ [Mips.LW (RA, SP, "-4"),  (* restore return addr *)
             Mips.JR (RA, [])]       (* return *)
        end

(************************************************)
(************************************************)
(*** The main entry point for Code Generation ***)
(***  compiles a program, i.e., a list of fun ***)
(***  declarations:                           ***)
(*** ``concat(List.map compileFun funs)''     ***)
(***    compiles all funs and concatentates   ***)
(***    the resulted list of instructions.    ***)
(***  Static code is added to implement built-***)
(***    in functions 'ord' and 'chr' and IO,  ***)
(***    e.g., putchar, getchar                ***) 
(************************************************)
(************************************************)
  fun compile funs =   
    let val () = stringTable := []
        val funsCode = List.concat (List.map compileFun funs)
        val (stringinit_sym, stringdata)
          = ListPair.unzip (List.map buildString (!stringTable))
        val (stringinit,_,_)
          = case stringinit_sym of
                [] => ([],[],0)
              | other => RegAlloc.registerAlloc (* call register allocator *)
                             (List.concat stringinit_sym) 
                             ["2"] 2 maxCaller maxReg
    in
        [Mips.TEXT "0x00400000",
         Mips.GLOBL "main"]
         (* initialisation: heap pointer and string pointers *)
      @ (Mips.LA (HP, "_heap_"):: stringinit)
        (* jump to main (and stop after returning) *)
      @ [Mips.JAL ("main",[])]
      @ (* stop code *)
        [Mips.LABEL "_stop_",
         Mips.LI ("2","10"), (* syscall exit = 10 *)
         Mips.SYSCALL]
      @  (* code for functions *)
        funsCode
         (* pre-defined ord: char -> int and chr: int -> char *)
      @ [Mips.LABEL "ord", (* char returned unmodified, interpreted as int *)
         Mips.JR (RA,[]),
         Mips.LABEL "chr", (* int values are truncated to 8 bit (ASCII), *)
	 Mips.ANDI ("2", "2", makeConst 255),
         Mips.JR (RA,[])]
         (* built-in read and write functions *)
      @ [Mips.LABEL "putint",     (* putint function *)
	 Mips.ADDI(SP,SP,"-8"),
	 Mips.SW ("2",SP,"0"),    (* save used registers *)
	 Mips.SW ("4",SP,"4"),
	 Mips.MOVE ("4","2"),     (* convention: number to be written in r2 *)
	 Mips.LI ("2","1"),       (* write_int syscall *)
	 Mips.SYSCALL,
	 Mips.LI ("2","4"),       (* writestring syscall *)
	 Mips.LA("4","_space_"),
	 Mips.SYSCALL,            (* write CR *)
	 Mips.LW ("2",SP,"0"),    (* reload used registers *)
	 Mips.LW ("4",SP,"4"),
	 Mips.ADDI(SP,SP,"8"),
	 Mips.JR (RA,[]),

	 Mips.LABEL "getint",     (* getint function *)
	 Mips.LI ("2","5"),       (* read_int syscall *)
	 Mips.SYSCALL,
	 Mips.JR (RA,[])]
      @  (* putChar *)
        [ Mips.LABEL "putchar",
	  Mips.ADDI(SP,SP,"-8"),
	  Mips.SW ("2",SP,"0"),    (* save used registers *)
	  Mips.SW ("4",SP,"4"),
	  Mips.MOVE ("4","2"),     (* convention: number to be written in r2 *)
          Mips.LI("2", "11"),
          Mips.SYSCALL,
	  Mips.LI ("2","4"),       (* writestring syscall *)
	  Mips.LA("4","_space_"),
	  Mips.SYSCALL,            (* write CR *)
	  Mips.LW ("2",SP,"0"),    (* reload used registers *)
	  Mips.LW ("4",SP,"4"),
	  Mips.ADDI(SP,SP,"8"),
	  Mips.JR (RA,[])
        ]
      @  (* array allocation *)
        [ Mips.LABEL "dynalloc", Mips.ADDI("4", "2", "0"), 
          Mips.LI("2","9"), Mips.SYSCALL, Mips.JR (RA,[]) 
        ]
      @  (* getChar *)
        [ Mips.LABEL "getchar",
          Mips.ADDI(SP,SP,"-8"),
          Mips.SW ("4",SP,"0"),    (* save used registers *)
	  Mips.SW ("5",SP,"4"),
          Mips.LI("2", "12"),
          Mips.SYSCALL,
          Mips.MOVE("5","2"),      (* temporarily move the result in reg $5*)
          Mips.LI ("2","4"),       (* writestring syscall *)
	  Mips.LA("4","_cr_"),
	  Mips.SYSCALL,            (* write CR *)
          Mips.MOVE("2", "5"),     (* put the result back in $2*)
          Mips.LW ("4", SP, "0"),  (* restore registers *)
          Mips.LW ("5", SP, "4"),
          Mips.ADDI(SP,SP,"8"),
          Mips.JR (RA,[])
        ]
      @ (* putstring *)
        [ Mips.LABEL "putstring",  (* putstring function *)
          Mips.ADDI(SP,SP,"-4"),   
          Mips.SW ("4", SP, "0"),  (* save register $4 *)
	  Mips.MOVE ("4","2"),     (* move string pointer to r4 *)
	  Mips.LI ("2","4"),       (* write_string syscall *)
	  Mips.SYSCALL,
          Mips.MOVE("2", "4"),
          Mips.LW ("4", SP, "0"),  (* restore register $4 *)
          Mips.ADDI(SP,SP,"4"),    
	  Mips.JR (RA,[])
        ]
      @  (* getString *)
        [ Mips.LABEL "getstring",  (* getstring function *)
	  Mips.MOVE("4",HP),       (* allocate at HP *)
          Mips.MOVE("5","2"),      (* N bytes *)
	  Mips.LI ("2","8"),       (* read_string syscall *)
	  Mips.SYSCALL,
	  Mips.MOVE("2",HP),       (* return HP *)
	  Mips.ADD(HP,HP,"5"),     (* increase HP by N *)
	  Mips.JR (RA,[])
        ]
      @  (* fixed error code for indexing errors *)
        [Mips.LABEL "_IllegalArrSizeError_",
	 Mips.LA ("4","_IllegalArrSizeString_"),
	 Mips.LI ("2","4"), Mips.SYSCALL, (* print string *)
	 Mips.MOVE ("4","5"),
	 Mips.LI ("2","1"), Mips.SYSCALL, (* print line number *)
	 Mips.LA ("4","_cr_"),
	 Mips.LI ("2","4"), Mips.SYSCALL, (* print CR *)
	 Mips.J "_stop_",
	(*Fixed error code for test*)
	Mips.LABEL "_test_",
	 Mips.LI ("2","4"), Mips.SYSCALL, (* print string *)
	 Mips.MOVE ("4","5"),
	 Mips.LI ("2","1"), Mips.SYSCALL, (* print line number *)
	 Mips.LA ("4","_cr_"),
	 Mips.LI ("2","4"), Mips.SYSCALL, (* print CR *)
	 Mips.J "_stop_",

	(*Fixed error code for out of bounds error*)
	Mips.LABEL "_IndexOutOfBoundsError_",
	 Mips.LA ("4","_IndexOutOfBoundsString_"),
	 Mips.LI ("2","4"), Mips.SYSCALL, (* print string *)
	 Mips.MOVE ("4","5"),
	 Mips.LI ("2","1"), Mips.SYSCALL, (* print line number *)
	 Mips.LA ("4","_cr_"),
	 Mips.LI ("2","4"), Mips.SYSCALL, (* print CR *)
	 Mips.J "_stop_",
         (* Fixed data (for error message) *)
	 Mips.DATA "",
	 Mips.LABEL "_cr_",       (* carriage return string *)
	 Mips.ASCIIZ "\n",
         Mips.LABEL "_space_",
         Mips.ASCIIZ " ",
	 Mips.LABEL "_IllegalArrSizeString_",
	 Mips.ASCIIZ "Error: Array size less or equal to 0 at line ",
	 Mips.LABEL "_IndexOutOfBoundsString_",
	 Mips.ASCIIZ "Error: Array index out of bounds at line "]
         (* String literals *)
       @ (Mips.COMMENT "String Literals" :: 
          List.concat stringdata)
         (* Heap (to allocate arrays in, word-aligned) *)
       @ [Mips.ALIGN "2",
	  Mips.LABEL "_heap_",
	  Mips.SPACE "100000"]
    end

end

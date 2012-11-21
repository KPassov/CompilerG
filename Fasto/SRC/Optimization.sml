structure Optimization  = struct
    open Fasto

  (* Use "raise Error (message,position)" for error messages *)
  exception Error of string*(int*int)
  exception NotInSymTab of string 

  (* Name generator.  Call with, e.g., t1 = "tmp"^newName () *)
  val counter = ref 0

  fun newName () = (counter := !counter + 1;
                  "_" ^ Int.toString (!counter)^ "_")

  fun zip (x::xs) (y::ys) = (x,y) :: (zip xs ys)
    | zip _       _       = [];

  (******************************************************************)
  (*** Adding/removing special funs "ord" and "chr" from FunSymTab***)
  (******************************************************************)
  fun add_spec_funs(funlst : FunDec list) : FunDec list = 
      let val noPos = (0,0)
          val specfuns = [("ord", Fasto.Int  noPos,  (* ord: char->int *)
                                 [("ft_prm_"^newName(), Fasto.Char noPos)], 
                                 Num(1,noPos), noPos)      
                         ,("chr", Fasto.Char noPos,  (* chr: int->char *)
                                 [("ft_prm_"^newName(), Fasto.Int  noPos)], 
                                 CharLit(#"a",noPos), noPos)
                         ]
      in specfuns@funlst
      end        

  fun rem_spec_funs(funlst : FunDec list) : FunDec list = 
        List.filter 
            (fn (fid, rtp, fargs, body, pdecl) => 
                (fid<>"ord" andalso fid<>"chr")  )
            funlst


  (******************************************************************)
  (*** Renaming Internal Variables of a Function with Unique Names***)
  (******************************************************************)
  fun unique_rename( exp : Exp, vtab ) : Exp = case exp of
         Let( Dec(id,e1,p1), e2, p2 ) => 
             let val new_id   = id^"_ft_exp_"^newName()
                 val new_vtab = SymTab.bind id new_id vtab
             in Let( Dec(new_id, unique_rename(e1, new_vtab), p1 ), 
                                 unique_rename(e2, new_vtab), p2    )
             end
       | Plus (e1, e2, p) =>  Plus ( unique_rename(e1, vtab), unique_rename(e2, vtab),  p )
       | Minus(e1, e2, p) =>  Minus( unique_rename(e1, vtab), unique_rename(e2, vtab),  p )
       | Equal(e1, e2, p) =>  Equal( unique_rename(e1, vtab), unique_rename(e2, vtab),  p )
       | Less (e1, e2, p) =>  Less ( unique_rename(e1, vtab), unique_rename(e2, vtab),  p )
       | If(e1, e2, e3, p)=>  If   ( unique_rename(e1, vtab), 
                                     unique_rename(e2, vtab), 
                                     unique_rename(e3, vtab), p )
       | Apply(id,args,p) => Apply ( id, map (fn x => unique_rename(x, vtab)) args,  p )
       | Map(id,e,t1,t2,p)=> Map   ( id, unique_rename(e, vtab), t1, t2, p )
       | Reduce(id,e,l,t,p)=>Reduce( id, unique_rename(e, vtab), unique_rename(l, vtab), t, p )
       | Iota (e, p)      => Iota  ( unique_rename(e, vtab), p )
       | Replicate(e,n,t,p)=>Replicate( unique_rename(e, vtab), unique_rename(n, vtab), t, p )
       | Write (e,t,p)    => Write ( unique_rename(e, vtab), t, p )
       | Index(id,e,t,p)  => 
            let val new_id   = case SymTab.lookup id vtab of NONE => id | SOME m => m
            in  Index( new_id, unique_rename(e, vtab), t, p )
            end
       | Var(id,p) => let val new_id   = case SymTab.lookup id vtab of NONE => id | SOME m => m 
                      in  Var( new_id, p ) end
       | _ => exp


  (*******************************************************************)
  (*** Dead-Function Elimination: Implement function ``live_funs''!***)
  (***   (delete the current implementation which identifies       ***)
  (***    all functions as live)                                   ***)
  (*******************************************************************)
  fun getFunId  (fid ,_,_,_,_) = fid
  fun getFunBody(_,_,_,body,_) = body

  fun live_funs ( 
            exp    : Fasto.Exp, 
            livefs : string list, 
            ftab   : (string * Fasto.FunDec) list  
      ) : string list 
    = map (fn (fid, fdec) => fid) ftab


  fun dead_fun_elim ( funs : Fasto.FunDec list ) : FunDec list = 
    let val ftab = map (fn f => (getFunId(f), f)) funs
    in  case (SymTab.lookup "main" ftab) of
          NONE => raise Error("Function main not found in SymTab", (0,0))
        | SOME mainf => 
            let val livefuns = live_funs(getFunBody(mainf), ["main"], ftab)
                fun getfun id = case (SymTab.lookup id ftab) of
                                  SOME f => f
                                | NONE   => raise NotInSymTab(id)
            in  (map getfun livefuns)
            end
    end

  (***************************************************************)
  (*** Map Fusion:   Two Phase Parse:                          ***)
  (*** 1. We propagate the map-fusion information top-down     ***)
  (***    a. Variables are assumed to have unique names in the ***)
  (***       function body->the renaming phase preceeds fusion ***)
  (***    b. Each Fasto.Let node associated with a map inherits***)
  (***       parrent-map information via symbol table "vtab"   ***)
  (***       and merges it with its own info. It also          ***)
  (***       initializes its reference counter and increases   ***)
  (***     the reference counter of its "parent" map node whith***)
  (***       whom it might fuse later.  If in the return pass  ***)
  (***       the current map node has reference count 1, i.e., ***)
  (***       only one map node uses it,then it sets its counter***)
  (***       to -1, signaling to its child that map fusion     ***)
  (***       is possible!                                      ***)
  (*** 2. see the "map_fusion_gen" function                    ***) 
  (***************************************************************)


  (***            LET node    RefCount RefCountMap  var_id   funs to comp   ***)  
  type SymTabEl = Fasto.Exp * int ref * int ref * ( string * string list ) list

  (** returns the persistent symbol table of the expression **)
  fun map_fusion_gather( exp : Exp, (vtab, ok) )   = 
    case exp of
      Let( Dec(id,e1,p1), e2, p2 ) =>
          let val count    = ref 0
              val countmap = ref 0
              val mapinf   = case e1 of
                  Map(fid, Var(arr_id,p), t1, t2, pos) =>
                      let (** propagate the potential-fusion information from parent **)
                          val (e3,ct,ctm,mapparinf) = case (SymTab.lookup arr_id vtab) of 
                                                        SOME m => m
                                                      | NONE   => raise NotInSymTab(arr_id)
                          val meincl = map (fn (idarr, fcomps) => (idarr, fid::fcomps)) mapparinf
                          val () = if(length(mapparinf) <> 0) then (  (*ct := !ct + 1;*) ctm := !ctm+1) else ()
                      in  (arr_id, [fid])::meincl
                      end 
                | otherwise => []

              val (vtab1, ok1) = map_fusion_gather( e1, (vtab,ok) )
              val  vtab2       = SymTab.bind id (exp, count, countmap, mapinf) vtab1
              val (vtab3, ok3) = map_fusion_gather( e2, (vtab2,ok1) )

              val (mye,myct,myctmap,myinf) = case (SymTab.lookup id vtab3) of   
                                               SOME m => m
                                             | NONE   => raise NotInSymTab(id)

              val succ = (!myct = !myctmap andalso !myctmap = 1)
              val ()   = if(succ) then myct := ~1 else ()
          in (vtab3, succ orelse ok3)
          end
             
       | Plus (e1, e2, p) =>  map_fusion_gather(e2, map_fusion_gather(e1, (vtab,ok)))
       | Minus(e1, e2, p) =>  map_fusion_gather(e2, map_fusion_gather(e1, (vtab,ok)))
       | Equal(e1, e2, p) =>  map_fusion_gather(e2, map_fusion_gather(e1, (vtab,ok)))
       | Less (e1, e2, p) =>  map_fusion_gather(e2, map_fusion_gather(e1, (vtab,ok)))
       | If(e1, e2, e3, p)=>  map_fusion_gather(e3, map_fusion_gather(e2, map_fusion_gather(e1, (vtab,ok))))
       | Apply(id,args,p) =>  foldl (fn(x,y)=> map_fusion_gather(x,y)) (vtab,ok) args
       | Map(id,e,t1,t2,p)=>  map_fusion_gather(e, (vtab,ok)) 
       | Reduce(id,e,l,t,p)=> map_fusion_gather(l, map_fusion_gather(e, (vtab,ok)))
       | Iota (e, p)      =>  map_fusion_gather(e, (vtab,ok)) 
       | Replicate(e,n,t,p)=> map_fusion_gather(e, map_fusion_gather(n, (vtab,ok)))
       | Write (e,t,p)    =>  map_fusion_gather(e, (vtab,ok)) 
       | Index(id,e,t,p)  => 
            let val (e1,ct,ctm,mapparinf) = case (SymTab.lookup id vtab) of  
                                              SOME m => m
                                            | NONE   => raise NotInSymTab(id)
                val () = ct := !ct + 1
            in  map_fusion_gather(e, (vtab,ok)) 
            end
       | Var(id,p) => 
            let val (e1,ct,ctm,mapparinf) = case (SymTab.lookup id vtab) of  
                                              SOME m => m
                                            | NONE   => raise NotInSymTab(id)
                val () = ct := !ct + 1
            in (vtab, ok)
            end
       | _ => (vtab, ok)

  (**********************************************************)
  (** Bottom-up parsing constructs the map-fused AbSyn     **)
  (** A fused node deletes itself as fusion makes it unused**)
  (** The maximal fusion is chosen, under the conservative **)
  (** condition that the fused array is not used anywhere. **) 
  (** Returns an abstract syntax tree with map-fused nodes **)
  (**********************************************************)

  fun make_funcomp( funids, funs : FunDec list ) : (FunDec * string) = 
    let fun make_funcomp_exp(  [],   elid ) = (Fasto.Var(elid, (0,0)), "_ft_exp_"^newName())
          | make_funcomp_exp( f::fs, elid ) = 
               let val (exp, fid) = make_funcomp_exp(fs, elid)
                   val let_var = "ft_var_"^newName()
               in  ( Fasto.Let( Fasto.Dec  ( let_var, exp, (0,0) ), 
                                Fasto.Apply( f, [Fasto.Var(let_var,(0,0))], (0,0) ),
                                (0,0) 
                              )
                   , f^"o"^fid 
                   )
                   (***   ( Fasto.Apply( f, [exp], (0,0) ), f^"o"^fid )    ***)
               end
        fun find_id(fid) = 
            case List.find (fn (ff, tp, ag, e, p) => ff = fid ) funs of
              SOME m => m
            | NONE   => raise Error("Function: "^fid^" not found in FunDecs!", (0,0))

        val elid      = "arg__ft_exp_"^newName()
        val (exp,fid) = make_funcomp_exp(funids, elid)
        val (f1, rtp , a1, body1, p1) = find_id(hd(funids))
        val (f2, rtp2, a2, body2, p2) = find_id(List.last(funids))
        val (f2argname, intp) = hd a2
        val newfun = (fid, rtp, [(elid, intp)], exp, (0,0))
    in (newfun, fid)
    end

  (** (string * string list) list -> (string * string list)  **)
(*
  fun select_max_fusion([], vtab) = 
        raise Error("Error in map_fusion_gen. Info should be non-empty!",(0,0))
    | select_max_fusion( [(arrid,fcomps)], vtab ) = (arrid, fcomps)
    | select_max_fusion( (id1,fcomps1)::(id2,fcomps2)::info, vtab ) = 
        let val (e1,ct,ctm,mapparinf) = case (SymTab.lookup id2 vtab) of 
                                          SOME m => m
                                        | NONE   => raise NotInSymTab(id2)
        in  if(!ct = ~1) then (id1,fcomps1)
            else  select_max_fusion((id2,fcomps2)::info, vtab)
        end
*)

  fun select_max_fusion([], vtab, prev) = prev
    | select_max_fusion((id1,fcomps1)::info, vtab, (id2,fcomps2)) =     
        let val (e1,ct,ctm,mapparinf) = case (SymTab.lookup id2 vtab) of   
                                               SOME m => m
                                             | NONE   => raise NotInSymTab(id2)
        in if(!ct = ~1) then select_max_fusion(info, vtab, (id1, fcomps1))
                        else (id2, fcomps2)
        end

  fun map_fusion_gen(exp : Exp, funs : FunDec list, vtab) : (Exp * FunDec list) = 
    case exp of
      Let( Dec(id,e1,p1), e2, p2 ) =>
          let val (e11, f11) = map_fusion_gen(e1, funs, vtab)
              val (e22, f22) = map_fusion_gen(e2, funs, vtab)
              val (mye,myct,myctmap,myinf) = case (SymTab.lookup id vtab) of  
                                               SOME m => m
                                             | NONE   => raise NotInSymTab(id)
              val refcount = !myct
          in  case refcount of
                ~1 => (e22, f22)
              | _  => if(myinf = []) then ( Let( Dec(id,e11,p1), e22, p2 ), f11@f22) 
                      else let val (newarr, flst) = select_max_fusion(tl myinf, vtab, hd myinf) (* select_max_fusion(List.rev myinf, vtab) *)
                           in  if(length(flst) < 2) then ( Let( Dec(id,e11,p1), e22, p2 ), f11@f22 )  (*>*)
                               else let val (newfun, newfid) = make_funcomp( flst, funs )
                                        val (rtp,intp) = case newfun of
                                                           (fffid, rettp, [(elid, inptp)], eee, ppp) => (rettp,inptp)
                                                         | otherwise => raise Error("Map fusion failed, illegal return of make_funcomp!",p2)
                                    in case e11 of
                                         Map(fid, Var(arr_id,p), t1, t2, pos) =>
                                             ( Let( Dec(id, Map(newfid,Var(newarr,p), intp, rtp, pos), p1), e22, p2),   (** t1,t2 **) 
                                               newfun::(f11@f22) )
                                       | otherwise => raise Error("Error in map_fusion_gen: Can't find MAP-FUSED NODE!",(0,0))
                                    end
                           end 
          end
             
    | Plus (e1, e2, p) =>  let val (e11,f11) = map_fusion_gen(e1, funs, vtab)
                               val (e22,f22) = map_fusion_gen(e2, funs, vtab)
                           in  ( Plus (e11, e22, p), f11@f22 )
                           end
    | Minus(e1, e2, p) =>  let val (e11,f11) = map_fusion_gen(e1, funs, vtab)
                               val (e22,f22) = map_fusion_gen(e2, funs, vtab)
                           in  ( Minus(e11, e22, p), f11@f22 )
                           end
    | Equal(e1, e2, p) =>  let val (e11,f11) = map_fusion_gen(e1, funs, vtab)
                               val (e22,f22) = map_fusion_gen(e2, funs, vtab)
                           in  ( Equal(e11, e22, p), f11@f22 )
                           end
    | Less (e1, e2, p) =>  let val (e11,f11) = map_fusion_gen(e1, funs, vtab)
                               val (e22,f22) = map_fusion_gen(e2, funs, vtab)
                           in  ( Less(e11, e22, p), f11@f22 )
                           end
    | If(e1, e2, e3, p)=>  let val (e11,f11) = map_fusion_gen(e1, funs, vtab)
                               val (e22,f22) = map_fusion_gen(e2, funs, vtab)
                               val (e33,f33) = map_fusion_gen(e3, funs, vtab)
                           in  ( If(e11, e22, e33, p), f11@f22@f33 )
                           end
    | Apply(id,args,p) =>  let val resss = map (fn x=>map_fusion_gen(x,funs,vtab)) args
                               val targs = map (fn (x,y) => x) resss
                               val tffs  = map (fn (x,y) => y) resss
                           in ( Apply(id, targs, p), foldl (op @) [] tffs )
                           end
    | Map(id,e,t1,t2,p)=>  let val (e11,f11) = map_fusion_gen(e, funs, vtab)
                           in  ( Map(id, e11, t1, t2, p), f11 )
                           end
    | Reduce(id,e,l,t,p)=> let val (e11,f11) = map_fusion_gen(e, funs, vtab)
                               val (e22,f22) = map_fusion_gen(l, funs, vtab)
                           in  ( Reduce(id, e11, e22, t, p), f11@f22 )
                           end
    | Iota (e, p)      =>  let val (e11,f11) = map_fusion_gen(e, funs, vtab)
                           in  ( Iota(e11, p), f11 )
                           end
    | Replicate(e,n,t,p)=> let val (e11,f11) = map_fusion_gen(e, funs, vtab)
                               val (e22,f22) = map_fusion_gen(n, funs, vtab)
                           in  ( Replicate(e11, e22, t, p), f11@f22 )
                           end
    | Write (e,t,p)    =>  let val (e11,f11) = map_fusion_gen(e, funs, vtab)
                           in  ( Write(e11, t, p), f11 )
                           end
    | Index(id,e,t,p)  =>  let val (e11,f11) = map_fusion_gen(e, funs, vtab)
                           in  ( Index(id, e11, t, p), f11 )
                           end
    | _ => (exp, [])


  (*************************************)
  (** Finally, Map-Fusion Driver      **)
  (*************************************)
  fun mapfusion_driver( funs : FunDec list ) : (bool * FunDec list) =
    let fun fusion (fid, rtp, fargs, body, pdecl) =
            let val vtab_ini = map (fn (x,y) => (x, (Var(x,(0,0)), ref 0, ref 0, [])) ) fargs
                val (vtab,succ)   = map_fusion_gather(body, (vtab_ini,false))
                val (nbody,nfuns) = map_fusion_gen(body, funs, vtab)
                val curr_fun      = (fid, rtp, fargs, nbody, pdecl)
            in (succ, curr_fun::nfuns)
            end
        val outs   = map fusion funs

        val succs  = map (fn (x,y)=>x) outs
        val succ   = List.foldl (fn (a,b) => a orelse b) false succs
        val newfuns= List.concat( map (fn (x,y)=>y) outs )
    in (succ, newfuns)
(*
    in  if(succ) then let val (s, itres) = mapfusion_driver( newfuns ) in (true,itres) end
        else (succ, newfuns)
*)

    end

  (*************************************************************)
  (*************************************************************)
  (*** 1. Function Inlining                                  ***)
  (*** inline(e : Fasto.Exp) : Fasto.Exp                     ***)
  (*************************************************************)
  (*************************************************************)

  (* Helpers for Inlining*)

  fun find_id_funlst(lst, []  ) = []
    | find_id_funlst(lst, (fid, rtp, fargs, body, pdecl)::fs) = 
       ( case( List.find (fn x => x = fid) lst ) of
           NONE   => find_id_funlst(lst, fs)
         | SOME m => [(fid, rtp, fargs, body, pdecl)]
       )

  fun checkVarsOnly([]   ) : bool = true
    | checkVarsOnly(e::es) : bool = (case e of Var(id,pos) => checkVarsOnly(es) | _ => false)



  (** Builds lst1 and lst2: all the functions that are used, and the functions that are used from Apply nodes **)
  fun find_callees(e : Exp, (lst1 : string list, lst2 : string list)) : (string list * string list) = 
    let fun find_explst([],   (lst1, lst2)) = (lst1, lst2)
          | find_explst(e::es,(lst1, lst2)) = find_explst( es, find_callees(e, (lst1, lst2)) )
    in case e of
         Let( Dec(id, e1, pos1), e2, pos2 ) => find_callees(e2, find_callees(e1, (lst1,lst2)))
       | Plus (e1, e2, pos) =>  find_callees(e2, find_callees(e1, (lst1,lst2)))
       | Minus(e1, e2, pos) =>  find_callees(e2, find_callees(e1, (lst1,lst2)))
       | Equal(e1, e2, pos) =>  find_callees(e2, find_callees(e1, (lst1,lst2)))
       | Less (e1, e2, pos) =>  find_callees(e2, find_callees(e1, (lst1,lst2)))
       | If(e1, e2, e3, pos)=>  find_callees(e3, find_callees(e2, find_callees(e1, (lst1,lst2))))
       | Apply(id,args,pos) =>  let val new_lst = case List.find (fn x => x = id) lst1 of
                                                NONE   => ( id::lst1, id::lst2 )
                                              | SOME m => ( lst1, lst2 )
                                in find_explst(args, new_lst)
                                end

       | Map(id,e,t1,t2,pos)=>  (*** we aggresively inline Map nodes => ***)
                                (***          beneficial for map fusion ***)
                                find_callees(e, (lst1,lst2))
                                
(*                              (*** conservative inlining considers treats function references ***)
                                (*** from inside a Map node as a function call                  ***)
                                let val new_lst = case List.find (fn x => x = id) lst1 of
                                                NONE   => (id :: lst1, lst2)
                                              | SOME m => ( lst1, lst2 )
                                in find_callees(e, new_lst)
                                end
*)
       | Reduce(id,e,lst,t,p)=>(*** we aggresively inline Reduce nodes => ***) 
                               (***      beneficial for map-reduce fusion ***)
                               find_callees(e, find_callees(lst, (lst1,lst2)))
(*                             (*** conservative inlining considers treats function references ***)
                               (*** from inside a Map node as a function call                  ***)
                               let val new_lst = case List.find (fn x => x = id) lst1 of
                                                NONE   => (id :: lst1, lst2)
                                              | SOME m => (lst1, lst2)
                               in find_callees(e, new_lst)
                               end
*)
       | Index(id,e,t,pos)     =>  find_callees(e, (lst1,lst2))
       | Iota (e, pos)         =>  find_callees(e, (lst1,lst2))
       | Replicate(e,el,t,pos) =>  find_callees(e, find_callees(el, (lst1,lst2)))
       | Write (e,t,pos)       =>  (* should I allow write to be inlined??? *)
                                   find_callees(e, (lst1,lst2)) 
       | _ => (lst1,lst2)
    end



  (******************************************************************)
  (***  Performing the substitution of arguments with fresh names ***)
  (******************************************************************)
  fun subs_vars_in_exp( exp : Exp, nms : (string * string) list ) : Exp = case exp of
         Let( Dec(id,e1,p1), e2, p2 ) => 
            Let( Dec(id, subs_vars_in_exp(e1, nms), p1 ), 
            subs_vars_in_exp(e2, nms), p2 
         )
       | Plus (e1, e2, p) =>  Plus ( subs_vars_in_exp(e1, nms), subs_vars_in_exp(e2, nms),  p )
       | Minus(e1, e2, p) =>  Minus( subs_vars_in_exp(e1, nms), subs_vars_in_exp(e2, nms),  p )
       | Equal(e1, e2, p) =>  Equal( subs_vars_in_exp(e1, nms), subs_vars_in_exp(e2, nms), p )
       | Less (e1, e2, p) =>  Less ( subs_vars_in_exp(e1, nms), subs_vars_in_exp(e2, nms),  p )
       | If(e1, e2, e3, p)=>  If   ( subs_vars_in_exp(e1, nms), 
                                     subs_vars_in_exp(e2, nms), 
                                     subs_vars_in_exp(e3, nms), p )
       | Apply(id,args,p) => Apply ( id, map (fn x => subs_vars_in_exp(x, nms)) args,  p )
       | Map(id,e,t1,t2,p)=> Map   ( id, subs_vars_in_exp(e, nms), t1, t2, p )
       | Reduce(id,e,l,t,p)=>Reduce( id, subs_vars_in_exp(e, nms), subs_vars_in_exp(l, nms), t, p )
       | Iota (e, p)      => Iota  ( subs_vars_in_exp(e, nms), p )
       | Replicate(e,n,t,p)=>Replicate( subs_vars_in_exp(e, nms), subs_vars_in_exp(n, nms), t, p )
       | Write (e,t,p)    => Write ( subs_vars_in_exp(e, nms), t, p )
       | Index(id,e,t,p)  => 
            let val filt = List.filter (fn (x,y) => x = id) nms
                val new_e = subs_vars_in_exp(e, nms)
                in  case filt of
                      []                   => Index(id,    new_e, t, p)
                    | (oldid, newid)::rest => Index(newid, new_e, t, p)
            end
       | Var(id,p) => 
            let val filt = List.filter (fn (x,y) => x = id) nms
            in case filt of
                      []                   => Var(id,    p)
                    | (oldid, newid)::rest => Var(newid, p)
            end
       | _ => exp

  fun subs_vars_in_fun( [],  (fid, rtp, fargs, nbody, pdecl), new_names ) : Exp = 
        subs_vars_in_exp(nbody, new_names)
    | subs_vars_in_fun( aa,  (fid, rtp, fargs, nbody, pdecl), new_names ) : Exp = 
        let val (fa,tp) = hd(fargs)
            val  new_fa  = fa^"_ft_exp_"^newName()
            val  new_exp = subs_vars_in_fun(tl(aa), (fid,rtp,tl(fargs),nbody,pdecl), (fa,new_fa)::new_names)
        in Let( Dec(new_fa, hd(aa), pdecl), new_exp, pdecl) end


  fun inline_in_body(exp : Exp, tobeinl : FunDec list, succ : bool) : (bool * Exp) = 
    case exp of
      Let( Dec(id, e1, pos1), e2, pos2 ) => let val (s1,e11) = inline_in_body(e1, tobeinl, succ)
                                                val (s2,e22) = inline_in_body(e2, tobeinl, succ)
                                            in (s1 orelse s2 orelse succ, Let( Dec(id, e11, pos1), e22, pos2 ) )
                                            end
    | Plus (e1, e2, pos) =>  let val (s1,e11) = inline_in_body(e1, tobeinl, succ)
                                 val (s2,e22) = inline_in_body(e2, tobeinl, succ)
                             in  (s1 orelse s2 orelse succ, Plus( e11, e22, pos ) )
                             end
    | Minus(e1, e2, pos) =>  let val (s1,e11) = inline_in_body(e1, tobeinl, succ)
                                 val (s2,e22) = inline_in_body(e2, tobeinl, succ)
                             in  (s1 orelse s2 orelse succ, Minus( e11, e22, pos ) )
                             end
    | Equal(e1, e2, pos) =>  let val (s1,e11) = inline_in_body(e1, tobeinl, succ)
                                 val (s2,e22) = inline_in_body(e2, tobeinl, succ)
                             in  (s1 orelse s2 orelse succ, Equal( e11, e22, pos ) )
                             end
    | Less (e1, e2, pos) =>  let val (s1,e11) = inline_in_body(e1, tobeinl, succ)
                                 val (s2,e22) = inline_in_body(e2, tobeinl, succ)
                             in  (s1 orelse s2 orelse succ, Less( e11, e22, pos ) )
                             end
    | If(e1, e2, e3, pos)=>  let val (s1,e11) = inline_in_body(e1, tobeinl, succ)
                                 val (s2,e22) = inline_in_body(e2, tobeinl, succ)
                                 val (s3,e33) = inline_in_body(e3, tobeinl, succ)
                             in  (s1 orelse s2 orelse s3 orelse succ, If( e11, e22, e33, pos ) )
                             end
    | Apply(id,args,pos) =>  let val callee  = find_id_funlst([id], tobeinl)
                                 val argres  = map (fn x => inline_in_body(x, tobeinl, succ)) args
                                 val new_arg = map (fn (b,x) => x) argres
                                 val new_succ= foldl (fn (x,y) => x orelse y) succ (map (fn (b,x)=>b) argres)
                             in if(callee = []) then ( new_succ, Apply(id, new_arg,pos) )
                                else (* HERE WE DO INLINING *)
                                     if (checkVarsOnly(args) = false ) 
                                     then ( print(pp_exp 0 exp); raise Error("Unormlized Code in Inline; Exits!", (0,0))  )
                                     else ( true, subs_vars_in_fun(args, hd(callee), []) )
                             end
    | Map(id,e,t1,t2,pos)=>  let val (s1,e11) = inline_in_body(e, tobeinl, succ)
                             in (s1 orelse succ, Map(id,e11,t1,t2,pos))
                             end
    | Reduce(id,e,lst,t,p)=> let val (s1,e11) = inline_in_body(e,   tobeinl, succ)
                                 val (s2,e22) = inline_in_body(lst, tobeinl, succ)
                             in (s1 orelse s2 orelse succ, Reduce(id,e11, e22, t, p) )
                             end
    | Index(id,e,t,pos)     =>  let val (s1,e11) = inline_in_body(e, tobeinl, succ) in (s1, Index(id,e11,t,pos)) end
    | Iota (e, pos)         =>  let val (s1,e11) = inline_in_body(e, tobeinl, succ) in (s1, Iota(e11,pos)) end
    | Replicate(e,el,t,pos) =>  let val (s1,e11) = inline_in_body(e,  tobeinl, succ)
                                    val (s2,e22) = inline_in_body(el, tobeinl, succ)
                                in (s1 orelse s2 orelse succ, Replicate(e11, e22, t, pos) )
                                end
    | Write (e,t,pos)       =>  let val (s1,e11) = inline_in_body(e, tobeinl, succ) in (s1, Write(e11,t,pos)) end
    | _ => (succ,exp)


  fun inline_in_caller( ((fid, rtp, fargs, body, pdecl), (l1,l2)), tobeinl ) : (bool * FunDec) =
      let val fails = find_id_funlst(l2, tobeinl)
      in if(fails=[]) then (false, (fid, rtp, fargs, body, pdecl))
         else let val (succ, nbody) = inline_in_body(body, tobeinl, false) 
              in  if(succ) then (succ, (fid, rtp, fargs, nbody, pdecl))
                  else raise Error("Inlining Have Failed: Broken Invariant in inline_in_caller!", (0,0))
              end
      end



  (***************************************************************)
  (*** Function Inlining Driver:                               ***)
  (*** 1. `tobeinl' are the functions that do not call others  ***)
  (*** 2. `others' are funs that might call others (map/apply) ***)
  (*** 3. attempt to inline `tobeinl' funs in `others' funs    ***)
  (*** 4. repeat to a fixed point                              ***) 
  (***************************************************************)
  fun inline_driver(funlst : FunDec list, succ : bool) : (bool * FunDec list) = 
      let val callees = map ( fn (fid, rtp, fargs, body, pdecl) 
                                => ( (fid, rtp, fargs, body, pdecl), find_callees(body, ([],[]) )) ) 
                             funlst
          val tobeinl = map (fn (f,(l1,l2)) =>f) (List.filter (fn (f,(l1,l2)) => (l1 = [])) callees)
          val others  = List.filter (fn (f, (l1,l2)) => (l1 <> [])) callees
          val partres = map (fn x => inline_in_caller(x,tobeinl)) others
          val bools   = map (fn(b,f) => b ) partres
          val res     = map (fn(b,f) => f ) partres
      in if(List.foldl (fn (a,b) => a orelse b) false bools) 
         then let val (b,fs) = inline_driver(res, true) 
              in ( true, tobeinl@fs ) 
              end
         else ( succ, funlst ) 
      end 
          


  (*************************************************************)
  (*************************************************************)
  (*** 1. LET-NORMALIZATION Optimization                     ***)
  (*** let_norm_exp(e : Fasto.Exp) : Fasto.Exp               ***)
  (*************************************************************)
  (*************************************************************)

  (* treats the case Let x = y in exp => subst(x|y, exp) *)
  fun elim_redundancy(exp) = case exp of
        Let( Dec(id1, Var(id2,p), pos1), ine, pos2 ) => 
            elim_redundancy( subs_vars_in_exp( ine, [(id1,id2)] ) )
      | otherwise => exp


  fun let_norm_exp( e:Fasto.Exp ) : Fasto.Exp= case e of
    Let( Dec(id, e1, pos1), e2, pos2 ) => 
        let val el_red  = elim_redundancy(e)
        in if(el_red <> e) then el_red
           else 
            let val e1_norm  = let_norm_exp(e1)
                val e2_norm2 = let_norm_exp(e2)
                val e2_norm  = case e2_norm2 of
                                 Map(s,emap,t1,t2,p) => 
                                     let val nm = "ft_map_"^newName()
                                     in Let(Dec(nm, e2_norm2,p), Var(nm,p), p) end
                               | otherwise => e2_norm2
            in case e1_norm of
                 Let( Dec(id1, e11, pos11), e12, pos12 ) => 
                   let val inner = let_norm_exp( Let( Dec(id, e12, pos1), e2_norm, pos2 ) )
                   in  Let( Dec(id1, e11, pos11), inner, pos12 ) 
                   end
               | _ => if(e1_norm = e1 andalso e2_norm = e2) then e
                      else  Let( Dec(id, e1_norm, pos1), e2_norm, pos2 )
            end
        end 

  | Plus(e1, e2, pos) =>  let fun f(l,p) = Plus (List.nth(l,0), List.nth(l,1),p) 
                          in  bind_exps ([e1,e2], [], f, pos)
                          end
  | Minus(e1, e2, pos)=>  let fun f(l,p) = Minus(List.nth(l,0), List.nth(l,1),p) 
                          in  bind_exps ([e1,e2], [], f, pos)
                          end

  | Equal(e1, e2, pos)=>  let fun f(l,p) = Equal(List.nth(l,0), List.nth(l,1),p) 
                          in  bind_exps ([e1,e2], [], f, pos)
                          end

  | Less(e1, e2, pos) =>  let fun f(l,p) = Less (List.nth(l,0), List.nth(l,1),p) 
                          in  bind_exps ([e1,e2], [], f, pos)
                          end

  | If(e1, e2, e3, pos) => let fun f(l,p) = If(hd(l), let_norm_exp(e2), let_norm_exp(e3), pos)
                           in  bind_exps ([e1], [], f, pos)
                           end

  | Apply(id,args,pos) => let fun f(l,p) = Apply(id,l,p)
                          in  bind_exps (args, [], f, pos)
                          end

(*
                             let val new_tmp = "ft_exp_"^newName()
                                 fun f(l,p) = Let (  Dec(new_tmp,Apply(id,l,p), p), 
                                                     Var(new_tmp, p), p 
                                                  )
                             in  bind_exps(args, [], f, pos)
                             end
*)

  | Index(id,e,t,pos) => let fun f(l,p) = Index(id,hd(l),t,p)
                         in  bind_exps ([e], [], f, pos)
                         end (* Index(id, let_norm_exp(e), t, pos) *)

  | Iota (e, pos)     => let fun f(l,p) = Iota(hd(l),p)
                         in  bind_exps([e], [], f, pos)
                         end

  | Replicate(e,el,t,pos) => let fun f(l,p) = Replicate(List.nth(l,0),List.nth(l,1),t,p)
                             in  bind_exps([e,el], [], f, pos)
                             end

  | Map(id,e,t1,t2,pos)   => let fun f(l,p) = Map(id,hd(l),t1,t2,p)
                             in  bind_exps([e], [], f, pos)
                             end

  | Reduce(id,e,lst,t,pos)=> let fun f(l,p) = Reduce(id,List.nth(l,0),List.nth(l,1),t,p)
                             in  bind_exps([e,lst], [], f, pos)
                             end
  | Write (e,t,pos)   => let fun f(l,p) = Write(hd(l),t,p) in bind_exps([e], [], f, pos) end 

  | _ => e 


  (*******************************************************************)
  (** Helper function for normalization: Parameters:                **)
  (**   1. list of expressions,                                     **)
  (**   2. an initially empty list of variables, i.e., Var(id,pos)  **)
  (**   3. a function that should create the desired innermost exp, **)
  (**        e.g., in case of Equal:                                **)
  (**          fun f(l,p) = Equal(List.nth(l,0), List.nth(l,1), p)  **)
  (**   4. the position in the code                                 **)
  (** The result is a normalized Let expression,                    **)
  (**       i.e., three-address-like code                           **)
  (*******************************************************************)
  and bind_exps ([],    vars, f, pos) = f( List.rev(vars), pos )
    | bind_exps (e::es, vars, f, pos) = ( case e of
            Var(id,pos) => bind_exps(es, e::vars, f, pos)
         |  _           => 
              let val new_nm = "ft_exp_"^newName()
                  val new_var= Var(new_nm, pos)
                  val e_norm = let_norm_exp(e)
                  val new_e  = bind_exps(es, new_var::vars, f, pos)
                  
              in case e_norm of 
                   Let( Dec(id, l_e, pos1), in_e, pos2 ) =>
                       let val inner = let_norm_exp( 
                               Let(Dec(new_nm, in_e, pos2), new_e, pos2) )
                       in  Let( Dec(id, l_e, pos1), inner, pos )
                       end
                 | _ => Let(Dec(new_nm, e_norm, pos), new_e, pos)
              end
        )





  (*************************************************************)
  (*************************************************************)
  (*** High-Level-Optimization Driver. To a fixed point:     ***)
  (***    1. Function Inlining                               ***)
  (***    2. Let Normalization                               ***)
  (***    3. Map Fusion                                      ***)
  (***    4. Dead-Code Elimination (perhaps when I have time)***)
  (*************************************************************)
  (*************************************************************)
      
  fun opt_fixpoint(funlst : FunDec list) : FunDec list = 
        let val bodys = map (fn (fid, rtp, fargs, body, pdecl) 
                                => let_norm_exp(body)) 
                            funlst

            val funnorm  = map (fn(new_body, (fid, rtp, fargs, body, p)) 
                                          => (fid,rtp,fargs,new_body,p)) 
                               (zip bodys funlst)

            val (succfus, funfus)  = mapfusion_driver( funnorm )

            (** Inline driver requires removal, 
                and then addition of the special funs **)
            val funfus1 = rem_spec_funs(funfus)
            val (succinl, funsinl1) = inline_driver(funfus1, false)
            val funsinl = add_spec_funs(funsinl1)

            val funsCleaned = dead_fun_elim ( funsinl )

        in  if(succinl) then opt_fixpoint(funsCleaned) else funsCleaned
        end


  fun opt_pgm(funlst1 : FunDec list) : FunDec list =
          (* first add the special functions *)
      let val funlst = add_spec_funs(funlst1)

          (* first make unique names for all function bodies *)
          fun rename_fun(fid, rtp, fargs, body, pdecl) =
            (fid, rtp, fargs, unique_rename( body, [] ), pdecl)

          val newfunlst = map (fn x=>rename_fun(x)) funlst   
          val res1       = opt_fixpoint(newfunlst)    

          val res = rem_spec_funs(res1)
      in ( print(prettyPrint res); res )
      end

end

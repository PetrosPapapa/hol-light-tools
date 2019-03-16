(* ========================================================================= *)
(* Extended tactics.                                                         *)
(* ------------------------------------------------------------------------- *)
(* These allow an arbitrary extension of the goal(state) that is managed     *)
(* through a tactic allowing, for example, the capture of more information   *)
(* as the tactics are applied.                                               *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                 2015 - 2016                               *)
(* ========================================================================= *)

needs "tools/lib.ml";;

type 'a etactic = 'a -> goal -> (goalstate * 'a);;


(* ------------------------------------------------------------------------- *)
(* Convert a normal tactic to an etactic.                                    *)
(* ------------------------------------------------------------------------- *)

let (ETAC:tactic -> 'a etactic) =
    fun tac s g -> tac g,s;;


(* ------------------------------------------------------------------------- *)
(* Use an etactic as a normal tactic given an initial state.                 *)
(* f is used to take care of the final state (e.g. print it out).            *)
(* ------------------------------------------------------------------------- *)
(* This can be used in an interactive setting using e().                     *)
(* ------------------------------------------------------------------------- *)

let (ETAC_TAC':('a -> unit) -> 'a -> 'a etactic -> tactic) =
  fun f s etac gl ->
  let gs,s' = etac s gl in
  f s' ; gs;;

let (ETAC_TAC:'a -> 'a etactic -> tactic) =
  fun s tac ->
  ETAC_TAC' (fun _ -> ()) s tac;;
 

(* ------------------------------------------------------------------------- *)
(* Convert an 'a etactic to a 'b tactic when 'a is a substate of 'b.         *)
(* The 2 function arguments are used as follows :                            *)
(* f : extracts substate 'a from 'b.                                         *)
(* g : updates state 'b given a new substate 'a.                             *)
(* ------------------------------------------------------------------------- *)

let (LIFT_ETAC:('b -> 'a) -> ('a -> 'b -> 'b) -> 'a etactic -> 'b etactic) =
  fun f g etac sb gl ->
  let gs,sa = etac (f sb) gl in
  gs,g sa sb;;


(* ------------------------------------------------------------------------- *)
(* Validity checking of etactics.                                            *)
(* ------------------------------------------------------------------------- *)
    
let (EVALID:'a etactic->'a etactic) =
  let fake_thm (asl,w) =
    let asms = itlist (union o hyp o snd) asl [] in
    mk_fthm(asms,w)
  and false_tm = `_FALSITY_` in
  fun tac state (asl,w) ->
    let (((mvs,i),gls,just),_ as res) = tac state (asl,w) in
    let ths = map fake_thm gls in
    let asl',w' = dest_thm(just null_inst ths) in
    let asl'',w'' = inst_goal i (asl,w) in
    let maxasms =
      itlist (fun (_,th) -> union (insert (concl th) (hyp th))) asl'' [] in
    if aconv w' w'' &
       forall (fun t -> exists (aconv t) maxasms) (subtract asl' [false_tm])
    then res else failwith "EVALID: Invalid tactic";;


(* ------------------------------------------------------------------------- *)
(* THEN and THENL for etactics.                                              *)
(* Too bad we can't trivially make them infix.                               *)
(* ------------------------------------------------------------------------- *)

let ETHEN,ETHENL =
  let propagate_empty i [] = []
  and propagate_thm th i [] = INSTANTIATE_ALL i th in
  let compose_justs n just1 just2 i ths =
    let ths1,ths2 = chop_list n ths in
    (just1 i ths1)::(just2 i ths2) in
  let rec seqapply ext l1 l2 = match (l1,l2) with
      ([],[]) -> (null_meta,[],propagate_empty),ext
    | ((tac:'a etactic)::tacs),((goal:goal)::goals) ->
        let (((mvs1,insts1),gls1,just1),ext1) = tac ext goal in
        let goals' = map (inst_goal insts1) goals in
        let (((mvs2,insts2),gls2,just2),ext2) = seqapply ext1 tacs goals' in
        (((union mvs1 mvs2,compose_insts insts1 insts2),
          gls1@gls2,compose_justs (length gls1) just1 just2),ext2)
    | _,_ -> failwith "seqapply: Length mismatch" in
  let justsequence just1 just2 insts2 i ths =
    just1 (compose_insts insts2 i) (just2 i ths) in
  let tacsequence (((mvs1,insts1),gls1,just1),ext1) tacl =
    let (((mvs2,insts2),gls2,just2),ext2) = seqapply ext1 tacl gls1 in
    let jst = justsequence just1 just2 insts2 in
    let just = if gls2 = [] then propagate_thm (jst null_inst []) else jst in
    (((union mvs1 mvs2,compose_insts insts1 insts2),gls2,just),ext2) in
  let (then_: 'a etactic -> 'a etactic -> 'a etactic) =
    fun tac1 tac2 s g ->
    let (_,gls,_),_ as gstate = tac1 s g in
    tacsequence gstate (replicate tac2 (length gls))
  and (thenl_: 'a etactic -> 'a etactic list -> 'a etactic) =
    fun tac1 tac2l s g ->
    let (_,gls,_),_ as gstate = tac1 s g in
    if gls = [] then tacsequence gstate []
    else tacsequence gstate tac2l in
  then_,thenl_
;;

(* ------------------------------------------------------------------------- *)
(* Other combinators etc.                                                    *)
(* ------------------------------------------------------------------------- *)

let ((EORELSE): 'a etactic -> 'a etactic -> 'a etactic) =
  fun tac1 tac2 s g ->
    try tac1 s g with Failure _ -> tac2 s g;;

let (FAIL_ETAC: string -> 'a etactic) =
  fun tok s g -> failwith tok;;

let (NO_ETAC: 'a etactic) =
  FAIL_ETAC "NO_ETAC";;

let (ALL_ETAC:'a etactic) =
  fun s g -> (null_meta,[g],fun _ [th] -> th),s;;

let (ALL_ETAC':('a -> 'a) -> 'a etactic) =
  fun f s g -> (null_meta,[g],fun _ [th] -> th),f s;;

let ETRY etac =
  EORELSE etac ALL_ETAC;;

let rec EREPEAT tac s g =
  (EORELSE (ETHEN tac (EREPEAT tac)) ALL_ETAC) s g;;

let EEVERY tacl =
  itlist (fun t1 t2 -> ETHEN t1 t2) tacl ALL_ETAC;;

let (EFIRST: 'a etactic list -> 'a etactic) =
  fun tacl s g -> (end_itlist (fun t1 t2 -> EORELSE t1 t2) tacl s) g;;

let EMAP_EVERY tacf lst =
  EEVERY (map tacf lst);;

let EMAP_FIRST tacf lst =
  EFIRST (map tacf lst);;

let (CHANGED_ETAC: 'a etactic -> 'a etactic) =
  fun tac s g ->
    let ((meta,gl,_),_ as gstate) = tac s g in 
    (* We don't compare states because we don't know how and normally don't need to. *)
    if meta = null_meta & length gl = 1 & equals_goal (hd gl) g
    then failwith "CHANGED_ETAC" else gstate;;

let rec REPLICATE_ETAC n tac =
  if n <= 0 then ALL_ETAC else ETHEN tac (REPLICATE_ETAC (n - 1) tac);;

let TIME_ETAC s (tac:'a etactic) st gl =
  stime s (tac st) gl;;

let (EVALID:'a etactic->'a etactic) =
  fun tac s (asl,w) ->
  let fake_thm (asl,w) =
    let asms = itlist (union o hyp o snd) asl [] in
    mk_fthm(asms,w)
  and false_tm = `_FALSITY_` in
  
  let (((mvs,i),gls,just),_ as res) = tac s (asl,w) in
  let ths = map fake_thm gls in
  let asl',w' = dest_thm(just null_inst ths) in
  let asl'',w'' = inst_goal i (asl,w) in
  let maxasms =
    itlist (fun (_,th) -> union (insert (concl th) (hyp th))) asl'' [] in
  if aconv w' w'' &
     forall (fun t -> exists (aconv t) maxasms) (subtract asl' [false_tm])
  then res else failwith "EVALID: Invalid tactic";;


(* ------------------------------------------------------------------------- *)
(* Extending refinements and goalstates.                                     *)
(* ------------------------------------------------------------------------- *)

let (eby:'a etactic->goalstate * 'a -> goalstate * 'a) =
  fun tac (((mvs,inst),gls,just),state) ->
    if gls = [] then failwith "No goal set" else
    let g = hd gls
    and ogls = tl gls in
    let ((newmvs,newinst),subgls,subjust),state' = tac state g in
    let n = length subgls in
    let mvs' = union newmvs mvs
    and inst' = compose_insts inst newinst
    and gls' = subgls @ map (inst_goal newinst) ogls in
    let just' i ths =
      let i' = compose_insts inst' i in
      let cths,oths = chop_list n ths in
      let sths = (subjust i cths) :: oths in
      just i' sths in
    ((mvs',inst'),gls',just'),state';;

let (erefinestack:(goalstate * 'a -> goalstate * 'a)->(goalstate * 'a) list->(goalstate * 'a) list) =
  fun r gs ->
    if gs = [] then failwith "No current goal" else
    let h = hd gs in
    r h :: gs;;

let (ETAC_PROOF : 'a -> goal * 'a etactic -> thm * 'a) =
  fun s (g,tac) ->
    let gstate = mk_goalstate g,s in
    let (_,sgs,just),s' = eby tac gstate in
    if sgs = [] then just null_inst [],s'
    else failwith "ETAC_PROOF: Unsolved goals";;

let eprove s (t,tac) =
  let th,s' = ETAC_PROOF s (([],t),tac) in
  let t' = concl th in
  if t' = t then th,s' else
  try EQ_MP (ALPHA t' t) th,s'
  with Failure _ -> failwith "prove: justification generated wrong theorem";;

let (apply_etac:'a etactic->(goalstate * 'a) list->(goalstate * 'a) list) =
  fun tac gs -> erefinestack (eby (EVALID tac)) gs;;

let get_ethm (gs:(goalstate * 'a) list) =
  let ((_,[],f),s)::_ = gs in
  f null_inst [],s ;;


(* ------------------------------------------------------------------------- *)
(* Examples with tactics that count tactic applications.                     *)
(* ------------------------------------------------------------------------- *)


let (COUNT_ETAC:tactic->int etactic) =
  fun tac s g ->
  tac g,s + 1;;

let PRINT_COUNT_TAC etac =
  let print_i i = (print_string "Count: "; print_int i ; print_newline() ) in
  ETAC_TAC' print_i 0 etac;;


(* Example: *)
(*
g ((fun x -> mk_imp (`p:bool`,itlist (curry mk_conj) (replicate `p:bool` (x-1)) `p:bool`)) 3);;
e (PRINT_COUNT_TAC (ETHEN (COUNT_ETAC DISCH_TAC) (ETHEN (EREPEAT (COUNT_ETAC CONJ_TAC)) (COUNT_ETAC (FIRST_ASSUM ACCEPT_TAC)))));;
(* or *)
e (PRINT_COUNT_TAC (EEVERY [COUNT_ETAC DISCH_TAC;EREPEAT (COUNT_ETAC CONJ_TAC);COUNT_ETAC (FIRST_ASSUM ACCEPT_TAC)]));;
(* Count should be 2*n (1 DISCH_TAC, n-1 CONJ_TACs, n ACCEPT_TACs) *)
*)

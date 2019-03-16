(* ========================================================================= *)
(* Substitutions using finite maps and their properties.                     *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                 2015 - 2017                               *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Dependencies                                                              *)
(* ------------------------------------------------------------------------- *)

needs "IsabelleLight/make.ml";;
needs "tools/Library/finite_map.ml";;
needs "tools/Library/option.ml";;
needs "tools/Library/lists.ml";;


(* ------------------------------------------------------------------------- *)
(* Definition                                                                *)
(* ------------------------------------------------------------------------- *)


let SUBST = new_definition `!x fm. SUB fm x =
	   let v = FLOOKUP fm x in
	   if v = NONE then x
	   else THE v`;;


(* ------------------------------------------------------------------------- *)
(* Properties                                                                *)
(* ------------------------------------------------------------------------- *)
		    

(* Basic *)		    

let SUBST_FDOM_THM = prove (`!x fm. SUB fm x = if x IN FDOM fm then FAPPLY fm x else x`,
   REWRITE_TAC[SUBST;FLOOKUP;LET_DEF;LET_END_DEF] THEN REPEAT GEN_TAC THEN
   case_tac `x IN FDOM fm` THEN simp[THE_DEF;distinctness "option"]);;

let SUBST_VAIN = prove (`!x fm. SUB fm x = x <=> (FLOOKUP fm x = NONE) \/ (FLOOKUP fm x = SOME x)`,
   REWRITE_TAC[SUBST;FLOOKUP_FEMPTY;LET_DEF;LET_END_DEF] THEN REPEAT GEN_TAC THEN EQ_TAC THENL [
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    case_tac `FLOOKUP fm x` THEN simp[THE_DEF] THEN FIRST_ASSUM CONTR_TAC ;
    DISCH_THEN DISJ_CASES_TAC THEN simp[THE_DEF;distinctness "option"] ]);;
	    
let SUBST_FEMPTY = prove (`!x. SUB FEMPTY x = x`, REWRITE_TAC[SUBST;FLOOKUP_FEMPTY;LET_DEF;LET_END_DEF]);;

let SUBST_FUPDATE = prove (`!x fm a b. SUB (FUPDATE fm (a,b)) x = if (x=a) then b else SUB fm x`,
   REWRITE_TAC[SUBST;FLOOKUP_FUPDATE] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
   simp[THE_DEF;distinctness "option";LET_DEF;LET_END_DEF]);;

let SUBST_ABSORB = prove (`!x fm. SUB (fm |+ (x,x)) x = x`, SIMP_TAC[SUBST;FLOOKUP_FUPDATE;LET_DEF;LET_END_DEF;THE_DEF;distinctness "option"]);;

let SUBST_FUPDATE_VAIN = prove (`!x y z fm. ~(x=z) ==> SUB (fm |+ (x,y)) z = SUB fm z`, SIMP_TAC[SUBST;FLOOKUP_FUPDATE]);;

let SUBST_NOT_FDOM_EQ_VAIN = prove (
  `!f g x. ~(x IN FDOM f) ==> SUB f x = SUB g x  ==> SUB g x = x`, MESON_TAC[SUBST_FDOM_THM]);;



(* FUPDATE_LIST *)

let SUBST_FUPDATE_LIST_ID = prove (`!x t. SUB (FEMPTY |++ (CONS (x,x) t)) x = SUB (FEMPTY |++ t) x`,
   SIMP_TAC[SUBST;FLOOKUP;LET_DEF;LET_END_DEF;FDOM_FUPDATE_LIST;FDOM_FEMPTY;MAP;FST;IN_SET_OF_LIST;MEM;THE_DEF;distinctness "option"] THEN
   REPEAT GEN_TAC THEN case_tac `MEM x (MAP FST t)` THEN simp[] THENL [
    simp[FUPDATE_LIST_THM;FUPDATE_LIST_APPLY_NOT_MEM];
    simp[FUPDATE_LIST_THM;FUPDATE_FUPDATE_LIST_MEM;THE_DEF;distinctness "option"] ] );;

let SUBST_FUPDATE_LIST_ABSORB = prove (`!x y fm t. SUB (FEMPTY |++ (CONS (x,x) t)) y = SUB (FEMPTY |++ t) y`,
   REPEAT GEN_TAC THEN case_tac `y = x` THENL [
   simp[SUBST;FLOOKUP;LET_DEF;LET_END_DEF;FDOM_FUPDATE_LIST;FDOM_FEMPTY;MAP;FST;IN_SET_OF_LIST;MEM;THE_DEF;distinctness "option"] ;
   simp[SUBST_FUPDATE_LIST_ID] ] THEN
   case_tac `MEM x (MAP FST t)` THENL [
   simp[FUPDATE_LIST_THM;FUPDATE_FUPDATE_LIST_COMMUTES;NOT_EQ_FAPPLY] ;
   simp[FUPDATE_LIST_CONS_MEM] ]);;

let SUBST_FUPDATE_LIST_CONS_EQ = prove (
  `!x y t. SUB (FEMPTY |++ CONS (x,y) t) x = if MEM x (MAP FST t) then SUB (FEMPTY |++ t) x else y`,
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN
      ASM SIMP_TAC[FUPDATE_LIST_CONS;FUPDATE_FUPDATE_LIST_MEM;FUPDATE_FUPDATE_LIST_COMMUTES;SUBST_FUPDATE]);;

let SUBST_FUPDATE_LIST_CONS_VAIN = prove (
  `!x y t a. ~(x=a) ==> SUB (FEMPTY |++ CONS (x,y) t) a = SUB (FEMPTY |++ t) a`,
  REPEAT GEN_TAC THEN case_tac `MEM x (MAP FST t)` THEN
    ASM SIMP_TAC[FUPDATE_LIST_CONS;FUPDATE_FUPDATE_LIST_MEM;FUPDATE_FUPDATE_LIST_COMMUTES;SUBST_FUPDATE]);;

let SUBST_FUPDATE_LIST_VAIN = prove (
  `!x l. ~MEM x (MAP FST l) ==> SUB (FEMPTY |++ l) x = x`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL [
    simp[FUPDATE_LIST_NIL;SUBST_FEMPTY] ;
    case_tac `h ` THEN simp[MAP;MEM;DE_MORGAN_THM;SUBST_FUPDATE_LIST_CONS_VAIN] ]);;


(* FUPDATE_RLIST *)

let SUBST_FUPDATE_RLIST_NIL = prove (`!fm x. SUB (fm |+++ []) x = SUB fm x`,
   REWRITE_TAC[FUPDATE_RLIST_THM;SUBST_FUPDATE]);;

let SUBST_FUPDATE_RLIST_CONS_EQ = prove (`!x y fm t. SUB (fm |+++ (CONS (x,y) t)) x = y`,
   REWRITE_TAC[FUPDATE_RLIST_THM;SUBST_FUPDATE]);;
						     
let SUBST_FUPDATE_RLIST_CONS_VAIN = prove (
   `!x y t fm a. ~(x=a) ==> SUB (fm |+++ CONS (x,y) t) a = SUB (fm |+++ t) a`,
   simp[FUPDATE_RLIST_THM;SUBST_FUPDATE]);;

let SUBST_FUPDATE_RLIST_CONS = prove (
   `!x y t fm a. SUB (fm |+++ CONS (x,y) t) a = if (x=a) then y else SUB (fm |+++ t) a`,
   SIMP_TAC[FUPDATE_RLIST_THM;SUBST_FUPDATE] THEN REPEAT GEN_TAC THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;


(* FUNION *)

let SUBST_EQ_FUNION = prove (`!f s t x. SUB s x = SUB t x ==> SUB (FUNION f s) x = SUB (FUNION f t) x`,
   SIMP_TAC[SUBST;FLOOKUP;FUNION;LET_DEF;LET_END_DEF;IN_UNION] THEN REPEAT GEN_TAC THEN
   case_tac `x IN FDOM f` THEN simp[]);;

(* `!s f t. (!x. SUB s x = SUB t x) ==> (!x. SUB (FUNION f s) x = SUB (FUNION f t) x)` *)
let SUBST_EQ_FUNION_FORALL = (GEN_ALL o (MATCH_MP MONO_FORALL) o (ISPECL [`f:(A,A)fmap`;`s:(A,A)fmap`;`t:(A,A)fmap`])) SUBST_EQ_FUNION;;


(* MAP SUBST *)

let MAP_SUBST_VAIN = prove (`!l fm P. (!x. P x ==> SUB fm x = x) ==> ALL P l ==> MAP (SUB fm) l = l`,
   LIST_INDUCT_TAC THEN simp[ALL;MAP] THEN meson[]);;

let MAP_SUBST_FUPDATE_VAIN = prove (`!l x y z fm. ~(MEM x l) ==> MAP (SUB (fm |+ (x,y))) l = MAP (SUB fm) l`,
   LIST_INDUCT_TAC THEN simp[SUBST_FUPDATE_VAIN; MEM; MAP; DE_MORGAN_THM]);;				    

let MAP_SUBST_FEMPTY = prove (`!l. MAP (SUB FEMPTY) l = l`, LIST_INDUCT_TAC THEN simp[MAP;SUBST_FEMPTY]);;

let MAP_SUBST_FUPDATE_LIST_ABSORB = prove (`!l x t. MAP (SUB (FEMPTY |++ CONS (x,x) t)) l = MAP (SUB (FEMPTY |++ t)) l`, LIST_INDUCT_TAC THEN simp[MAP;SUBST_FUPDATE_LIST_ABSORB]);;

let MAP_SUBST_EQ_FUNION = prove (
  `!l f s t. MAP (SUB s) l = MAP (SUB t) l ==> MAP (SUB (FUNION f s)) l = MAP (SUB (FUNION f t)) l`,
  LIST_INDUCT_TAC THEN simp[MAP;CONS_11] THEN meson[SUBST_EQ_FUNION]);;

let FORALL_SUBST_MAP = prove (`!f g l. (!x. SUB f x = SUB g x) ==> MAP (SUB f) l = MAP (SUB g) l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN simp[MAP]);;

let FORALL_MEM_SUBST_MAP = prove (
   `!f g l. (!x. MEM x l ==> SUB f x = SUB g x) ==> MAP (SUB f) l = MAP (SUB g) l`,
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN simp[MAP;MEM]);;

let MEM_MAP_SUB_FUPDATE = prove(
  `!l s a b x. ~(x=b) ==> MEM x (MAP (SUB (s |+ (a,b))) l) ==> MEM x (MAP (SUB s) l)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN simp[MEM;MAP;SUBST;FLOOKUP_FUPDATE] THEN
    COND_CASES_TAC THENL [
      REPEAT LET_TAC THEN REPEAT (FIRST_X_ASSUM (SUBST1_TAC o GSYM)) THEN simp[distinctness "option";THE_DEF] ;
      ALL_TAC ] THEN meson[]);;

(* g `!x f g. SUB (SUB x f) g = SUB x (FMERGE (\vf vg. FAPPLY  g f)`;; Composition is hard! - needs fmap composition *)


(* Evaluation conversion *)

let SUBST_CONV eqconv tm =
  let rec subst_conv tm =
    try (
    let fmap = (rand o rator) tm in
    if is_fupdate fmap then
    (PURE_ONCE_REWRITE_CONV[SUBST_FUPDATE] THENC
     PATH_CONV "llr" eqconv THENC
     PURE_ONCE_REWRITE_CONV[COND_CLAUSES] THENC subst_conv) tm
    else PURE_REWRITE_CONV[SUBST_FEMPTY] tm)
    with Failure _ -> ALL_CONV tm in
  (PURE_REWRITE_CONV[FUPDATE_LIST_THM;FUPDATE_RLIST_THM] THENC subst_conv) tm;;


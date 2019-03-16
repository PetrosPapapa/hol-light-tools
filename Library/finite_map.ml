(* ========================================================================= *)
(* Port of finite map theory from HOL4.                                      *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                    2015                                   *)
(* ========================================================================= *)
(* Original by Graham Collins and Donald Syme for HOL88 (or HOL90?) in 1995  *)
(* Updated by Michael Norrish for HOL4 in 2002                               *)
(* Including additions by Thomas Tuerk in HOL4 in 2009                       *)
(* Including additions by Ramana Kumar in HOL4 (unknown when)                *)
(* Including some of my own additions in HOL Light in 2015                   *)
(* ========================================================================= *)

needs "IsabelleLight/make.ml";;
needs "tools/make.ml";;
needs "tools/Library/sum.ml";;
needs "tools/Library/lists.ml";;
needs "tools/Library/sets.ml";;

let prove_abs_fn_onto th = try (
   let [th1;th2] = CONJUNCTS th in
   let (bv_th1,bod) = dest_forall(concl th1) in
   let (a,rrand) = dest_comb(lhs bod) in
   let rr = rator rrand in
   let rb = mk_comb(rr, bv_th1) in
   let bth1 = SPEC bv_th1 th1 in
   let thm1 = EQT_ELIM(TRANS (SPEC rb th2) (EQT_INTRO (AP_TERM rr bth1))) in
   let thm2 = SYM bth1 in
   let (r,bod) = dest_forall(concl th2) in
   let pp = rator(lhs bod) in
   let ex = mk_exists(r,
                      mk_conj(mk_eq(bv_th1,mk_comb(a, r)), mk_comb(pp, r)))
   in GEN bv_th1 (EXISTS(ex,rb) (CONJ thm2 thm1)))
   with Failure _ -> failwith "prove_abs_fn_onto";;

(*
let prove_rep_fn_onto th =
   let [th1;th2] = CONJUNCTS th in
       let (bvar,bod) = dest_forall(concl th2) in
       let (_,eq) = dest_eq bod in
       let (re, ar) = dest_comb(lhs eq) in
       let a = mk_var("a", type_of ar) in
       let sra = mk_eq(bvar, mk_comb(re, a)) in
       let ex = mk_exists(a, sra) in
       let imp1 = EXISTS (ex,ar) (SYM(ASSUME eq)) in
       let aa = rator ar in
       let ass = AP_TERM re (SPEC a th1) in SYM(ASSUME sra), ass, DISCH eq imp1;;
       let th = SUBST[v |-> SYM(ASSUME sra)]
                 (mk_eq(mk_comb(RE,mk_comb(A, v)),v)) ass
       let imp2 = CHOOSE (a,ASSUME ex) th
       let swap = IMP_ANTISYM_RULE (DISCH eq imp1) (DISCH ex imp2)
   in
   GEN Bvar (TRANS (SPEC Bvar th2) swap)
   end
   handle HOL_ERR _ => raise ERR "prove_rep_fn_onto" ""
        | Bind => raise ERR "prove_rep_fn_onto"
                            ("Theorem not of right form: must be\n "^
                             "|- (!a. to (from a) = a) /\\ "^
                             "(!r. P r = (from (to r) = r))")

let prove_rep_fn_one_one th =
   let thm = CONJUNCT1 th in
   let (_,bod) = dest_forall(concl thm) in
   let (al, randr) = dest_comb(lhs bod) in
   let (rr, _)= dest_comb randr in
   let (_,[aty;rty]) = dest_type (type_of rr) in
   let a = mk_var("a", aty) in
   let a' = variant [a] a in
   let a_eq_a' = mk_eq(a,a') 
   and ra_eq_ra' = mk_eq(mk_comb(rr,a), mk_comb(rr, a')) in
   let th1 = AP_TERM al (ASSUME ra_eq_ra') in rr,DISCH a_eq_a' (AP_TERM rr (ASSUME a_eq_a'));;
   al,th1,REWRITE_RULE[SPEC a thm;SPEC a' thm] th1;;

   let ga1 = genvar aty 
   and ga2 = genvar aty in
   let th2 = SUBST [ga1 |-> SPEC a thm, ga2 |-> SPEC a' thm] in
(mk_eq(ga1, ga2)) th1
       val th3 = DISCH a_eq_a' (AP_TERM R (ASSUME a_eq_a'))
   in
      GEN a (GEN a' (IMP_ANTISYM_RULE (DISCH Ra_eq_Ra' th2) th3))
   end
   handle HOL_ERR _ => raise ERR "prove_rep_fn_one_one"  ""
        | Bind => raise ERR "prove_rep_fn_one_one"
                            ("Theorem not of right form: must be\n "^
                             "|- (!a. to (from a) = a) /\\ "^
                             "(!r. P r = (from (to r) = r))")
let prove_abs_fn_one_one th =
  let [th1;th2] = CONJUNCTS th in
let (r, bod) = dest_forall(concl th2) in
let pp = rator(lhs bod) in
       let (aa, rrand) = dest_comb(lhs(snd(dest_forall(concl th1)))) in
let rr = rator rrand in
       let r' = variant [r] r in
       let r_eq_r' = mk_eq (r, r') in
       let ppr = mk_comb(pp, r) in
       let ppr' = mk_comb(pp, r') in
       let as1 = ASSUME ppr in
       let as2 = ASSUME ppr' in
       let t1 = EQ_MP (SPEC r th2) as1 in
       let t2 = EQ_MP (SPEC r' th2) as2 in
       let eq = mk_eq(mk_comb(aa, r), mk_comb(aa, r')) in eq,t1,t2,AP_TERM rr (ASSUME eq),ppr,ppr';;
       let v1 = genvar(type_of r)
       ;et v2 = genvar(type_of r)
        i1 = DISCH eq (SUBST [v1 |-> t1, v2 |-> t2]
                            (mk_eq(v1,v2)) (AP_TERM R (ASSUME eq)))
       val i2    = DISCH r_eq_r' (AP_TERM A (ASSUME r_eq_r'))
       val thm   = IMP_ANTISYM_RULE i1 i2
       val disch = DISCH Pr (DISCH Pr' thm)
 *)

let IS_FMAP_RULES,IS_FMAP_INDUCT,IS_FMAP_CASES = new_inductive_definition
    `is_fmap (\a. INR one) /\
     (!f a b. is_fmap f ==> is_fmap (\x. if x=a then INL b else f x))`;;

let [IS_FMAP_EMPTY;IS_FMAP_UPDATE] = CONJUNCTS IS_FMAP_RULES;;

let IS_FMAP_STRONG = derive_strong_induction(IS_FMAP_RULES,IS_FMAP_INDUCT);;

let IS_FMAP_EXISTS = prove (`?x:'a -> 'b + 1. is_fmap x`, 
      EXISTS_TAC (`\x:'a. (INR one):'b + 1`) THEN REWRITE_TAC [IS_FMAP_EMPTY]);;

let FMAP_TY_DEF = new_type_definition "fmap" ("fmap_abs","fmap_rep") IS_FMAP_EXISTS;;


(* Injectivity & Surjectivity *)

let FMAP_REP_11 = prove (
    `!(f:(A,B)fmap) g. fmap_rep f = fmap_rep g <=> f = g`,
      REPEAT GEN_TAC THEN EQ_TAC THENL [
      DISCH_THEN (ASSUME_TAC o (AP_TERM `fmap_abs:(A->B+1)->(A,B)fmap`)) ; ALL_TAC ]
      THEN simp[FMAP_TY_DEF]);;

let FMAP_REP_ONTO = prove (
    `!r:A->B+1. is_fmap r <=> ?a. r = fmap_rep a`,
      GEN_TAC THEN EQ_TAC THENL [
      DISCH_THEN (ASSUME_TAC o (EQ_MP (ISPEC `r:A->B+1` (CONJUNCT2 FMAP_TY_DEF)))) THEN
      EXISTS_TAC `fmap_abs (r:A->B+1)` ;
      DISCH_THEN (CHOOSE_THEN SUBST1_TAC) ] THEN simp[FMAP_TY_DEF]);;

let FMAP_ABS_11 = prove (
    `!(f:A->B+1) g. is_fmap f ==> is_fmap g ==> (fmap_abs f = fmap_abs g <=> f = g)`,
      REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN EQ_TAC THENL [
      DISCH_THEN (ASSUME_TAC o (AP_TERM `fmap_rep:(A,B)fmap->(A->B+1)`)) THEN
      FIRST_X_ASSUM (SUBST1_TAC o GSYM o (EQ_MP (ISPEC `f:A->B+1` (CONJUNCT2 FMAP_TY_DEF)))) THEN
      FIRST_X_ASSUM (SUBST1_TAC o GSYM o (EQ_MP (ISPEC `g:A->B+1` (CONJUNCT2 FMAP_TY_DEF)))) ;
      ALL_TAC ] THEN simp[]);;

(* !a. ?r. a = fmap_abs r /\ is_fmap r *)
let FMAP_ABS_ONTO = prove_abs_fn_onto FMAP_TY_DEF;;


(* Cancellation theorems *)

let IS_FMAP_REP = prove (`!f:(A,B)fmap. is_fmap (fmap_rep f)`,simp[FMAP_TY_DEF]);;

let FMAP_REP_ABS_EMPTY = prove (
    `fmap_rep (fmap_abs ((\a. INR one):'a -> 'b + 1)) = \a. INR one`,
      REWRITE_TAC[REWRITE_RULE[FMAP_TY_DEF] IS_FMAP_EMPTY]);;

let FMAP_REP_ABS_UPDATE = prove (
    `!(f:(A,B)fmap) x y.
       fmap_rep (fmap_abs (\a. if a=x then INL y else fmap_rep f a))
         = \a. if a=x then INL y else fmap_rep f a`,
         GEN_TAC THEN
	 REWRITE_TAC[REWRITE_RULE[IS_FMAP_REP;FMAP_TY_DEF] (ISPEC `fmap_rep (f:(A,B)fmap)` IS_FMAP_UPDATE)]);;

let IS_FMAP_REP_ABS = prove (
    `!f:A->B+1. is_fmap f ==> (fmap_rep (fmap_abs f) = f)`,
      REWRITE_TAC[FMAP_TY_DEF]);;


(* Definitions of update, empty, apply, domain *)

let FUPDATE = new_definition `FUPDATE (f:(A,B)fmap) (x,y)
      = fmap_abs (\a. if a=x then INL y else fmap_rep f a)`;;

let FEMPTY = new_definition `FEMPTY:(A,B)fmap = fmap_abs (\a. INR one)`;;
							 
let FAPPLY = new_definition `FAPPLY (f:(A,B)fmap) x = OUTL (fmap_rep f x)`;;

let FDOM = new_definition `FDOM (f:(A,B)fmap) x = ISL (fmap_rep f x)`;;


let UPDATE_REP = new_basic_definition `update_rep = \(f:A->B+1) x y. \a. if a=x then INL y else f a`;;

let EMPTY_REP = new_basic_definition `empty_rep = (\a. INR one):A->B+1`;;


(* Syntax *)

parse_as_infix("|+",(18,"left"));; 
override_interface("|+",`FUPDATE`);;

let is_fmap_ty = ((=) "fmap") o fst o dest_type;;
let dest_fmap_ty ty =
  if (is_fmap_ty ty) then
  let _,args = dest_type ty in hd args, (hd o tl) args
  else failwith "dest_fmap_ty";;

let mk_fupdate f = curry mk_icomb (mk_icomb (`FUPDATE:(A,B)fmap->(A#B)->(A,B)fmap`,f));;
let dest_fupdate = dest_binary "FUPDATE";;
let is_fupdate = is_binary "FUPDATE";;

let list_mk_fupdate (f,updl) = rev_itlist (C mk_fupdate) updl f;;

let rec strip_fupdate x =
  if (is_fupdate x)
  then 
    let args = (snd o strip_comb) x in
    let ls,rs = hd args,(hd o tl) args in
    let f,res = strip_fupdate ls in
    f,res @ [rs]
  else x,[];;


(* Some theorems *)

let FAPPLY_FUPDATE = prove (`!(f:(A,B)fmap) x y. FAPPLY (FUPDATE f (x,y)) x = y`,
	       REWRITE_TAC[FUPDATE;FAPPLY;FMAP_REP_ABS_UPDATE;OUTL]);;

let NOT_EQ_FAPPLY = prove (
    `!(f:(A,B)fmap) a x y . ~(a=x) ==> (FAPPLY (FUPDATE f (x,y)) a = FAPPLY f a)`,
       simp[FUPDATE;FAPPLY;FMAP_REP_ABS_UPDATE;OUTL]);;

let UPDATE_COMMUTES_REP = prove (
    `!(f:A->B+1) a b c d. ~(a=c) ==> update_rep (update_rep f a b) c d = update_rep (update_rep f c d) a b`,
       GEN_ALL_TAC THEN REWRITE_TAC[UPDATE_REP] THEN DISCH_TAC THEN MATCH_MP_TAC EQ_EXT THEN GEN_TAC THEN
       BETA_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let FUPDATE_COMMUTES = prove (
    `!(f:(A,B)fmap) a b c d. ~(c=a) ==> FUPDATE (FUPDATE f (c,d)) (a,b) = FUPDATE (FUPDATE f (a,b)) (c,d)`,
       SIMP_TAC[FUPDATE;FMAP_REP_ABS_UPDATE;REWRITE_RULE[UPDATE_REP] UPDATE_COMMUTES_REP]);;

let UPDATE_SAME_REP = prove (
    `!(f:A->B+1) a b c. update_rep (update_rep f a b) a c = update_rep f a c`,
       GEN_ALL_TAC THEN REWRITE_TAC[UPDATE_REP] THEN MATCH_MP_TAC EQ_EXT THEN GEN_TAC THEN
       BETA_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let FUPDATE_EQ = prove (
    `!(f:(A,B)fmap) a b c. FUPDATE (FUPDATE f (a,b)) (a,c) = FUPDATE f (a,c)`,
       SIMP_TAC[FUPDATE;FMAP_REP_ABS_UPDATE;REWRITE_RULE[UPDATE_REP] UPDATE_SAME_REP]);;

let FDOM_FEMPTY = prove (
    `FDOM (FEMPTY:(A,B)fmap) = {}`,
       REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; FDOM;FEMPTY;FMAP_REP_ABS_EMPTY;IN;ISL]);;

let FDOM_UPDATE_REP = prove (
    `!f a b x. ISL(update_rep (f:'a -> 'b+1 ) a b x) = ((x=a) \/ ISL (f x))`,
       GEN_ALL_TAC THEN REWRITE_TAC[UPDATE_REP] THEN COND_CASES_TAC THEN REWRITE_TAC[ISL]);;

let FDOM_FUPDATE = prove (
    `!f a b. FDOM (FUPDATE (f:(A,B)fmap) (a,b)) = a INSERT FDOM f`,
       GEN_ALL_TAC THEN REWRITE_TAC[EXTENSION;IN_INSERT;IN;FDOM;FUPDATE;FMAP_REP_ABS_UPDATE;
				    REWRITE_RULE[UPDATE_REP] FDOM_UPDATE_REP]);;

let FAPPLY_FUPDATE_THM = prove (
    `!(f:(A,B)fmap) a b x. FAPPLY(FUPDATE f (a,b)) x = if x=a then b else FAPPLY f x`,
       GEN_ALL_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[FAPPLY_FUPDATE;NOT_EQ_FAPPLY]);;

let NOT_EQ_EMPTY_UPDATE_REP = prove (
    `!(f:A->B+1) a b. ~(empty_rep = update_rep f a b)`,
       GEN_ALL_TAC THEN REWRITE_TAC[EMPTY_REP;UPDATE_REP] THEN
       DISCH_THEN (MP_TAC o GEN_ALL o BETA_RULE o (fun x -> AP_THM x `x:A`)) THEN
       REWRITE_TAC[NOT_FORALL_THM] THEN EXISTS_TAC `a:A` THEN REWRITE_TAC[distinctness "sum"]);;

let NOT_EQ_FEMPTY_FUPDATE = prove (
    `!(f:(A,B)fmap) a b. ~(FEMPTY = FUPDATE f (a,b))`,
       GEN_ALL_TAC THEN
       DISCH_THEN (MP_TAC o (AP_TERM `FDOM:(A,B)fmap->A->bool`)) THEN
       REWRITE_TAC[FDOM_FEMPTY;FDOM_FUPDATE;NOT_EMPTY_INSERT]);;

let FDOM_EQ_FDOM_FUPDATE = prove (
    `!(f:(A,B)fmap) x. x IN FDOM f ==> (!y. FDOM (FUPDATE f (x,y)) = FDOM f)`,
       REWRITE_TAC[FDOM_FUPDATE] THEN SET_TAC[]);;


let IS_FMAP_STRONG_META_RULE = prove (
    `(P:(A,B)fmap->bool) (fmap_abs (\a. INR one))
     ===> (!f a b.
              is_fmap f
              ==> P (fmap_abs f)
              ==> P (fmap_abs (\x. if x = a then INL b else f x)))
     ===> (is_fmap a ==> P (fmap_abs a))`,
       MIMP_TAC THEN DISCH_TAC THEN DISCH_TAC THEN 
       MP_THEN ASSUME_TAC (REWRITE_RULE[o_DEF;GSYM IMP_IMP]
				       (ISPEC `((P:(A,B)fmap->bool) o fmap_abs)` IS_FMAP_STRONG)) THEN
       FIRST_X_ASSUM (MP_THEN ASSUME_TAC) THEN assumption);;

let FMAP_SIMPLE_INDUCT = prove (
    `!P:(A,B)fmap->bool.
        P FEMPTY /\
        (!f. P f ==> !x y. P (FUPDATE f (x,y)))
        ==>
        !f. P f`,
       REWRITE_TAC[FUPDATE;FEMPTY] THEN GEN_ALL_TAC THEN STRIP_TAC THEN GEN_TAC THEN
       CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) (ISPEC `f:(A,B)fmap` FMAP_ABS_ONTO) THEN
       erule IS_FMAP_STRONG_META_RULE THEN GEN_ALL_TAC THEN
       FIRST_X_ASSUM (ASSUME_TAC o (SPEC `fmap_abs f:(A,B)fmap`)) THEN
       DISCH_THEN ((fun x -> REWRITE_ASM_TAC[x]) o (MATCH_MP IS_FMAP_REP_ABS)) THEN
       DISCH_TAC THEN FIRST_X_ASSUM (MP_THEN ASSUME_TAC) THEN assumption);;

let FMAP_SIMPLE_INDUCT_TAC = MATCH_MP_TAC FMAP_SIMPLE_INDUCT THEN CONJ_TAC;;


let FDOM_EQ_EMPTY = prove(
    `!f:(A,B)fmap. (FDOM f = {}) <=> (f = FEMPTY)`,
       GEN_TAC THEN EQ_TAC THENL
       [ SPEC_TAC (`f:(A,B)fmap`,`f:(A,B)fmap`) ; SIMP_TAC[FDOM_FEMPTY]] THEN
       FMAP_SIMPLE_INDUCT_TAC THENL
       [ DISCH_TAC THEN REFL_TAC ; REWRITE_TAC[FDOM_FUPDATE] THEN SET_TAC[]]);;

let FUPDATE_ABSORB_THM = prove (
    `!(f:(A,B)fmap) x y.
       x IN FDOM f /\ (FAPPLY f x = y) ==> (FUPDATE f (x,y) = f)`,
       FMAP_SIMPLE_INDUCT_TAC THENL
       [ REWRITE_TAC[FDOM_FEMPTY;NOT_IN_EMPTY] ; GEN_TAC THEN DISCH_TAC THEN GEN_ALL_TAC ] THEN
       REWRITE_TAC[FDOM_FUPDATE;IN_INSERT] THEN case_tac `x=x'` THEN simp[FAPPLY_FUPDATE_THM] THENL
       [ meson[FUPDATE_COMMUTES] ; simp[FUPDATE_EQ] ]);;

let FDOM_FAPPLY = prove (
    `!(f:(A,B)fmap) x. x IN FDOM f ==> ?y. FAPPLY f x = y`,
       FMAP_SIMPLE_INDUCT_TAC THEN REWRITE_TAC[FDOM_FEMPTY;NOT_IN_EMPTY;FDOM_FUPDATE;IN_INSERT] THEN
       meson[]);;

let FDOM_FUPDATE_ABSORB = prove (
    `!(f:(A,B)fmap) x. x IN FDOM f ==> ?y. FUPDATE f (x,y) = f`,
       GEN_ALL_TAC THEN DISCH_TAC THEN
       FIRST_ASSUM ((CHOOSE_THEN ASSUME_TAC) o (MATCH_MP FDOM_FAPPLY)) THEN
       MATCH_EXISTS_TAC `y` THEN simp[FUPDATE_ABSORB_THM]);;

let FDOM_F_FEMPTY = prove (
    `!f:(A,B)fmap. (!a. ~(a IN FDOM f)) = (f = FEMPTY)`,
      FMAP_SIMPLE_INDUCT_TAC THEN 
      REWRITE_TAC[FDOM_FEMPTY;NOT_IN_EMPTY;FDOM_FUPDATE;IN_INSERT;NOT_EQ_FEMPTY_FUPDATE] THEN
      meson[]);;

let FDOM_FINITE = prove (
    `!f:(A,B)fmap. FINITE (FDOM f)`,
      FMAP_SIMPLE_INDUCT_TAC THEN
      REWRITE_TAC[FDOM_FEMPTY;FDOM_FUPDATE;FINITE_RULES;FINITE_INSERT]);;


extend_basic_rewrites[
IN_INTER;
INTER_EMPTY;
NOT_IN_EMPTY;
IN_INSERT;
UNION_EMPTY;
FAPPLY_FUPDATE;
FUPDATE_EQ;
FDOM_FEMPTY;
FDOM_FUPDATE;
NOT_EQ_FEMPTY_FUPDATE;
FDOM_FINITE];;


let FAPPLY_FUPD_EQ = prove ( `!fmap k1 v1 k2 v2.
   (FAPPLY (fmap |+ (k1, v1)) k2 = v2) <=> 
   (k1 = k2 /\ v1 = v2 \/ ~(k1 = k2) /\ FAPPLY fmap k2 = v2)`,
   SIMP_TAC[FAPPLY_FUPDATE_THM; EQ_IMP_THM] THEN MESON_TAC[]);;


(* Cardinality *)

let FCARD = new_definition `!fm . FCARD fm = CARD (FDOM fm)`;;

(* Basic cardinality properties *)

let FCARD_FEMPTY = prove (`FCARD FEMPTY = 0`, REWRITE_TAC[FCARD;CARD_CLAUSES]);;

let FCARD_FUPDATE = prove (
    `!fm a b. FCARD (FUPDATE fm (a,b)) = if a IN FDOM fm then FCARD fm else SUC (FCARD fm)`,
       simp[FCARD;CARD_CLAUSES]);;

let FCARD_FUPDATE_1 = prove (
    `!fm a b. FCARD (FUPDATE fm (a,b)) = if a IN FDOM fm then FCARD fm else 1 + FCARD fm`,
       simp[FCARD;CARD_CLAUSES] THEN ARITH_TAC);;


let FCARD_0_FEMPTY_LEMMA = prove (`!f. (FCARD f = 0) ==> (f = FEMPTY)`,
       FMAP_SIMPLE_INDUCT_TAC THEN REWRITE_TAC[NOT_EQ_FEMPTY_FUPDATE;FCARD_FUPDATE] THEN
       GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN COND_CASES_TAC THENL [
       DISCH_TAC THEN FIRST_X_ASSUM (MP_THEN ASSUME_TAC) THEN simp[] ;
       ARITH_TAC]);;

let FCARD_0_FEMPTY = prove ( `!f:(A,B)fmap. FCARD f = 0 <=> f = FEMPTY`,
       GEN_TAC THEN EQ_TAC THENL [ REWRITE_TAC[FCARD_0_FEMPTY_LEMMA] ; SIMP_TAC[FCARD_FEMPTY]]);;


let FCARD_SUC_LEFT_LEMMA = prove (
   `!(f:(A,B)fmap) n. (FCARD f = SUC n) ==> (?f' x y. ~(x IN FDOM f') /\ (FCARD f' = n) /\
                      (f = FUPDATE f' (x, y)))`,
      FMAP_SIMPLE_INDUCT_TAC THEN REWRITE_TAC[FCARD_FEMPTY;NOT_SUC;FCARD_FUPDATE] THEN
      REPEAT STRIP_TAC THEN case_tac `(x:A) IN FDOM (f:(A,B)fmap)` THENL [
      MAP_EVERY MATCH_EXISTS_TAC [`f`;`x`;`y`] ; ALL_TAC ] THEN simp[SUC_INJ] THEN
      FIRST_X_ASSUM (MATCH_MP_THEN (REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC)) THEN
      case_tac `(x:A) = (x':A)` THENL [
      MAP_EVERY MATCH_EXISTS_TAC [`FUPDATE f' (x,y)`;`x'`;`y'`] ;
      MAP_EVERY MATCH_EXISTS_TAC [`f'`;`x'`;`y`] ] THEN
      simp[FDOM_FUPDATE;FCARD_FUPDATE;FUPDATE_COMMUTES]);;

let FCARD_SUC_RIGHT_LEMMA = prove (
   `!(f:(A,B)fmap) n. (?f' x y. ~(x IN FDOM f') /\ (FCARD f' = n) /\
                     (f = FUPDATE f' (x, y))) ==> (FCARD f = SUC n)`,
      REWRITE_TAC[IMP_CONJ;FORALL_AND_THM;GSYM LEFT_FORALL_IMP_THM] THEN
      FMAP_SIMPLE_INDUCT_TAC THEN REWRITE_TAC[FCARD_FEMPTY;NOT_SUC;FCARD_FUPDATE] THEN
      GEN_TAC THEN REPEAT DISCH_TAC THEN GEN_ALL_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
      DISCH_THEN (ASSUME_TAC o (AP_TERM `FCARD:(A,B)fmap->num`)) THEN simp[FCARD_FUPDATE]);;

let FCARD_SUC = prove (
   `!(f:(A,B)fmap) n. (FCARD f = SUC n) <=> (?f' x y. ~(x IN FDOM f') /\ (FCARD f' = n) /\
                      (f = FUPDATE f' (x, y)))`,
      GEN_ALL_TAC THEN EQ_TAC THEN REWRITE_TAC[FCARD_SUC_LEFT_LEMMA;FCARD_SUC_RIGHT_LEMMA]);;


(* A more useful induction theorem *)

(* We don't have Induct_on in HOL Light so we force it through the subgoal. *)
(* MESON makes the jump from the subgoal and the actual goal. *)

let fmap_INDUCT = prove (
   `!P. P FEMPTY /\
       (!f:(A,B)fmap. P f ==> !x y. ~(x IN FDOM f) ==> P (FUPDATE f (x,y)))
          ==>
       !f. P f`,
       REPEAT STRIP_TAC THEN subgoal_tac `!n f. FCARD (f:(A,B)fmap) = n ==> P f` THENL [
       INDUCT_TAC THEN GEN_TAC THEN DISCH_TAC THEN simp[FCARD_0_FEMPTY;FCARD_SUC] THEN
       FIRST_X_ASSUM (REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN simp[]; meson[]]);;

let FMAP_INDUCT_TAC = MATCH_MP_TAC fmap_INDUCT THEN CONJ_TAC THENL [ ALL_TAC;
				   GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC ];;

let FM_PULL_APART = prove (
    `!fm (k:A). k IN FDOM fm ==> ?fm0 v. (fm = FUPDATE fm0 (k, v)) /\
                                 ~(k IN FDOM fm0)`,
   FMAP_INDUCT_TAC THEN simp[] THEN REPEAT STRIP_TAC THEN simp[] THENL
   [ meson[] ; FIRST_X_ASSUM (MATCH_MP_THEN ASSUME_TAC) ] THEN
   MAP_EVERY (FIRST_X_ASSUM o X_MATCH_CHOOSE_TAC) [`fm0`;`v`] THEN
   SUBGOAL_TAC "" `~((k:A)=x)` [meson[]] THEN
   MAP_EVERY MATCH_EXISTS_TAC [`FUPDATE fm0 (x, y)`;`v`] THEN
   simp[FUPDATE_COMMUTES]);;


(* Equality of finite maps *)

let FUPDATE_EQ_NOT_X = prove (
   `!(f:(A,B)fmap) x.
      ?f'. !y. (FUPDATE f (x,y) = FUPDATE f' (x,y)) /\ ~(x IN FDOM f')`,
      FMAP_INDUCT_TAC THENL [
      GEN_TAC THEN MATCH_EXISTS_TAC `FEMPTY` THEN REWRITE_TAC[] ;
      DISCH_TAC THEN GEN_TAC ] THEN
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (SPEC `x':A`)) THEN case_tac `x:A = x'` THENL [
      MATCH_EXISTS_TAC `FUPDATE f' (x,y)` THEN GEN_TAC THEN simp[] THEN meson[FUPDATE_COMMUTES];
      MATCH_EXISTS_TAC `f` THEN simp[] THEN simp[]]);;

let NOT_FDOM_FAPPLY_FEMPTY = prove (
   `!(f:(A,B)fmap) x. ~(x IN FDOM f) ==> (FAPPLY f x = FAPPLY FEMPTY x)`,
      FMAP_INDUCT_TAC THENL [ REWRITE_TAC[] ; DISCH_TAC THEN GEN_TAC ] THEN
      case_tac `x':A = x` THEN simp[NOT_EQ_FAPPLY]);;

let FMAP_EQ_1 = prove (`!(f:(A,B)fmap) g. (f=g) ==> (FDOM f = FDOM g) /\ (FAPPLY f = FAPPLY g)`,simp[]);;

let FMAP_EQ_2 = prove (`!(f:(A,B)fmap) g. (FDOM f = FDOM g) /\ (FAPPLY f = FAPPLY g) ==> (f = g)`,
   FMAP_INDUCT_TAC THENL [ meson[FCARD_0_FEMPTY;FCARD] ; simp[]] THEN REPEAT STRIP_TAC THEN
   SUBGOAL_TAC "" `?h:(A,B)fmap. (FUPDATE g (x, FAPPLY g x) = FUPDATE h (x, FAPPLY g x)) /\ ~(x IN FDOM h)` [meson[FUPDATE_EQ_NOT_X]] THEN
   SUBGOAL_TAC "" `x IN FDOM (g:(A,B)fmap)` [meson[IN_INSERT]] THEN
   SUBGOAL_TAC "" `FUPDATE (g:(A,B)fmap) (x, FAPPLY g x) = g` [simp[FUPDATE_ABSORB_THM]] THEN
   FIRST_X_ASSUM (X_MATCH_CHOOSE_TAC `h:(A,B)fmap`) THEN
   FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC) THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM (SUBST_ALL_TAC o GSYM) THEN
   SUBGOAL_TAC "" `!v. FAPPLY (FUPDATE (f:(A,B)fmap) (x, y)) v = FAPPLY (FUPDATE h (x, FAPPLY g x)) v` [meson[]] THEN
   SUBGOAL_TAC "" `y = FAPPLY (g:(A,B)fmap) x` [meson[FAPPLY_FUPDATE]] THEN
   ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [
    simp[EXTENSION;FDOM_FUPDATE] THEN meson[] ;
   REWRITE_TAC[FUN_EQ_THM] ] THEN
  X_GEN_TAC `z:A` THEN case_tac `x:A = z` THENL [
   FIRST_X_ASSUM (MP_TAC o (SPEC `z:A`)) THEN simp[FAPPLY_FUPDATE_THM] ;
   meson[NOT_FDOM_FAPPLY_FEMPTY] ]);;


let FMAP_EQ = prove (`!(f:(A,B)fmap) g. (FDOM f = FDOM g) /\ (FAPPLY f = FAPPLY g) <=> (f = g)`,
   REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[FMAP_EQ_1; FMAP_EQ_2]);;

(* A more useful equality *)
let FMAP_EQ_THM = prove (
    `!(f:(A,B)fmap) g. (FDOM f = FDOM g /\ (!x. x IN FDOM f ==> (FAPPLY f x = FAPPLY g x)))
                       <=> (f = g)`,
   REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[GSYM FMAP_EQ] THEN
   MATCH_MP_TAC EQ_EXT THEN GEN_TAC THEN
   case_tac `x IN FDOM (f:(A,B)fmap)` THEN meson[NOT_FDOM_FAPPLY_FEMPTY]);;


let FMAP_EXT = GSYM FMAP_EQ_THM;;



(* Submaps *)

let SUBMAP = new_definition `!(f:(A,B)fmap) g. SUBMAP f g =
			       !x. x IN FDOM f ==> x IN FDOM g /\ (FAPPLY f x = FAPPLY g x)`;;

parse_as_infix("SUBMAP",(16,"right"));;


let SUBMAP_FEMPTY = prove (`!(f:(A,B)fmap) . FEMPTY SUBMAP f`, REWRITE_TAC[SUBMAP]);;

let SUBMAP_REFL = prove (`!(f:(A,B)fmap) . f SUBMAP f`, REWRITE_TAC[SUBMAP]);;

let SUBMAP_ANTISYM = prove (`!(f:(A,B)fmap) g. (f SUBMAP g /\ g SUBMAP f) <=> f = g`,
   REPEAT GEN_TAC THEN EQ_TAC THENL [
    REWRITE_TAC[SUBMAP;FMAP_EXT;EXTENSION] THEN MESON_TAC[] ;
    DISCH_TAC THEN ASM_REWRITE_TAC[SUBMAP_REFL] ]);;

let SUBMAP_TRANS = prove (`!f g h. f SUBMAP g /\ g SUBMAP h ==> f SUBMAP h`, SIMP_TAC[SUBMAP]);;

let SUBMAP_FUPDATE = prove (`!f k v. ~(k IN FDOM f) ==> f SUBMAP (FUPDATE f (k,v))`,
   SIMP_TAC[SUBMAP] THEN meson[FAPPLY_FUPDATE_THM]);;

let EQ_FDOM_SUBMAP = prove (`!f g. (f = g) <=> f SUBMAP g /\ (FDOM f = FDOM g)`, 
   REWRITE_TAC[FMAP_EXT;SUBMAP] THEN MESON_TAC[]);;

let SUBMAP_FUPDATE_EQN = prove (`!f x y. f SUBMAP (FUPDATE f (x,y)) <=> ~(x IN FDOM f) \/ (FAPPLY f x = y)`,
   SIMP_TAC[FAPPLY_FUPDATE_THM;SUBMAP;EQ_IMP_THM] THEN MESON_TAC[]);;

extend_basic_rewrites[SUBMAP_FUPDATE_EQN];;



(* Restriction *)

let FMAP_RES_LEMMA = prove (`!(f:(A,B)fmap) r.
     ?res. (FDOM res = FDOM f INTER r)
       /\  (!x. FAPPLY res x = if x IN FDOM f INTER r then FAPPLY f x else FAPPLY FEMPTY x)`,
   FMAP_INDUCT_TAC THENL [
    GEN_TAC THEN MATCH_EXISTS_TAC `FEMPTY` THEN REWRITE_TAC[IN_INTER;INTER_EMPTY] ;
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM ((X_MATCH_CHOOSE_TAC `res`) o SPEC_ALL) THEN
    FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC) THEN case_tac `(x:A) IN r` ] THENL [
   MATCH_EXISTS_TAC `res` ;
   MATCH_EXISTS_TAC `FUPDATE res (x,y)` ] THEN
   SIMP_TAC[FAPPLY_FUPDATE_THM;EXTENSION] THENL [ CONJ_TAC THEN GEN_TAC ; ALL_TAC ] THEN
   simp[IN_INTER] THEN meson[]);;


let DRESTRICT = new_specification ["DRESTRICT"] (CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) FMAP_RES_LEMMA);;

let [FDOM_DRESTRICT;FAPPLY_DRESTRICT] = ((map GEN_ALL) o CONJUNCTS o SPEC_ALL) DRESTRICT;;

let DRESTRICT_FEMPTY = prove (`!r. DRESTRICT FEMPTY r = FEMPTY`, 
   REWRITE_TAC[FMAP_EXT;DRESTRICT;IN_INTER;INTER_EMPTY]);;

let DRESTRICT_FUPDATE = prove (`!(f:(A,B)fmap) r x y.
     DRESTRICT (FUPDATE f (x,y)) r =
        if x IN r then FUPDATE (DRESTRICT f r) (x,y) else DRESTRICT f r`,
   SIMP_TAC[DRESTRICT_FEMPTY;FMAP_EXT;FDOM_DRESTRICT;FAPPLY_DRESTRICT;FAPPLY_FUPDATE_THM;EXTENSION] THEN 
   REPEAT GEN_TAC THEN CONJ_TAC THEN GEN_TAC THENL [
    EQ_TAC THEN COND_CASES_TAC THEN simp[FDOM_DRESTRICT;FDOM_FUPDATE] THEN meson[] ;
    simp[DRESTRICT_FEMPTY;FMAP_EXT;FDOM_DRESTRICT;FAPPLY_DRESTRICT;FAPPLY_FUPDATE_THM;EXTENSION] THEN
    REPEAT COND_CASES_TAC THEN
    simp[DRESTRICT_FEMPTY;FMAP_EXT;FDOM_DRESTRICT;FAPPLY_DRESTRICT;FAPPLY_FUPDATE_THM;EXTENSION]]);;

let STRONG_DRESTRICT_FUPDATE = prove (`!(f:(A,B)fmap) r x y.
      x IN r ==> (DRESTRICT (FUPDATE f (x,y)) r =
                  FUPDATE (DRESTRICT f (r DELETE x)) (x,y))`,
   SIMP_TAC [DRESTRICT_FEMPTY;DRESTRICT_FUPDATE;FMAP_EXT;
	     FDOM_DRESTRICT;FAPPLY_DRESTRICT;FAPPLY_FUPDATE_THM;EXTENSION;IN_DELETE] THEN 
   meson[]);;

(* let NOT_FDOM_DRESTRICT = prove (`!(f:(A,B)fmap) x. ~(x IN FDOM f) ==> (DRESTRICT f (COMPL {x}) = f)`,);; *)

let DRESTRICT_SUBMAP = prove (`!(f:(A,B)fmap) r. (DRESTRICT f r) SUBMAP f`,
   FMAP_INDUCT_TAC THENL [ 
    REWRITE_TAC[DRESTRICT_FEMPTY;SUBMAP_FEMPTY] ;
    simp[DRESTRICT;SUBMAP] ]);;

let DRESTRICT_DRESTRICT = prove (
   `!(f:(A,B)fmap) P Q. DRESTRICT (DRESTRICT f P) Q = DRESTRICT f (P INTER Q)`,
   FMAP_INDUCT_TAC THEN simp[DRESTRICT_FEMPTY;DRESTRICT_FUPDATE] THEN
   REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN 
   simp[DRESTRICT_FUPDATE] THEN FIRST_ASSUM CONTR_TAC);;

let DRESTRICT_IS_FEMPTY = prove (`!f:(A,B)fmap. DRESTRICT f {} = FEMPTY`,
   GEN_TAC THEN
   SUBGOAL_TAC "" `FDOM (DRESTRICT (f:(A,B)fmap) {}) = {}` [SIMP_TAC[FDOM_DRESTRICT]] THEN
   simp[FDOM_EQ_EMPTY]);;

(* let FUPDATE_DRESTRICT = prove (
   `!(f:(A,B)fmap) x y. FUPDATE f (x,y) = FUPDATE (DRESTRICT f (COMPL {x})) (x,y)`, );; *)

(* let STRONG_DRESTRICT_FUPDATE_THM = prove (
   `!(f:(A,B)fmap) r x y. DRESTRICT (FUPDATE f (x,y)) r = 
       if x IN r then FUPDATE (DRESTRICT f (COMPL {x} INTER r)) (x,y)
       else DRESTRICT f (COMPL {x} INTER r)`, );; *)

let DRESTRICT_UNIV = prove (`!(f:(A,B)fmap). DRESTRICT f UNIV = f`,
   SIMP_TAC[DRESTRICT;FMAP_EXT] THEN REWRITE_TAC[INTER_UNIV]);;

let SUBMAP_DRESTRICT = prove (`!(f:(A,B)fmap) P. DRESTRICT f P SUBMAP f`, SIMP_TAC[DRESTRICT;SUBMAP]);;

extend_basic_rewrites[
DRESTRICT_FEMPTY;
DRESTRICT_FUPDATE;
DRESTRICT_SUBMAP;
DRESTRICT_DRESTRICT;
SUBMAP_DRESTRICT];;


(* Union *)

let FUNION_LEMMA = prove (`!(f:(A,B)fmap) g.
     ?union.
       (FDOM union = FDOM f UNION FDOM g) /\
       (!x. FAPPLY union x = if x IN FDOM f then FAPPLY f x else FAPPLY g x)`,
   FMAP_INDUCT_TAC THENL[
    GEN_TAC THEN MATCH_EXISTS_TAC `g` THEN SIMP_TAC[] ;
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (X_MATCH_CHOOSE_TAC `union` o SPEC `g:(A,B)fmap`) THEN
    MATCH_EXISTS_TAC `FUPDATE union (x,y)` THEN
    simp[FAPPLY_FUPDATE_THM;EXTENSION;IN_INSERT;INSERT_UNION;IN_UNION] THEN
    meson[]]);;

let FUNION = new_specification ["FUNION"] (CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) FUNION_LEMMA);;

let [FDOM_FUNION;FAPPLY_FUNION] = ((map GEN_ALL) o CONJUNCTS o SPEC_ALL) FUNION;;


let FUNION_FEMPTY_1 = prove (`!g. FUNION FEMPTY g = g`, SIMP_TAC[FMAP_EXT;FUNION]);;

let FUNION_FEMPTY_2 = prove (`!g. FUNION g FEMPTY = g`, SIMP_TAC[FMAP_EXT;FUNION]);;

let FUNION_FEMPTY = CONJ FUNION_FEMPTY_1 FUNION_FEMPTY_2;;

let FUNION_FUPDATE_1 = prove (`!(f:(A,B)fmap) g x y.
     FUNION (FUPDATE f (x,y)) g = FUPDATE (FUNION f g) (x,y)`,
   SIMP_TAC[FMAP_EXT;FUNION;FAPPLY_FUPDATE_THM;EXTENSION] THEN
   REPEAT GEN_TAC THEN CONJ_TAC THEN GEN_TAC THEN
   REPEAT COND_CASES_TAC THEN meson[IN_UNION;INSERT_UNION;IN_INSERT]);; 

let FUNION_FUPDATE_2 = prove (`!(f:(A,B)fmap) g x y.
     FUNION f (FUPDATE g (x,y)) =
        if x IN FDOM f then FUNION f g
        else FUPDATE (FUNION f g) (x,y)`,
   SIMP_TAC [FMAP_EXT;FUNION;FAPPLY_FUPDATE_THM;EXTENSION] THEN
   REPEAT GEN_TAC THEN CONJ_TAC THEN GEN_TAC THENL [
    REPEAT COND_CASES_TAC THEN simp[FUNION;IN_UNION] ;
    REPEAT COND_CASES_TAC THEN simp[FMAP_EXT;FUNION;FAPPLY_FUPDATE_THM;EXTENSION] ] THEN
   meson[]);;

let FUNION_FUPDATE = CONJ FUNION_FUPDATE_1 FUNION_FUPDATE_2;;

let FUNION_DRESTRICT = prove (`!(f:(A,B)fmap) r q.
     DRESTRICT f (r UNION q) = FUNION (DRESTRICT f r) (DRESTRICT f q)`,
   SIMP_TAC [FMAP_EXT;FUNION;FAPPLY_FUPDATE_THM;EXTENSION;DRESTRICT] THEN
   REPEAT GEN_TAC THEN CONJ_TAC THEN GEN_TAC THENL [
    ALL_TAC ; REPEAT COND_CASES_TAC ] THEN
   ASM SET_TAC[]);;

let FUNION_IDEMPOT = prove (`!f. FUNION f f = f`, FMAP_INDUCT_TAC THEN simp[FUNION_FEMPTY;FUNION_FUPDATE]);;



(* Merging *)

let FMERGE_EXISTS = prove (`!m (f:(A,B)fmap) g.
     ?merge.
       (FDOM merge = FDOM f UNION FDOM g) /\
       (!x. FAPPLY merge x = if ~(x IN FDOM f) then FAPPLY g x else
					 if ~(x IN FDOM g) then FAPPLY f x else
					(m (FAPPLY f x) (FAPPLY g x)))`,
   GEN_TAC THEN GEN_TAC THEN FMAP_INDUCT_TAC THENL [
    MATCH_EXISTS_TAC `f` THEN SIMP_TAC[UNION_EMPTY] THEN
    meson[NOT_FDOM_FAPPLY_FEMPTY] ;
    FIRST_X_ASSUM (X_MATCH_CHOOSE_TAC `merge`) THEN
    FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC) THEN
    DISCH_TAC THEN case_tac `x IN FDOM f` ] THENL [
     C_EXISTS_TAC `FUPDATE merge (x,y)` ;
     C_EXISTS_TAC `FUPDATE merge (x,m (FAPPLY f x) y)`
   ] THEN simp[] THEN REPEAT STRIP_TAC THENL [
    SET_TAC[] ; case_tac `x':A = x` ; SET_TAC[] ; case_tac `x':A = x`] THEN
    simp[FAPPLY_FUPDATE_THM]);;

let FMERGE = new_specification ["FMERGE"] (CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) FMERGE_EXISTS);;

let [FDOM_FMERGE;FAPPLY_FMERGE] = ((map GEN_ALL) o CONJUNCTS o SPEC_ALL) FMERGE;;


let FMERGE_FEMPTY = prove (
  `(!m f. FMERGE m f FEMPTY = f) /\ (!m f. FMERGE m FEMPTY f = f)`,
  SIMP_TAC[FMAP_EXT;FDOM_FMERGE;FAPPLY_FMERGE]);;

let FMERGE_FUNION = prove (`FUNION = FMERGE (\x y. x)`,
   SIMP_TAC[FUN_EQ_THM; FMERGE; FMAP_EXT; FUNION; IN_UNION] THEN MESON_TAC[]);;

let FUNION_FMERGE = prove (
  `!f1 f2 m. DISJOINT (FDOM f1) (FDOM f2) ==> FMERGE m f1 f2 = FUNION f1 f2`,
  SIMP_TAC[FUN_EQ_THM; FMERGE; FMAP_EXT; FUNION; IN_UNION; DISJOINT; INTER; EXTENSION] THEN MESON_TAC[]);;

let FMERGE_NO_CHANGE = 
  let thm = prove (`(!x. (P x = Q x)) ==> ((!x. P x) = (!x. Q x))`, MESON_TAC[]) in
  prove (
    `(!m f1 f2. FMERGE m f1 f2 = f1 <=>
	(!x. (x IN FDOM f2) ==> x IN FDOM f1 /\ m (FAPPLY f1 x) (FAPPLY f2 x) = FAPPLY f1 x)) /\
     (!m f1 f2. FMERGE m f1 f2 = f2 <=>
	(!x. (x IN FDOM f1) ==> x IN FDOM f2 /\ m (FAPPLY f1 x) (FAPPLY f2 x) = FAPPLY f2 x))`,
    SIMP_TAC[FMAP_EXT;EXTENSION;FMERGE;GSYM FORALL_AND_THM;IN_UNION] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC thm THEN GEN_TAC THENL [
	case_tac `x IN FDOM f1` ;
	case_tac `x IN FDOM f2`] THEN
      simp[] THEN meson[]);;

let FMERGE_COMM = prove(
  `!m. (!x y. FMERGE m x y = FMERGE m y x) <=> (!x y. m x y = m y x)`,
  SIMP_TAC[FMAP_EXT; FMERGE] THEN GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
    POP_ASSUM MP_TAC THEN SIMP_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
    C_EXISTS_TAC `FUPDATE FEMPTY (z,x)` THEN
    C_EXISTS_TAC `FUPDATE FEMPTY (z,y)` THEN
    SIMP_TAC[FDOM;IN_UNION] THEN MESON_TAC[] ;
    SIMP_TAC[UNION_COMM] ; 
    meson[IN_UNION]]);;

let FMERGE_ASSOC = prove (
  `!m. (!x y z. FMERGE m x (FMERGE m y z) = FMERGE m (FMERGE m x y) z) <=>
       (!x y z. m x (m y z) = m (m x y) z)`,
  SIMP_TAC[FMAP_EXT; FMERGE; UNION_ASSOC; IN_UNION] THEN GEN_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL [
   POP_ASSUM MP_TAC THEN SIMP_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
   C_EXISTS_TAC `FUPDATE FEMPTY (e,x)` THEN
   C_EXISTS_TAC `FUPDATE FEMPTY (e,y)` THEN
   C_EXISTS_TAC `FUPDATE FEMPTY (e,z)` THEN
   C_EXISTS_TAC `e` THEN REWRITE_TAC[IN_UNION] THEN meson[] ;
   simp[] THEN meson[] ;
   simp[] THEN meson[] ;
   simp[] THEN meson[] ]);;

let FMERGE_DRESTRICT = prove(
  `!f st1 st2 vs. DRESTRICT (FMERGE f st1 st2) vs =
                  FMERGE f (DRESTRICT st1 vs) (DRESTRICT st2 vs)`,
  SIMP_TAC[FMAP_EXT;DRESTRICT;FMERGE;EXTENSION;IN_INTER;IN_UNION] THEN MESON_TAC[]);;

let FMERGE_EQ_FEMPTY = prove (
  `!m f g. (FMERGE m f g = FEMPTY) <=> (f = FEMPTY /\ g = FEMPTY)`,
  SIMP_TAC[FMAP_EXT;FMERGE;EMPTY_UNION;IN_UNION] THEN
  REWRITE_TAC[FDOM_EQ_EMPTY] THEN REPEAT GEN_TAC THEN EQ_TAC THENL [
    REPEAT STRIP_TAC THEN simp[] ;
    REPEAT STRIP_TAC ] THENL [
    simp[] ; simp[] ;
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) ;
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) ] THEN
    REWRITE_ASM_TAC[] THEN FIRST_ASSUM CONTR_TAC);;



(* "assoc" for finite maps *)

let FLOOKUP = new_definition
  `FLOOKUP (f:(A,B)fmap) x = if x IN FDOM f then SOME (FAPPLY f x) else NONE`;;


let FLOOKUP_FEMPTY = prove (`!f. FLOOKUP FEMPTY f = NONE`, REWRITE_TAC[FLOOKUP]);;

let FLOOKUP_FUPDATE = prove ( `!fm k1 k2 v.
   FLOOKUP (FUPDATE fm (k1,v)) k2 = if k1 = k2 then SOME v else FLOOKUP fm k2`,
    SIMP_TAC[FLOOKUP;FAPPLY_FUPDATE_THM] THEN MESON_TAC[]);;

let FLOOKUP_SUBMAP = prove (
  `!f g k v. f SUBMAP g /\ FLOOKUP f k = SOME v ==> FLOOKUP g k = SOME v`,
  REWRITE_TAC[FLOOKUP;SUBMAP] THEN MESON_TAC[distinctness "option"]);;

let SUBMAP_FUPDATE_FLOOKUP = prove(
  `f SUBMAP (FUPDATE f (x,y)) <=> (FLOOKUP f x = NONE) \/ (FLOOKUP f x = SOME y)`,
  SIMP_TAC[FLOOKUP] THEN MESON_TAC[distinctness "option";injectivity "option"]);;


(* Some variance from original here because we don't have 'case'. *)
let FLOOKUP_FUNION_THM = prove (
  `!f1 f2 k. FLOOKUP (FUNION f1 f2) k =
    if FLOOKUP f1 k = NONE then FLOOKUP f2 k else FLOOKUP f1 k`,
      SIMP_TAC[FLOOKUP;FUNION;IN_UNION] THEN
	MESON_TAC[distinctness "option"]);;

let FLOOKUP_FUNION = prove (
  `!f1 f2 k v. FLOOKUP (FUNION f1 f2) k =
    let v = FLOOKUP f1 k in
    if v = NONE then FLOOKUP f2 k else v`,
      LET_TAC THEN POP_ASSUM (SUBST1_TAC o GSYM) THEN
	REWRITE_TAC[FLOOKUP_FUNION_THM]);;

let FLOOKUP_EXT = prove (`f1 = f2 <=> FLOOKUP f1 = FLOOKUP f2`,
   SIMP_TAC[FMAP_EXT;FUN_EQ_THM;FLOOKUP;IN] THEN
     MESON_TAC[distinctness "option";injectivity "option"]);;


(* Iterated updates *)

let FUPDATE_LIST = new_definition `FUPDATE_LIST = FOLDL FUPDATE`;;

parse_as_infix("|++",(17,"left"));; 
override_interface("|++",`FUPDATE_LIST`);;

let mk_fupdate_list f = curry mk_icomb (mk_icomb (`FUPDATE_LIST:(A,B)fmap->(A#B)list->(A,B)fmap`,f));;
let dest_fupdate_list = dest_binary "FUPDATE_LIST";;
let is_fupdate_list = is_binary "FUPDATE_LIST";;

let FUPDATE_LIST_THM = prove (
   `(!f. f |++ [] = f) /\
    (!f h t. f |++ (CONS h t) = (FUPDATE f h) |++ t)`,
   REWRITE_TAC[FUPDATE_LIST;FOLDL]);;

let [FUPDATE_LIST_NIL;FUPDATE_LIST_CONS] = CONJUNCTS FUPDATE_LIST_THM;;


let FUPDATE_LIST_APPLY_NOT_MEM = prove(
   `!kvl f k. ~MEM k (MAP FST kvl) ==> FAPPLY (f |++ kvl) k = FAPPLY f k`,
   LIST_INDUCT_TAC THEN simp[FUPDATE_LIST_THM] THEN
   REPEAT GEN_TAC THEN case_tac `h` THEN simp[FST;MAP;MEM;DE_MORGAN_THM;FAPPLY_FUPDATE_THM]);;

let FUPDATE_LIST_APPEND = prove (
   `!kvl1 kvl2 fm. fm |++ (APPEND kvl1 kvl2) = fm |++ kvl1 |++ kvl2`,
   LIST_INDUCT_TAC THEN simp[FUPDATE_LIST_THM;APPEND]);;

let FUPDATE_FUPDATE_LIST_COMMUTES = prove (
   `!kvl fm k v. ~MEM k (MAP FST kvl) ==> fm |+ (k,v) |++ kvl = (fm |++ kvl) |+ (k,v)`,
   LIST_INDUCT_TAC THEN simp[FUPDATE_LIST_THM] THEN
   REPEAT GEN_TAC THEN case_tac `h` THEN simp[FST;MAP;MEM;DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (ASSUME_TAC o (MATCH_MP FUPDATE_COMMUTES)) THEN simp[]);;

let FUPDATE_FUPDATE_LIST_MEM = prove (
   `!kvl fm k v. MEM k (MAP FST kvl) ==> (fm |+ (k,v) |++ kvl = fm |++ kvl)`,
   LIST_INDUCT_TAC THEN simp[FUPDATE_LIST_THM;MAP;MEM] THEN
   case_tac `h` THEN simp[FST] THEN REPEAT GEN_TAC THEN DISCH_THEN DISJ_CASES_TAC THENL
   [ simp[] ; case_tac `k = x` ] THEN simp[] THEN
   FIRST_X_ASSUM (ASSUME_TAC o (MATCH_MP FUPDATE_COMMUTES)) THEN simp[]);;

let FUPDATE_LIST_CONS_MEM = prove (
   `!kvl fm k v. MEM k (MAP FST kvl) ==> (fm |++ (CONS (k,v) kvl) = fm |++ kvl)`,
   REWRITE_TAC[FUPDATE_LIST_CONS;FUPDATE_FUPDATE_LIST_MEM]);;

let FUPDATE_EQ_FUPDATE_LIST = prove (
  `!fm k v. fm |+ (k,v) = fm |++ [k,v]`,
   REWRITE_TAC[FUPDATE_LIST;FOLDL]);;

let FUPDATE_LIST_FUPDATE_APPEND = prove (
  `!kvl fm x. (fm |++ kvl) |+ x = fm |++ (APPEND kvl [x])`,
   REWRITE_TAC[FUPDATE_LIST_APPEND;FUPDATE_LIST_THM]);;

let FUPDATE_LIST_FUPDATE_CONS = prove (
   `!(kvl:(A#B)list) fm k v. (fm |++ kvl) |+ (k,v) = fm |++ (CONS (k,v) (FILTER (\x. ~(k = FST x)) kvl))`,
   LIST_INDUCT_TAC THEN simp[FUPDATE_LIST_THM;FILTER] THEN REPEAT GEN_TAC THEN case_tac `h` THEN
   simp[FST] THEN COND_CASES_TAC THENL [
    FIRST_X_ASSUM (ASSUME_TAC o (MATCH_MP FUPDATE_COMMUTES)) THEN simp[FUPDATE_LIST_CONS] ;
    simp[FUPDATE_EQ] ]);;

let FDOM_FUPDATE_LIST = prove (
   `!kvl fm. FDOM (fm |++ kvl) = FDOM fm UNION set_of_list (MAP FST kvl)`,
   LIST_INDUCT_TAC THEN simp[FUPDATE_LIST_THM;MAP;set_of_list] THEN
   case_tac `h` THEN simp[] THEN SET_TAC[]);;

let IN_FDOM_FUPDATE_LIST = prove (
  `!x l. x IN FDOM (FEMPTY |++ l) <=> MEM x (MAP FST l)`, simp[FDOM_FUPDATE_LIST;IN_SET_OF_LIST]);;

let FUNION_FUPDATE_LIST_1 = prove ( `!l f g. FUNION (f |++ l) g = FUNION f g |++ l`,
   LIST_INDUCT_TAC THEN simp[FUPDATE_LIST_THM;FUNION_FEMPTY] THEN
   case_tac `h` THEN case_tac `MEM x (MAP FST t)` THENL [
    simp[FUPDATE_FUPDATE_LIST_COMMUTES;FUNION_FUPDATE] ;
    simp[FUPDATE_FUPDATE_LIST_MEM;FUNION_FUPDATE] ]);;

let FUNION_FUPDATE_LIST_2 = prove (
   `!l f g. FUNION f (g |++ l) = FUNION f g |++ (FILTER (\x. ~(FST x IN FDOM f)) l)`,
   LIST_INDUCT_TAC THEN simp[FUPDATE_LIST_THM;FUNION_FEMPTY;FILTER] THEN
   case_tac `h` THEN REPEAT GEN_TAC THEN
   COND_CASES_TAC THEN case_tac `MEM x (MAP FST t)` THEN
   simp[FUPDATE_FUPDATE_LIST_COMMUTES;FUPDATE_FUPDATE_LIST_MEM;FUNION_FUPDATE;FUPDATE_LIST_THM]);;

let FUNION_FUPDATE_LIST = CONJ FUNION_FUPDATE_LIST_1 FUNION_FUPDATE_LIST_2;;

let FUNION_FEMPTY_FUPDATE_LIST = prove ( `!f k l. FUNION (FEMPTY |++ l) (f |++ k) = f |++ (APPEND k l)`,
   simp[FUNION_FUPDATE_LIST;FILTER_T;FUNION_FEMPTY;FUPDATE_LIST_APPEND]);;



(* Iterated updates in reverse order *)

let FUPDATE_RLIST = new_definition `FUPDATE_RLIST fm l = FUPDATE_LIST fm (REVERSE l)`;;

parse_as_infix("|+++",(17,"left"));; 
override_interface("|+++",`FUPDATE_RLIST`);;

let mk_fupdate_rlist f = curry mk_icomb (mk_icomb (`FUPDATE_RLIST:(A,B)fmap->(A#B)list->(A,B)fmap`,f));;
let dest_fupdate_rlist = dest_binary "FUPDATE_RLIST";;
let is_fupdate_rlist = is_binary "FUPDATE_RLIST";;

let FUPDATE_RLIST_THM = prove (
   `(!f. f |+++ [] = f) /\
    (!f h t. f |+++ (CONS h t) = (f |+++ t) |+ h)`,
    REWRITE_TAC[FUPDATE_RLIST;REVERSE;GSYM FUPDATE_LIST_FUPDATE_APPEND;FUPDATE_LIST_NIL]);;
    
let [FUPDATE_RLIST_NIL;FUPDATE_RLIST_CONS] = CONJUNCTS FUPDATE_RLIST_THM;;

let FUPDATE_RLIST_APPLY_NOT_MEM = prove(
   `!kvl f k. ~MEM k (MAP FST kvl) ==> FAPPLY (f |+++ kvl) k = FAPPLY f k`,
   REPEAT GEN_TAC THEN DISCH_THEN (ASSUME_TAC o (ONCE_REWRITE_RULE[GSYM MEM_REVERSE])) THEN
   simp[MAP_REVERSE;FUPDATE_RLIST;FUPDATE_LIST_APPLY_NOT_MEM]);;

let FUPDATE_RLIST_APPEND = prove (
   `!kvl1 kvl2 fm. fm |+++ (APPEND kvl1 kvl2) = fm |+++ kvl2 |+++ kvl1`,
   simp[FUPDATE_RLIST;FUPDATE_LIST_APPEND;REVERSE_APPEND]);;

let FUPDATE_FUPDATE_RLIST_COMMUTES = prove (
   `!kvl fm k v. ~MEM k (MAP FST kvl) ==> fm |+ (k,v) |+++ kvl = (fm |+++ kvl) |+ (k,v)`,
   REPEAT GEN_TAC THEN DISCH_THEN (ASSUME_TAC o (ONCE_REWRITE_RULE[GSYM MEM_REVERSE])) THEN
   simp[FUPDATE_RLIST;FUPDATE_FUPDATE_LIST_COMMUTES;MAP_REVERSE]);;
											
let FUPDATE_FUPDATE_RLIST_MEM = prove (
   `!kvl fm k v. MEM k (MAP FST kvl) ==> (fm |+ (k,v) |+++ kvl = fm |+++ kvl)`,
   REPEAT GEN_TAC THEN DISCH_THEN (ASSUME_TAC o (ONCE_REWRITE_RULE[GSYM MEM_REVERSE])) THEN
   simp[FUPDATE_RLIST;FUPDATE_FUPDATE_LIST_MEM;MAP_REVERSE]);;

let FUPDATE_EQ_FUPDATE_RLIST = prove (
  `!fm x. fm |+ x = fm |+++ [x]`,
   REWRITE_TAC[FUPDATE_RLIST;REVERSE;APPEND;FUPDATE_LIST;FOLDL]);;
					
let FDOM_FUPDATE_RLIST = prove (
   `!kvl fm. FDOM (fm |+++ kvl) = FDOM fm UNION set_of_list (MAP FST kvl)`,
   simp[FUPDATE_RLIST;FDOM_FUPDATE_LIST;GSYM MAP_REVERSE;SET_OF_LIST_REVERSE]);;

let IN_FDOM_FUPDATE_LIST = prove (
  `!x l. x IN FDOM (FEMPTY |+++ l) <=> MEM x (MAP FST l)`, simp[FDOM_FUPDATE_RLIST;IN_SET_OF_LIST]);;

let FUNION_FUPDATE_RLIST_1 = prove ( `!l f g. FUNION (f |+++ l) g = FUNION f g |+++ l`,
   simp[FUPDATE_RLIST;FUNION_FUPDATE_LIST_1]);;
						  
let FUNION_FUPDATE_RLIST_2 = prove (
   `!l f g. FUNION f (g |+++ l) = FUNION f g |+++ (FILTER (\x. ~(FST x IN FDOM f)) l)`,
   simp[FUPDATE_RLIST;FUNION_FUPDATE_LIST_2;FILTER_REVERSE]);;

let FUNION_FUPDATE_RLIST = CONJ FUNION_FUPDATE_RLIST_1 FUNION_FUPDATE_RLIST_2;;

let FUNION_FEMPTY_FUPDATE_RLIST = prove ( `!f k l. FUNION (FEMPTY |+++ l) (f |+++ k) = f |+++ (APPEND l k)`,
   simp[FUPDATE_RLIST;FUNION_FEMPTY_FUPDATE_LIST;REVERSE_APPEND]);;


(* Other properties *)

let SUBMAP_FUNION_EQ = prove (
  `(!f1 f2 f3. DISJOINT (FDOM f1) (FDOM f2) ==>
              (f1 SUBMAP (FUNION f2 f3) = f1 SUBMAP f3)) /\
  (!f1 f2 f3. DISJOINT (FDOM f1) (FDOM f3 DIFF FDOM f2) ==>
              (f1 SUBMAP (FUNION f2 f3) = f1 SUBMAP f2))`,
   SIMP_TAC[EXTENSION; FUNION; IN_UNION; SUBMAP; DISJOINT; IN_DIFF] THEN MESON_TAC[]);;

let SUBMAP_FUNION = prove (
  `!f1 f2 f3. f1 SUBMAP f2 \/ (DISJOINT (FDOM f1) (FDOM f2) /\ f1 SUBMAP f3) ==>
             f1 SUBMAP FUNION f2 f3`, 
   SIMP_TAC[EXTENSION; FUNION; IN_UNION; SUBMAP; DISJOINT; IN_INTER] THEN MESON_TAC[]);;

let SUBMAP_FUNION_ID = prove (
  `(!f1 f2. f1 SUBMAP FUNION f1 f2) /\
  (!f1 f2. DISJOINT (FDOM f1) (FDOM f2) ==> f2 SUBMAP (FUNION f1 f2))`,
   SIMP_TAC[SUBMAP_REFL; SUBMAP_FUNION; DISJOINT_SYM]);;

let FEMPTY_SUBMAP = prove ( `!h. h SUBMAP FEMPTY = (h = FEMPTY)`,
   SIMP_TAC[FMAP_EXT; EXTENSION; SUBMAP] THEN MESON_TAC[]);;

let FUNION_EQ_FEMPTY = prove (
  `!h1 h2. (FUNION h1 h2 = FEMPTY) <=> (h1 = FEMPTY /\ h2 = FEMPTY)`,
   SIMP_TAC[FMAP_EXT; EXTENSION; FUNION; IN_UNION] THEN MESON_TAC[]);;

let FUNION_EQ = prove (
  `!f1 f2 f3. DISJOINT (FDOM f1) (FDOM f2) /\ DISJOINT (FDOM f1) (FDOM f3) ==>
             (FUNION f1 f2 = FUNION f1 f3 <=> f2 = f3)`,
   SIMP_TAC[GSYM SUBMAP_ANTISYM;FUNION;SUBMAP;IN_UNION;DISJOINT;EXTENSION;IN_INTER;IN_DIFF] THEN MESON_TAC[]);;

let FUNION_EQ_IMPL = prove ( `!f1 f2 f3.
    DISJOINT (FDOM f1) (FDOM f2) /\
    DISJOINT (FDOM f1) (FDOM f3) /\
    f2 = f3
  ==>
    (FUNION f1 f2 = FUNION f1 f3)`, SIMP_TAC[]);;

let FUNION_COMM = prove (
  `!f g. DISJOINT (FDOM f) (FDOM g) ==> (FUNION f g = FUNION g f)`,
   SIMP_TAC[FMAP_EXT;FUNION;IN_UNION;DISJOINT;EXTENSION;IN_INTER] THEN MESON_TAC[]);;

let FUNION_ASSOC = prove (
  `!f g h. (FUNION f (FUNION g h) = FUNION (FUNION f g) h)`,
   SIMP_TAC[FMAP_EXT;FUNION;IN_UNION;EXTENSION] THEN MESON_TAC[]);;

let DRESTRICT_FUNION = prove (
  `!h s1 s2. FUNION (DRESTRICT h s1) (DRESTRICT h s2) =
               DRESTRICT h (s1 UNION s2)`,
   SIMP_TAC[DRESTRICT;FMAP_EXT;EXTENSION;FUNION;IN_UNION;IN_INTER] THEN MESON_TAC[]);;

let DRESTRICT_IDEMPOT = prove (
  `!s vs. DRESTRICT (DRESTRICT s vs) vs = DRESTRICT s vs`, SIMP_TAC[INTER_IDEMPOT]);;

let SUBMAP_FUNION_ABSORPTION = prove (
  `!f g. f SUBMAP g = (FUNION f g = g)`, 
   SIMP_TAC[SUBMAP;FMAP_EXT;EXTENSION;FUNION] THEN SET_TAC[]);;
let SUBMAP_FUNION_ABSORB = SUBMAP_FUNION_ABSORPTION;;

(* (pseudo) injectivity results about fupdate *)

let FUPD11_SAME_KEY_AND_BASE = prove (
  `!f k v1 v2. (f |+ (k, v1) = f |+ (k, v2)) = (v1 = v2)`,
  MESON_TAC[FAPPLY_FUPDATE_THM]);;

let FUPD11_SAME_NEW_KEY = prove ( `!f1 f2 k v1 v2.
         ~(k IN FDOM f1) /\ ~(k IN FDOM f2) ==>
         (f1 |+ (k, v1) = f2 |+ (k, v2) <=> (f1 = f2) /\ (v1 = v2))`,
   SIMP_TAC[FMAP_EXT; FAPPLY_FUPDATE_THM; EXTENSION] THEN MESON_TAC[]);;

let SAME_KEY_UPDATES_DIFFER = prove (
  `!f1 f2 k v1 v2. ~(v1 = v2) ==> ~(f1 |+ (k, v1) = f2 |+ (k, v2))`,
  SIMP_TAC[FMAP_EXT;FAPPLY_FUPDATE_THM;EXTENSION] THEN MESON_TAC[]);;

let FUPD11_SAME_BASE = prove (`!f k1 v1 k2 v2.
        (f |+ (k1, v1) = f |+ (k2, v2)) <=> (
        k1 = k2 /\ v1 = v2 \/
        ~(k1 = k2) /\ k1 IN FDOM f /\ k2 IN FDOM f /\
        f |+ (k1, v1) = f /\ f |+ (k2, v2) = f)`,
   SIMP_TAC[FMAP_EXT;FAPPLY_FUPDATE_THM;EXTENSION] THEN MESON_TAC[]);;

let FUPD_SAME_KEY_UNWIND = prove (`!f1 f2 k v1 v2.
       f1 |+ (k, v1) = f2 |+ (k, v2) ==>
	   (v1 = v2 /\ (!v. f1 |+ (k, v) = f2 |+ (k, v)))`,
   SIMP_TAC[FMAP_EXT;FAPPLY_FUPDATE_THM;EXTENSION] THEN MESON_TAC[]);;
				  

let FUPDATE_ELIM = FUPDATE_ABSORB_THM;;
  (*prove (`!k v f.
    k IN FDOM f /\ FAPPLY f k = v ==> f |+ (k,v) = f`,
   SIMP_TAC[FMAP_EXT;FAPPLY_FUPDATE_THM;EXTENSION] THEN MESON_TAC[]);;
   *)


(* fupdate_NORMALISE_CONV *)

let fmap_EQ_UPTO = new_definition `fmap_EQ_UPTO f1 f2 vs =
  ((FDOM f1 INTER (COMPL vs) = FDOM f2 INTER (COMPL vs)) /\
  (!x. x IN FDOM f1 INTER (COMPL vs) ==> (FAPPLY f1 x = FAPPLY f2 x)))`;;

let fmap_EQ_UPTO___EMPTY = prove (`!f1 f2. (fmap_EQ_UPTO f1 f2 EMPTY) = (f1 = f2)`,
   REWRITE_TAC[fmap_EQ_UPTO;COMPL_EMPTY;INTER_UNIV;FMAP_EQ_THM;IN_UNIV]);;

let fmap_EQ_UPTO___EQ = prove (`!vs f. fmap_EQ_UPTO f f vs`, REWRITE_TAC[fmap_EQ_UPTO]);;

let fmap_EQ_UPTO___FUPDATE_BOTH = prove (`!f1 f2 ks k v.
    (fmap_EQ_UPTO f1 f2 ks) ==>
	 (fmap_EQ_UPTO (f1 |+ (k,v)) (f2 |+ (k,v)) (ks DELETE k))`,
   REWRITE_TAC[fmap_EQ_UPTO;EXTENSION;IN_COMPL;IN_DELETE] THEN
   REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN simp[FAPPLY_FUPDATE_THM] THENL [
    case_tac `x=k` THEN simp[] ;
    COND_CASES_TAC THEN meson[] ]);;

let fmap_EQ_UPTO___FUPDATE_BOTH___NO_DELETE = prove (`!f1 f2 ks k v.
    (fmap_EQ_UPTO f1 f2 ks) ==>
	 (fmap_EQ_UPTO (f1 |+ (k,v)) (f2 |+ (k,v)) ks)`,
   REWRITE_TAC[fmap_EQ_UPTO;EXTENSION;IN_COMPL] THEN
   REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN simp[FAPPLY_FUPDATE_THM] THENL [
    case_tac `x=k` THEN simp[] ;
    COND_CASES_TAC THEN meson[] ]);;

let fmap_EQ_UPTO___FUPDATE_SING = prove (`!f1 f2 ks k v.
    (fmap_EQ_UPTO f1 f2 ks) ==>
	 (fmap_EQ_UPTO (f1 |+ (k,v)) f2 (k INSERT ks))`,
   REWRITE_TAC[fmap_EQ_UPTO;EXTENSION;IN_COMPL] THEN
   REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN simp[FAPPLY_FUPDATE_THM] THENL [
    case_tac `x=k` THEN simp[] ;
    FIRST_ASSUM CONTR_TAC ;
    COND_CASES_TAC THEN meson[] ]);;


let rec add_fup p kL2 thm =
  match p with
    | ([], []) -> thm
    | (k::kL, v::vL) ->
       let c = concl thm in
       let ks = rand c
       and f2 = (rand o rator) c
       and f1 = (rand o rator o rator) c
       and (kL2, inkL2) = try (snd (remove (fun x -> x = k) kL2) , true ) with Failure _ -> (kL2, false) 
       and inkL = mem k kL in

       let kL2 = if inkL then k::kL2 else kL2 
       and imp_thm = if inkL then fmap_EQ_UPTO___FUPDATE_SING else
		     if inkL2 then
                     fmap_EQ_UPTO___FUPDATE_BOTH
		     else
                     fmap_EQ_UPTO___FUPDATE_BOTH___NO_DELETE in
       let imp_thm_inst = ISPECL [f1;f2;ks;k;v] imp_thm in
       let thm1 = MP imp_thm_inst thm in
       add_fup (kL, vL) kL2 thm1
    | _ -> failwith "add_fup: Invalid arguments";;

let FUPDATE_NORMALISE_CONV t =
  let emp_conv = SIMP_CONV [EXTENSION; NOT_IN_EMPTY; IN_DELETE; IN_INSERT] in
  let base,kvL = strip_fupdate t in
  let kL,vL = unzip (map dest_pair kvL) in
  let kty,vty = dest_fmap_ty (type_of base) in
  let typed_empty_tm = inst [kty,`:A`] `{}:A->bool` in
  
  let thm0 = ISPECL [typed_empty_tm; base] fmap_EQ_UPTO___EQ in
  let thm1 = add_fup (kL, vL) [] thm0 in

  let emp_eq = emp_conv (mk_eq ((rand o concl) thm1, typed_empty_tm)) in
  let emp_thm = EQ_MP (GSYM emp_eq) ((TAUT o rhs o concl) emp_eq) in
  let thm2 = CONV_RULE (RAND_CONV (K emp_thm) THENC REWR_CONV fmap_EQ_UPTO___EMPTY) thm1 in
  thm2;;

let FUPDATE_LIST_NORMALISE_CONV =
  REWRITE_CONV [FUPDATE_LIST_THM] THENC
  FUPDATE_NORMALISE_CONV THENC
  ONCE_REWRITE_CONV [GSYM FUPDATE_LIST_NIL] THENC
  REWRITE_CONV [GSYM FUPDATE_LIST_CONS];;

let FUPDATE_RLIST_NORMALISE_CONV =
  PURE_REWRITE_CONV [FUPDATE_RLIST_THM] THENC
  FUPDATE_NORMALISE_CONV THENC
  PURE_REWRITE_CONV[FUPDATE_EQ_FUPDATE_RLIST;GSYM FUPDATE_RLIST_APPEND;APPEND];;


(*
let xfm = list_mk_fupdate (`FEMPTY:(num,num)fmap`,[`1,2`;`2,3`;`3,4`;`4,5`;`1,6`;`2,7`]);;
let xfml = mk_fupdate_list `FEMPTY:(num,num)fmap` `[1,2;2,3;3,4;4,5;1,6;2,7]`;;
 *)

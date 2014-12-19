(* ========================================================================= *)
(* Small library that generates fresh variables.                             *)
(* Useful for freshness conditions in substitutions, etc.um.                 *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                 2010 - 2014                               *)
(* ========================================================================= *)
(* The general idea is to use a choice function ch that generates fresh      *)
(* variables.                                                                *)
(* The function must satisfy the freshness condition:                        *)
(* (!S (n:A). ~(MEM (ch n S) S))                                             *)
(* ------------------------------------------------------------------------- *)
(* In the current version we focus on variables of type :num, but this could *)
(* be extended in the future.                                                *)
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)
(* Function that picks fresh names for a list of names using a choice        *)
(* function.                                                                 *)
(* Applies the choice function over a list of variables.                     *)
(* ------------------------------------------------------------------------- *)

let FRESHL = new_recursive_definition list_RECURSION
  `(FRESHL ch [] l = []) /\
  (FRESHL ch (CONS h t) l = if (MEM h l) then (
     let h' = ch h l in
       CONS h' (FRESHL ch t (CONS h' l))) else (
     CONS h (FRESHL ch t l)))`;;


(* ------------------------------------------------------------------------- *)
(* Some properties.                                                          *)
(* ------------------------------------------------------------------------- *)

let FRESHL_EMPTY = prove (`!ch l. FRESHL ch l [] = l`,
			  GEN_TAC THEN LIST_INDUCT_TAC THEN simp[FRESHL;MEM]);;

let FRESHL_LDIFF_VAIN = prove (`! ch l v. FRESHL ch l (v LDIFF l) = l`,
			       GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC 
				 THEN simp[FRESHL;NOT_MEM_LDIFF_CONS;LDIFF_CONS]);;

let LENGTH_FRESHL = prove ( `!ch (k:(A)list) l . LENGTH (FRESHL ch k l) = LENGTH k`,
			    GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
			      simp[LENGTH;FRESHL;SUC_INJ] THEN COND_CASES_TAC THENL
			      [ LET_TAC THEN
				  FIRST_X_ASSUM (ASSUME_TAC o GSYM o (SPEC `CONS (h':A) l`)) ;
				ALL_TAC ] THEN simp[LENGTH;SUC_INJ]);;



(* ------------------------------------------------------------------------- *)
(* Propagation of the choice hypothesis for FRESHL.                          *)
(* ------------------------------------------------------------------------- *)

let FRESHL_HYP = prove(
  `!l x v. (!S (n:A). ~(MEM (ch n S) S)) ==> ~((MEM x (FRESHL ch l v)) /\ (MEM x v))`,
  REWRITE_TAC[TAUT `!p q. ~(p /\ q) <=> p ==> ~q`] 
    THEN LIST_INDUCT_TAC THEN simp[FRESHL;MEM] THEN GEN_ALL_TAC
    THEN DISCH_THEN (ASSUME_TAC o SPEC_ALL) THEN
    ASM_CASES_TAC `MEM (h:A) v` THEN simp[] THEN TRY LET_TAC THEN simp[MEM]
    THEN DISCH_THEN (DISJ_CASES_THEN ASSUME_TAC) THEN 
    REPEAT (POP_ASSUM ((fun x -> simp[x]) o SYM)) THEN erule_tac [`a`,`x`] allE 
    THENL [erule_tac [`a`,`CONS h' v`] allE ; erule_tac [`a`,`v`] allE]
    THEN drule mp THEN simp[MEM;DE_MORGAN_THM]);;


(* ========================================================================= *)


(* ------------------------------------------------------------------------- *) 
(* Choice function for numbers.                                              *)
(* ------------------------------------------------------------------------- *) 

let NCHOICE = new_definition
  `NCH n S = SUC (ITLIST MAX S n)`;;


(* ------------------------------------------------------------------------- *) 
(* Choice hypothesis.                                                        *)
(* ------------------------------------------------------------------------- *) 

let ALL_LT_NCH = prove (
  `!S n. ALL (\x. x < NCH n S) S`, 
  LIST_INDUCT_TAC THEN GEN_TAC THEN 
    simp[ALL;NCHOICE;ITLIST;MAX;DE_MORGAN_THM] THEN 
    COND_CASES_TAC THENL
    [ CONJ_TAC THEN simp[LT_SUC_LE] THEN assumption ; 
      simp[LT_SUC_LE;LE_REFL;NOT_LE] ] THEN 
    FIRST_X_ASSUM (ASSUME_TAC o (SPEC `n:num`)) THEN 
    simp[GSYM ALL_MEM] THEN GEN_TAC THEN
    FIRST_X_ASSUM (ASSUME_TAC o (SPEC `x:num`)) THEN 
    DISCH_TAC THEN drule mp 
    THENL [ assumption ; 
	    rule_tac [`n`,`ITLIST MAX t n`] 
	      ((MIMP_RULE o ARITH_RULE) `m <= n ==> n < p ==> m <= p`)] 
    THEN assumption);;

let NCHOICE_HYP = prove ( 
  `!S n. ~(MEM (NCH n S) S)`, 
  REWRITE_TAC[NOT_MEM_ALL] THEN GEN_ALL_TAC THEN
    rule_tac [`P`,`(\x. x < NCH n S)`] ((ONCE_REWRITE_RULE[MIMP_THM] o SPEC_ALL) ALL_IMP) THEN
    CONJ_TAC THENL [ GEN_TAC ; simp[ALL_LT_NCH] ] THEN 
    DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN simp [ARITH_RULE `m < n ==> ~(m = n)`]);;


(* ------------------------------------------------------------------------- *) 
(* Properties                                                                *)
(* ------------------------------------------------------------------------- *) 

let NCHOICE_NIL = prove (`!n . NCH n [] = SUC n`, simp[NCHOICE;ITLIST]);;

let NCHOICE_CONS_LT = prove (
		      `!n h t. h < n ==> NCH n (CONS h t) = NCH n t`,
			       REWRITE_TAC[NCHOICE;SUC_INJ;ITLIST_MAX] THEN REPEAT GEN_TAC THEN
			       DISCH_THEN (SUBST1_TAC o GSYM o (MATCH_MP (ARITH_RULE `a < b ==> b = MAX a b`)))
			       THEN REFL_TAC);;

let NCHOICE_CONS_LE = prove (
		      `!n h t. h <= n ==> NCH n (CONS h t) = NCH n t`,
			       REWRITE_TAC[NCHOICE;SUC_INJ;ITLIST_MAX] THEN REPEAT GEN_TAC THEN
			       DISCH_THEN (SUBST1_TAC o GSYM o (MATCH_MP (ARITH_RULE `a <= b ==> b = MAX a b`)))
			       THEN REFL_TAC);;

let NCHOICE_CONS_GT = prove (
		      `!n h t. h > n ==> NCH n (CONS h t) = NCH h t`,
			       REWRITE_TAC[NCHOICE;SUC_INJ;ITLIST_MAX] THEN REPEAT GEN_TAC THEN
			       DISCH_THEN (SUBST1_TAC o GSYM o (MATCH_MP (ARITH_RULE `a > b ==> a = MAX a b`)))
			       THEN REFL_TAC);;

let NCHOICE_CONS_GE = prove (
		      `!n h t. h >= n ==> NCH n (CONS h t) = NCH h t`,
			       REWRITE_TAC[NCHOICE;SUC_INJ;ITLIST_MAX] THEN REPEAT GEN_TAC THEN
			       DISCH_THEN (SUBST1_TAC o GSYM o (MATCH_MP (ARITH_RULE `a >= b ==> a = MAX a b`)))
			       THEN REFL_TAC);;

let NCH_VAIN_IMP_LE = prove (
		      `!t h n . SUC n = NCH n (CONS h t) ==> h <= n`,
			   simp[ITLIST;NCHOICE;SUC_INJ] THEN REPEAT GEN_TAC THEN 
			   case_tac `h < ITLIST MAX t n` THEN simp[] THENL
			   [ MATCH_MP_THEN ASSUME_TAC (ARITH_RULE `~(a < b) ==> a = MAX a b`) ;
			     MATCH_MP_THEN ASSUME_TAC (ARITH_RULE `a < b ==> b = MAX a b`)] THEN 
			   FIRST_X_ASSUM (SUBST1_TAC o GSYM) THENL 
			   [ ARITH_TAC ; DISCH_THEN SUBST1_TAC ] THEN simp[LT_IMP_LE]);;

let NCHOICE_0 = prove (
		`!h t. NCH 0 (CONS h t) = NCH h t`,
		    MATCH_ACCEPT_TAC (MATCH_MP NCHOICE_CONS_GE (REWRITE_RULE[GSYM GE] (SPEC `h:num` LE_0))));;

(* ! n l. n < NCH n l *)
let LT_NCHOICE = (GEN_ALL o CONJUNCT1 o (REWRITE_RULE[ALL;NCHOICE_0]) o (SPECL [`CONS (n:num) l`;`0`])) ALL_LT_NCH;;


let NCHOICE_LT =
  let hypthm = SPECL [`h:num`;`t:(num)list`] LT_NCHOICE in
  prove (`!t h n . NCH h t < n ==> h < n`,
           REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o (CONJ hypthm)) THEN REWRITE_TAC[LT_TRANS]);;

let NCHOICE_LE =
  let hypthm = SPECL [`h:num`;`t:(num)list`] LT_NCHOICE in
  prove (`!t h n . NCH h t <= n ==> h < n`,
	   REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o (CONJ hypthm)) THEN REWRITE_TAC[LTE_TRANS]);;


let NCHOICE_ORDER = prove(
		    `!l m n. m <= n ==> NCH m l <= NCH n l`,
		      LIST_INDUCT_TAC THENL [ simp[NCHOICE_NIL;LE_SUC] ; REPEAT GEN_TAC] THEN
		      DISCH_TAC THEN FIRST_ASSUM (MATCH_MP_THEN ASSUME_TAC) THEN
		      case_tac `h <= m` THEN simp[NOT_LE;GSYM GT] THENL [
				      MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_GT ;
				      MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_LE ] THEN simp[] THENL
				      [ case_tac `h <= n` THEN simp[NOT_LE;GSYM GT] ;
                   			MP_THEN (MP_THEN ASSUME_TAC) (((SPECL [`h:num`;`m:num`;`n:num`]) o (REWRITE_RULE[GSYM IMP_IMP])) LE_TRANS) THEN
						MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_LE THEN simp[]
						
				      ] THENL [
				      MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_GT ;
				      MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_LE ] THEN simp[LE_REFL]);;


let NCHOICE_ORDER_0 = prove (
		      `!n l. NCH 0 l <= NCH n l`,
			     MATCH_ACCEPT_TAC (MATCH_MP NCHOICE_ORDER (SPEC_ALL LE_0)));;


(*  !h t n. NCH h t < n ==> NCH 0 t < n *)
let NCHOICE_LT_WEAKEN_LEMMA = GEN_ALL (MP (((SPECL [`NCH 0 t`;`NCH h t`;`n:num`]) o (REWRITE_RULE[GSYM IMP_IMP])) LET_TRANS) (SPECL [`h:num`;`t:(num)list`] NCHOICE_ORDER_0));;

(*  !h t n. NCH h t <= n ==> NCH 0 t <= n *)
let NCHOICE_LE_WEAKEN_LEMMA = GEN_ALL (MP (((SPECL [`NCH 0 t`;`NCH h t`;`n:num`]) o (REWRITE_RULE[GSYM IMP_IMP])) LE_TRANS) (SPECL [`h:num`;`t:(num)list`] NCHOICE_ORDER_0));;


let NCH_0_LT_IMP_VAIN =
  let le_thm = prove (`!l n. NCH 0 l < n ==> NCH n l <= SUC n`,
	              LIST_INDUCT_TAC THEN GEN_TAC THEN simp[NCHOICE_NIL;LE_REFL;NCHOICE_0] THEN
		      DISCH_TAC THEN
		      MATCH_MP_THEN ASSUME_TAC NCHOICE_LT THEN
		      MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_LT THEN 
		      MATCH_MP_THEN ASSUME_TAC NCHOICE_LT_WEAKEN_LEMMA THEN 
		      FIRST_ASSUM ((MP_THEN ASSUME_TAC) o SPEC `n:num`) THEN simp[]) in
  let le_antisym = (GEN_ALL o (REWRITE_RULE[GSYM IMP_IMP]) o fst o EQ_IMP_RULE o SPEC_ALL) LE_ANTISYM in
  let part1 = MATCH_MP le_antisym (SPEC_ALL (REWRITE_RULE[GSYM LE_SUC_LT] LT_NCHOICE)) in

  prove (`!l n. NCH 0 l < n ==> NCH n l = SUC n`,simp[le_thm;part1]);;


let NCH_0_LE_IMP_VAIN =
  let le_thm = prove (`!l n. NCH 0 l <= n ==> NCH n l <= SUC n`,
	              LIST_INDUCT_TAC THEN GEN_TAC THEN simp[NCHOICE_NIL;LE_REFL;NCHOICE_0] THEN
		      DISCH_TAC THEN
		      MATCH_MP_THEN ASSUME_TAC NCHOICE_LE THEN
		      MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_LT THEN 
		      MATCH_MP_THEN ASSUME_TAC NCHOICE_LE_WEAKEN_LEMMA THEN 
		      FIRST_ASSUM ((MP_THEN ASSUME_TAC) o SPEC `n:num`) THEN simp[]) in
  let le_antisym = (GEN_ALL o (REWRITE_RULE[GSYM IMP_IMP]) o fst o EQ_IMP_RULE o SPEC_ALL) LE_ANTISYM in
  let part1 = MATCH_MP le_antisym (SPEC_ALL (REWRITE_RULE[GSYM LE_SUC_LT] LT_NCHOICE)) in

  prove (`!l n. NCH 0 l <= n ==> NCH n l = SUC n`,simp[le_thm;part1]);;


let NCH_LT_IMP_VAIN =
  let le_thm =  prove (
      `!l n m. NCH m l < n ==> NCH n l <= SUC n`,
	      LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
	      [ simp[NCHOICE_NIL;LE_REFL] ; DISCH_TAC] THEN
	      case_tac `h <= n` THEN simp[NOT_LE;GSYM GT] THENL
	      [ MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_GT ;
		MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_LE ] THEN
	      simp[GT] THEN
	      MATCH_MP_THEN ASSUME_TAC NCHOICE_LT THEN
	      MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_LT THEN 
	      MATCH_MP_THEN ASSUME_TAC NCHOICE_LT_WEAKEN_LEMMA THEN
	      simp[NCHOICE_0;ARITH_RULE `a < b ==> a <= SUC b`] THEN 
	      MATCH_MP_THEN ASSUME_TAC NCHOICE_LT_WEAKEN_LEMMA THEN
	      simp[NCH_0_LT_IMP_VAIN;LE_REFL]) in
  let le_antisym = (GEN_ALL o (REWRITE_RULE[GSYM IMP_IMP]) o fst o EQ_IMP_RULE o SPEC_ALL) LE_ANTISYM in
  let part1 = MATCH_MP le_antisym (SPEC_ALL (REWRITE_RULE[GSYM LE_SUC_LT] LT_NCHOICE)) in

  prove (`!l n m. NCH m l < n ==> NCH n l = SUC n`,REPEAT GEN_TAC THEN DISCH_TAC THEN
						MATCH_MP_THEN ASSUME_TAC le_thm THEN
						simp[part1]);;

let NCH_LE_IMP_VAIN =
  let le_thm =  prove (
      `!l n m. NCH m l <= n ==> NCH n l <= SUC n`,
	      LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
	      [ simp[NCHOICE_NIL;LE_REFL] ; DISCH_TAC] THEN
	      case_tac `h <= n` THEN simp[NOT_LE;GSYM GT] THENL
	      [ MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_GT ;
		MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_LE ] THEN
	      simp[GT] THEN
	      MATCH_MP_THEN ASSUME_TAC NCHOICE_LE THEN
	      MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_LT THEN 
	      MATCH_MP_THEN ASSUME_TAC NCHOICE_LE_WEAKEN_LEMMA THEN
	      simp[NCHOICE_0;ARITH_RULE `a <= b ==> a <= SUC b`] THEN 
	      MATCH_MP_THEN ASSUME_TAC NCHOICE_LE_WEAKEN_LEMMA THEN
	      simp[NCH_0_LE_IMP_VAIN;LE_REFL]) in
  let le_antisym = (GEN_ALL o (REWRITE_RULE[GSYM IMP_IMP]) o fst o EQ_IMP_RULE o SPEC_ALL) LE_ANTISYM in
  let part1 = MATCH_MP le_antisym (SPEC_ALL (REWRITE_RULE[GSYM LE_SUC_LT] LT_NCHOICE)) in

  prove (`!l n m. NCH m l <= n ==> NCH n l = SUC n`,REPEAT GEN_TAC THEN DISCH_TAC THEN
						MATCH_MP_THEN ASSUME_TAC le_thm THEN
						simp[part1]);;
  

let NCHOICE_MAX = prove (
		  `!l a m n. NCH m l = NCH n l ==> NCH (MAX a m) l = NCH (MAX a n) l`,
			 REWRITE_TAC[NCHOICE;SUC_INJ] THEN LIST_INDUCT_TAC THENL
			 [ simp[APPEND;ITLIST] ; simp[APPEND;ITLIST_MAX] ] THEN
			 REPEAT GEN_TAC THEN DISCH_TAC THEN
			 FIRST_X_ASSUM (MATCH_MP_THEN ASSUME_TAC) THEN
			 ONCE_REWRITE_TAC[ARITH_RULE `MAX a (MAX b c) = MAX b (MAX a c)`] THEN
			 assumption);;

let NCHOICE_CONS_COMM = prove (
    `!l a b n. NCH n (CONS a (CONS b l)) = NCH n (CONS b (CONS a l))`,
	       simp[NCHOICE;SUC_INJ] THEN LIST_INDUCT_TAC THEN
	       simp[APPEND;ITLIST_MAX;ARITH_RULE `MAX a (MAX b c) = MAX b (MAX a c)`]);;

let NCHOICE_CONS_ELIM = prove (
   `!l x n. MEM x l ==> NCH n (CONS x l) = NCH n l`,
       simp[NCHOICE;SUC_INJ] THEN LIST_INDUCT_TAC THEN simp[MEM] THEN
       REPEAT GEN_TAC THEN simp[MEM] THEN DISCH_THEN DISJ_CASES_TAC THEN 
       simp[ITLIST_MAX; ARITH_RULE `MAX a (MAX a b) = MAX a b`; REWRITE_RULE[NCHOICE;SUC_INJ] NCHOICE_CONS_COMM]);;

let NCHOICE_APPEND = prove (`NCH n (APPEND k l) = NCH (PRE (NCH n l)) k`, simp[NCHOICE;ITLIST_APPEND;PRE]);;

let NCHOICE_APPEND_SYM = prove (
       `!k l n. NCH n (APPEND k l) = NCH n (APPEND l k)`,
       simp[NCHOICE;SUC_INJ] THEN LIST_INDUCT_TAC THENL
       [ simp[APPEND;APPEND_NIL] ; LIST_INDUCT_TAC ] THEN
       simp[APPEND;APPEND_NIL;ITLIST_MAX;ARITH_RULE `MAX a (MAX b c) = MAX b (MAX a c)`]);;

let NCHOICE_APPEND_ASSOC = prove (
    `!k l m n. NCH n (APPEND (APPEND k l) m) = NCH n (APPEND k (APPEND l m))`,
     simp[NCHOICE;SUC_INJ] THEN LIST_INDUCT_TAC THEN simp[APPEND;APPEND_NIL;ITLIST]);;

(*
let NCH_VAIN_IMP_LT = prove (
		      `!t h n . n = NCH n (CONS h t) ==> h < n`,
			   simp[ITLIST;NCHOICE;SUC_INJ] THEN REPEAT GEN_TAC THEN 
			   case_tac `h < ITLIST MAX t n` THEN simp[] THENL
			   [ MATCH_MP_THEN ASSUME_TAC (ARITH_RULE `~(a < b) ==> a = MAX a b`) ;
			     MATCH_MP_THEN ASSUME_TAC (ARITH_RULE `a < b ==> b = MAX a b`)] THEN 
			   FIRST_X_ASSUM (SUBST1_TAC o GSYM) THENL 
			   [ ARITH_TAC ; DISCH_THEN SUBST1_TAC ] THEN simp[LT]);;
 *)

let NCHOICE_CASES = prove (
		    `!l n. NCH n l = SUC n \/ NCH n l = NCH 0 l`,
			    LIST_INDUCT_TAC THENL [ simp[NCHOICE_NIL] ; GEN_TAC ] THEN
			    case_tac `h <= n` THEN simp[NOT_LE;GSYM GT] THENL
			    [ MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_GT ;
			      MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_LE ] THEN
			    simp[NCHOICE_0] THEN 
			    FIRST_X_ASSUM (DISJ_CASES_TAC o (SPEC `n:num`)) THEN
			    simp[] THEN
			    MATCH_MP_THEN (ASSUME_TAC o (SPEC `h:num`)) NCHOICE_MAX THEN
			    MATCH_MP_THEN ASSUME_TAC (ARITH_RULE `a <= b ==> MAX a b = b`) THEN
			    simp[ARITH_RULE `MAX h 0 = h`]);;


let NCHOICE_N_LT_CASES = prove (
	 `!l n a. a < NCH n l ==> a < NCH 0 l \/ a <= n`,
	       REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC_ALL NCHOICE_CASES) THEN simp[LT_SUC_LE]);;


let NCHOICE_LT_0_CASE =
  let le_antisym1 = ((REWRITE_RULE[GSYM IMP_IMP]) o fst o EQ_IMP_RULE o (SPECL [`h:num`;`n:num`])) LE_ANTISYM
  and le_antisym2 = ((REWRITE_RULE[GSYM IMP_IMP]) o fst o EQ_IMP_RULE o (SPECL [`NCH n l`;`NCH 0 l`])) LE_ANTISYM in
  let part1 = 
    prove (`!l n. n < NCH 0 l ==> NCH n l <= NCH 0 l`,
			   LIST_INDUCT_TAC THENL [ simp[NCHOICE_NIL;LT;LE] ; GEN_TAC ] THEN DISCH_TAC THEN 
			   case_tac `h <= n` THEN simp[NOT_LE;GSYM GT] THENL
			   [ MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_GT ;
			     MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_LE ] THEN
			   simp[NCHOICE_0;LE_REFL;GT] THEN
			   ASM_STRUCT_CASES_TAC (SPECL [`t:(num)list`;`h:num`] NCHOICE_CASES) THEN
			   simp[LT_SUC_LE] THEN MP_THEN (MP_THEN ASSUME_TAC) le_antisym1 THEN
			   simp[LE_REFL])
  and part2 = SPEC_ALL NCHOICE_ORDER_0 in
  prove (`!l n. n < NCH 0 l ==> NCH n l = NCH 0 l`,
	      REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_THEN ASSUME_TAC part1 THEN
	      MP_THEN ASSUME_TAC le_antisym2 THEN simp[part2]);;


let NCHOICE_LT_CASE =
  let le_antisym_lemma = ((REWRITE_RULE[GSYM IMP_IMP]) o fst o EQ_IMP_RULE o (SPECL [`NCH n l`;`NCH m l`])) LE_ANTISYM 
and part1 = prove (
      `!l n m. m < NCH n l ==> NCH m l <= NCH n l`,
	      LIST_INDUCT_TAC THENL
	      [ simp[NCHOICE_NIL] THEN simp[LE_SUC;LE_LT;LT;DISJ_SYM;SUC_INJ;LT] ;
		REPEAT GEN_TAC THEN DISCH_TAC ] THEN
	      case_tac `h <= n` THEN simp[NOT_LE;GSYM GT] THENL
	      [ MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_GT ;
		MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_LE ] THEN
	      simp[] THEN
	      case_tac `h <= m` THEN simp[NOT_LE;GSYM GT] THENL
	      [ MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_GT;
		MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_LE;
		MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_GT;
		MATCH_MP_THEN ASSUME_TAC NCHOICE_CONS_LE ] THEN
	      simp[LE_REFL;NCHOICE_ORDER]) in
  prove(
  `!l n m. m < NCH n l /\ n <= m ==> NCH m l = NCH n l`,
	   REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
  	   MATCH_MP_THEN (ASSUME_TAC o SPEC_ALL) NCHOICE_ORDER THEN
	   MATCH_MP_THEN ASSUME_TAC part1 THEN
	   MATCH_MP_THEN ASSUME_TAC le_antisym_lemma THEN
	   FIRST_ASSUM (MP_THEN ACCEPT_TAC));;


let NCHOICE_RAISE_0 = prove (
    `!k l . NCH 0 k = NCH 0 l ==> !n. NCH n k = NCH n l`,
	    REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
	    case_tac `n < NCH 0 k` THEN RULE_ASSUM_TAC (REWRITE_RULE [NOT_LT]) THENL
	      [ REPEAT (MATCH_MP_THEN ASSUME_TAC NCH_0_LE_IMP_VAIN THEN simp[]) ;
		REPEAT (MATCH_MP_THEN ASSUME_TAC NCHOICE_LT_0_CASE THEN simp[])]);;

let NCHOICE_RAISE = prove (
    `!m n k l. NCH n k = NCH n l /\ n <= m ==> NCH m k = NCH m l`,
 	    REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
	    case_tac `m < NCH n k` THEN RULE_ASSUM_TAC (REWRITE_RULE [NOT_LT]) THENL
	      [ REPEAT (MATCH_MP_THEN ASSUME_TAC NCH_LE_IMP_VAIN THEN simp[]) ;
		REPEAT (MATCH_MP_THEN ASSUME_TAC (REWRITE_RULE[GSYM IMP_IMP] NCHOICE_LT_CASE) THEN simp[])]);;


let NCHOICE_APPEND_VAIN = prove (
  `! n k l m. NCH n l = NCH n m ==> NCH n (APPEND l k) = NCH n (APPEND m k)`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN simp[NCHOICE_APPEND] THEN
     rule_tac [`n`,`n`] ((MIMP_RULE o SPEC_ALL) NCHOICE_RAISE) THEN
     CONJ_TAC THEN simp[LT_NCHOICE;ARITH_RULE `a < b ==> a <= PRE b`]);;


(* ------------------------------------------------------------------------- *) 
(* Version of FRESHL with NCHOICE.                                           *)
(* ------------------------------------------------------------------------- *) 

let FRESHNL = new_definition `!l v. FRESHNL l v = FRESHL NCH l v`;;

let FRESHNL_EMPTY = prove (`!ch l. FRESHNL l [] = l`, REWRITE_TAC[FRESHNL;FRESHL_EMPTY]);;
			  
let FRESHNL_LDIFF_VAIN = prove (`!l v. FRESHNL l (v LDIFF l) = l`,
				REWRITE_TAC[FRESHNL;FRESHL_LDIFF_VAIN]);;

(* ------------------------------------------------------------------------- *) 
(* Propagation of the choice hypothesis for FRESHNL.                         *)
(* ------------------------------------------------------------------------- *) 

let FRESHNL_HYP =  prove(
  `!l x v. ~((MEM x (FRESHNL l v)) /\ (MEM x v))`,
  GEN_ALL_TAC THEN REWRITE_TAC[FRESHNL] THEN
    rule ((MIMP_RULE o SPEC_ALL) FRESHL_HYP) THEN
      ACCEPT_TAC NCHOICE_HYP);;

let FRESHNL_HYP_IMP = EQT_ELIM ((REWRITE_CONV [FRESHNL_HYP;TAUT `a ==> ~b <=> ~(b /\ a)`])
				`!l x v. MEM x v ==> ~(MEM x (FRESHNL l v))`);;


(* ------------------------------------------------------------------------- *) 
(* Properties                                                                *)
(* ------------------------------------------------------------------------- *) 

let LENGTH_FRESHNL = prove (`!l v . LENGTH (FRESHNL l v) = LENGTH l`,
		  simp[FRESHNL;LENGTH_FRESHL]);;
					
(* ------------------------------------------------------------------------- *) 
(* FRESHNL computation.                                                      *)
(* ------------------------------------------------------------------------- *) 

let FRESHNL_CONV =
  let rec fconv tm =
    (ONCE_REWRITE_CONV[FRESHL] THENC TRY_CONV(
      (PATH_CONV "llr" (REWRITE_CONV[MEM] THENC NUM_REDUCE_CONV)) THENC CONDS_ELIM_CONV
	THENC TRY_CONV (
	  (PATH_CONV "r" (REWRITE_CONV[NCHOICE;ITLIST_MAX;ITLIST] THENC NUM_REDUCE_CONV))
	    THENC let_CONV)
	THENC PATH_CONV "r" fconv)
    ) tm in
  PURE_REWRITE_CONV[FRESHNL] THENC fconv;;


 

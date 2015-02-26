(* ========================================================================= *)
(* Extension of lists library with simple theorems and definitions.          *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                 2010 - 2014                               *)
(* ========================================================================= *)

needs "IsabelleLight/make.ml";;
needs "tools/make.ml";;

let is_nil tm = try ( (fst o dest_const) tm = "NIL" ) with Failure _ -> false;;


(* MEM *)

let MEM_EXISTS = prove (`! l. ~(l=[]) ==> ?x:A. MEM x l`,
			LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MEM;NOT_CONS_NIL] THEN
			  EXISTS_TAC `h:A` THEN REWRITE_TAC[]);; 

(* !l. (!x. ~MEM x l) ==> l = [] *)
let NO_MEM_EMPTY = ((GEN `l:(A)list`) o (REWRITE_RULE[NOT_EXISTS_THM]) o (CONV_RULE CONTRAPOS_CONV) o SPEC_ALL) MEM_EXISTS;;

let MEM_EX_EQ = prove (`! x l . MEM x l <=> EX (\a . x = a) l`,
	       GEN_TAC THEN LIST_INDUCT_TAC THEN simp[MEM;EX]);;

(*  !x l. ~MEM x l <=> ALL (\x'. ~(x = x')) l *)
let NOT_MEM_ALL_DIFF = ((REWRITE_RULE [NOT_EX]) o (ONCE_REWRITE_RULE [TAUT `(a <=> b) <=> (~a <=> ~b)`])) MEM_EX_EQ;;
  
(* APPEND *)

let APPEND_EQ = prove (`!a b c . APPEND a b = APPEND a c <=> b = c`,
		       LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND;CONS_11]);;

let LENGTH_APPEND_EQ = prove(
  `!a b c d . LENGTH a = LENGTH c ==> (APPEND a b = APPEND c d <=> a = c /\ b = d)`,
  LIST_INDUCT_TAC THEN GEN_TAC THENL [
    REPEAT GEN_TAC THEN
      DISCH_THEN (SUBST1_TAC o (REWRITE_RULE[LENGTH;LENGTH_EQ_NIL]) o GSYM) THEN
      simp[APPEND] ;
    LIST_INDUCT_TAC ] THEN GEN_TAC THEN
    simp[APPEND;LENGTH;NOT_SUC;SUC_INJ;CONS_11;CONJ_ASSOC]);;

let EX_APPEND = prove (`!P k l. EX P (APPEND k l) <=> EX P k \/ EX P l`,
   GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[EX;APPEND;DISJ_ASSOC]);;
				      

(* FILTER *)

let FILTER_CLAUSES = prove (
 `!l. ((!x:A. P x) ==> FILTER  P l = l) /\
      ((!x:A. ~(P x)) ==> FILTER P l = [])`,
      LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER] THEN
      POP_ASSUM (CONJUNCTS_THEN ASSUME_TAC) THEN
      CONJ_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM (fun x -> FIRST_ASSUM (fun y -> ASSUME_TAC (MP x y))) THEN
      ASM_REWRITE_TAC[]);;

(* !l. FILTER (\z. T) l = l  *)
let FILTER_T = GEN_ALL (MATCH_MP ((CONJUNCT1 o SPEC_ALL) FILTER_CLAUSES) (TAUT `!x.(\z. T) x`));;

(* !l. FILTER (\z. F) l = [] *)
let FILTER_F = GEN_ALL (MATCH_MP ((CONJUNCT2 o SPEC_ALL) FILTER_CLAUSES) (TAUT `!x. ~((\z. F) x)`));;

let FILTER_FILTER = prove (
  `!l. FILTER P (FILTER Q l) = FILTER (\x. P x /\ Q x) l`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[FILTER;COND_ELIM_THM] THEN
    DISCH_THEN (DISJ_CASES_TAC o (REWRITE_RULE[DE_MORGAN_THM])) THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[FILTER] THEN
    FIRST_ASSUM (CONTR_TAC o UNDISCH o NOT_ELIM));;

let FILTER_SYM = prove (
		 `!l. FILTER P (FILTER Q l) = FILTER Q (FILTER P l)`,
		 REWRITE_TAC[FILTER_FILTER;CONJ_SYM]);;

(* MAP *)

let MAP_I = prove ( `!l. MAP (\x. x) l = l`, LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP]);;

let MAP_APPEND_I = prove (
    `!f l k . MAP f (APPEND l k) = APPEND l k <=> MAP f l = l /\ MAP f k = k`,
     GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP;APPEND;CONS_11;CONJ_ASSOC]);;

(* Pairs *)

(* ALL *)

let ALL_SND = prove (`!P l. ALL (\(v,t). P t) l <=> ALL P (MAP SND l)`,
	GEN_TAC THEN induct_tac THENL [ALL_TAC ; induct_tac] THEN  simp[ALL;MAP;SND]);;				
let ALL_SND_ZIP = prove (
  `!P k l. (LENGTH k = LENGTH l) ==> (ALL (\(v,t). P t) (ZIP k l) <=> ALL P l)`,
   simp[ALL_SND;MAP_SND_ZIP]);;


(* EX *)

let EX_FST = prove (`!P l. EX (\(v,t). P v) l <=> EX P (MAP FST l)`,
     GEN_TAC THEN induct_tac THENL [ALL_TAC ; induct_tac] THEN simp[EX;MAP;FST]);;			     

let EX_FST_ZIP = prove (
  `!P k l. (LENGTH k = LENGTH l) ==> (EX (\(v,t). P v) (ZIP k l) <=> EX P k)`,
   simp[EX_FST;MAP_FST_ZIP]);;							

    
(* ZIP *)

let ZIP_APPEND_MAP = prove (
  `!k l. ZIP (APPEND k l) (MAP P (APPEND k l)) = APPEND (ZIP k (MAP P k)) (ZIP l (MAP P l))`,
  LIST_INDUCT_TAC THEN simp[MAP_APPEND;MAP;ZIP;APPEND]);;


(* REVERSE *)

let MEM_REVERSE = prove (`!x l. MEM x (REVERSE l) <=> MEM x l`,
   GEN_TAC THEN LIST_INDUCT_TAC THEN simp[MEM_APPEND;MEM;REVERSE;DISJ_SYM]);;

let SET_OF_LIST_REVERSE = prove (`!l. set_of_list (REVERSE l) = set_of_list l`,
   LIST_INDUCT_TAC THEN simp[set_of_list;SET_OF_LIST_APPEND;REVERSE;APPEND] THEN SET_TAC[]);;

let FILTER_REVERSE = prove (`!P l. FILTER P (REVERSE l) = REVERSE (FILTER P l)`,
   GEN_TAC THEN LIST_INDUCT_TAC THEN simp[FILTER;REVERSE;APPEND;FILTER_APPEND] THEN
   COND_CASES_TAC THEN simp[REVERSE;APPEND;APPEND_NIL]);;


(* ------------------------------------------------------------------------- *)
(* Theorem ITLIST_MAX is used to increase the efficiency of fresh variable   *)
(* generation (see fresh.ml).                                                *)
(* It is a simple property about ITLIST and MAX so as to quickly calculate   *)
(* the maximum number of a list.                                             *)
(* ------------------------------------------------------------------------- *)
(* Using normal ITLIST recursion creates a term that grows exponentially.    *)
(* This theorem creates a linear application of MAX over all the elements of *)
(* the list thanks to the associativity and commutativity of MAX.            *)
(* ------------------------------------------------------------------------- *)
(* I decided to prove this more generally for any associative and            *)
(* commutative function and thus created ITLIST_LINEAR.                      *)
(* ------------------------------------------------------------------------- *)
(* Note update: Now with the introduction of FOLDL I should be using that    *)
(* instead.                                                                  *)
(* ------------------------------------------------------------------------- *)

let ITLIST_LINEAR = prove ( 
  `!FN .(!a b c . FN a ( FN b c ) = FN b (FN a c)) ==> 
  (!t h x. ITLIST FN (CONS h t) x = ITLIST FN t (FN h x))`,
  GEN_ALL_TAC THEN DISCH_THEN (LABEL_TAC "ac") THEN 
    LIST_INDUCT_TAC THEN GEN_ALL_TAC THEN REWRITE_TAC[ITLIST]
    THEN REMOVE_THEN "ac" (fun x -> ONCE_REWRITE_TAC[x])
    THEN simp[ITLIST]);;

let ITLIST_MAX = prove (
  `!t h x. ITLIST MAX (CONS h t) x = ITLIST MAX t (MAX h x)`,
  rule (MIMP_RULE (ISPEC `MAX` ITLIST_LINEAR)) THEN ARITH_TAC);;




(* misc. *)

let NOT_MEM_ALL = prove (
  `!n l. ~(MEM n l) <=> ALL (\x. ~(x = n)) l`, 
   GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM;ALL;DE_MORGAN_THM] THEN
   EQ_TAC THEN DISCH_TAC THEN erule conjE THEN erule iffE THENL
   [ drule mp ; drule_tac [`q`,`~(MEM n t)`] mp] THENL
   [assumption ; simp[] ; assumption; simp[]]);;



(* DEL *)

parse_as_infix ("DEL",(21,"left"));;

let DEL_DEF = new_definition `l DEL x = FILTER (\z. ~(z = x)) l`;;

let DEL_RECURSION = prove(
  `(!x. [] DEL x = []) /\
    (!h t x. CONS h t DEL x = if h = x then t DEL x else CONS h (t DEL x))`,
    REWRITE_TAC[DEL_DEF;FILTER] THEN GEN_ALL_TAC THEN COND_CASES_TAC THEN simp[]);;

let [EMPTY_DEL;CONS_DEL] = CONJUNCTS DEL_RECURSION;;

(* This version is better for computation. *)
let CONS_DEL_REC = prove (
   `(!h t x. CONS h t DEL x = APPEND (if h = x then [] else [h]) (t DEL x))`,
    REWRITE_TAC[DEL_DEF;FILTER] THEN GEN_ALL_TAC THEN COND_CASES_TAC THEN simp[APPEND]);;


let NOT_MEM_DEL = prove(`~(MEM x (l DEL x))`, GEN_ALL_TAC THEN REWRITE_TAC[DEL_DEF;MEM_FILTER]);;

let MEM_DEL = prove (`!l x y. MEM x (l DEL y) <=> MEM x l /\ ~(x = y)`, GEN_ALL_TAC THEN REWRITE_TAC[DEL_DEF;MEM_FILTER;CONJ_SYM]);;

let DEL_NON_MEM = prove(
  `!l (x:A). ~(MEM x l) <=> (l DEL x = l)`, 
  LIST_INDUCT_TAC THEN GEN_TAC THEN 
    REWRITE_TAC[EMPTY_DEL;CONS_DEL;MEM;FILTER;DE_MORGAN_THM;CONS_11] 
    THEN EQ_TAC THENL
    [ DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN simp[CONS_11] ;
      COND_CASES_TAC ] THENL
    [ simp[] THEN DISCH_THEN (ASSUME_TAC o (fun x -> MK_COMB ((REFL `MEM (x:A)`),x))) THEN
	simp[MEM_DEL;MEM] ;
      DISCH_TAC THEN simp[CONS_11]]);;

(*let MEM_DEL_EQ = prove();;
g `(MEM x l <=> MEM x' l) <=> (MEM x (l DEL x')) <=> (MEM x' (s DEL x))`;;
*)

let DEL_DEL = prove(`!l x. (l DEL x) DEL x = l DEL x`, REWRITE_TAC[DEL_DEF;FILTER_FILTER]);;

let DEL_COMM = prove(`!l x y. (l DEL x) DEL y = (l DEL y) DEL x`, REWRITE_TAC[DEL_DEF;FILTER_FILTER;CONJ_SYM]);;

let FILTER_DEL = prove(`!l P x. FILTER (\x. P x) (l DEL x) = (FILTER (\x. P x) l) DEL x`, REWRITE_TAC[DEL_DEF;FILTER_FILTER;CONJ_SYM]);;

let SET_OF_LIST_DEL = prove (`!l x. set_of_list(l DEL x) = set_of_list(l) DELETE x`, REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; IN_DELETE; MEM_DEL]);;

let APPEND_DEL = prove (`!k l x. APPEND k l DEL x = APPEND (k DEL x) (l DEL x)`,
			 LIST_INDUCT_TAC THEN simp[APPEND;DEL_DEF;FILTER] THEN
			 REPEAT GEN_TAC THEN COND_CASES_TAC THEN simp[APPEND;FILTER]);;

(* ------------------------------------------------------------------------- *)
(* Conversion to compute DEL as an operation.                                *)
(* The eqconv parameter must be a conversion that can calculate equalities   *)
(* between 2 elements of the list.                                           *)
(* For example for (num)list you can use DEL_CONV NUM_REDUCE_CONV            *)
(* ------------------------------------------------------------------------- *)

let rec DEL_CONV eqconv tm =
  let consconv tm = if is_cons tm then PATH_CONV "r" (DEL_CONV eqconv) tm else DEL_CONV eqconv tm in
  try (
  if ((is_const o rand o rator) tm) then
  PURE_REWRITE_CONV[EMPTY_DEL] tm
  else
  (PURE_ONCE_REWRITE_CONV[CONS_DEL_REC] THENC
			 PATH_CONV "lrllr" eqconv THENC
			 REWRITE_CONV[APPEND] THENC consconv) tm
  ) with Failure _ -> failwith "DEL_CONV";;


(* DEL1 *)

parse_as_infix ("DEL1",(21,"left"));;

let DEL1 = new_recursive_definition list_RECURSION
    `([] DEL1 x = []) /\
    (CONS h t DEL1 x = if h = x then t else CONS h (t DEL1 x))`;;

let [EMPTY_DEL1;CONS_DEL1] = CONJUNCTS DEL1;;

let DEL1_NON_MEM = prove (
  `!l (x:A). ~(MEM x l) ==> (l DEL1 x = l)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN simp[EMPTY_DEL1;CONS_DEL1;MEM;DE_MORGAN_THM]);;

let DEL1_COMM = prove (
  `!l x y. (l DEL1 x) DEL1 y = (l DEL1 y) DEL1 x`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN simp[EMPTY_DEL1;CONS_DEL1]
    THEN REPEAT COND_CASES_TAC THEN TRY (POP_ASSUM SUBST_ALL_TAC) 
    THEN simp[CONS_DEL1]);;

(*
let FILTER_DEL = prove(`!l P x. FILTER (\x. P x) (l DEL x) = (FILTER (\x. P x) l) DEL x`, REWRITE_TAC[DEL_DEF;FILTER_FILTER;CONJ_SYM]);;
*)



(* LDIFF *)

parse_as_infix ("LDIFF",(18,"left"));;

let LDIFF = new_definition `k LDIFF l = FILTER (\z. ~(MEM z l)) k`;; 

let LDIFF_RECURSION = prove(
  `(!l:(A)list. [] LDIFF l = []) /\
   (!h t l. (CONS h t) LDIFF l = if (MEM h l) then t LDIFF l else CONS h (t LDIFF l))`,
  REWRITE_TAC[LDIFF;FILTER] THEN GEN_ALL_TAC THEN COND_CASES_TAC THEN simp[]);;

let [EMPTY_LDIFF;CONS_LDIFF] = CONJUNCTS LDIFF_RECURSION;;

(* This version is better for computation. We end up using LDIFF_CONS which is even better. *)
let CONS_LDIFF_REC = prove (
   `(!h t l. (CONS h t) LDIFF l = APPEND (if (MEM h l) then [] else [h]) (t LDIFF l))`,
    REWRITE_TAC[LDIFF;FILTER] THEN GEN_ALL_TAC THEN COND_CASES_TAC THEN simp[APPEND]);;



let MEM_LDIFF = prove (`!x k l. MEM x (k LDIFF l) <=> MEM x k /\ ~(MEM x l)`,
		        REWRITE_TAC[LDIFF;MEM_FILTER;CONJ_SYM]);;

let NOT_MEM_LDIFF = prove (`!x l k. ~(MEM x l) ==> ~(MEM x (l LDIFF k))`,
			    GEN_ALL_TAC THEN REWRITE_TAC[MEM_LDIFF;DE_MORGAN_THM] THEN 
			    DISCH_TAC THEN DISJ1_TAC THEN assumption);;

let LDIFF_MEM = prove (`!(x:A) k l. MEM x k ==> ~(MEM x (l LDIFF k))`,simp[MEM_LDIFF]);;

let NOT_MEM_LDIFF_CONS = prove (`!x l t. ~(MEM x (l LDIFF CONS x t))`,
				REWRITE_TAC[MEM_LDIFF;DE_MORGAN_THM;MEM]);;

let LDIFF_EMPTY = prove (`!l. l LDIFF [] = l`, REWRITE_TAC[LDIFF;MEM;FILTER_T]);;

let LDIFF_LDIFF_ID = prove (`!l t. (l LDIFF t) LDIFF t = l LDIFF t`,REWRITE_TAC[LDIFF;FILTER_FILTER]);;

let LDIFF_LDIFF = prove (`!l m n. l LDIFF m LDIFF n = l LDIFF (APPEND m n)`, 
			 REWRITE_TAC [LDIFF;FILTER_FILTER;MEM_APPEND;DE_MORGAN_THM;CONJ_ACI]);;

let LDIFF_EQ_EMPTY = prove (`!l. l LDIFF l = []`,
                     LIST_INDUCT_TAC THEN simp[LDIFF_EMPTY;LDIFF;MEM;FILTER;DE_MORGAN_THM;GSYM FILTER_FILTER]);;

let LDIFF_CONS = prove(`!l h t. l LDIFF (CONS h t) = (l DEL h) LDIFF t`,
                 REWRITE_TAC[LDIFF;FILTER;MEM;DEL_DEF;FILTER_FILTER;DE_MORGAN_THM;CONJ_SYM]);;

let FILTER_LDIFF = prove(`!l k P. FILTER (\x. P x) (l LDIFF k) = (FILTER (\x. P x) l) LDIFF k`,
		   REWRITE_TAC[LDIFF;FILTER_FILTER;CONJ_SYM]);; 

let SET_OF_LIST_LDIFF = prove (`!l1 l2. set_of_list(l1 LDIFF l2) = set_of_list(l1) DIFF set_of_list(l2)`,
			REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; IN_DIFF; MEM_LDIFF]);;

let APPEND_LDIFF = prove( `!k l m. APPEND k l LDIFF m = APPEND (k LDIFF m) (l LDIFF m)`,
                   LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND;LDIFF_RECURSION] THEN 
                   REPEAT GEN_TAC THEN COND_CASES_TAC THEN simp[APPEND]);;

let LDIFF_APPEND_SYM = prove (`!k l m. k LDIFF (APPEND l m) = k LDIFF (APPEND m l)`,
			      REWRITE_TAC[GSYM LDIFF_LDIFF;LDIFF;FILTER_FILTER;CONJ_SYM]);;

let LDIFF_DISJOINT =
  let right = prove (`!k l. k LDIFF l = [] ==> !(a:A) . MEM a k ==> MEM a l`,
		     LIST_INDUCT_TAC THEN REWRITE_TAC[LDIFF_RECURSION;MEM] THEN
		       GEN_TAC THEN FIRST_X_ASSUM (ASSUME_TAC o SPEC_ALL) THEN
		       COND_CASES_TAC THENL [
			 DISCH_TAC THEN FIRST_X_ASSUM (MP_THEN ASSUME_TAC) THEN
			   GEN_TAC THEN DISCH_THEN DISJ_CASES_TAC;
			 ALL_TAC] THEN
		       simp[NOT_CONS_NIL])
  and left = prove (`!k l . (!(a:A) . MEM a k ==> MEM a l) ==> k LDIFF l = []`,
		    LIST_INDUCT_TAC THEN REWRITE_TAC[LDIFF_RECURSION;MEM] THEN
		      GEN_TAC THEN FIRST_X_ASSUM (ASSUME_TAC o SPEC_ALL) THEN
		      simp[MEM;CONS_LDIFF]) in
  prove (`!k l. k LDIFF l = [] <=> !(a:A) . MEM a k ==> MEM a l`,
	 REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[right;left]);;


(* ------------------------------------------------------------------------- *)
(* Conversion to compute LDIFF as an operation.                              *)
(* The eqconv parameter must be a conversion that can calculate equalities   *)
(* between 2 elements of the list.                                           *)
(* For example for (num)list you can use LDIFF_CONV NUM_REDUCE_CONV          *)
(* ------------------------------------------------------------------------- *)

let rec LDIFF_CONV eqconv tm =
  try (
  if ((is_nil o rand) tm) then
  PURE_REWRITE_CONV[LDIFF_EMPTY] tm
  else
  (PURE_ONCE_REWRITE_CONV[LDIFF_CONS] THENC
   PATH_CONV "lr" (DEL_CONV eqconv) THENC
   LDIFF_CONV eqconv) tm
  ) with Failure _ -> failwith "LDIFF_CONV";;


(* FOLD *)
(* Taken from HOL4 *)

let FOLDR = new_recursive_definition list_RECURSION
  `(!f e.     FOLDR (f:a->b->b) e [] = e) /\
  (!f e x l. FOLDR f e (CONS x l) = f x (FOLDR f e l))`;;

let FOLDL = new_recursive_definition list_RECURSION
  `(!f e. FOLDL (f:b->a->b) e [] = e) /\
  (!f e x l. FOLDL f e (CONS x l) = FOLDL f (f e x) l)`;;

let FOLDR_EQ_ITLIST = prove (`!l f e. FOLDR f e l = ITLIST f l e`,
   LIST_INDUCT_TAC THEN ASM SIMP_TAC[FOLDR;ITLIST]);;

(* let FOLDL_EQ_FOLDR = prove (  
  `!f l e. (ASSOC f /\ COMM f) ==>
   ((FOLDL f e l) = (FOLDR f e l))`, ...);; *)

let FOLDR_CONS = prove (
  `!f ls a. FOLDR (\x y. CONS (f x) y) a ls = APPEND (MAP f ls) a`,
   GEN_TAC THEN LIST_INDUCT_TAC THEN ASM SIMP_TAC[FOLDR;MAP;APPEND;CONS_11]);;


let FOLDL_APPEND = prove (
   `!k l f e. FOLDL f e (APPEND k l) = FOLDL f (FOLDL f e k) l`,
   LIST_INDUCT_TAC THEN simp[FOLDL;APPEND]);;

let FOLDL_REVERSE_EQ_FOLDR = prove (
   `!l f e. FOLDL f e (REVERSE l) = FOLDR (\x y. f y x) e l`,
   LIST_INDUCT_TAC THEN simp[FOLDL;FOLDR;REVERSE;FOLDL_APPEND]);;


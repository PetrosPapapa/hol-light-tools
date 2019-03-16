(* ========================================================================= *)
(* Extension of sets library with simple theorems and definitions.           *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                 2010 - 2017                               *)
(* ========================================================================= *)

needs "IsabelleLight/make.ml";;


let DELETE_DIFF = prove (`!a s t. s DELETE a DIFF t = (s DIFF t) DELETE a`, SET_TAC[]);;

let DISJOINT_DIFF = prove (`!s p. DISJOINT (s DIFF p) p`, SET_TAC[]);;

let DIFF_UNION = prove (`!s p . (s DIFF p) UNION p = s UNION p`, SET_TAC[]);;

let UNION_EQ = prove (`!a b c. a = b ==> c UNION a = c UNION b`, SET_TAC[]);; 

let SET_CONV = REWRITE_CONV[EXTENSION; SUBSET; PSUBSET; DISJOINT; SING] THENC
    REWRITE_CONV[NOT_IN_EMPTY; IN_UNIV; IN_UNION; IN_INTER; IN_DIFF; IN_INSERT;
                IN_DELETE; IN_REST; IN_INTERS; IN_UNIONS; IN_IMAGE;
                IN_ELIM_THM; IN; UNWIND_THM1; UNWIND_THM2];;

let IMAGE_I = prove (`!s. IMAGE (\x. x) s = s`, SET_TAC[]);;

(* COMPL *)
(* (as seen in HOL4 ) *)

let COMPL = new_definition `COMPL P = UNIV DIFF P`;;

let IN_COMPL = prove (`!(x:A) s. x IN (COMPL s) <=> ~(x IN s)`, REWRITE_TAC[COMPL;IN_DIFF;IN_UNIV]);;

let COMPL_COMPL = prove (`!s:A->bool. COMPL (COMPL s) = s`,REWRITE_TAC[EXTENSION;IN_COMPL]);;

let COMPL_CLAUSES = prove (`!(s:A->bool). (COMPL s INTER s = {}) /\ (COMPL s UNION s = UNIV)`,
   REWRITE_TAC[EXTENSION;IN_COMPL;IN_INTER;IN_UNION;NOT_IN_EMPTY;IN_UNIV;DE_MORGAN_THM;EXCLUDED_MIDDLE;DISJ_SYM]);;

let COMPL_SPLITS = prove (`!(p:A->bool) q. p INTER q UNION COMPL p INTER q = q`,
   REWRITE_TAC[EXTENSION;IN_COMPL;IN_INTER;IN_UNION;NOT_IN_EMPTY;IN_UNIV] THEN CONV_TAC TAUT);;

let INTER_UNION_COMPL = prove (`!(s:A->bool) t. s INTER t = COMPL (COMPL s UNION COMPL t)`,
   REWRITE_TAC[EXTENSION;IN_COMPL;IN_INTER;IN_UNION;NOT_IN_EMPTY;IN_UNIV;DE_MORGAN_THM]);;

let COMPL_EMPTY = prove (`COMPL {} = UNIV`, REWRITE_TAC[EXTENSION;IN_COMPL;NOT_IN_EMPTY;IN_UNIV]);;

let COMPL_INTER = prove (`(x INTER COMPL x = {}) /\ (COMPL x INTER x = {})`,
   REWRITE_TAC[EXTENSION;IN_COMPL;IN_INTER;NOT_IN_EMPTY;DE_MORGAN_THM;EXCLUDED_MIDDLE;DISJ_SYM]);;

let COMPL_UNION = prove (`!s t. COMPL (s UNION t) = COMPL s INTER COMPL t`,
   REWRITE_TAC[EXTENSION;IN_COMPL;IN_UNION;IN_INTER;DE_MORGAN_THM;EXCLUDED_MIDDLE;DISJ_SYM]);;

let COMPL_INSERT = prove (`!s x. COMPL (x INSERT s) = COMPL s DELETE x`,
   REWRITE_TAC[EXTENSION;IN_COMPL;IN_INSERT;IN_DELETE;DE_MORGAN_THM;CONJ_SYM]);;

					   

(* ========================================================================= *)
(* Extension of sets library with simple theorems and definitions.           *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                 2010 - 2015                               *)
(* ========================================================================= *)

needs "IsabelleLight/make.ml";;


let DELETE_DIFF = prove (`!a s t. s DELETE a DIFF t = (s DIFF t) DELETE a`, SET_TAC[]);;

let DISJOINT_DIFF = prove (`!s p. DISJOINT (s DIFF p) p`, SET_TAC[]);;

let DIFF_UNION = prove (`!s p . (s DIFF p) UNION p = s UNION p`, SET_TAC[]);;

let UNION_EQ = prove (`!a b c. a = b ==> c UNION a = c UNION b`, SET_TAC[]);; 

let SET_REDUCE_CONV = REWRITE_CONV[EXTENSION; SUBSET; PSUBSET; DISJOINT; SING] THENC
    REWRITE_CONV[NOT_IN_EMPTY; IN_UNIV; IN_UNION; IN_INTER; IN_DIFF; IN_INSERT;
                IN_DELETE; IN_REST; IN_INTERS; IN_UNIONS; IN_IMAGE;
                IN_ELIM_THM; IN; UNWIND_THM1; UNWIND_THM2];;

let IMAGE_I = prove (`!s. IMAGE (\x. x) s = s`, SET_TAC[]);;

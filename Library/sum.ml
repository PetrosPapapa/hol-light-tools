(* ========================================================================= *)
(* Extension of sum library with simple theorems and definitions.            *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                    2015                                   *)
(* ========================================================================= *)

needs "IsabelleLight/make.ml";;

(* In HOL4 these are defined as specifications which is stronger.            *)
(* This will do for now, but I'll try to update if possible.                 *)

let ISL = new_recursive_definition sum_RECURSION
    `(!x. ISL (INL x :A+B) = T) /\ (!y. ISL (INR y :A+B) = F)`;;

let ISR = new_recursive_definition sum_RECURSION
    `(!x. ISR (INL x :A+B) = F) /\ (!y. ISR (INR y :A+B) = T)`;;


let ISL_OR_ISR = prove (`!x:A+B. ISL x \/ ISR x`, induct_tac THEN REWRITE_TAC[ISL;ISR]);;

let ISL_IMP_INL = prove (`!x:A+B. ISL x ==> INL (OUTL x) = x`, induct_tac THEN REWRITE_TAC[ISL;OUTL]);;

let ISR_IMP_INR = prove (`!x:A+B. ISR x ==> INR (OUTR x) = x`, induct_tac THEN REWRITE_TAC[ISR;OUTR]);;

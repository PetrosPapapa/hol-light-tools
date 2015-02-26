(* ========================================================================= *)
(* Various useful, general purpose theorems and rules.                       *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                 2010 - 2015                               *)
(* ========================================================================= *)

let EQ_IMP_THM = TAUT `!t1 t2. (t1 <=> t2) <=> (t1 ==> t2) /\ (t2 ==> t1)`;;

let MATCH_EQ_MP = MATCH_MP o CONJUNCT1 o PURE_REWRITE_RULE[EQ_IMP_THM;FORALL_AND_THM];;
							      
(* ------------------------------------------------------------------------- *)
(* Undischarge N antecedents from the conclusion of a theorem.               *)
(* Useful when you have discharged the hypothesis, rewritten it, and now you *)
(* want to put it back without affecting any original antecedents of the     *)
(* conclusion.                                                               *)
(* ------------------------------------------------------------------------- *)

let rec UNDISCHN n thm = 
  match n with 
      0 -> thm
    | _ -> UNDISCHN (n-1) (UNDISCH thm);;

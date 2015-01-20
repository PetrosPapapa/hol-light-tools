(* ========================================================================= *)
(* Various useful, general purpose rules.                                    *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                 2010 - 2015                               *)
(* ========================================================================= *)

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

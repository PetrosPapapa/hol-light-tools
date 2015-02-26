(* ========================================================================= *)
(* Various useful, general purpose tactics.                                  *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                 2010 - 2015                               *)
(* ========================================================================= *)


let MP_THEN thmtc = fun x -> FIRST_ASSUM (fun y -> (thmtc (MP x y)));;
let MATCH_MP_THEN thmtc = fun x -> FIRST_ASSUM (fun y -> (thmtc (MATCH_MP x y)));;
let EQ_MP_THEN thmtc = fun x -> FIRST_ASSUM (fun y -> (thmtc (EQ_MP x y)));;

let ITLIST_TAC tac l = itlist (THEN) (map tac l) ALL_TAC;;

(* ------------------------------------------------------------------------- *)
(* Copies a labelled assumption giving it a new unique label.                *)
(* ------------------------------------------------------------------------- *)
(* e.g. LABEL_INIT_TAC ("x","y") will get the assumption with label "x"      *)
(* and copy it to a new assumption labelled "y" (assuming such label does not*)
(* already exist).                                                           *)
(* ------------------------------------------------------------------------- *)

let (COPY_TAC:(string * string)->tactic) =
 fun (s,n) (asl,w as gl) ->
 try ( ignore(assoc n asl) ;
       (warn true ("COPY_TAC: assumption "^n^" already exists") ; ALL_TAC gl))
 with Failure _ ->
   try (
     let th = assoc s asl in
     LABEL_TAC n th gl
   ) with Failure _ ->
     (warn true ("COPY_TAC: could not find assumption "^s) ; ALL_TAC gl);;
 
let COPYL_TAC l = ITLIST_TAC COPY_TAC l;;


(* ------------------------------------------------------------------------- *)
(* Renames labelled assumptions giving them new unique labels.               *)
(* ------------------------------------------------------------------------- *)

let (RENAME_TAC:(string * string)->tactic) =
 fun (s,n) (asl,w as gl) ->
 try ( ignore(assoc n asl) ;
       (warn true ("RENAME_TAC: assumption "^n^" already exists") ; ALL_TAC gl))
 with Failure _ ->
   try (
     REMOVE_THEN s (LABEL_TAC n) gl
   ) with Failure _ ->
     (warn true ("RENAME_TAC: could not find assumption "^s) ; ALL_TAC gl);;
 
let RENAMEL_TAC l = ITLIST_TAC RENAME_TAC l;;


let REMOVE_TAC s = REMOVE_THEN s (fun x -> ALL_TAC);;


(* ------------------------------------------------------------------------- *)
(* ROTATE_N_TAC:                                                             *)
(* Rotates assumptions N times.                                              *)
(* ------------------------------------------------------------------------- *)
(* Pops the entire assumption list doing nothing (K ALL_TAC) then maps       *)
(* LABEL_TAC to the rotated list of assumptions. The list is reversed so as  *)
(* to match the external order. The result is applied to (asl,w) so as to    *)
(* obtain the resulting goalstate as required by the tactic type.            *)
(* ------------------------------------------------------------------------- *)

let (ROTATE_N_TAC :int->tactic) = 
  fun n (asl,w) ->
    let rotateasm = fun (asl) -> (tl asl)@[hd asl] in
    (POP_ASSUM_LIST(K ALL_TAC) THEN 
       MAP_EVERY (fun (s,th) -> LABEL_TAC s th) (funpow n rotateasm (rev asl))) 
      (asl,w);;


(* ------------------------------------------------------------------------- *)
(* ROTATE_TAC:                                                               *)
(* Rotates assumptions once.                                                 *)
(* ------------------------------------------------------------------------- *)

let (ROTATE_TAC :tactic) = (ROTATE_N_TAC 1);;


(* ------------------------------------------------------------------------- *)
(* CONTEXT_THEN:                                                             *)
(* Instantiates type variables in a term before using it in a tactic.        *)
(* Types are instantiated so that free variables in the term match the types *)
(* of free variables with the same name in the goal.                         *)
(* ------------------------------------------------------------------------- *)
(* CONTEXT_TTHEN is used for thm_tactics.                                    *)
(* ------------------------------------------------------------------------- *)
(* This is different from the HOL4 approach in CONTEXT_TAC.                  *)
(* In that, they parse strings and enforce the appropriate type.             *)
(* Here, the term has already been typed and we instantiate the type         *)
(* variables. This increases the overhead, but maintains the consistency of  *)
(* having terms as arguments instead of strings (easier for the novice user).*)
(* ------------------------------------------------------------------------- *)

let (CONTEXT_THEN :(term -> tactic) -> term -> tactic) =
  let trymatch = fun v1 v2 ->
    match (term_match [v2] v1 v2) with
	[],[],ti -> ti
      | _  -> failwith "" in
  
  fun tac tm g ->
    let gvs = gl_frees g
    and tvs = frees tm in
    let subs = mapfilter (fun x -> tryfind (trymatch x) gvs) tvs in
    tac (inst (flat subs) tm) g;;

let (CONTEXT_TTHEN:(term -> thm_tactic) -> term -> thm_tactic) =
  fun ttac ->
    C (fun thm -> CONTEXT_THEN (fun tm -> ttac tm thm));;


(* Some useful context tactics. *)

let C_EXISTS_TAC = CONTEXT_THEN MATCH_EXISTS_TAC;;
let C_GEN_TAC = CONTEXT_THEN X_MATCH_GEN_TAC;;
let C_CHOOSE_TAC = CONTEXT_TTHEN X_MATCH_CHOOSE_TAC;;

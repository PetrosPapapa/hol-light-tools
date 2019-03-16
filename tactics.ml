(* ========================================================================= *)
(* Various useful, general purpose tactics.                                  *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                 2010 - 2015                               *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Modus ponens tactics.                                                     *)
(* ------------------------------------------------------------------------- *)

let MP_THEN thmtc = fun x -> FIRST_ASSUM (fun y -> (thmtc (MP x y)));;
let MATCH_MP_THEN thmtc = fun x -> FIRST_ASSUM (fun y -> (thmtc (MATCH_MP x y)));;
let EQ_MP_THEN thmtc = fun x -> FIRST_ASSUM (fun y -> (thmtc (EQ_MP x y)));;


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
 
let COPYL_TAC l = MAP_EVERY COPY_TAC l;;


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
 
let RENAMEL_TAC l = MAP_EVERY RENAME_TAC l;;


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


(* ------------------------------------------------------------------------- *)
(* META_SPEC_ALL_TAC:                                                        *)
(* Like META_SPEC_TAC but specialises all universally quantified variables.  *)
(* ------------------------------------------------------------------------- *)
(* META_SPEC_ALL_LABEL_TAC:                                                  *)
(* Same as META_SPEC_ALL_TAC but also adds a label to the assumption.        *)
(* ------------------------------------------------------------------------- *)

let (META_SPEC_ALL_LABEL_TAC: string -> thm -> tactic) =
  fun lbl thm (asl,w) ->
    try (
      let vars,_ = strip_forall (concl thm) in
      let sth = SPECL vars thm in
      (vars,null_inst),[((lbl,sth)::asl),w],
      fun i [th] -> PROVE_HYP (SPECL (map (instantiate i) vars) thm) th
    ) with Failure _ -> failwith "META_SPEC_ALL_TAC";;

let (META_SPEC_ALL_TAC: thm -> tactic) = META_SPEC_ALL_LABEL_TAC "";;


let REMOVE_ALL_ASSUMS_TAC = REPEAT (POP_ASSUM (fun x -> ALL_TAC));;

let REMOVE_ASSUMS_TAC l = MAP_EVERY (fun s -> REMOVE_THEN s (fun x -> ALL_TAC)) l;;
let KEEP_ASSUMS_TAC:string list -> tactic =
  fun l (asl,w) ->
  let remove = subtract (map fst asl) l in
  REMOVE_ASSUMS_TAC remove (asl,w);;


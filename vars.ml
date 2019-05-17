(* ========================================================================= *)
(* Various variable manipulation tools.                                      *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                 2010 - 2014                               *)
(* ========================================================================= *)

needs "IsabelleLight/make.ml";;

(* Match 2 variables *)
(* (Can't remember... is this alpha equivalence?) *)

let vars_match v1 v2 = 
  if is_var v1 && is_var v2 then
    try ( let _ = term_match [v1] v1 v2 in true ) with Failure _ -> false
  else false;;


(* ------------------------------------------------------------------------- *)
(*
  Find a free var in a term by name.
*)
(* ------------------------------------------------------------------------- *)

let find_var: string -> term -> term =
  fun n tm ->
  let f v = try ( n = (fst o dest_var) v ) with Failure _ -> false in
  find f (frees tm);;


(* ------------------------------------------------------------------------- *)
(* Renames a variable with a given function. *)
(* ------------------------------------------------------------------------- *)

let rename_var: (string -> string) -> term -> term =
  fun f tm -> 
  let name,ty = dest_var tm in
  mk_var(f name,ty);;


(* ------------------------------------------------------------------------- *)
(* Given a variable, add a number to its name, then return it.               *)
(* ------------------------------------------------------------------------- *)

let number_var: int -> term -> term =
  fun int tm -> rename_var (fun s -> s^(string_of_int int)) tm;;

(* ------------------------------------------------------------------------- *)
(* number_var for a list of variables.                                       *)
(* ------------------------------------------------------------------------- *)

let number_vars: int -> term list -> term list = 
  fun i -> map (number_var i);;


(* ------------------------------------------------------------------------- *)
(* Apply number_var to an instlist (see Isabelle Light).                     *)
(* If you number the variables of a theorem/meta_rule, you want their        *)
(* references in the instlist to have the same numbering.                    *)
(* ------------------------------------------------------------------------- *)

let number_vars_instlist: int -> (term * term) list -> (term * term) list = 
  fun i -> map (fun x,y -> number_var i x,y);;


(* ------------------------------------------------------------------------- *)
(* Same as number_vars, but returns the composed instantiation for all vars. *)
(* ------------------------------------------------------------------------- *)

let number_vars_inst: int -> term list -> instantiation = 
  fun i vars ->
    let pairs = zip vars (number_vars i vars) in
    let insts = map (fun x,y -> term_match [] x y) pairs in 
    itlist compose_insts insts null_inst;;


(* ------------------------------------------------------------------------- *)
(* number_vars for a term.                                                   *)
(* ------------------------------------------------------------------------- *)

let number_vars_tm: int -> term -> term =
  fun i tm -> instantiate (number_vars_inst i (frees tm)) tm;;


(* ------------------------------------------------------------------------- *)
(* number_vars for a theorem.                                                *)
(* ------------------------------------------------------------------------- *)

let number_vars_thm: int -> thm -> thm =
  fun i thm -> INSTANTIATE (number_vars_inst i (thm_frees thm)) thm;;


(* ------------------------------------------------------------------------- *)
(* number_vars for a meta_rule.                                              *)
(* ------------------------------------------------------------------------- *)

let number_vars_meta_rule: int -> meta_rule -> meta_rule =
  fun i rl -> inst_meta_rule (number_vars_inst i (meta_rule_frees rl)) rl;;


(* ------------------------------------------------------------------------- *)
(* Eliminate numbers from variable names 
   This is useful for renaming variables that you want to reuse in derived 
   rules.
*)
(* ------------------------------------------------------------------------- *)

let unnumber_var = 
  let mapNums c = match c with 
      "0" -> "O"
    | "1" -> "I"
    | "2" -> "R"
    | "3" -> "E"
    | "4" -> "A"
    | "5" -> "S"
    | "6" -> "G"
    | "7" -> "T"
    | "8" -> "B"
    | "9" -> "P"
    | s -> s in
  rename_var (implode o map mapNums o explode);;

(* ------------------------------------------------------------------------- *)
(* unnumber_vars for a term.                                                   *)
(* ------------------------------------------------------------------------- *)

let unnumber_vars_tm: term -> term =
  fun tm -> 
  let sub = map (fun v -> unnumber_var v,v) (frees tm) in
  subst sub tm;;


(* ------------------------------------------------------------------------- *)
(* Same as mk_primed_var but using an underscore "_" instead.                *)
(* ------------------------------------------------------------------------- *)

let mk_undered_var =
  let rec svariant avoid s =
    if mem s avoid or (can get_const_type s & not(is_hidden s)) then
      svariant avoid (s^"_")
    else s in
  fun avoid v ->
    let s,ty = dest_var v in
    let s' = svariant (mapfilter (fst o dest_var) avoid) s in
    mk_var(s',ty);;


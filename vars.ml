(* ========================================================================= *)
(* Various variable manipulation tools.                                      *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                 2010 - 2019                               *)
(* ========================================================================= *)

needs "IsabelleLight/make.ml";;
needs "tools/terms.ml";;

(* Match 2 variables *)
(* (Can't remember... is this alpha equivalence?) *)

let vars_match v1 v2 = 
  if is_var v1 && is_var v2 then
    try ( let _ = term_match [v1] v1 v2 in true ) with Failure _ -> false
  else false;;


(* ------------------------------------------------------------------------- *)
(* Apply a function to all free variables in a term.                         *)
(* ------------------------------------------------------------------------- *)

let mapvars: (term -> term) -> term -> term =
  fun f tm -> 
  let vars = frees tm in
  let sub = zip (map f vars) vars in
  vsubst sub tm;; 


(* ------------------------------------------------------------------------- *)
(* Apply a function to all free variables in a theorem.                      *)
(* ------------------------------------------------------------------------- *)

let mapvars_thm: (term -> term) -> thm -> thm =
  fun f thm ->
  let vars = thm_frees thm in
  let sub = zip (map f vars) vars in
  INST sub thm;; 


(* ------------------------------------------------------------------------- *)
(* Apply a function to all free variables in a meta_rule.                    *)
(* ------------------------------------------------------------------------- *)

let mapvars_meta_rule: (term -> term) -> meta_rule -> meta_rule =
  fun f rl -> 
  let vars = meta_rule_frees rl in
  let inst = itinst f vars in
  inst_meta_rule inst rl;;



(* ------------------------------------------------------------------------- *)
(* Renames a variable with a given function. *)
(* ------------------------------------------------------------------------- *)

let rename_var: (string -> string) -> term -> term =
  fun f tm -> 
  let name,ty = dest_var tm in
  mk_var(f name,ty);;


(* ------------------------------------------------------------------------- *)
(* Apply rename_var to an instlist (see Isabelle Light).                     *)
(* If you rename the variables of a theorem/meta_rule, you want their        *)
(* references in the instlist to have matching names.                        *)
(* ------------------------------------------------------------------------- *)

let rename_vars_instlist: (string -> string) -> (term * term) list -> (term * term) list = 
  fun f -> map (fun x,y -> rename_var f x,y);;



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
(* number_vars for a term, a theorem, and a meta_rule.                       *)
(* ------------------------------------------------------------------------- *)

let number_vars_tm: int -> term -> term = 
  fun i tm -> mapvars (number_var i) tm;;

let number_vars_thm: int -> thm -> thm =
  fun i thm -> mapvars_thm (number_var i) thm;;

let number_vars_meta_rule: int -> meta_rule -> meta_rule =
  fun i rl -> mapvars_meta_rule (number_var i) rl;;


(* ------------------------------------------------------------------------- *)
(* Adds a prefix to a variable name. *)
(* ------------------------------------------------------------------------- *)

let prefix_var: string -> term -> term =
  fun s -> rename_var (fun n -> s ^ n);; 

(* ------------------------------------------------------------------------- *)
(* Adds a prefix and a number to a variable name. *)
(* ------------------------------------------------------------------------- *)

let prefix_num_var: string -> int -> term -> term =
  fun s i -> rename_var (fun n -> s ^ n ^ (string_of_int i));; 

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


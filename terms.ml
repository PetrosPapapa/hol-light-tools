(* ========================================================================= *)
(* Various term construction/destruction/manipulation tools.                 *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                 2010 - 2019                               *)
(* ========================================================================= *)

needs("tools/lib.ml");;

(* ------------------------------------------------------------------------- *)
(* Determine the size of a term based on the number of combinators:          *)
(* term_size (a comb b comb c)  = 1 + (term_size a) + (term_size b)          *)
(*                                  + (term_size c)                          *)
(* term_size of everything else is 1.                                        *)
(* ------------------------------------------------------------------------- *)

let rec term_size tm = 
  if (is_comb tm) then
    itlist (+) (((map term_size) o snd o strip_comb) tm) 1
  else 1;;


(* Flatten an expression for an associative binary operator. *)
(* See eg. flat_munion in multisets.ml                       *)

let rec flat_binary = 
  fun b x ->
    if (is_binary b x) 
    then (flat o (map (flat_binary b)) o snd o strip_comb) x 
    else [x];;


(* From a /\ b /\ c to [a;b;c].                                              *)
(* ------------------------------------------------------------------------- *)
let rec conj_list tm =
  try(
  let (tm1,tm2) = dest_conj tm in tm1::(conj_list tm2)
  ) with Failure _ -> [tm];;



(* Generalize a term fully. *)
let gen_all tm =
  list_mk_forall (frees tm,tm);;



(* ------------------------------------------------------------------------- *)
(* Tests if a term can be matched to a target.                               *)
(* Useful for case splits in syntax manipulation and conversions.            *)
(* ------------------------------------------------------------------------- *)

let can_match consts tm target = 
  try ( ignore (term_match consts tm target) ; true ) 
  with Failure _ -> false;;



(* ------------------------------------------------------------------------- *)
(* Tries to match every term in wlist with a term in tlist, regardless of    *) 
(* their order using a term matching function f.                             *)
(* Makes sure no term from tlist is matched to twice.                        *)
(* Fails if no match is found for any of the members of wlist.               *)
(* ------------------------------------------------------------------------- *)

let rec match_list =
  fun f wlist tlist -> 
    if (wlist = []) then null_inst else
    let i,tlist = try tryremove (f (hd wlist)) tlist 
                  with Failure _ -> failwith ("match_list: No match for `" ^ string_of_term (hd wlist) ^ "`") in
    compose_insts i (match_list f (tl wlist) tlist);;


(* Some debugging prints that I have not yet cleaned up... *)
(*   print_string ("Matched: `" ^ string_of_term (hd wlist) ^ "` to `" ^ string_of_term y ^"` leaving the rest:") ; 
   print_newline(); print_tml tlist ; print_newline() ; *)


(* ------------------------------------------------------------------------- *)
(* match_list using term_match                                               *)
(* ------------------------------------------------------------------------- *)

let term_match_list avoids wlist tlist = match_list (term_match avoids) wlist tlist ;;

(* ------------------------------------------------------------------------- *)
(* match_list using term_match                                               *)
(* ------------------------------------------------------------------------- *)

let term_unify_list metas wlist tlist = match_list (term_unify metas) wlist tlist ;;



(* Apply find_term to each member of a list until one is found.              *)
(* ------------------------------------------------------------------------- *)
let rec list_find_term f alist =
  if (alist = []) then failwith "list_find_term: No matches!"
  else try let _ = find_term f (hd alist) in hd alist with Failure _ -> list_find_term f (tl alist);;


(* ------------------------------------------------------------------------- 
Create a chain of (right-associative) combs over a list
e.g.
# fold_comb `(==>)` [`p:bool`;`q:bool`;`r:bool`];;
val it : term = `p ==> q ==> r`
   ------------------------------------------------------------------------- *)

let fold_comb op tl =
  match tl with
    | [] -> op
    | [h] -> mk_comb(op,h)
    | _ -> itlist (fun x y -> list_mk_comb (op,[x;y])) (butlast tl) (last tl);;


(* ------------------------------------------------------------------------- *)
(* Create a tuple out of a list of terms.                                    *)
(* ------------------------------------------------------------------------- *)

let mk_tuple tl =
  match tl with
    | [] -> failwith "mk_tuple"
    | [h] -> h
    | _ -> itlist (curry mk_pair) (butlast tl) (last tl);;

(* ------------------------------------------------------------------------- *)
(* Convert a term that is a tuple into a list of its element terms.          *)
(* ------------------------------------------------------------------------- *)

let dest_tuple tm = 
  try let tms,l = splitlist dest_pair tm in tms @ [l]
  with Failure _ -> failwith "dest_tuple";;


(* ------------------------------------------------------------------------- *)
(* An often used shortcut that allows REPEATC for conversions that may not   *)
(* affect the term, but won't fail either (such as REWRITE_CONV).            *)
(* ------------------------------------------------------------------------- *)

let REPEAT_CONV = REPEATC o CHANGED_CONV;;


let is_strconst s tm = try ((fst o dest_const) tm = s) with Failure _ -> false;;
let is_strcomb s tm = try ((fst o dest_const o fst o strip_comb) tm = s) with Failure _ -> false;;

let type_matches tp tm =
  try (
  let _ = type_match tp (type_of tm) [] in true )
  with Failure _ -> false;;


(* ------------------------------------------------------------------------- *)
(* 
   Apply a function to a term and then generate the corresponding 
   instantiation.
*)
(* ------------------------------------------------------------------------- *)

let mapinst: (term -> term) -> term -> instantiation = 
  fun f tm -> term_match [] tm (f tm);;

(* ------------------------------------------------------------------------- *)
(* 
   Apply term_finst to a list of terms and compose all the instantiations.
*)
(* ------------------------------------------------------------------------- *)

let itinst: (term -> term) -> term list -> instantiation = 
  fun f tms -> itlist compose_insts (map (mapinst f) tms) null_inst;;


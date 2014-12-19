(* ========================================================================= *)
(* Various term construction/destruction/manipulation tools.                 *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                 2010 - 2014                               *)
(* ========================================================================= *)

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
(* their order.                                                              *)
(* Makes sure no term from tlist is matched to twice.                        *)
(* Fails if no match is found for any of the members of wlist.               *)
(* Invokes term_match twice for every match, but I can't think of a better   *)
(* way to do this at the moment.                                             *)
(* ------------------------------------------------------------------------- *)

let rec term_match_list =
  fun avoids wlist tlist -> 
    if (wlist = []) then null_inst else
    let y,tlist = try remove (
      fun t -> 
	try (let _ = term_match avoids (hd wlist) t in true) 
	with Failure _ -> false
     ) tlist with Failure _ -> failwith ("match_list: No match for `" ^ string_of_term (hd wlist) ^ "`!") in
    compose_insts (term_match avoids (hd wlist) y) (term_match_list avoids (tl wlist) tlist);;

(* Some debugging prints that I have not yet cleaned up... *)
(*   print_string ("Matched: `" ^ string_of_term (hd wlist) ^ "` to `" ^ string_of_term y ^"` leaving the rest:") ; 
   print_newline(); print_tml tlist ; print_newline() ; *)


(* Apply find_term to each member of a list until one is found.              *)
(* ------------------------------------------------------------------------- *)
let rec list_find_term f alist =
  if (alist = []) then failwith "list_find_term: No matches!"
  else try let _ = find_term f (hd alist) in hd alist with Failure _ -> list_find_term f (tl alist);;



(* ------------------------------------------------------------------------- *)
(* Convert a term that is a tuple into a list of its element terms.          *)
(* ------------------------------------------------------------------------- *)

let dest_tuple tm = 
  try let tms,l = splitlist dest_pair tm in tms @ [l]
  with Failure _ -> failwith "dest_tuple";;



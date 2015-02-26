(* ========================================================================= *)
(* Useful multiset tools, theorems, tactics, abbreviations etc.              *)
(* Based on multiset library in Examples/multiwf.ml                          *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                  2010-2015                                *)
(* ========================================================================= *)

(* Library *)
needs "Examples/multiwf.ml";;
needs "tools/rules.ml";;

(* Syntax sugar *)
parse_as_prefix "'";;
override_interface("'",`msing`);;
parse_as_infix("^",(12,"right"));;
override_interface("^",`(munion)`);;
unspaced_binops := ["^";"'"] @ (!unspaced_binops);;

(* Tools *)
let is_msing tm = 
  try fst(dest_const(rator tm)) = "msing"
  with Failure _ -> false;;

let mk_msing tm = mk_icomb (`msing`,tm);;

let is_munion = is_binary "munion";;

let mk_munion (tm1,tm2) = mk_icomb (mk_icomb (`(munion)`,tm1),tm2);;

let list_mk_munion = end_itlist (curry mk_munion);;

(* Flattens ALL munions *)
(* eg. flat_munion `(' a ^ ' b) ^ ' c` = [`' a`;`' b`;`' c`] *)
let rec flat_munion = 
  fun x ->
    if (is_munion x) 
    then (flat o (map flat_munion) o snd o strip_comb) x 
    else [x];;

(* Strips one level of munions (right associative) *)
(* eg. flat_munion `(' a ^ ' b) ^ ' c` = [`' a ^ ' b`;`' c`] *)
let rec strip_munion = 
  fun x ->
    if (is_munion x) 
    then 
      let args = (snd o strip_comb) x in
      let ls,rs = hd args,(hd o tl) args in
      ls :: (strip_munion rs)
    else [x];;

(* Adjusts a list of multisets (representing an munion) so as to be of length n *)
(* If it's too short, it adds empty multisets in the beggining. *)
(* If it's too long, it adds the last two multisets using munion. *)
(* Empty multiset is given by the user to ensure correct type. *)
let rec adjust_munion_list_length empty n l  =
  if (length l = n) then l
  else if (length l < n) then adjust_munion_list_length empty n ([empty] @ l)
  else adjust_munion_list_length empty n (((butlast o butlast)l) @ [mk_munion ((last o butlast) l,last l)]);;


												  
(* Theorems *)

let MUNION_COMM = prove
 (`M1 munion M2 = M2 munion M1`,
  REWRITE_TAC[MEXTENSION; MUNION; ADD_AC]);;

let MUNION_EMPTY2 = prove
 (`mempty munion M = M`,
  REWRITE_TAC[MUNION_COMM; MUNION_EMPTY]);;


(* Rules and Tactics *)

let ELIM_EMPTY_TAC = REWRITE_TAC[MUNION_EMPTY;MUNION_EMPTY2];;

let ELIM_ONE_EMPTY_TAC = ONCE_REWRITE_TAC[MUNION_EMPTY;MUNION_EMPTY2];;

let NORMALIZE_MULTISET = PURE_REWRITE_RULE[MUNION_AC;MUNION_EMPTY;MUNION_EMPTY2];;

let NORMALIZE_MULTISET_ALL thm  = 
  ((UNDISCHN ((length o hyp) thm)) o NORMALIZE_MULTISET o DISCH_ALL) thm;;

let NORM_MSET_CONV = PURE_REWRITE_CONV[MUNION_AC;MUNION_EMPTY;MUNION_EMPTY2];;



(* Attempt to prove that two multisets are equal. *)
(* Quite useful because the multisets in the result are not normalized. *)

let multiset_eq tm1 tm2 =
  TRANS (NORM_MSET_CONV tm1) ((GSYM o NORM_MSET_CONV) tm2);;

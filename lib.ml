(* ========================================================================= *)
(* Useful OCaml functions.                                                   *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                 2010-2017                                 *)
(* ========================================================================= *)

needs "IsabelleLight/support.ml";; (* for print_varandtype *)


(* ------------------------------------------------------------------------- *)
(* Same as tryfind, but also returns the updated list without the element.   *)
(* ------------------------------------------------------------------------- *)

let rec tryremove p l =
  match l with
    [] -> failwith "tryremove"
  | (h::t) -> try (p h),t with Failure _ -> 
              let y,r = tryremove p t in y,h::r;;

(* ------------------------------------------------------------------------- *)
(* Same as tryremove, but also returns the element that was removed (paired).*)
(* ------------------------------------------------------------------------- *)

let rec tryremove' p l =
  match l with
    [] -> failwith "tryremove"
  | (h::t) -> try (h,(p h)),t with Failure _ -> 
              let y,r = tryremove' p t in y,h::r;;


(* ------------------------------------------------------------------------- *)
(* Remove all elements of list r from list l ONCE.                           *)
(* ------------------------------------------------------------------------- *)

let rec remove_list l r =
  match r with
    | [] -> l
    | h::t ->
      let res = try (snd (remove (fun x -> x = h) l)) with Failure _ -> l in
      remove_list res t;;

(* ------------------------------------------------------------------------- *)
(* Same, but removes elements from both lists.                               *)
(* ------------------------------------------------------------------------- *)

let remove_common_once wlist tlist =
  let rec remove_common' =
    fun acc wlist tlist -> 
      if (wlist = []) then rev acc,tlist else
	try (
	  let y,tlist' = remove (fun t -> t = hd wlist) tlist in
	  remove_common' acc (tl wlist) tlist'
	) with Failure _ ->
	  remove_common' ((hd wlist)::acc) (tl wlist) tlist in
  remove_common' [] wlist tlist;;


(* ------------------------------------------------------------------------- *)
(* Uses a function f to filter elements in list l from another list r.
   Elements from l can only be matched once. 
   Is the inverse of remove_list, and also generalized beyond equality. *)
(* ------------------------------------------------------------------------- *)

let filter_once f l r = 
  let rec filter_once' f l r acc =
    match r with
    | [] -> rev acc
    | (h :: t) -> 
       try ( let li,rest = remove (C f h) l in
             filter_once' f rest t (h :: acc) )
       with Failure _ -> filter_once' f l t acc in
  filter_once' f l r [];;


(* ------------------------------------------------------------------------- *)
(* Adds an integer index to every element of a list.                         *)
(* ------------------------------------------------------------------------- *)

let index_list l = zip (0--(length l - 1)) l ;;

(* ------------------------------------------------------------------------- 
Add/update an associative 
*)

let assoc_add a b l =
  (a,b) :: (List.remove_assoc a l);;


(* ------------------------------------------------------------------------- *)
(* The following functions allow us to iterate over all possible subsets of  *)
(* a list in a lazy manner.                                                  *)
(* First we create an index  list of 0s that has the size of the given list. *)
(* This corresponds to the empty subset.                                     *)
(* Each possible subset is then obtained by adding 1 to the binary number    *)
(* represented by the index list. Each member in the index list signifies    *)
(* whether or not the element in the same position in the main list will be  *)
(* included in the subset.                                                   *)
(* e.g. for list [1,2,3,4,5], the index list [1,0,0,1,0] corresponds to      *)
(* subset [1.4].                                                             *)
(* This way, instead of pre-calculating all 2^n subsets, we just hold a      *)
(* single index list of size n in memory.                                    *)
(* ------------------------------------------------------------------------- *)
(* createSubsetIndex creates a list of 0s of size (length l).                *)
(* ------------------------------------------------------------------------- *)
(* nextSubsetIndex adds 1 to the binary number represented by the index list *)
(* effectively obtaining the next subset.                                    *)
(* Returns "None" when we try to add 1 to a list of 1s (we have traversed all*)
(* subsets).                                                                 *)
(* ------------------------------------------------------------------------- *)
(* getIndexedSubset retrieves the actual subset corrsponding to a given      *)
(* index list.                                                               *)
(* ------------------------------------------------------------------------- *)

let rec nextSubsetIndex l =
  match l with
    | [] -> None
    | (h :: tl) ->
	if (h == 0) then Some(1 :: tl)
	else match (nextSubsetIndex(tl)) with
	       | None -> None
	       | Some(ntl) -> Some(0 :: ntl);;
				  
let rec getIndexedSubset index l =
  match (index,l) with
    | [],[] -> []
    | (ih :: it),(lh :: lt) ->
	if (ih > 0) then lh :: (getIndexedSubset it lt) else getIndexedSubset it lt
    | _ -> failwith "getIndexedSubset";;
		    
let createSubsetIndex l =
  let rec subsetIndex n index =
    if (n == 0) then index
    else subsetIndex (n-1) (0 :: index) in
  subsetIndex (length l) [];;
	      

(* ------------------------------------------------------------------------- *)
(* Topological sort for a dependency tree.                                   *)
(* Perhaps not the most efficient, but it will do.                           *)
(* ------------------------------------------------------------------------- *)

let rec dependency_sort isParentOf l =
  match l with 
    | [] -> []
    | (h::t) -> 
	let deps,nodeps = partition (isParentOf h) t in
	(dependency_sort isParentOf deps) @ [h] @ (dependency_sort isParentOf nodeps);;

(* ------------------------------------------------------------------------- *)
(* Apply a function to both members of a pair. Same as 'f ## f' in HOL4.     *)
(* ------------------------------------------------------------------------- *)

let hashf f (x,y) = (f x, f y) ;;

(* ------------------------------------------------------------------------- *)
(* Invert pairs.                                                             *)
(* Used to invert substitutions.                                             *)
(* ------------------------------------------------------------------------- *)

let invpair (x,y) = y,x;;

let invpairs l = map invpair l;;

(* ------------------------------------------------------------------------- *)
(* Function used for indented prints.                                        *)
(* ------------------------------------------------------------------------- *)

let rec print_depth depth prn arg =
  match depth with
      0 -> (prn arg ; print_newline ())
    | _ -> (print_string " " ; print_depth (depth -1) prn arg);;


(* ------------------------------------------------------------------------- *)
(* print_goalstack_all :                                                     *) 
(* Alternative goalstack printer that always prints all subgoals.            *)
(* Also prints list of metavariables with their types.                       *)
(* ------------------------------------------------------------------------- *)
(* Original printer only prints more than one subgoals iff they were         *)
(* generated by the last step. Otherwise it only prints the 'active' subgoal.*)
(* Replace by #install_printer print_goalstack_all;;                         *)
(* Revert to original by #install_printer print_goalstack;;                  *)
(* ------------------------------------------------------------------------- *)

let (print_goalstack_all:goalstack->unit) =
  let print_goalstate k gs =
    let ((mvs,_),gl,_) = gs in
    let n = length gl in
    let s = if n = 0 then "No subgoals" else
              (string_of_int k)^" subgoal"^(if k > 1 then "s" else "")
           ^" ("^(string_of_int n)^" total)" in
    let print_mv v = print_string " `" ; print_varandtype std_formatter v ; print_string "`;" in
    print_string s; print_newline();
    if (length mvs > 0) then (
      print_string "Metas:" ; let _ = map print_mv mvs in () ; print_newline()
    ) ; 
    if gl = [] then () else
    do_list (print_goal o C el gl) (rev(0--(k-1))) in
  fun l ->
    if l = [] then print_string "Empty goalstack"
    else 
      let (_,gl,_ as gs) = hd l in
      print_goalstate (length gl) gs;;


(* ------------------------------------------------------------------------- *)
(* print_thl:                                                                *)
(* Print a list of theorems (for debugging).                                 *)
(* ------------------------------------------------------------------------- *)

let print_thl thl = 
  map (fun thm -> ( print_thm thm ; print_newline ())) thl;;


(* ------------------------------------------------------------------------- *)
(* print_tml:                                                                *)
(* Print a list of terms (for debugging).                                    *)
(* ------------------------------------------------------------------------- *)

let print_tml tml = 
    map (fun tm -> ( print_term tm ; print_newline ())) tml;;


(* ------------------------------------------------------------------------- *)
(* count_goals : unit -> int                                                 *) 
(* Shortcut to count the subgoals in the current goalstate.                  *)
(* ------------------------------------------------------------------------- *)

let count_goals () =
  if (!current_goalstack = []) then 0 else
  (length o snd3 o hd) !current_goalstack;;


(* ------------------------------------------------------------------------- *)
(* top_asms : goalstack -> (string * thm) list                               *) 
(* Shortcut to get the assumption list of the top goal of a given goalstack. *)
(* ------------------------------------------------------------------------- *)

let top_asms (gs:goalstack) = (fst o hd o snd3 o hd) gs;;


(* ------------------------------------------------------------------------- *)
(* top_metas : goalstack -> term list                                        *) 
(* Returns the list of metavariables in the current goalstate.               *)
(* ------------------------------------------------------------------------- *)
(* This also exists in Isabelle Light.                                       *)
(* ------------------------------------------------------------------------- *)

let top_metas (gs:goalstack) = (fst o fst3 o hd) gs;;


(* ------------------------------------------------------------------------- *)
(* top_inst : goalstack -> instantiation                                     *) 
(* Returns the metavariable instantiations in the current goalstate.         *)
(* ------------------------------------------------------------------------- *)

let top_inst (gs:goalstack) = (snd o fst3 o hd) gs;;


(* ------------------------------------------------------------------------- *)
(* e_all : tactic -> goalstack                                               *) 
(* Same as "e" but applies tactic to ALL subgoals.                           *)
(* ------------------------------------------------------------------------- *)
(* This could be done better by implementing a by_all function, but it'll    *)
(* do for now since it's rarely used anyway.                                 *) 
(* ------------------------------------------------------------------------- *)

let e_all tac =
  let c = (count_goals()) in
  let rec f i = ( 
    if (i = 0) 
    then (!current_goalstack) 
    else let _ = e tac in let _ = r 1 in f (i-1) 
   ) in f c;;


(* ------------------------------------------------------------------------- *)
(* refine for any goalstate.                                                 *)
(* ------------------------------------------------------------------------- *)

let (refinestack:refinement->goalstack->goalstack) =
  fun r gs ->
    if gs = [] then failwith "No current goal" else
    let h = hd gs in
    r h :: gs;;

(* ------------------------------------------------------------------------- *)
(* e for any goalstate.                                                      *)
(* ------------------------------------------------------------------------- *)

let (apply_tac:tactic->goalstack->goalstack) =
  fun tac gs -> refinestack (by(VALID tac)) gs;;


(* ------------------------------------------------------------------------- *)
(* top_thm for any goalstate.                                                *)
(* ------------------------------------------------------------------------- *)

let get_thm (gs:goalstack) =
  let (_,[],f)::_ = gs in
  f null_inst [] ;;


(* ------------------------------------------------------------------------- *)
(* Timing.                                                                   *)
(* ------------------------------------------------------------------------- *)

let my_timestamp = ref 0.0;;

let truncate_float n f =
  let factor = 10.0 ** (float_of_int n) in
  ((float_of_int o truncate) (f *. factor)) /. factor;;

let reset_time () = my_timestamp := Sys.time();;
let get_time () = truncate_float 4 (Sys.time() -. (!my_timestamp));;
let rget_time() = let t = get_time () in reset_time (); t;;

let stime s f x =
  let start_time = Sys.time() in
  try let result = f x in
      let finish_time = Sys.time() in
      report(s ^ ": "^(string_of_float(truncate_float 4 (finish_time -. start_time))));
      result
  with e ->
      let finish_time = Sys.time() in
      Format.print_string(s ^ " - FAILED: "^
                          (string_of_float(truncate_float 4 (finish_time -. start_time))));
      print_newline();
      raise e;;

let TIME_TAC s (tac:tactic) gl =
  stime s tac gl;;

(* ========================================================================= *)
(* A counter/labelling systems that provides fresh labels for each proof     *)
(* step.                                                                     *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                 2010-2015                                 *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* We use this counter in proofs so that we automatically number the         *)
(* theorems being applied so that their names/metavariables are always fresh *)
(* while we're still able to reference them in the instlist.                 *)
(* ------------------------------------------------------------------------- *)

let proofctr = ref 0;;

let reset_proofctr () = proofctr := 0;;

let dec_proofctr () = let x = (!proofctr) in proofctr := x - 1;;

let fresh_proofctr =
  fun () -> let count = !proofctr in
             (proofctr := count + 1;
	      count);;


(* ------------------------------------------------------------------------- *)
(* Proof counter stack in order to be able to undo/redo tactics with         *)
(* proof steps.                                                              *)
(* ------------------------------------------------------------------------- *)

let proofctrstack = ref ([]:int list);;

let reset_proofctrstack () = let _ = reset_proofctr () in proofctrstack := [];;

let proofctrpush x = 
  let l = !proofctrstack in
    proofctrstack := x :: l;;

let proofctrpop () = 
  let l = !proofctrstack in
    if length l = 0 then failwith "proofctrpop: Can't back up any more" else
      proofctrstack := tl l;
    hd l;;

(* ------------------------------------------------------------------------- *)
(* Set a goal after reseting the proof counter.                              *)
(* ------------------------------------------------------------------------- *)

let g tm = let _ = reset_proofctrstack () in g tm;;

(* ------------------------------------------------------------------------- *)
(* Go back while maintaining the proof counter.                              *)
(* ------------------------------------------------------------------------- *)

let b () = let _ = proofctr :=  (proofctrpop ()) in b ();;

(* ------------------------------------------------------------------------- *)
(* Apply a tactic while maintaining proofctrstack.                           *)
(* ------------------------------------------------------------------------- *)
(* Note that the tactics are responsible to update the proof counter if they *)
(* use it.                                                                   *)
(* ------------------------------------------------------------------------- *)

let e tac = let _ = proofctrpush (!proofctr) in 
  try (e tac) 
  with Failure s -> 
    let _ = proofctr :=  (proofctrpop ()) in failwith s;;


(* ------------------------------------------------------------------------- *)
(* Break off "_N" from the end of a string and reattach "_f(N)".             *)
(* If anything fails (N is not a number or no "_" is found) just attach "_D" *)
(* where D the default value "dflt".                                         *)
(* ------------------------------------------------------------------------- *)

let fresh_label dflt freshf s =
  if s = "" then "" else
    try (
      let index = String.rindex s '_' in
      let smain = String.sub s 0 index
      and snum = int_of_string (String.sub s (index+1) ((String.length s) - index - 1))
      in (smain ^ "_" ^ (string_of_int (freshf snum)))
    ) with _ -> (s ^ "_" ^ (string_of_int dflt));;

let set_label s n =
  fresh_label n (fun x -> n) s;;

let inc_label s =
  fresh_label 0 ((+) 1) s;;


(* ------------------------------------------------------------------------- *)
(* Same as above but attaches proofctr so that the new label is always       *)
(* fresh for each rule being applied.                                        *)
(* ------------------------------------------------------------------------- *)

let proofctr_label s =
  set_label s (!proofctr);;

let proofctr_label_var tm =
  let s,t = dest_var tm in
  mk_var (proofctr_label s,t);;



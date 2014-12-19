(* ========================================================================= *)
(* Various useful, general purpose tactics.                                  *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                 2010 - 2014                               *)
(* ========================================================================= *)


let MP_THEN thmtc = fun x -> FIRST_ASSUM (fun y -> (thmtc (MP x y)));;
let MATCH_MP_THEN thmtc = fun x -> FIRST_ASSUM (fun y -> (thmtc (MATCH_MP x y)));;
let EQ_MP_THEN thmtc = fun x -> FIRST_ASSUM (fun y -> (thmtc (EQ_MP x y)));;


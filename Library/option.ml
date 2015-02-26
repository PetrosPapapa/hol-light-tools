(* ========================================================================= *)
(* Extension of option with simple theorems and definitions.                 *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                    2015                                   *)
(* ========================================================================= *)

needs "IsabelleLight/make.ml";;

let THE_DEF = new_recursive_definition option_RECURSION
				       `!x. THE (SOME x) = x`;;

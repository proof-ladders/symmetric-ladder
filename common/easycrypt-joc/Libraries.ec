(* ------------------------------------------------------- *)
(* Library Building Blocks *)
(* ------------------------------------------------------- *)
require import AllCore.

(* All libraries have an init and fin function *)
module type LibBase = {
  proc init() : unit
  proc fin() : unit
}.

(* Basic composition of two bases *)
module CompBase (L1 : LibBase) (L2 : LibBase) : LibBase = {
  proc init() = {
    L2.init();
    L1.init();
  }
  proc fin() = {
    L1.fin();
    L2.fin();
  }
}.

(*
   An adversarial library is an adversary composed with the library
   it is attempting to distinguish.
*)
module type LibAdv = {
  include LibBase
  proc run() : bool
}.

(* Given an adverarial library there is only one way to play the game *)
module Game (A : LibAdv) = {
  proc main() = {
    var b;

    A.init();
    b <@ A.run();
    A.fin();
    return b;
  }
}.

(* ------------------------------------------------------- *)
(* TO MOVE *)
(* Helpers for performing different types of game hops *)
(* ------------------------------------------------------- *)

(* Switch to game z from game x applying an assumption *)
lemma asmp (z x y a : real): `|z - y| <= a - `|x - z| => `|x - y| <= a.
proof. by smt(). qed.

(* Useful for up-to-bad impossible reasoning *)
lemma abs_eq x y: `|x - y| <= 0%r => x = y.
proof.
by move => /normr_le0 /RField.subr_eq0.
qed.

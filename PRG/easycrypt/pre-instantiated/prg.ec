require import AllCore List Distr.

type t.

op [lossless full uniform] dt : t distr.

(* PRG 2: a 2-expanding PRG
   we don't have a concrete realization because we prove the result
   for every 2-PRG. *)
(** Syntax: a 2-PRG is a `query` that takes input from a type `t` and
    outputs two elements of `t` **)
module type PRG2 = {
  proc query(s : t) : t * t
}.

(** Security: a 2-PRG is secure if its output on a uniformly random
    element of `t` cannot be distinguished from a uniformly random
    pair of elements of `t` **)
module PRG2i : PRG2 = {
  proc query(s : t) = {
    var x,y;
    
    x <$ dt;
    y <$ dt;
    return (x,y);
  }
}.

(*** This is the type of 2-PRG distinguishers, algorithms that take in
     two elements of `t` and output a boolean ***)
module type Dist2 = {
  proc distinguish(v : t * t) : bool
}.

(*** And the experiment, which samples an input from `t`, runs the
     2-PRG it is parameterized by, then runs a distinguisher on its
     output. ***)
module IND_2 (F : PRG2) (D : Dist2) = {
  proc game() : bool = {
    var b; 
    var s;
    var x,y;
    
    s <$ dt;

    (x,y) <@ F.query(s);

    b <@ D.distinguish(x,y);
    return b;
  }
}.

(* 3-PRG: the same, but outputting 3 elements from `t`
   We could define a generic PRG theory, and instantiate it twice.
   Do that as an exercise! *)
module type PRG3 = {
  proc query(s : t) : t * t * t
}.

module PRG3i : PRG3 = {
  proc query(s : t) = {
    var a,b,c;
    
    a <$ dt;
    b <$ dt;
    c <$ dt;
    return (a,b,c);
  }
}.

module type Dist3 = {
  proc distinguish(v : t * t * t) : bool
}.

module IND_3 (G : PRG3) (D : Dist3) = {
  proc game() : bool = {
    var b; 
    var s;
    var x,y,z;
    
    s <$ dt;

    (x,y,z) <@ G.query(s);

    b <@ D.distinguish(x,y,z);
    return b;
  }
}.

(* We now define the construction we want to prove something about
   (finally): a generic construction that turns any 2-PRG it takes as
   parameter into a 3-PRG *)
module PRG3r (P : PRG2) : PRG3 = {
  proc query(s : t) = {
    var a,b1,b2,c;

    (a, b1) <@ P.query(s);
    (b2, c) <@ P.query(b1);
    return (a,b2,c);
  }
}.

print PRG3r.

(* We want to show that for every 2-PRG P, and for every
   3-Distinguisher D, the advantage of D in distinguishing PRG3r(P)
   from PRG3i is bounded from above by twice the advantage of R1(P, D)
   distinguishing P from PRG2i, plus twice the advantage of R2(D)
   distinguishing P from PRG2i; where R1 and R2 are defined as
   below. *)

module R1 (P : PRG2) (D : Dist3) : Dist2 = {
  proc distinguish(a : t, b1 : t) : bool = {
    var b : bool; 
    var b2,c : t;
    
    (b2, c) <@ P.query(b1);
    b <@ D.distinguish(a,b2,c);

    return b;
  }
}.

print R1.

module R2 (D : Dist3) : Dist2 = {
  proc distinguish(b1 : t, c : t) : bool = {
    var b : bool; 
    var a : t;
    
    a <$ dt;
    b <@ D.distinguish(a,b1,c);

    return b;
  }
}.

print R2.

(* The rest of the file is the proof analyzing the relation between
   advantages. *)
section PROOFS.
  (** The section allows us to quantify over P and D once, and be able
      to use them everywhere. The following are universal
      quantifications. **)
  declare module P <: PRG2.
  declare module D <: Dist3 { -P (*** In EasyCrypt, all modules can
                                      access all memory; we prove
                                      security only against distinguishers
                                      that can't share memory with P ***) }.

  (* In this proof, we're just going to "walk" the advantage from one
     side to the other *)
  local lemma eqpr_IND3PRG3PD_IND2PRG2R1 &m:
      Pr[IND_3(PRG3r(P), D).game() @ &m : res]
    = Pr[IND_2(P, R1(P, D)).game() @ &m : res].
  proof.
  byequiv (: ={glob D, glob P} ==> ={res})=> //.
  (* Here, the proof is literally by inlining *)
  by proc; inline *; sim.
  qed.

  (* Advantage of R1(P, D) in distinguishing P from PRG2i *)

  local lemma eqpr_IND2PRG2iR1_IND2PRG2R2 &m:
      Pr[IND_2(PRG2i, R1(P, D)).game() @ &m : res]
    = Pr[IND_2(P, R2(D)).game() @ &m : res].
  proof.
  byequiv (: ={glob D, glob P} ==> ={res})=> //.
  proc; inline *; sim.
  (* Inlining is not enough: we need to swap some statements to align
     the random samplings. *)
  swap {2} [2..4] 1.
  wp; sim.
  swap {2} 1 1.
  by sim; auto.
  qed.

  (* Advantage of R2(D) in distinguishing P from PRG2i *)

  local lemma eqpr_IND2PRG2iR2_IND3PRG3iD &m:
      Pr[IND_2(PRG2i, R2(D)).game() @ &m : res]
    = Pr[IND_3(PRG3i, D).game() @ &m : res].
  proof.
  byequiv (: ={glob D} ==> ={res})=> //.
  proc; inline *.
  swap {1} 8 -5.
  by sim.
  qed.
 
  (* Note how this lemma is not local; it will leave the section when
     we close it *)
  lemma main_result &m : 
       `|  Pr[IND_3(PRG3r(P), D).game() @ &m : res]
         - Pr[IND_3(PRG3i, D).game() @ &m : res]    |
    <=   `|  Pr[IND_2(P, R1(P, D)).game() @ &m : res]
           - Pr[IND_2(PRG2i, R1(P, D)).game() @ &m : res] |
       + `|  Pr[IND_2(P, R2(D)).game() @ &m : res]
           - Pr[IND_2(PRG2i, R2(D)).game() @ &m : res] |.
  proof.
  (* We just "walk" the advantage as planned, and conclude with the
     triangle inequality *)
  rewrite eqpr_IND3PRG3PD_IND2PRG2R1.
  rewrite eqpr_IND2PRG2iR1_IND2PRG2R2.
  rewrite eqpr_IND2PRG2iR2_IND3PRG3iD.
  exact: StdOrder.RealOrder.ler_dist_add.
  qed.
end section PROOFS.

(* And note in what the below outputs: `main_result` is now
   universally quantified over P and D with the stated restrictions *)
print main_result.

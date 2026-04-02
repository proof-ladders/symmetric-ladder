(*^ This file formally defines a construction of a length-tripling
    Pseudo-Random Generator (PRG) from a length-doubling PRG, and
    formally establishes bounds on the insecurity of the construction
    (as a PRG) from the insecurity of the assumption (as a PRG). The
    syntax and security of PRGs are defined generically in the
    accompanying file `PRG.eca`.

    The length-doubling and length-tripling are left somewhat
    abstract: we avoid specializing the formalization to bitstrings,
    keeping the underlying type abstract and representing doubling and
    tripling as tupling. Instantiating the underlying type (`t` in the
    below) to fixed-length bitstrings, and making the concatenation
    explicit is an interesting further step.
^*)
require import AllCore Distr.
require (*--*) PRG.

(*& The theory is parameterized by an abstract type that models the
    fixed type of seeds, which we will double and triple by
    tupling. As mentioned earlier, this allows us to variously
    instantiate the same result with different types. &*)
type t.

(*& We assume a lossless (total probability 1), full (every element of
    type `t` has non-zero probability) and uniform (every element of
    the support has the same probability) distribution over `t`. This
    implies finiteness, and could be modelled more directly. &*)
(*& Note: this distribution is also used as the implementation of our
    sgen algorithm. &*)
op [lossless full uniform] dt : t distr.

(*& We first instantiate the generic PRG theory, which defines syntax
    and security (see `PRG.eca`) with the types and distributions
    considered here. This gives us a local copy (`PRG2`) specialized
    to length-doubling with `t` as base type. &*)
(*& In a type expression like `t * t`, the * represents tupling.
    When instantiating `dout` with a distribution, we use `*` (which
    is defined in EasyCrypt's library) to construct a product
    distribution. &*)
clone PRG as PRG2 with
  type seed   <- t,
  type output <- t * t,
  op   dout   <- dt `*` dt
proof *. (* There are no assumptions to discharge *)

(*^ We restrict our setting slightly by considering PRGs whose sgen
    is sampling in dt. This allows us to prove things quantified only
    on the query algorithm. ^*)

(*& First we define a module type for PRGs without a seed generation
    algorithm. This is what allows us to quantify only on the `query`
    algorithm. &*)
module type SeededPRG = {
  include PRG2.PRG [query]
}.

(*& Then we define a simple wrapper that constructs a full PRG (which
    fits the syntax defined in `PRG2`) from a seeded PRG. &*)
module PRG2r (S : SeededPRG) : PRG2.PRG = {
  proc sgen() = {
    var s;

    s <$ dt;
    return s;
  }

  proc query = S.query
}.

(*& We then instantiate the PRG theory for length-tripling. &*)
clone PRG as PRG3 with
  type seed  <- t,
  type output <- t * (t * t),
  op   dout   <- dt `*` (dt `*` dt)
proof *.

(*& And we can then define the construction of a PRG3 from a
    PRG2. This is the object of our proof: &*)
module PRG3r (P : PRG2.PRG) : PRG3.PRG = {
  proc sgen = P.sgen

  proc query(s : t) = {
    var a,b1,b2,c;

    (a, b1) <@ P.query(s);
    (b2, c) <@ P.query(b1);
    return (a,(b2,c));
  }
}.

print PRG3r.

(*^ We want to show that for every 2-PRG P, and for every
    3-Distinguisher D, the advantage of D in distinguishing PRG3r(P)
    from PRG3i is bounded from above by the sum of the advantages of
    two reductions. We explicitly define those reductions as R1 and
    R2. ^*)

module R1 (P : SeededPRG) (D : PRG3.Dist) : PRG2.Dist = {
  proc distinguish(a : t, b1 : t) : bool = {
    var b : bool; 
    var b2, c : t;
    
    (b2, c) <@ P.query(b1);
    b <@ D.distinguish(a,(b2,c));

    return b;
  }
}.

print R1.

module R2 (D : PRG3.Dist) : PRG2.Dist = {
  proc distinguish(b2 : t, c : t) : bool = {
    var b : bool; 
    var a : t;
    
    a <$ dt;
    b <@ D.distinguish(a,(b2,c));

    return b;
  }
}.

print R2.

(*^ The rest of the file is the proof analyzing the relation between
    advantages and is elided in the generated documentation for
    now. ^*)
section PROOFS.
  (** The section allows us to quantify over P and D once, and be able
      to use them everywhere. The following are universal
      quantifications. **)
  declare module P <: SeededPRG.
  declare module D <: PRG3.Dist { -P (*** In EasyCrypt, all modules
                                          can, unless otherwise
                                          specified, access all
                                          memory; we prove security
                                          only against distinguishers
                                          that can't share memory with
                                          P; through this
                                          restriction. ***) }.

  (* In this proof, we're just going to "walk" the advantage from one
     side to the other *)
  local lemma eqpr_IND3PRG3PD_IND2PRG2R1 &m:
      Pr[PRG3.IND_real(PRG3r(PRG2r(P)), D).game() @ &m : res]
    = Pr[PRG2.IND_real(PRG2r(P), R1(P, D)).game() @ &m : res].
  proof.
  byequiv (: ={glob D, glob P} ==> ={res})=> //.
  (* Here, the proof is literally by inlining *)
  proc; inline *.
  wp; call (: true); conseq />.
  wp; call (: true); conseq />.
  wp; call (: true); conseq />.
  by auto.
  qed.

  (* Advantage of R1(P, D) in distinguishing P from PRG2i *)

  local lemma eqpr_IND2PRG2iR1_IND2PRG2R2 &m:
      Pr[PRG2.IND_ideal(R1(P, D)).game() @ &m : res]
    = Pr[PRG2.IND_real(PRG2r(P), R2(D)).game() @ &m : res].
  proof.
  byequiv (: ={glob D, glob P} ==> ={res})=> //.
  proc; inline *; sim.
  (* Inlining is not enough: we need to swap some statements to align
     the random samplings. *)
  swap {2} 5 -4.
  wp; call (: true); conseq |>.
  rnd: *0; auto=> |>; split=> [[] x y _|_ [] x y].
  + rewrite dprod_dlet dmap_dlet /=.
    congr; apply: eq_dlet=> // x' //=.
    by rewrite dlet_dunit dmap_comp /(\o) /=.
  rewrite supp_dmap=> |> {x y} [] |> x y.
  rewrite supp_dprod=> |> x'_in_dt y'_in_dt.
  rewrite supp_dlet; exists x=> |>.
  by rewrite supp_dmap; exists y.
  qed.

  (* Advantage of R2(D) in distinguishing P from PRG2i *)

  local lemma eqpr_IND2PRG2iR2_IND3PRG3iD &m:
      Pr[PRG2.IND_ideal(R2(D)).game() @ &m : res]
    = Pr[PRG3.IND_ideal(D).game() @ &m : res].
  proof.
  byequiv (: ={glob D} ==> ={res})=> //.
  proc; inline *.
  swap {1} 3 -2.
  wp; call (: true); conseq |>.
  wp; rnd: *0; auto=> |>; split=> [[] x y _|_ [] x [] y z].
  + rewrite dprod_dlet dmap_dlet /=.
    congr; apply: eq_dlet=> // x' //=.
    by rewrite dlet_dunit dmap_comp /(\o) /=.
  rewrite supp_dlet=> |> x' x_in_dt.
  rewrite supp_dmap=> |> {x} yz_in_dt2.
  rewrite supp_dmap; exists (x', (y, z)).
  by rewrite supp_dprod.
  qed.
 
  (* Note how this lemma is not local; it will leave the section when
     we close it *)
  lemma main_result &m : 
       `|  Pr[PRG3.IND_real(PRG3r(PRG2r(P)), D).game() @ &m : res]
         - Pr[PRG3.IND_ideal(D).game() @ &m : res]    |
    <=   `|  Pr[PRG2.IND_real(PRG2r(P), R1(P, D)).game() @ &m : res]
           - Pr[PRG2.IND_ideal(R1(P, D)).game() @ &m : res] |
       + `|  Pr[PRG2.IND_real(PRG2r(P), R2(D)).game() @ &m : res]
           - Pr[PRG2.IND_ideal(R2(D)).game() @ &m : res] |.
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

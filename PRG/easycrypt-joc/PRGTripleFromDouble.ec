(* ------------------------------------------------------- *)
(* 
  Constructing a triple length extending PRG from a
  double length extension PRG.
*)
(* ------------------------------------------------------- *)

require import Libraries.
require import AllCore List.
require import Distr DList DMap.
require (*  *) PRG BitStrings.
(*   *) import StdOrder.IntOrder.

(* Initial input length of the bit strings *)
op lambda : { int | 0 < lambda } as gt0_lam.

(* Bitstrings of length lambda, 2 * lambda, 3 * lambda. *)
clone import BitStrings as BS with
  op lambda <- lambda,
  lemma gt0_lam <- gt0_lam
proof *.

(* ------------------------------------------------------- *)
(* The construction *)
(* ------------------------------------------------------- *)

clone PRG as Double with
  type t_in <- bits_lam,
  type t_out <- bits_2lam,
  op d_in <- dbits_lam,
  op d_out <- dbits_2lam
proof*.

clone PRG as Triple with
  type t_in <- bits_lam,
  type t_out <- bits_3lam,
  op d_in <- dbits_lam,
  op d_out <- dbits_3lam
proof*.

module H (G : Double.G) : Triple.G = {
  proc run(s) = {
    var a, b, c, d, t;
    
    t <@ G.run(s);
    (a, b) <- half t;
    t <@ G.run(b);
    (c, d) <- half t;
    return concat12 a (c || d); (* a || c || d *)
  }
}.

section.


(* ------------------------------------------------------- *)
(* Intermediate games for the proof of security *)
(* ------------------------------------------------------- *)

(* Identifies the reduction to Double.API from a Triple.Lib *)
local module type Factor (L : Double.API) = {
  include Triple.Lib
}.

module Inline1 (G : Double.G) : Triple.Lib = Triple.PRG_real(H(G)) with {
  proc sample [
    var a, b, c, d : bits_lam
    var r : bits_2lam

    (* The procedure call to inline *)
    ^t<@ ~ {
      r <@ G.run(s);
      (a, b) <- half r;
      r <@ G.run(b);
      (c, d) <- half r;
      t <- concat12 a (c || d);
    }
  ]
}.

(* The first reduction *)
module (Factor1 (G : Double.G) : Factor) (L : Double.API) = Inline1(G) with {
  proc sample [
    [^s<$ .. ^r<@] ~ {r <@ L.sample(); }
  ]
}.

module Inline2 (G : Double.G) : Triple.Lib = Factor1(G, Double.PRG_rand(G)) with {
  proc sample [
    ^r<@ ~ { r <$ dbits_2lam; }
  ]
}.

module Split (G : Double.G) = Inline2(G) with {
  proc sample[
    [^r<$ .. ^(a)<-] ~ {a <$ dbits_lam; b <$ dbits_lam;}
  ]
}.

(* The second reduction *)
module (Factor2 (G : Double.G) : Factor) (L : Double.API) = Split(G) with {
  proc sample [
    [^b<$ .. ^r<@] ~ {r <@ L.sample(); }
  ]
}.


module Inline3 (G : Double.G) : Triple.Lib = Factor2(G, Double.PRG_rand(G)) with {
  proc sample [
    ^r<@ ~ { r <$ dbits_2lam; }
  ]
}.

(* ------------------------------------------------------- *)
(* The PRG we use to build our construction *)
(* ------------------------------------------------------- *)

declare module G <: Double.G {
  -Inline1,
  -Factor1,
  -Inline2, -Split,
  -Factor2,
  -Inline3
}.

(* ------------------------------------------------------- *)
(* The Adversary *)
(* ------------------------------------------------------- *)

(* It cannot look inside the state of the games or the PRG *)
declare module A <: Triple.Adv{
  -G,

  -Inline1,
  -Factor1,
  -Inline2, -Split,
  -Factor2,
  -Inline3
}.

(* ------------------------------------------------------- *)
(* Properly build factored libraries/adversaries *)
(* ------------------------------------------------------- *)
module (Factor_Adv (F : Factor) (A : Triple.Adv) : Double.Adv) (L : Double.API) = {
  include CompBase(A(F(L)), F(L))
  include A(F(L))[-init, fin]
}.

local module Factor_Lib (F : Factor ) (L : Double.Lib) = {
  include CompBase(F(L), L)
  include F(L)[-init, fin]
}.

module Factor1_Adv (A : Triple.Adv) = Factor_Adv(Factor1(G), A).
module Factor2_Adv (A : Triple.Adv) = Factor_Adv(Factor2(G), A).
local module Factor1_Lib (L : Double.Lib) = Factor_Lib(Factor1(G), L).
local module Factor2_Lib (L : Double.Lib) = Factor_Lib(Factor2(G), L).

local lemma Factor1_real &m:
  Pr[Game(Triple.LibAdv(A, Factor1_Lib(Double.PRG_real(G)))).main() @ &m : res]
 =
  Pr[Game(Double.LibAdv(Factor1_Adv(A), Double.PRG_real(G))).main() @ &m : res].
proof. by byequiv => //; proc; inline; sim. qed.

local lemma Factor1_rand &m:
  Pr[Game(Triple.LibAdv(A, Factor1_Lib(Double.PRG_rand(G)))).main() @ &m : res]
 =
  Pr[Game(Double.LibAdv(Factor1_Adv(A), Double.PRG_rand(G))).main() @ &m : res].
proof. by byequiv => //; proc; inline; sim. qed.

local lemma Factor2_real &m:
  Pr[Game(Triple.LibAdv(A, Factor2_Lib(Double.PRG_real(G)))).main() @ &m : res]
 =
  Pr[Game(Double.LibAdv(Factor2_Adv(A), Double.PRG_real(G))).main() @ &m : res].
proof. by byequiv => //; proc; inline; sim. qed.

local lemma Factor2_rand &m:
  Pr[Game(Triple.LibAdv(A, Factor2_Lib(Double.PRG_rand(G)))).main() @ &m : res]
 =
  Pr[Game(Double.LibAdv(Factor2_Adv(A), Double.PRG_rand(G))).main() @ &m : res].
proof. by byequiv => //; proc; inline; sim. qed.

(* ------------------------------------------------------- *)
(* Extra program equivalences for use in the proof *)
(* ------------------------------------------------------- *)
local clone DProd.ProdSampling as ProdProg11 with
  type t1 <- bits_lam,
  type t2 <- bits_lam.

local clone DMapSampling as DMapProg2 with
  type t1 <- bits_lam * bits_lam,
  type t2 <- bits_2lam.

local clone DProd.ProdSampling as ProdProg12 with
  type t1 <- bits_lam,
  type t2 <- bits_2lam.

local clone DMapSampling as DMapProg3 with
  type t1 <- bits_lam * bits_2lam,
  type t2 <- bits_3lam.

(* ------------------------------------------------------- *)
(* Proof Steps *)
(* ------------------------------------------------------- *)

(* Inline the real PRG Triple Extend game. *)
local lemma Step1 &m:
  Pr[Game(Triple.LibAdv(A, Triple.PRG_real(H(G)))).main() @ &m : res]
 =
  Pr[Game(Triple.LibAdv(A, Inline1(G))).main() @ &m : res].
proof.
byequiv => //.
proc; inline.
sim (: ={glob G}).
by proc; inline; sim.
qed.

(* Factor out the real PRG Double Extend game. *)
local lemma Step2 &m:
  Pr[Game(Triple.LibAdv(A, Inline1(G))).main() @ &m : res]
 =
  Pr[Game(Triple.LibAdv(A, Factor1_Lib(Double.PRG_real(G)))).main() @ &m : res].
proof.
byequiv => //.
proc; inline.
sim (: ={glob G}).
by proc; inline; sim.
qed.

(* Inline the random PRG Double Extend game. *)
local lemma Step3 &m:
  Pr[Game(Triple.LibAdv(A, Factor1_Lib(Double.PRG_rand(G)))).main() @ &m : res]
 =
  Pr[Game(Triple.LibAdv(A, Inline2(G))).main() @ &m : res].
proof.
byequiv => //.
proc; inline.
sim (: ={glob G}).
proc; inline.
by sim.
qed.

(* Show that halfing the sampling of 2 * lambda length bitstring can be replaced by two separate samplings. *)
local lemma Step4 &m:
  Pr[Game(Triple.LibAdv(A, Inline2(G))).main() @ &m : res]
 =
  Pr[Game(Triple.LibAdv(A, Split(G))).main() @ &m : res].
proof.
byequiv => //.
proc; inline.
sim (: ={glob G}).
proc; inline.
proc rewrite {1} ^r<$ split_dbits_2lam.
outline {1} 1 ~ DMapProg2.S.sample.
rewrite equiv [{1} 1 DMapProg2.sample].
inline.
cfold {1} ^d0<-; cfold {1} ^f<-.
outline {1} 1 ~ ProdProg11.S.sample. 
rewrite equiv [{1} 1 ProdProg11.sample_sample2].
inline.
sim.
auto => /> a _ b _.
by rewrite half_concat11.
qed.

(* Factor out the real PRG Double Extend game. *)
local lemma Step5 &m:
  Pr[Game(Triple.LibAdv(A, Split(G))).main() @ &m : res]
 =
  Pr[Game(Triple.LibAdv(A, Factor2_Lib(Double.PRG_real(G)))).main() @ &m : res].
proof.
byequiv => //.
proc; inline.
sim (: ={glob G}).
by proc; inline; sim.
qed.

(* Inline the random PRG Double Extend game. *)
local lemma Step6 &m:
  Pr[Game(Triple.LibAdv(A, Factor2_Lib(Double.PRG_rand(G)))).main() @ &m : res]
 =
  Pr[Game(Triple.LibAdv(A, Inline3(G))).main() @ &m : res].
proof.
byequiv (: ={glob A, glob G} ==> ={res}) => //.
proc; inline.
sim (: ={glob G}).
by proc; inline; sim.
qed.

(* Show equivalence to the random PRG Triple Extend game. *)
local lemma Step7 &m:
  Pr[Game(Triple.LibAdv(A, Inline3(G))).main() @ &m : res]
 =
  Pr[Game(Triple.LibAdv(A, Triple.PRG_rand(H(G)))).main() @ &m : res].
proof.
byequiv (: ={glob A, glob G} ==> ={res}) => //.
proc; inline.
sim (: ={glob G}).
proc; inline.
proc rewrite {2} ^t<$ split_dbits_3lam.
outline {2} 1 ~ DMapProg3.S.sample.
rewrite equiv [{2} 1 DMapProg3.sample].
inline.
cfold {2} ^d<-; cfold {2} ^f<-.
outline {2} 1 ~ ProdProg12.S.sample. 
rewrite equiv [{2} 1 ProdProg12.sample_sample2].
inline.
sim.
auto => /> a _ b _.
congr. 
by rewrite concat11_half.
qed.

lemma Security &m:
  `| Pr[Game(Triple.LibAdv(A, Triple.PRG_real(H(G)))).main() @ &m : res]
   - Pr[Game(Triple.LibAdv(A, Triple.PRG_rand(H(G)))).main() @ &m : res] |
 <= 
  `| Pr[Game(Double.LibAdv(Factor1_Adv(A), Double.PRG_real(G))).main() @ &m : res]
   - Pr[Game(Double.LibAdv(Factor1_Adv(A), Double.PRG_rand(G))).main() @ &m : res] |
  + 
  `| Pr[Game(Double.LibAdv(Factor2_Adv(A), Double.PRG_real(G))).main() @ &m : res]
   - Pr[Game(Double.LibAdv(Factor2_Adv(A), Double.PRG_rand(G))).main() @ &m : res] |.
proof.
rewrite Step1 Step2.
rewrite Factor1_real.
apply (asmp Pr[Game(Triple.LibAdv(A, Factor1_Lib(Double.PRG_rand(G)))).main() @ &m : res]).
rewrite -{1}Factor1_rand.
rewrite Step3 Step4 Step5.
rewrite Factor2_real.
apply (asmp Pr[Game(Triple.LibAdv(A, Factor2_Lib(Double.PRG_rand(G)))).main() @ &m : res]).
rewrite -{1}Factor2_rand.
rewrite Step6 Step7.
smt().
qed.

end section.

print Security.

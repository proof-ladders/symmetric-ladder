(* ------------------------------------------------------- *)
(* 
  Constructing a PRF with double the key size of another
  PRF.
*)
(* ------------------------------------------------------- *)

require import Libraries.
require import AllCore List FMap FSet.
require import Distr DList DMap Dexcepted.
require (*  *) PRF BitStrings Sampling.
(*   *) import StdOrder.IntOrder.

(* Maximum calls that an adversary makes to the `query` oracle *)
op max_queries : { int | 0 <= max_queries } as ge0_mq.

(* Initial input length of the bit strings *)
op lambda : { int | 0 < lambda } as gt0_lam.

(* Bitstrings of length lambda, 2 * lambda, 3 * lambda. *)
clone import BitStrings as BS with
  op lambda <- lambda,
  lemma gt0_lam <- gt0_lam
proof *.

(* This lemma is key for the proof of Step 12 *)
lemma dbits_lam_excepted_ll (f : (bits_lam, bits_lam) fmap) (s : bits_lam fset) (x : bits_lam) : x \notin f => card s = fsize f => is_lossless (dbits_lam \ (mem s)).
proof.
move => x_nin_f card_s_f.
rewrite /is_lossless weight_dexcepted.
apply iftrue.
rewrite Bits_lam.DWord.dunifin_ll.
rewrite Bits_lam.DWord.dunifinE.
rewrite -(eq_count (mem (elems s))).
+ by move => ?; rewrite memE.
rewrite Bits_lam.count_mem.
+ exact uniq_elems.
rewrite cardE in card_s_f.
rewrite card_s_f.
rewrite Bits_lam.word_card /=.
case (1%r = (fsize f)%r / (2 ^ lambda)%r) => //.
have exp2lam_ne0: (2 ^ lambda)%r <> 0%r.
+ rewrite eq_fromint -lt0n.
  + exact expr_ge0.
  exact expr_gt0.
have : fsize f < 2 ^ lambda. 
+ apply (ltr_le_trans (fsize f.[x <- witness])).
  - rewrite fsize_set x_nin_f b2i1 /=.
    smt(ge0_fsize).
  rewrite /fsize fdomE.
  rewrite -Bits_lam.word_card Bits_lam.card_size_to_seq.
  rewrite uniq_card_oflist.
  - exact Finite.uniq_to_seq.
  apply Finite.sub_size_to_seq.
  - done.
  exact Bits_lam.is_finite.
rewrite -(RField.divrr (2 ^ lambda)%r) //.
rewrite RField.eqr_div //.
smt(). (* FIXME: unstable *)
qed.

(* ------------------------------------------------------- *)
(* The construction *)
(* ------------------------------------------------------- *)

clone PRF as Single with
  type key <- bits_lam,
  type t_in <- bits_lam,
  type t_out <- bits_lam,
  op d_key <- dbits_lam,
  op d_out <- dbits_lam
proof*.

clone PRF as Double with
  type key <- bits_2lam,
  type t_in <- bits_lam,
  type t_out <- bits_lam,
  op d_key <- dbits_2lam,
  op d_out <- dbits_lam
proof*.

clone Sampling as BD with
  op max_samples <- max_queries,
  type t <- bits_lam,
  op dt <- dbits_lam
proof*.
realize ge0_ms by exact ge0_mq.
realize dt_ll by exact Bits_lam.DWord.dunifin_ll.

module H (F : Single.F) : Double.F = {
  proc run(k, x) = {
    var k1, k2, y, r : bits_lam;
    
    (k1, k2) <- half k;
    y <@ F.run(k1, x);
    r <@ F.run(k2, y);
    return r;
  }
}.

section Security.
(* ------------------------------------------------------- *)
(* Intermediate games for the proof of security *)
(* ------------------------------------------------------- *)

(* Identifies the reduction to Single.API from a Double.Lib *)
module type Factor_PRF (L : Single.API) = {
  include Double.Lib
}.

(* Identifies the reduction to BD.API from a Double.Lib *)
module type Factor_BDAY (L : BD.API) = {
  include Double.Lib
}.

module Inline1 (F : Single.F) : Double.Lib = Double.PRF_real(H(F)) with {
  proc query [
    var k1, k2, y : bits_lam
    ^t<@ ~ {
      (k1, k2) <- half k;
      y <@ F.run(k1, x);
      t <@ F.run(k2, y);
    }
  ]
}.

module Split1 (F : Single.F) : Double.Lib = Inline1(F) with {
  var k1 : bits_lam
  var k2 : bits_lam
  
  proc init [
    ^k<$ + {(k1, k2) <- half k;}
  ]
  
  proc query [
    [^(k1)<- .. ^t<@] ~ {y <@ F.run(Split1.k1, x); t <@ F.run(Split1.k2, y);}
  ]
}.

module Split2 (F : Single.F) : Double.Lib = Split1(F) with {
  - var k
  
  proc init [
    [^ <$ .. ^()<-] ~ {k1 <$ dbits_lam; k2 <$ dbits_lam;}
  ]
}.

module Caching (F : Single.F) : Double.Lib = Split2(F) with {
  var l : (bits_lam, bits_lam) fmap

  proc init [
    ^k2<$ + { l <- empty; }
  ]

  proc query [
    [^y<@ .. ^l<-] + ^ (l.[x] = None)
    ^t<@ + {l.[x] <- t;}
  ] res ~ (oget l.[x])
}.

module (Factor1 (F : Single.F) : Factor_PRF) (L : Single.API) = Caching(F) with {
  - var k1
  
  proc init [
    ^ <$ -
  ]

  proc query [
    ^if.^y<@ ~ {y <@ L.query(x); }
  ]
}.

module Inline2 (F : Single.F) : Double.Lib = Factor1(F, Single.PRF_rand(F)) with {
  var l1 : (bits_lam, bits_lam) fmap

  proc init [
    -1 + { l1 <- empty; }
  ]

  proc query [
    ^if.^y<@ ~ {
      if (l1.[x] = None) {
        t <$ dbits_lam;
        l1.[x] <- t;
      }
      y <- oget l1.[x];
    }
  ]
}.

module (Factor2 (F : Single.F) : Factor_PRF) (L : Single.API) = Inline2(F) with {
  - var k2

  proc init [
    ^ <$ -
  ]

  proc query [
    ^if.^t<@ ~ {t <@ L.query(y); }
  ]
}.

module Inline3 (F : Single.F) : Double.Lib = Factor2(F, Single.PRF_rand(F)) with {
  var l2 : (bits_lam, bits_lam) fmap

  proc init [
    -1 + { l2 <- empty; }
  ]

  proc query [
    ^if.^t<@ ~ {
      if (l2.[y] = None) {
        t <$ dbits_lam;
        l2.[y] <- t;
      }
      t <- oget l2.[y];
    }
  ]
}.

module Simplify1 (F : Single.F) : Double.Lib = Inline3(F) with {
  - var l1

  proc init [
    ^ <-{2} -
  ]

  proc query [
    ^if.^if -
    ^if.^y<- ~ {y <$ dbits_lam;}
  ]
}.

module (Factor3 (F : Single.F) : Factor_BDAY) (L : BD.API) = Simplify1(F) with {
  proc query [
    ^if.^y<$ ~ {y <@ L.sample(); }
  ]
}.

module Inline4 (F : Single.F) : Double.Lib = Factor3(F, BD.BDAY_uniq) with {
  var ys : bits_lam fset

  proc init [
    -1 + { ys <- fset0; }
  ]

  proc query [
    ^if.^y<@ ~ {
      y <$ dbits_lam \ (mem ys);
      ys <- ys `|` fset1 y;
    }
  ]
}.

(* ------------------------------------------------------- *)
(* The PRF we use to build our construction *)
(* ------------------------------------------------------- *)

(* It can only access it's own memory *)
declare module F <: Single.F {
  -Inline1, -Caching, -Split1, -Split2, 
  -Factor1, 
  -Inline2, 
  -Factor2, 
  -Simplify1, -Inline3,
  -Factor3, 
  -Inline4, 

  -Double.PRF_real, -Double.PRF_rand, -Double.Count,
  -Single.PRF_real, -Single.PRF_rand,
  -BD.BDAY_rand, -BD.BDAY_uniq, -BD.Count
}.

(* We must have that the PRF can be represented by a stateless operator. *)
(* This is needed to allow for caching. *)
op F : bits_lam * bits_lam -> bits_lam.
declare axiom F_sem g v: phoare[F.run: glob F = g /\ arg = v ==> glob F = g /\ res = F v] = 1%r.

(* ------------------------------------------------------- *)
(* The Adversary *)
(* ------------------------------------------------------- *)

(* It can only access it's own memory *)
declare module A <: Double.Adv {
  -F,

  -Inline1, -Caching, -Split1, -Split2, 
  -Factor1, 
  -Inline2, 
  -Factor2, 
  -Simplify1, -Inline3,
  -Factor3, 
  -Inline4, 

  -Double.PRF_real, -Double.PRF_rand, -Double.Count,
  -Single.PRF_real, -Single.PRF_rand,
  -BD.BDAY_rand, -BD.BDAY_uniq, -BD.Count
}.

(* It cannot make more than `max_queries` number of queries to `query` *)
declare axiom A_bounded: forall (L <: Double.Lib{-A, -Double.Count}),
  hoare[Game(Double.LibAdv(A, Double.Count(L))).main: true ==> Double.Count.cq <= max_queries].

(* ------------------------------------------------------- *)
(* Properly build factored libraries/adversaries *)
(* ------------------------------------------------------- *)
module (Factor_PRF_Adv (F : Factor_PRF) (A : Double.Adv) : Single.Adv) (L : Single.API) = {
  include CompBase(A(F(L)), F(L))
  include A(F(L))[-init, fin]
}.

local module Factor_PRF_Lib (F : Factor_PRF) (L : Single.Lib) = {
  include CompBase(F(L), L)
  include F(L)[-init, fin]
}.

module (Factor_BDAY_Adv (F : Factor_BDAY) (A : Double.Adv) : BD.Adv) (L : BD.API) = {
  include CompBase(A(F(L)), F(L))
  include A(F(L))[-init, fin]
}.

local module Factor_BDAY_Lib (F : Factor_BDAY) (L : BD.Lib) = {
  include CompBase(F(L), L)
  include F(L)[-init, fin]
}.

module Factor1_Adv = Factor_PRF_Adv(Factor1(F), A).
module Factor2_Adv = Factor_PRF_Adv(Factor2(F), A).
module Factor3_Adv = Factor_BDAY_Adv(Factor3(F), A).
local module Factor1_Lib (L : Single.Lib) = Factor_PRF_Lib(Factor1(F), L).
local module Factor2_Lib (L : Single.Lib) = Factor_PRF_Lib(Factor2(F), L).
local module Factor3_Lib (L : BD.Lib) = Factor_BDAY_Lib(Factor3(F), L).

local lemma Factor1_equiv_real:
  equiv[Game(Double.LibAdv(A, Factor1_Lib(Single.PRF_real(F)))).main ~ Game(Single.LibAdv(Factor1_Adv, Single.PRF_real(F))).main:
  ={glob A, glob F} ==> ={res, glob A, glob F}].
proof. by proc; inline; sim. qed.

local lemma Factor1_pr_real &m: 
  Pr[Game(Double.LibAdv(A, Factor1_Lib(Single.PRF_real(F)))).main() @ &m : res]
 =
  Pr[Game(Single.LibAdv(Factor1_Adv, Single.PRF_real(F))).main() @ &m : res].
proof. by byequiv Factor1_equiv_real. qed.

local lemma Factor1_equiv_rand:
  equiv[Game(Double.LibAdv(A, Factor1_Lib(Single.PRF_rand(F)))).main ~ Game(Single.LibAdv(Factor1_Adv, Single.PRF_rand(F))).main:
  ={glob A, glob F} ==> ={res, glob A, glob F}].
proof. by proc; inline; sim. qed.

local lemma Factor1_pr_rand &m: 
  Pr[Game(Double.LibAdv(A, Factor1_Lib(Single.PRF_rand(F)))).main() @ &m : res]
 =
  Pr[Game(Single.LibAdv(Factor1_Adv, Single.PRF_rand(F))).main() @ &m : res].
proof. by byequiv Factor1_equiv_rand. qed.

local lemma Factor2_equiv_real:
  equiv[Game(Double.LibAdv(A, Factor2_Lib(Single.PRF_real(F)))).main ~ Game(Single.LibAdv(Factor2_Adv, Single.PRF_real(F))).main:
  ={glob A, glob F} ==> ={res, glob A, glob F}].
proof. by proc; inline; sim. qed.

local lemma Factor2_pr_real &m: 
  Pr[Game(Double.LibAdv(A, Factor2_Lib(Single.PRF_real(F)))).main() @ &m : res]
 =
  Pr[Game(Single.LibAdv(Factor2_Adv, Single.PRF_real(F))).main() @ &m : res].
proof. by byequiv Factor2_equiv_real. qed.

local lemma Factor2_equiv_rand:
  equiv[Game(Double.LibAdv(A, Factor2_Lib(Single.PRF_rand(F)))).main ~ Game(Single.LibAdv(Factor2_Adv, Single.PRF_rand(F))).main:
  ={glob A, glob F} ==> ={res, glob A, glob F}].
proof. by proc; inline; sim. qed.

local lemma Factor2_pr_rand &m: 
  Pr[Game(Double.LibAdv(A, Factor2_Lib(Single.PRF_rand(F)))).main() @ &m : res]
 =
  Pr[Game(Single.LibAdv(Factor2_Adv, Single.PRF_rand(F))).main() @ &m : res].
proof. by byequiv Factor2_equiv_rand. qed.

local lemma Factor3_equiv (L <: BD.Lib{-Factor3_Lib, -Factor3_Adv, -A}):
  equiv[Game(Double.LibAdv(A, Factor3_Lib(L))).main ~
        Game(BD.LibAdv(Factor3_Adv, L)).main: ={glob A, glob L} ==> ={res, glob A, glob L}].
proof. by proc; inline; sim. qed.

local lemma Factor3_equiv' (L <: BD.Lib{-Factor3_Lib, -Factor3_Adv, -A}):
  equiv[Game(BD.LibAdv(Factor3_Adv, L)).main ~ Game(Double.LibAdv(A, Factor3_Lib(L))).main: ={glob A, glob L} ==> ={res, glob A, glob L}].
proof. by symmetry; conseq (Factor3_equiv L). qed.

local lemma Factor3_pr &m (L <: BD.Lib{-Factor3_Lib, -Factor3_Adv, -A}):
  Pr[Game(Double.LibAdv(A, Factor3_Lib(L))).main() @ &m : res]
 =
  Pr[Game(BD.LibAdv(Factor3_Adv, L)).main() @ &m : res].
proof. by byequiv (Factor3_equiv L). qed.

(* ------------------------------------------------------- *)
(* Extra program equivalences for use in the proof *)
(* ------------------------------------------------------- *)
local clone DProd.ProdSampling as ProdProg with
  type t1 <- bits_lam,
  type t2 <- bits_lam.

local clone DMapSampling as DMapProg with
  type t1 <- bits_lam * bits_lam,
  type t2 <- bits_2lam.

(* ------------------------------------------------------- *)
(* Proof Steps *)
(* ------------------------------------------------------- *)

(* Inline the real PRF with double length key. *)
local lemma Step1 &m:
  Pr[Game(Double.LibAdv(A, Double.PRF_real(H(F)))).main() @ &m : res]
 =
  Pr[Game(Double.LibAdv(A, Inline1(F))).main() @ &m : res].
proof.
byequiv => //.
proc; inline.
sim (: ={glob F} /\ ={k}(Double.PRF_real, Inline1)).
by proc; inline; sim.
qed.

(* Half the PRF key initially, rather than on every query. *)
local equiv Step2_equiv: Inline1(F).query ~ Split1(F).query: 
  ={arg, glob F} /\ ={k}(Inline1, Split1) /\ (half Split1.k = (Split1.k1, Split1.k2)){2}
 ==>
  ={res, glob F} /\ ={k}(Inline1, Split1) /\ (half Split1.k = (Split1.k1, Split1.k2)){2}.
proof.
proc.
do 2! call (: true).
by auto => />.
qed.

local lemma Step2 &m:
  Pr[Game(Double.LibAdv(A, Inline1(F))).main() @ &m : res]
 =
  Pr[Game(Double.LibAdv(A, Split1(F))).main() @ &m : res].
proof.
byequiv => //.
proc; inline.
do 3! (call (:
  ={glob F} /\ ={k}(Inline1, Split1) /\ (half Split1.k = (Split1.k1, Split1.k2)){2}
); first by conseq Step2_equiv).
by auto.
qed.

(* Sample each half of the PRF key separately. *)
local lemma Step3 &m:
  Pr[Game(Double.LibAdv(A, Split1(F))).main() @ &m : res]
 =
  Pr[Game(Double.LibAdv(A, Split2(F))).main() @ &m : res].
proof.
byequiv => //.
proc; inline.
proc rewrite {1} ^Split1.k<$ split_dbits_2lam.
outline {1} 1 ~ DMapProg.S.sample.
rewrite equiv [{1} 1 DMapProg.sample].
inline.
cfold {1} ^d<-; cfold {1} ^f<-.
outline {1} 1 ~ ProdProg.S.sample. 
rewrite equiv [{1} 1 ProdProg.sample_sample2].
inline.
sim.
auto => /> a _ b _.
by rewrite half_concat11.
qed.

(* Cache the PRF queries. *)
local equiv Step4_equiv: Split2(F).query ~ Caching(F).query: 
  ={arg, glob F} /\ ={k1, k2}(Split2, Caching)
  /\ (forall x, x \in Caching.l => Some (F (Caching.k2, (F (Caching.k1, x)))) = Caching.l.[x]){2}
==>
  ={res, glob F} /\ ={k1, k2}(Split2, Caching)
  /\ (forall x, x \in Caching.l => Some (F (Caching.k2, (F (Caching.k1, x)))) = Caching.l.[x]){2}.
proof.
proc.
seq 1 0 : ((y = F (Split2.k1, x)){1} /\ #pre).
- exlim (glob F){1}, Split2.k1{1}, x{1} => gF k1' x'.
  call {1} (F_sem gF (k1', x')).
  by auto.
seq 1 0 : ((t = F (Split2.k2, y)){1} /\ #pre).
- exlim (glob F){1}, Split2.k2{1}, y{1} => gF k2' y'.
  call {1} (F_sem gF (k2', y')).
  by auto.
if {2}; first last.
- auto => />.
  move => &2 inv.
  by rewrite -domE => /inv <-.
wp.
seq 0 1 : ((y = F (Caching.k1, x)){2} /\ #pre).
- exlim (glob F){2}, Caching.k1{2}, x{2} => gF k1' x'.
  call {2} (F_sem gF (k1', x')).
  by auto.
seq 0 1 : ((t = F (Caching.k2, y)){2} /\ #pre).
- exlim (glob F){2}, Caching.k2{2}, y{2} => gF k2' y'.
  call {2} (F_sem gF (k2', y')).
  by auto.
auto => />.
move => &2 inv cache_none.
rewrite get_set_sameE /=.
move => x.
rewrite mem_set.
case; first last.
- move => <<-.
  by rewrite get_set_sameE.
case (x = x{!2}).
- move => ->.
  by rewrite domE.
move => x_neq /inv ->.
by rewrite get_set_neqE.
qed.

local lemma Step4 &m:
  Pr[Game(Double.LibAdv(A, Split2(F))).main() @ &m : res]
 =
  Pr[Game(Double.LibAdv(A, Caching(F))).main() @ &m : res].
proof.
byequiv => //.
proc; inline.
do 3! (call (:
  ={glob F} /\ ={k1, k2}(Split2, Caching)
  /\ (forall x, x \in Caching.l => Some (F (Caching.k2, (F (Caching.k1, x)))) = Caching.l.[x]){2}
); first by conseq Step4_equiv).
auto => />.
move => k1 _ k2 _ x.
by rewrite mem_empty.
qed.

(* Factor out the first PRF query as the real PRF game. *)
local lemma Step5 &m:
  Pr[Game(Double.LibAdv(A, Caching(F))).main() @ &m : res]
 =
  Pr[Game(Double.LibAdv(A, Factor1_Lib(Single.PRF_real(F)))).main() @ &m : res].
proof.
byequiv => //.
proc; inline.
sim (: ={glob F} /\ ={k2, l}(Caching, Factor1) /\ Caching.k1{1} = Single.PRF_real.k{2}).
by proc; inline; sim.
qed.

(* Inline the random PRF game. *)
local lemma Step6 &m:
  Pr[Game(Double.LibAdv(A, Factor1_Lib(Single.PRF_rand(F)))).main() @ &m : res]
 =
  Pr[Game(Double.LibAdv(A, Inline2(F))).main() @ &m : res].
proof.
byequiv => //.
proc; inline.
swap {1} ^Single.PRF_rand.l<- @ ^ <@. (* Line things up for sim *)
sim (: ={glob F} /\ ={k2, l}(Factor1, Inline2) /\ Single.PRF_rand.l{1} = Inline2.l1{2}).
by proc; inline; sim.
qed.

(* Factor out the second PRF query as the real PRF game. *)
local lemma Step7 &m:
  Pr[Game(Double.LibAdv(A, Inline2(F))).main() @ &m : res]
 =
  Pr[Game(Double.LibAdv(A, Factor2_Lib(Single.PRF_real(F)))).main() @ &m : res].
proof.
byequiv => //.
proc; inline.
sim (: ={glob F} /\ ={l, l1}(Inline2, Factor2) /\ Inline2.k2{1} = Single.PRF_real.k{2}).
by proc; inline; sim.
qed.

(* Inline the random PRF game. *)
local lemma Step8 &m:
  Pr[Game(Double.LibAdv(A, Factor2_Lib(Single.PRF_rand(F)))).main() @ &m : res]
 =
  Pr[Game(Double.LibAdv(A, Inline3(F))).main() @ &m : res].
proof.
byequiv (: ={glob A, glob F} ==> _) => //.
proc; inline.
swap {1} ^Single.PRF_rand.l<- @ ^ <@. (* Line things up for sim *)
sim (: ={glob F} /\ ={l, l1}(Factor2, Inline3) /\ Single.PRF_rand.l{1} = Inline3.l2{2}).
by proc; inline; sim.
qed.

(* Remove the unnecessary query log *)
local equiv Step9_equiv: Inline3(F).query ~ Simplify1(F).query:
   ={arg, glob F} /\ ={l, l2}(Inline3, Simplify1)
   /\ (forall x, x \in Inline3.l <=> x \in Inline3.l1){1}
 ==>
   ={res, glob F} /\ ={l, l2}(Inline3, Simplify1) 
   /\ (forall x, x \in Inline3.l <=> x \in Inline3.l1){1}.
proof.
proc.
if => //.
rcondt {1} ^if.
- auto => />.
  move => &hr inv.
  by rewrite -2!domNE (inv x{m}).
seq 1 1 : (t{1} = y{2} /\ #pre); first by auto.
sp; wp.
conseq (: _ ==> ={l2}(Inline3, Simplify1)).
- move => />.
  move => &2 l1 inv lx_none l2.
  rewrite !get_set_sameE /=.
  move => x.
  by rewrite 2!mem_set (inv x).
sim.  
move => />.
move => &2 l1 inv lx_none.
by rewrite get_set_sameE.
qed.

local lemma Step9 &m:
  Pr[Game(Double.LibAdv(A, Inline3(F))).main() @ &m : res]
 =
  Pr[Game(Double.LibAdv(A, Simplify1(F))).main() @ &m : res].
proof.
byequiv (: ={glob A, glob F} ==> _) => //.
proc; inline.
do 3! (call (:
   ={glob F} /\ ={l, l2}(Inline3, Simplify1) 
   /\ (forall x, x \in Inline3.l <=> x \in Inline3.l1){1}
); first by conseq Step9_equiv).
by auto.
qed.

(* Factor out the sample of y as the real BDAY bound game. *)
local lemma Step10 &m:
  Pr[Game(Double.LibAdv(A, Simplify1(F))).main() @ &m : res]
 =
  Pr[Game(Double.LibAdv(A, Factor3_Lib(BD.BDAY_rand))).main() @ &m : res].
proof.
byequiv (: ={glob A, glob F} ==> _) => //.
proc; inline.
sim (: ={glob F} /\ ={l, l2}(Simplify1, Factor3)).
by proc; inline; sim.
qed.

(* Inline the sample from the uniq BDAY bound game. *)
local lemma Step11 &m:
  Pr[Game(Double.LibAdv(A, Factor3_Lib(BD.BDAY_uniq))).main() @ &m : res]
 =
  Pr[Game(Double.LibAdv(A, Inline4(F))).main() @ &m : res].
proof.
byequiv (: ={glob A, glob F} ==> _) => //.
proc; inline.
swap {2} ^Inline4.ys<- @ 1.
sim (: ={glob F} /\ ={l, l2}(Factor3, Inline4) /\ BD.BDAY_uniq.s{1} = Inline4.ys{2}).
by proc; inline; sim.
qed.

(* Show that l2 is no longer needed. *)
local equiv Step12_equiv: Inline4(F).query ~ Double.PRF_rand(H(F)).query:
  ={arg, glob F} /\ ={l}(Inline4, Double.PRF_rand)
  /\ (forall y, y \in Inline4.ys <=> y \in Inline4.l2){1}
  /\ (card Inline4.ys = fsize Inline4.l){1}
 ==>
  ={res, glob F} /\ ={l}(Inline4, Double.PRF_rand)
  /\ (forall y, y \in Inline4.ys <=> y \in Inline4.l2){1}
  /\ (card Inline4.ys = fsize Inline4.l){1}.
proof.
proc; inline.
if => //.
rcondt {1} ^if.
- auto => />.
  move => &hr inv_ys_l2 inv_ys_l lx_none y.
  by rewrite supp_dexcepted inv_ys_l2 domNE.
auto => />.
move => &1 &2 inv_ys_l2 inv_ys_l /domNE x_nin_l.
split.  
- exact (dbits_lam_excepted_ll Double.PRF_rand.l{2} Inline4.ys{1} x{2}).
move => _ y.
rewrite supp_dexcepted.
move => [_ ^ y_nin_ys].
rewrite inv_ys_l2 => y_nin_l2. 
move => r _.
rewrite !get_set_sameE /=.
split.
- move => z.
  by rewrite mem_set in_fsetU1 (inv_ys_l2 z).
by rewrite fcardU1 fsize_set x_nin_l y_nin_ys inv_ys_l.
qed.

local lemma Step12 &m:
  Pr[Game(Double.LibAdv(A, Inline4(F))).main() @ &m : res]
 =
  Pr[Game(Double.LibAdv(A, Double.PRF_rand(H(F)))).main() @ &m : res].
proof.
byequiv (: ={glob A, glob F} ==> _) => //.
proc; inline.
do 3! (call (:
   ={glob F} /\ ={l}(Inline4, Double.PRF_rand)
  /\ (forall y, y \in Inline4.ys <=> y \in Inline4.l2){1}
  /\ (card Inline4.ys = fsize Inline4.l){1}
); first by conseq Step12_equiv).
auto => />.
split.
+ move => y.
  by rewrite in_fset0 mem_empty.
by rewrite fcards0 fsize_empty.
qed.

section Counting.

declare module L <: BD.Lib { +BD.BDAY_rand, +BD.BDAY_uniq, +BD.Bound, +BD.Bads}.

local hoare sample_le_query: Double.Count(Factor3_Lib(BD.Count(L))).query:
  BD.Count.cs <= Double.Count.cq
 ==>
  BD.Count.cs <= Double.Count.cq.
proof.
proc; inline.
sp; wp.
if.
+ sp; wp. 
  seq 1 : (#pre); 1: by call (: true).
  by sp; if; auto => /#.
by auto => /#.
qed.

lemma A_bounded_bday: 
  hoare[Game(BD.LibAdv(Factor3_Adv, BD.Count(L))).main: true ==> BD.Count.cs <= max_queries].
proof.
conseq (Factor3_equiv' (BD.Count(L))) (: _ ==> BD.Count.cs <= max_queries) => [/# | // |].
conseq (Double.Counting_equiv (Factor3_Lib((BD.Count(L)))) A) (: _ ==> BD.Count.cs <= max_queries) => [/# | // |].
conseq (: _ ==> BD.Count.cs <= Double.Count.cq) (A_bounded (Factor3_Lib(BD.Count(L)))) => [/# |].
proc; inline.
call (: true).
do 3! (call (: BD.Count.cs <= Double.Count.cq); 1: by conseq sample_le_query).
wp; call (: true).
by auto.
qed.

end section Counting.

lemma Security &m:
  `| Pr[Game(Double.LibAdv(A, Double.PRF_real(H(F)))).main() @ &m : res] 
  - Pr[Game(Double.LibAdv(A, Double.PRF_rand(H(F)))).main() @ &m : res] |
 <= 
  `| Pr[Game(Single.LibAdv(Factor1_Adv, Single.PRF_real(F))).main() @ &m : res] 
  - Pr[Game(Single.LibAdv(Factor1_Adv, Single.PRF_rand(F))).main() @ &m : res] |
  + `| Pr[Game(Single.LibAdv(Factor2_Adv, Single.PRF_real(F))).main() @ &m : res] 
  - Pr[Game(Single.LibAdv(Factor2_Adv, Single.PRF_rand(F))).main() @ &m : res] |
  + (max_queries * (max_queries - 1))%r / (2 ^ (lambda + 1))%r.
proof.
rewrite Step1 Step2 Step3 Step4 Step5.
rewrite Factor1_pr_real.
rewrite (asmp Pr[Game(Single.LibAdv(Factor1_Adv, Single.PRF_rand(F))).main() @ &m :res]).
rewrite -{1}Factor1_pr_rand.
rewrite Step6 Step7.
rewrite Factor2_pr_real.
rewrite (asmp Pr[Game(Single.LibAdv(Factor2_Adv, Single.PRF_rand(F))).main() @ &m :res]).
rewrite -{1}Factor2_pr_rand.
rewrite Step8 Step9 Step10.
rewrite (Factor3_pr &m BD.BDAY_rand).
rewrite (asmp Pr[Game(BD.LibAdv(Factor3_Adv, BD.BDAY_uniq)).main() @ &m :res]).
rewrite -{1}(Factor3_pr &m BD.BDAY_uniq).
rewrite Step11 Step12.
have := (BD.Security Factor3_Adv _ &m).
+ move => L.
  by conseq (A_bounded_bday L).
rewrite Bits_lam.DWord.dunifin1E Bits_lam.word_card.
smt(ge0_lam exprS).
qed.

end section Security.

print Security.

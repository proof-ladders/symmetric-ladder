# PRG Length Extension (``modular'' EasyCrypt)

This directory contains a proof of security for constructing a length-tripling
PRG from a length-doubling PRG. Doubling and tripling are modelled as tupling.

The relevant files:
- `PRG.eca` provides a generic definition of syntax and security for PRGs;
- `prg3.ec` provides the length extension construction and its proof of
  security.

The result only applies to length-doubling PRGs whose seed generation is
(perfectly) equivalent to sampling from the same ideal distribution each half
of the output simulates. In this specific proof, we choose to prove the result
by quantifying only over the seed generation distribution and the
length-doubling PRG's `query` algorithm (a sub-syntax we call a `SeededPRG`),
and relying on the security of the PRG whose seed generation samples from the
distribution, and whose `query` algorithm is the one quantified.

## Checking the proof

Using the latest release of EasyCrypt (available as branch `release`), the
following command will check the proof: `easycrypt prg3.ec`.
One can also check interactively using emacs and ProofGeneral. The security
lemma is found on line 171.

The output should contain:
- three modules:
  + PRG3r (the construction), and
  + R1, and R2 (the reductions); and
- the security statement.

The security statement should print something like:

```
lemma main_result:
  forall (P <: SeededPRG)
         (D <: PRG3.Distr { -P })
         &m,
       `|  Pr[PRG3.IND_real(PRG3r(PRG2r(P)), D).game() @ &m : res]
         - Pr[PRG3.IND_ideal(D).game() @ &m : res]    |
    <=   `|  Pr[PRG2.IND_real(PRG2r(P), R1(P, D)).game() @ &m : res]
           - Pr[PRG2.IND_ideal(R1(P, D)).game() @ &m : res] |
       + `|  Pr[PRG2.IND_real(PRG2r(P), R2(D)).game() @ &m : res]
           - Pr[PRG2.IND_ideal(R2(D)).game() @ &m : res] |.
```

This lemma states that for any length-doubling seeded PRG `P` (which we then
construct into a full PRG `PRG2r(P)`), the advantage of a distinguisher `D`
(disjoint in memory from `P`) distinguishing the construction applied to
`PRG2r(P)` from a truly random length-tripling generator is bounded by the sum
of the advantages of two reductions (`R1(P, D)` and `R2(D)`) distinguishing the
length-doubling PRG from a truly random length-doubling generator.

The complexity analysis for the reductions needs to be carried out by
inspection.

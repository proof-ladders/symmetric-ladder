# PRG Length Extension (``pure'' EasyCrypt)

This directory contains a proof of security for constructing a length tripling PRG from a length doubling PRG for bitstrings of length `lambda`.

The relevant files are:
- `prg.ec` provides the length extension construction and its proof of security.

## Checking the proof

Using the latest release of EasyCrypt (available as branch `release`), the following command will check the proof: `easycrypt prg.ec`.
One can also check interactively using ProofGeneral. The security lemma is found on line 187.

The output should contain:
- three modules:
  + PRG3r (the construction), and
  + R1, and R2 (the reductions); and
- the security statement.

The security statement should print something like:

```
lemma main_result:
  forall (P <: PRG2)
         (D <: Distr3 { -P })
         &m,
       `|  Pr[IND_3(PRG3r(P), D).game() @ &m : res]
         - Pr[IND_3(PRG3i, D).game() @ &m : res]    |
    <=   `|  Pr[IND_2(P, R1(P, D)).game() @ &m : res]
           - Pr[IND_2(PRG2i, R1(P, D)).game() @ &m : res] |
       + `|  Pr[IND_2(P, R2(D)).game() @ &m : res]
           - Pr[IND_2(PRG2i, R2(D)).game() @ &m : res] |.
```

This lemma states that for any length-doubling PRG `P`, the advantage of a
distinguisher `D` (disjoint in memory from `P`) distinguishing the construction
applied to `P` from a truly random length-tripling generator is bounded by the
sum of the advantages of two reductions (`R1(P, D)` and `R2(D)`) distinguishing
the length-doubling PRG from a truly random length-doubling generator.

The complexity analysis for the reduction needs to be carried out by inspection.


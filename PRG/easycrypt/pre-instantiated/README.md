# PRG Length Extension (``pure'' EasyCrypt)

This directory contains a proof of security for constructing a length tripling
PRG from a length doubling PRG. Doubling and tripling are modelled as tupling.

The relevant files are:
- `prg.ec` provides the length extension construction and its proof of security.

This proof file provides pre-instantiated definitions of length-doubling and
length-tripling PRGs with purely distributional seed generation, rather than
using a single definition of syntax and security for PRGs that is then
instantiated twice. This simplifies the proof slightly, at some cost in the
readability of the definitions.

A more idiomatic proof (relying on a local, but still general, definition of
PRG syntax and security; rather than on the EasyCrypt standard library) can be
found in a sibling folder.

## Checking the proof

Using the latest release of EasyCrypt (available as branch `release`), the
following command will check the proof: `easycrypt prg.ec`.
One can also check interactively using emacs and ProofGeneral. The security
lemma is found on line 187.

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

The complexity analysis for the reductions needs to be carried out by
inspection.


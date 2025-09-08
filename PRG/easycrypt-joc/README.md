# PRG Length Extension

This directory contains a proof of security for constructing a length tripling PRG from a length double PRG for bitstrings of length `lambda`.

The relevant files are:
- `easycrypt.project` used to include the files found in /commmon/easycrypt-joc
- `PRG.eca` provides the PRG library interface, and a few useful wrappers.
- `PRGTripleFromDouble.ec` provides the length extension construction and its proof of security.

## Checking the proof

Using the latest release of EasyCrypt (at present r2025.08), the following command will check the proof: `easycrypt PRGTripleFromDouble.ec`.
One can also check interactively using ProofGeneral. The security lemma is found on line 314.

The output should contain: three modules H (the construction), Factor1, and Factor2 the reductions; and the security statement.

The security statement should print something like:

```
lemma Security:
  forall (G <: Double.G {-Inline2, -Inline3, -Inline1, -Factor1, -Split, -Factor2})
         (A(L : Triple.API) <: Triple.Adv {-Inline2, -Inline3, -Inline1, -Factor1, -Split, -Factor2, -G})
         &m,
    `|Pr[Game(Triple.LibAdv(A, Triple.PRG_real(H(G)))).main() @ &m : res]
      - Pr[Game(Triple.LibAdv(A, Triple.PRG_rand(H(G)))).main() @ &m : res]|
    <=
    `|Pr[Game(Double.LibAdv(Factor_Adv(Factor1(G), A), Double.PRG_real(G))).main () @ &m : res]
      - Pr[Game(Double.LibAdv(Factor_Adv(Factor1(G), A), Double.PRG_rand(G))).main () @ &m : res]|
    + `|Pr[Game(Double.LibAdv(Factor_Adv(Factor2(G), A), Double.PRG_real(G))).main () @ &m : res]
        - Pr[Game(Double.LibAdv(Factor_Adv(Factor2(G), A), Double.PRG_rand(G))).main () @ &m : res]|.
```

Parsing through the wrappers needed for the Joy of Cryptography framework, this lemma states that the advantage of an adversary `A` distinguishing
the length tripling PRG game is bounded by the advantages of the two reductions against the length doubling PRG game.


# PRF Cascade

This directory contains a proof of security of a construction for doubling the key size of an existing PRF.

The relevant files are:
- `easycrypt.project` used to include the files found in /commmon/easycrypt-joc
- `Cache.eca` provides a library for delaying computation of a lossless procedure.
- `Birthday.eca` presents two descriptions of the Birthday bound game, and tightly bounds the probability of collision.
- `Sampling.eca` provides a library for applying Birthday bound style reasoning with a variety of bounds.
- `PRF.eca` provides the PRG library interface, and a few useful wrappers.
- `PRFCascade.ec` provides the cascade construction and the proof of its security.

## Checking the proof

Using the latest release of EasyCrypt (at present r2025.08), the following command will check the proof: `easycrypt PRFCascade.ec`.
One can also check interactively using ProofGeneral. The security lemma is found on line 727.

The output should contain: three modules H (the construction), Factor1, and Factor2 the reductions; and the security statement.

The security statement should print something like:

```
lemma Security:
  forall (F <: Single.F {...}), 
      (forall (g : (glob F)) (v : bits_lam * bits_lam), phoare[ F.run : (glob F) = g /\ arg = v ==> (glob F) = g /\ res = Top.F v] = 1%r) =>
    forall (A(L : Double.API) <: Double.Adv {...}),
      (forall (L <: Double.Lib{-Double.Count, -A}), hoare[ Game(Double.LibAdv(A, Double.Count(L))).main : true ==> Double.Count.cq <= max_queries]) =>
      forall &m,
        `|Pr[Game(Double.LibAdv(A, Double.PRF_real(H(F)))).main() @ &m : res] -
         - Pr[Game(Double.LibAdv(A, Double.PRF_rand(H(F)))).main() @ &m : res]|
      <=
        `|Pr[Game(Single.LibAdv(Factor_PRF_Adv(Factor1(F), A), Single.PRF_real(F))).main() @ &m : res]
	 - Pr[Game(Single.LibAdv(Factor_PRF_Adv(Factor1(F), A), Single.PRF_rand(F))).main() @ &m : res]|
      +
        `|Pr[Game(Single.LibAdv(Factor_PRF_Adv(Factor2(F), A), Single.PRF_real(F))).main() @ &m : res]
         - Pr[Game(Single.LibAdv(Factor_PRF_Adv(Factor2(F), A), Single.PRF_rand(F))).main() @ &m : res]|
      + (max_queries * (max_queries - 1))%r / (2 ^ (lambda + 1))%r.
```

Parsing through the wrappers needed for the Joy of Cryptography framework, this lemma states: for a stateless PRF `F`, the
the advantage of an adversary `A` that makes at most `max_queries` to the double key length PRF library, is bounded by the advantages of 
the two reductions against the single key length PRF library and the birthday bound of the number of queries.


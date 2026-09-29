# MAIS-O11: proof assembly and a separation obstruction

This is a Lean 4.19.0 / Std project. It does **not** solve either PA-bin part of MAIS-O11.

It checks a concrete binary-reference proof-suffix construction, its character bound, and the following numerical implication. If

`direct ≤ reflection + a * (Nat.log2 (reflection + 2) + 1)`

and a factor `1 + 1/q` separation holds, then

`reflection ≤ 8 * (q * a)^2 + 1`.

For exponentially hard direct proofs and polynomially bounded `a`, the requested fixed-factor separation is impossible at every sufficiently large index. `no_separation_after` gives an explicit threshold and exposes every growth and cost hypothesis.

The proof-suffix model has parameterized formulas, axioms, implication, and generalization. Its input prefix is an expanded formula history. Its serialization and line-reference character counts are concrete, but a full PA-bin parser and arithmetic `Bew` predicate are not implemented.

Run in this directory:

```bash
lake build
lake env lean Audit.lean
```

The audited dependencies are among `propext` and `Quot.sound`. There are no admitted proofs or user-declared axioms.

Read `RESEARCH-NOTE.md` for the complete mathematical argument, the finite Gödel obstruction, and the audit of alternative candidate families. The discussion of ordinary PA arithmetization in that note is not a completed Lean PA implementation.

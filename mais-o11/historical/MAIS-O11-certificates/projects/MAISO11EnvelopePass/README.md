MAIS-O11 envelope certificate — Lean 4.19.0, Std only

Run from this directory:

```bash
lake build
lake env lean Audit.lean
```

`Envelope.lean` proves that absence of a fixed-factor witness is equivalent to
sublinearity of the finite-budget maximum excess. It proves that this negative
condition implies `F(k,n) <= 2*k + C1*(n+1) + B`, and that failure of every joint
linear bound gives witnesses for every fixed integer factor.

`FiniteFiles.lean` enumerates finite-alphabet files of bounded length and derives
the finite-budget interface from an arbitrary decoder and the defining property
of minimum reflection length.

`Audit.lean` prints the main signatures and their axioms. `checked-output.txt`
records the successful clean verification. `RESEARCH-NOTE.md` explains the proof,
its application to the question, and its limits.

The decoder and finite-valued length functions are parameters. This project is
not a PA implementation and does not prove either the positive or the negative
alternative for actual PA-bin. It verifies the relationship between those
alternatives without assuming polynomial internalization.

Only Lean's standard logical axioms occur in the audited dependencies. The source
contains no admitted proofs, custom axioms, unsafe declarations, or native_decide.

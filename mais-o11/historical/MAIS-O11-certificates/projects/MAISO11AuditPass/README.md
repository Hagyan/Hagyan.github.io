# MAIS-O11: PA-bin continuation audit

This is a **checked audit and conditional upper-bound development**. It is
not a proof of either requested PA-bin result. No PA-bin checker, proof
predicate, or concrete instance of the quantitative interfaces is supplied.

The project uses **Lean 4.19.0**, `Std`, and the unchanged `FirstPass.lean`
from the earlier project. No Mathlib download is needed.

## Run

Open this folder in VS Code and run:

```sh
lake build
lake env lean -DwarningAsError=true Audit.lean
```

If `lake` is not on your terminal's path:

```sh
"$HOME/.elan/bin/lake" build
"$HOME/.elan/bin/lake" env lean -DwarningAsError=true Audit.lean
```

## What the new file proves

`AuditPass.lean` proves:

1. An explicit exponential-versus-polynomial inequality.
2. **The previous `SeparationHypotheses` imply that no polynomial Loeb
   overhead bound exists for that system.** Therefore that interface cannot
   be instantiated for PA-bin while the polynomial conjecture also holds.
3. The internal Loeb axiom from the previous logical interface and one
   explicitly stated propositional rule.
4. A construction of a direct certificate from a reflection certificate,
   a certificate noticing it, and an internal-Loeb-axiom certificate.
5. An exact cost bound for this construction, including both modus-ponens
   operations and the formula sizes they charge.
6. A uniform polynomial bound under the stated bounds on those primitives;
   a linear cost for noticing gives linear dependence on the supplied
   reflection-proof length.

The main theorem names are:

```lean
MAISO11.first_pass_excludes_polynomial_overhead
MAISO11.internal_lob_axiom
MAISO11.QuantitativeLobTools.uniform_budget
MAISO11.QuantitativeLobTools.linear_premise_bound
MAISO11.first_pass_and_polynomial_tools_incompatible
```

## Exactly what remains unproved

The fields of `QuantitativeLobTools` include actual certificate-producing
operations and bounds on their lengths. In particular, `notice_bound`
requires polynomial-size internal verification of reflection proofs in
the given object system. `lob_bound` requires polynomial-size proofs of
its internal Loeb instances. These are hypotheses; this project does not
prove them for PA-bin.

The result in item 2 is an incompatibility theorem. It does not prove that
the polynomial conjecture is true or false, and does not rule out the
smaller factor-plus-toll speedup requested in part 1.

`RESEARCH-NOTE.md` explains the mathematics, the failed transfer from the
guarded checker, the source evidence, and the remaining concrete obligations.

## Verification and assumptions

`Audit.lean` prints the interface and the theorem signatures before listing
their foundational axiom dependencies. The local run is recorded in
`checked-output.txt`.

There are no `sorry` placeholders, custom Lean axioms, or native-decision
shortcuts in the delivered Lean source. The foundational dependencies
printed by the checked theorems are either none or Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.

An axiom audit does **not** list hypotheses in theorem parameters. The
remaining arithmetic assumptions are visible in the printed structures.
All lengths are lengths assigned to object-system proof certificates;
none is the length of a Lean script.

## Files

- `FirstPass.lean`: unchanged earlier conditional formalization.
- `AuditPass.lean`: new mathematical results and proof-cost calculation.
- `Audit.lean`: theorem and assumption audit.
- `RESEARCH-NOTE.md`: human-readable account of the result and its limits.
- `checked-output.txt`: actual successful verification transcript.
- `lean-toolchain`, `lakefile.toml`: pinned, dependency-free build.
- `SHA256SUMS`: hashes of the delivered files.

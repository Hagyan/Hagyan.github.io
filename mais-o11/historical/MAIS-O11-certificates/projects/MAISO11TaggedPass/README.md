# MAIS-O11: connective-tag certificate

Requires **Lean 4.19.0**. Uses only Lean Core/Std; no Mathlib download.

From this directory:

```sh
lake build
lake env lean Audit.lean
```

If extracted into Downloads on a Mac:

```sh
cd ~/Downloads
unzip MAIS-O11-tagged-checker.zip
cd MAISO11TaggedPass
lake build
lake env lean Audit.lean
```

Do not reuse an existing directory with that name when extracting unless you
intend to update it. No global Lean configuration change is needed.

## What is verified

`TaggedSyntax.lean` contains actual inductive syntax and functions, not an
assumed PA model:

- Terms, formulas, capture-avoiding substitution with de Bruijn binders.
- Connective shapes, unary conjunction tags, and guard-index collection.
- Substitution invariance of guards; guard preservation for MP,
  generalization, and the universal-instantiation axiom.
- Empty guards for the conjunction-free core language.
- An executable Boolean guard checker on expanded traces, with a proof of
  agreement with its specification.
- Extraction of the target's guard; injectivity and truth of the tags.
- Identity of ordinary and guarded acceptance on already expanded traces,
  **assuming all guards hold**.

`TaggedBounds.lean` proves elementary numerical consequences:

- Exponentials exceed each fixed polynomial at arbitrarily large indices.
- Factor-two separation, including an arbitrary additive toll, follows from
  the stated exponential lower and polynomial upper bounds.
- Those bounds exclude polynomial Löb overhead for the family.
- The displayed lower bound for bridge proofs excludes polynomial bridges.

The elementary exponential lemma is reused from the previous audit pass;
the package is otherwise standalone.

## What is not verified

This is **not an end-to-end Lean proof of the mathematical PA construction**.
The ordinary checker on expanded traces, guard truth, the diagonal formula,
and the numerical proof-length bounds are explicit parameters where used.
The complete serialized PA checker, its arithmetization, diagonalization,
proof generators, and character counts still need formalization.

In particular, the `tag_nodes` theorem counts formula nodes. It is not a
PA-bin written-character theorem. The mathematical note explains why this
particular family has linear printed size, separately from the certificate.

The construction concerns a chosen guarded PA presentation. It does not
settle either requested question for the prescribed PA-bin verifier.

## Verification transcript

`checked-output.txt` records the successful build and axiom audit.
`Audit.lean` prints foundational dependencies. An empty or standard-only
dependency list does not erase hypotheses in a theorem's statement.

There are no admitted proofs, custom axiom declarations, or native decision
oracles in the two source modules. SHA256SUMS records the delivered bytes.

The full mathematical proof and scope audit are in `RESEARCH-NOTE.md`.

# MAIS-O11: conditional first pass

This project is pinned to **Lean 4.19.0** and uses only libraries bundled with
Lean. It requires no Mathlib checkout or third-party Lean packages.

## What has been checked

`FirstPass.lean` proves:

1. The abstract finite Goedel contradiction argument: given consistency and
   the two internal proof transformations in `FiniteDiagonal`, every proof
   of the nth designated sentence has length greater than n.
2. Loeb's rule from explicit propositional reasoning, the three
   Hilbert--Bernays--Loeb conditions, and a diagonal fixed point.
3. A linear proof translation transfers that lower bound to every direct
   proof in the source system.
4. Logarithmic upper bounds on reflection proofs and sentence size give an
   explicit increasing subsequence with factor-two separation, including an
   arbitrary nonnegative integer toll constant C1.
5. Shortest proofs exist for provable sentences with natural-valued lengths.
6. Distinct reflection sentences and finitely many short-proof conclusions
   imply that even the shortest reflection proofs tend to infinity.

The final theorem is:

```lean
MAISO11.SeparationHypotheses.conditional_main
```

If `H : SeparationHypotheses B S` is supplied, it proves for every C1 that
the explicitly defined indices `H.witnessIndex C1 i` are strictly increasing,
and there are shortest direct and reflection proofs p and r at every index
with

```text
2 * length(r) + C1 * (sentenceSize(P) + 1) < length(p).
```

It also proves that all reflection proofs on this subsequence eventually
exceed every fixed length bound. The strict inequality is stronger than the
requested weak inequality with delta = 1.

The scale is `logSize n = Nat.log2 n + 2`. For positive n this is exactly
one plus the usual binary digit length. At zero it equals 2. The witness
sequence is a closed formula built from the supplied constants, rather
than a proof-search computation.

## What remains a hypothesis

**No instance of `SeparationHypotheses` for PA or the proposed guarded
verifier has been constructed.** This certificate proves a conditional
theorem. It does not prove that its arithmetic hypotheses can all be met.

The fields of the three interfaces are printed by `Audit.lean`:

| Interface | Construction work still required |
| --- | --- |
| `FiniteDiagonal` | Actual arithmetic syntax and proof lengths; the finite diagonal family; consistency; the two internal proof transformations. |
| `LobConditions` | Verify the stated logical rules, derivability conditions, and diagonal fixed point for the actual arithmetic proof predicate. |
| `SeparationHypotheses` | Implement the proof translation and prove its linear bound; supply accepted reflection proofs and their bounds; prove size, distinctness, and finite-enumeration properties. |

In particular, the guard, self-referential verifier, and compressed-file
translation from the manuscript are not implemented here. Their consequences
are required by these interfaces. This project does not certify the whole
eleven-page construction, a result for the fixed PA_bin presentation, or
MAIS-O11(2).

Lengths refer to certificates in the hypothetical object proof systems.
They do not count characters in this Lean source, tactic invocations,
kernel reductions, or bytes in an `.olean` file. The first pass works with
the integer constant C1 that appears in character-counting bounds.

## Run the verification

If you used the standalone installer, it already ran these checks and
printed the location of a fresh project folder in Documents. To repeat
them, open that folder in VS Code, select **Terminal > New Terminal**, and run:

```sh
lake build
lake env lean -DwarningAsError=true Audit.lean
```

If your terminal cannot find `lake` but Lean was installed through the
standard Elan setup, use:

```sh
"$HOME/.elan/bin/lake" build
"$HOME/.elan/bin/lake" env lean -DwarningAsError=true Audit.lean
```

Elan reads `lean-toolchain` and selects the pinned version. If needed, it
downloads that version from the official Lean distribution. An existing
default Lean version is not changed by this project.

The installer uses a fresh directory for every run. It does not overwrite
an existing Lean project. If Elan itself is missing, the installer obtains
it from Lean's official installer and leaves shell startup files unchanged.

## Interpreting the audit

The tested dependency audit for `conditional_main` is:

```text
[propext, Classical.choice, Quot.sound]
```

These are Lean's standard foundational axioms. The abstract `lob_rule`
proof reports no axiom dependencies. There are no unfinished proofs,
custom `axiom` declarations, or native decision-procedure shortcuts in the
project. Warnings are treated as errors.

**The axiom audit is not a list of theorem hypotheses.** Hypotheses are
parameters to a conditional theorem and therefore need not appear in
`#print axioms`. Read the structures printed above the axiom audit to see
the remaining mathematical obligations.

`checked-output.txt` is the actual transcript from a successful Lean 4.19.0
run in the development environment. Running the code on your Mac performs
a fresh verification; it does not merely display that saved transcript.

## Files

- `FirstPass.lean`: the abstract definitions and proved theorems.
- `Audit.lean`: prints the interfaces, theorem type, and axiom dependencies.
- `lean-toolchain`: the pinned Lean release.
- `lakefile.toml`: the dependency-free Lake project configuration.
- `checked-output.txt`: the developer's successful verification transcript.
- `SHA256SUMS`: checksums of the source, configuration, and documentation.

The next substantive step is to implement the base proof syntax and actual
written-character length, then prove the finite diagonal interface for that
implementation. Producing a value of `SeparationHypotheses B S` is the
eventual obligation needed to apply this conditional certificate.

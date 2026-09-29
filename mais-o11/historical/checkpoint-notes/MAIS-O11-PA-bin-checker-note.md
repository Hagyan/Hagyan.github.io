# MAIS-O11: executable checker milestone

## Result

This checkpoint adds an executable checker for the emitted definition/axiom/MP fragment. Lean 4.19.0 verifies soundness, completeness with respect to the existing four-family axiom predicate, and acceptance of the previously constructed polynomial-length trace files. The new proofs are in `CompactChecker.lean`.

The three principal statements are:

1. `axiomCheck_iff f`: the Boolean axiom checker accepts precisely the formulas satisfying `IsAxiom f`.
2. `checkWhole_sound`: if checking an input string returns a formula `f`, then `Nonempty (Derivation f)` holds. This theorem applies to arbitrary inputs, not only generated examples.
3. `compiled_trace_checked g`: for every grammar `g : Grammar b n`, there exist a record count `k` and records `fs` with `k ≤ traceN n` such that the actual concatenated definition and record string is accepted, returns the intended expanded trace formula, and has length at most `fullCharacters b g.mass g.mass`.

The checker reconstructs its dictionary from the input definition records. It does not receive a separately trusted dictionary. The register count and record count are explicit external parameters, since this format has no header. An empty proof is rejected because it has no conclusion.

## The mathematical step: recovering instantiation witnesses

The universal-instantiation family has shape `(∀x A) → A[t/x]`, but its serialized axiom record does not specify `t`. Here `t` must be closed, as the current proof records are closed formulas.

The checker collects all term subexpressions of the proposed consequent, replacing every free variable of each collected term by zero. It adds zero as an extra candidate. It then substitutes each candidate into `A` and tests exact syntactic equality with the consequent.

Why is this complete? A closed substitution term that actually affects the formula occurs as a subterm of the result. Occurrences underneath additional quantifiers have shifted variable contexts, but the closed term contains no free variables, so erasing variables recovers the same term. If the term is absent from the candidate list, replacing it by zero cannot affect the formula.

Lean proves that last assertion through `term_subst_unchanged` and `formula_subst_unchanged`. These are structural induction arguments comparing two substitutions. If every substitution entry on which the substitutions differ erases to `t`, and `t` does not occur in the resulting candidate list, the two substituted expressions are equal. The quantifier step proves that this condition is preserved by lifting substitutions. Specializing to substitution of a closed term versus zero proves `instance_candidate`.

This handles both ordinary and vacuous instantiation. No witness annotations were added to the serialized proof format.

## Axiom and inference checks

The exact accepted axiom families are those already present in `CompactProof.IsAxiom`:

- Universal variable reflexivity: `∀x (x = x)`.
- Universal instantiation with a closed term.
- Contraposition: `(A → ¬B) → (B → ¬A)`.
- Conjunction introduction: `A → (B → (A ∧ B))`, using the existing abbreviation for conjunction.

Each MP record names two earlier lines. The checker tests that the second expands to the implication from the first to the proposed conclusion. `Records.check_iff` proves that the Boolean result is equivalent to the previous `Records.valid` proposition. The full checker composes this with the certified parser and returns the last expanded formula.

## Verification and audit

`lake build` verifies the checker theorem chain. `lake env lean CheckerDemo.lean` checks the quantified examples and runs eight executable acceptance/rejection tests. They cover nested instantiation, a valid full proof, incorrect MP, unjustified axiom labeling, incorrect record count, trailing garbage, an empty proof, and parsed definitions with referenced terms. The command-line checker also accepts `examples/reflexivity.pabin` and rejects `examples/invalid-mp.pabin`.

The printed axiom dependencies for `instance_candidate`, `axiomCheck_iff`, and `checkWhole_sound` are `[propext, Quot.sound]`. For `compiled_trace_checked`, they are `[propext, Classical.choice, Quot.sound]`, inherited from the earlier existence construction. The theorem proofs use no `sorry`, `admit`, custom axiom declarations, or `native_decide`. Executable test outcomes supplement the general kernel-checked theorems; they are not used as theorem assumptions.

## Scope and remaining problem

This is a checker for the exact emitted fragment. It does not recognize every PA axiom scheme or generalization record, and its completeness claim is relative to `IsAxiom` and `Records.valid`, not the entirety of PA-bin.

The file-length polynomial is inherited and remains proved. **No polynomial running-time bound in compressed input length is proved.** The definition parser and formula checker expand abbreviations. Expanded terms may be much larger than their compressed definitions, and the witness search operates on those expanded terms. Thus executable checkability has been established, but efficient checkability in the needed compressed representation has not.

The general trace file remains an existential witness from the earlier noncomputable construction. The new executable is a checker, not a general trace exporter. Its two bundled concrete files are computably produced small examples.

Neither part 1 nor part 2 of MAIS-O11 is resolved here. In particular, this checkpoint supplies no strict comparison between shortest proofs of `P` and `□P → P`, and no PA proof of a polynomial bound for its own proof verification.

The next target is a checker that retains abbreviation sharing, with proved equality and substitution checks on that representation. A polynomial bound on its work must precede the proposed polynomial PA internalization. The current checker and soundness theorem provide an explicit specification against which that faster checker can be verified.

#!/usr/bin/env bash
# MAIS-O11: creates and verifies a fresh, conditional Lean project.
# The concrete arithmetic construction remains an explicit hypothesis.
set -euo pipefail
trap 'printf "\nSetup stopped. See the error above; this is not a successful verification.\n" >&2' ERR

mais_toolchain='leanprover/lean4:v4.19.0'
mais_elan=''
if [ -x "$HOME/.elan/bin/elan" ]; then
  mais_elan="$HOME/.elan/bin/elan"
elif command -v elan >/dev/null 2>&1; then
  mais_elan="$(command -v elan)"
fi

if [ -z "$mais_elan" ]; then
  printf 'Installing Elan from the official Lean installer.\n'
  mais_bootstrap="$(mktemp -d "${TMPDIR:-/tmp}/mais-elan.XXXXXX")"
  curl -fsSL https://elan.lean-lang.org/elan-init.sh -o "$mais_bootstrap/elan-init.sh"
  sh "$mais_bootstrap/elan-init.sh" -y --no-modify-path --default-toolchain none
  mais_elan="${ELAN_HOME:-$HOME/.elan}/bin/elan"
  if [ ! -x "$mais_elan" ]; then
    printf 'Elan installation did not produce the expected executable: %s\n' "$mais_elan" >&2
    exit 1
  fi
fi

mais_parent="$HOME/Documents"
mkdir -p "$mais_parent"
mais_project="$(mktemp -d "$mais_parent/MAIS-O11-First-Pass.XXXXXX")"
cd "$mais_project"
printf 'Creating project: %s\n' "$mais_project"

cat > 'FirstPass.lean' <<'MAIS_FILE_0_END'
import Std

/-!
MAIS-O11: first, conditional formalization pass.

This file proves abstract implications. It does NOT construct PA, the finite
diagonal sentences, the guarded verifier, or the interpretation on proof files.
The unproved construction obligations are the fields of `FiniteDiagonal`,
`LobConditions`, and `SeparationHypotheses`. No instance of those structures
for the proposed arithmetic construction is supplied here.

All lengths below are object-system lengths supplied by `ProofSystem.length`.
They are not lengths of Lean source files, tactic scripts, or kernel terms.
-/

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11

/-- An abstract syntax of certificates together with their assigned lengths. -/
structure ProofSystem (Formula : Type) where
  Proof : Formula → Type
  length : {A : Formula} → Proof A → Nat

def Provable {F : Type} (S : ProofSystem F) (A : F) : Prop :=
  Nonempty (S.Proof A)

def IsShortest {F : Type} (S : ProofSystem F) {A : F}
    (p : S.Proof A) : Prop :=
  ∀ q : S.Proof A, S.length p ≤ S.length q

/-- Natural-valued proof lengths attain a minimum whenever a proof exists. -/
theorem exists_shortest {F : Type} (S : ProofSystem F) {A : F}
    (h : Provable S A) : ∃ p : S.Proof A, IsShortest S p := by
  classical
  have aux : ∀ n : Nat, (∃ p : S.Proof A, S.length p = n) →
      ∃ p : S.Proof A, IsShortest S p := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hex
      obtain ⟨p, hp⟩ := hex
      by_cases hs : ∃ q : S.Proof A, S.length q < n
      · obtain ⟨q, hq⟩ := hs
        exact ih (S.length q) hq ⟨q, rfl⟩
      · refine ⟨p, ?_⟩
        intro q
        have hn : ¬ S.length q < n := fun hlt => hs ⟨q, hlt⟩
        omega
  obtain ⟨p⟩ := h
  exact aux (S.length p) ⟨p, rfl⟩

/- The two internal proof constructions used in the finite Goedel argument. -/
structure FiniteDiagonal {F : Type} (B : ProofSystem F) where
  sentence : Nat → F
  guard : Nat → F
  neg : F → F
  consistent : ∀ A : F, B.Proof A → B.Proof (neg A) → False
  toGuard : ∀ n : Nat, B.Proof (sentence n) → B.Proof (guard n)
  refuteShort : ∀ (n : Nat) (p : B.Proof (sentence n)),
    B.length p ≤ n → B.Proof (neg (guard n))

/-- Conditional finite Goedel lower bound: every proof exceeds n symbols. -/
theorem finite_diagonal_lower_bound {F : Type} {B : ProofSystem F}
    (D : FiniteDiagonal B) (n : Nat) (p : B.Proof (D.sentence n)) :
    n < B.length p := by
  by_cases h : B.length p ≤ n
  · exact False.elim
      (D.consistent (D.guard n) (D.toGuard n p) (D.refuteShort n p h))
  · omega

/-
The first three logical fields are ordinary propositional reasoning.
The next three are the Hilbert--Bernays--Loeb conditions. `fixedPoint`
is the two directions of the diagonal equivalence for each target A.
All are hypotheses about the object system, not extra axioms of Lean.
-/
structure LobConditions {F : Type} (S : ProofSystem F) where
  imp : F → F → F
  box : F → F
  mp : ∀ A B : F, Provable S (imp A B) → Provable S A → Provable S B
  chain : ∀ A B C : F,
    Provable S (imp A B) → Provable S (imp B C) → Provable S (imp A C)
  underMP : ∀ A B C : F,
    Provable S (imp A (imp B C)) → Provable S (imp A B) →
    Provable S (imp A C)
  necessitate : ∀ A : F, Provable S A → Provable S (box A)
  boxMP : ∀ A B : F, Provable S (imp (box (imp A B)) (imp (box A) (box B)))
  boxBox : ∀ A : F, Provable S (imp (box A) (box (box A)))
  fixedPoint : ∀ A : F, ∃ G : F,
    Provable S (imp G (imp (box G) A)) ∧
    Provable S (imp (imp (box G) A) G)

/-- Loeb's rule, proved from the explicitly listed logical hypotheses. -/
theorem lob_rule {F : Type} {S : ProofSystem F}
    (L : LobConditions S) (A : F)
    (hR : Provable S (L.imp (L.box A) A)) : Provable S A := by
  obtain ⟨G, hForward, hBackward⟩ := L.fixedPoint A
  have h1 := L.necessitate _ hForward
  have h2 := L.mp _ _ (L.boxMP G (L.imp (L.box G) A)) h1
  have h3 := L.chain _ _ _ h2 (L.boxMP (L.box G) A)
  have h4 := L.underMP _ _ _ h3 (L.boxBox G)
  have h5 := L.chain _ _ _ h4 hR
  have hG := L.mp _ _ hBackward h5
  exact L.mp _ _ h5 (L.necessitate G hG)

/-- A concrete logarithmic scale, including the n = 0 case. -/
def logSize (n : Nat) : Nat := n.log2 + 2

/-- Conditions still to be established for the arithmetic construction. -/
structure SeparationHypotheses {F G : Type}
    (B : ProofSystem F) (S : ProofSystem G) where
  diagonal : FiniteDiagonal B
  logic : LobConditions S
  target : Nat → G
  sentenceSize : G → Nat
  C : Nat
  C_pos : 0 < C
  a : Nat
  b : Nat
  translate : ∀ n : Nat, S.Proof (target n) → B.Proof (diagonal.sentence n)
  translationBound : ∀ (n : Nat) (p : S.Proof (target n)),
    B.length (translate n p) ≤ C * (S.length p + 1)
  reflectionProof : ∀ n : Nat, S.Proof (logic.imp (logic.box (target n)) (target n))
  reflectionBound : ∀ n : Nat,
    S.length (reflectionProof n) ≤ a * logSize n
  sizeBound : ∀ n : Nat, sentenceSize (target n) + 1 ≤ b * logSize n
  reflectionDistinct : ∀ i j : Nat,
    logic.imp (logic.box (target i)) (target i) =
      logic.imp (logic.box (target j)) (target j) → i = j
  shortConclusions : Nat → List G
  shortConclusionsComplete : ∀ (M : Nat) (A : G) (p : S.Proof A),
    S.length p ≤ M → A ∈ shortConclusions M

namespace SeparationHypotheses

variable {F G : Type} {B : ProofSystem F} {S : ProofSystem G}

def reflection (H : SeparationHypotheses B S) (n : Nat) : G :=
  H.logic.imp (H.logic.box (H.target n)) (H.target n)

theorem target_provable (H : SeparationHypotheses B S) (n : Nat) :
    Provable S (H.target n) :=
  lob_rule H.logic (H.target n) ⟨H.reflectionProof n⟩

/-- The division-free form of length > n/C - 1, for EVERY direct proof. -/
theorem direct_lower_bound (H : SeparationHypotheses B S)
    (n : Nat) (p : S.Proof (H.target n)) :
    n < H.C * (S.length p + 1) :=
  Nat.lt_of_lt_of_le
    (finite_diagonal_lower_bound H.diagonal n (H.translate n p))
    (H.translationBound n p)

def tollCoefficient (H : SeparationHypotheses B S) (C1 : Nat) : Nat :=
  2 * H.a + C1 * H.b

def threshold (H : SeparationHypotheses B S) (C1 n : Nat) : Nat :=
  H.tollCoefficient C1 * logSize n

theorem reflection_and_toll_bound (H : SeparationHypotheses B S)
    (C1 n : Nat) :
    2 * S.length (H.reflectionProof n) + C1 * (H.sentenceSize (H.target n) + 1)
      ≤ H.threshold C1 n := by
  calc
    _ ≤ 2 * (H.a * logSize n) + C1 * (H.b * logSize n) :=
      Nat.add_le_add (Nat.mul_le_mul_left 2 (H.reflectionBound n))
        (Nat.mul_le_mul_left C1 (H.sizeBound n))
    _ = H.threshold C1 n := by
      simp [threshold, tollCoefficient, Nat.add_mul, Nat.mul_assoc]

theorem separation_at (H : SeparationHypotheses B S) (C1 n : Nat)
    (hn : H.C * (H.threshold C1 n + 1) ≤ n)
    (p : S.Proof (H.target n)) :
    2 * S.length (H.reflectionProof n) + C1 * (H.sentenceSize (H.target n) + 1)
      < S.length p := by
  have hlarge : H.threshold C1 n < S.length p := by
    by_cases hsmall : S.length p ≤ H.threshold C1 n
    · have hm := Nat.mul_le_mul_left H.C (Nat.add_le_add_right hsmall 1)
      have hl := H.direct_lower_bound n p
      omega
    · omega
  exact Nat.lt_of_le_of_lt (H.reflection_and_toll_bound C1 n) hlarge

/- An explicit family of sufficiently large indices: no search oracle. -/
def exponent (H : SeparationHypotheses B S) (C1 i : Nat) : Nat :=
  2 * H.C * (H.tollCoefficient C1 + 1) + i + 1

def witnessIndex (H : SeparationHypotheses B S) (C1 i : Nat) : Nat :=
  2 ^ (2 * H.exponent C1 i)

theorem witness_large_enough (H : SeparationHypotheses B S) (C1 i : Nat) :
    H.C * (H.threshold C1 (H.witnessIndex C1 i) + 1) ≤ H.witnessIndex C1 i := by
  let k := H.tollCoefficient C1
  let t := H.exponent C1 i
  have ht : 2 * (H.C * (k + 1)) ≤ t + 1 := by
    dsimp [t, exponent, k]
    simp only [Nat.mul_assoc]
    omega
  have hpow : t + 1 ≤ 2 ^ t := Nat.lt_two_pow_self
  have hmul := Nat.mul_le_mul hpow hpow
  have hlog : logSize (H.witnessIndex C1 i) = 2 * t + 2 := by
    simp [logSize, witnessIndex, t, Nat.log2_two_pow]
  rw [threshold, hlog]
  change H.C * (k * (2 * t + 2) + 1) ≤ 2 ^ (2 * t)
  calc
    H.C * (k * (2 * t + 2) + 1) ≤ H.C * ((k + 1) * (2 * t + 2)) := by
      apply Nat.mul_le_mul_left
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    _ = (2 * (H.C * (k + 1))) * (t + 1) := by
      simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (t + 1) * (t + 1) := Nat.mul_le_mul_right (t + 1) ht
    _ ≤ 2 ^ t * 2 ^ t := hmul
    _ = 2 ^ (2 * t) := by rw [← Nat.pow_add]; congr 1; omega

theorem witness_increasing (H : SeparationHypotheses B S) (C1 : Nat)
    (i j : Nat) (hij : i < j) : H.witnessIndex C1 i < H.witnessIndex C1 j := by
  apply Nat.pow_lt_pow_of_lt (by decide : 1 < 2)
  simp only [exponent]
  omega

theorem witness_ge_index (H : SeparationHypotheses B S) (C1 i : Nat) :
    i ≤ H.witnessIndex C1 i := by
  have h := @Nat.lt_two_pow_self (2 * H.exponent C1 i)
  have hi : i ≤ 2 * H.exponent C1 i := by simp only [exponent]; omega
  exact Nat.le_trans hi (Nat.le_of_lt h)

theorem factor_two_for_every_direct_proof (H : SeparationHypotheses B S)
    (C1 i : Nat) (p : S.Proof (H.target (H.witnessIndex C1 i))) :
    2 * S.length (H.reflectionProof (H.witnessIndex C1 i)) +
      C1 * (H.sentenceSize (H.target (H.witnessIndex C1 i)) + 1) < S.length p :=
  H.separation_at C1 _ (H.witness_large_enough C1 i) p

/-- The exact minimum-length comparison, with delta = 1 and the toll. -/
theorem shortest_proof_separation (H : SeparationHypotheses B S) (C1 i : Nat) :
    ∃ p : S.Proof (H.target (H.witnessIndex C1 i)),
    ∃ r : S.Proof (H.reflection (H.witnessIndex C1 i)),
      IsShortest S p ∧ IsShortest S r ∧
      2 * S.length r + C1 * (H.sentenceSize (H.target (H.witnessIndex C1 i)) + 1)
        < S.length p := by
  obtain ⟨p, hp⟩ := exists_shortest S (H.target_provable (H.witnessIndex C1 i))
  obtain ⟨r, hr⟩ := exists_shortest S ⟨H.reflectionProof (H.witnessIndex C1 i)⟩
  refine ⟨p, r, hp, hr, ?_⟩
  have hgap := H.factor_two_for_every_direct_proof C1 i p
  have hmin := hr (H.reflectionProof (H.witnessIndex C1 i))
  omega

end SeparationHypotheses

/-- An injective sequence eventually leaves any fixed finite list. -/
theorem eventually_outside_list {F : Type} (f : Nat → F)
    (hinj : ∀ i j : Nat, f i = f j → i = j) (xs : List F) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → f n ∉ xs := by
  classical
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons x xs ih =>
    obtain ⟨N, hN⟩ := ih
    by_cases hx : ∃ k : Nat, f k = x
    · obtain ⟨k, hk⟩ := hx
      refine ⟨N + k + 1, ?_⟩
      intro n hn hmem
      cases List.mem_cons.mp hmem with
      | inl heq =>
        have heqnk := hinj n k (heq.trans hk.symm)
        omega
      | inr hin => exact hN n (by omega) hin
    · refine ⟨N, ?_⟩
      intro n hn hmem
      cases List.mem_cons.mp hmem with
      | inl heq => exact hx ⟨n, heq⟩
      | inr hin => exact hN n hn hin

namespace SeparationHypotheses

variable {F G : Type} {B : ProofSystem F} {S : ProofSystem G}

/-- Even the shortest reflection proofs eventually exceed every fixed bound. -/
theorem reflection_lengths_diverge (H : SeparationHypotheses B S) (M : Nat) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ r : S.Proof (H.reflection n), M < S.length r := by
  obtain ⟨N, hN⟩ := eventually_outside_list H.reflection
    H.reflectionDistinct (H.shortConclusions M)
  refine ⟨N, ?_⟩
  intro n hn r
  by_cases hs : S.length r ≤ M
  · exact False.elim (hN n hn (H.shortConclusionsComplete M _ r hs))
  · omega

theorem witness_reflection_lengths_diverge (H : SeparationHypotheses B S)
    (C1 M : Nat) : ∃ I : Nat, ∀ i : Nat, I ≤ i →
      ∀ r : S.Proof (H.reflection (H.witnessIndex C1 i)), M < S.length r := by
  obtain ⟨N, hN⟩ := H.reflection_lengths_diverge M
  exact ⟨N, fun i hi r => hN _ (Nat.le_trans hi (H.witness_ge_index C1 i)) r⟩

/--
The first-pass certificate. Supplying H is the uncompleted construction work.
For every toll constant C1, our explicit increasing witness family has
shortest-proof separation with delta = 1 and divergent reflection lengths.
-/
theorem conditional_main (H : SeparationHypotheses B S) (C1 : Nat) :
    (∀ i j : Nat, i < j → H.witnessIndex C1 i < H.witnessIndex C1 j) ∧
    (∀ i : Nat,
      ∃ p : S.Proof (H.target (H.witnessIndex C1 i)),
      ∃ r : S.Proof (H.reflection (H.witnessIndex C1 i)),
        IsShortest S p ∧ IsShortest S r ∧
        2 * S.length r + C1 * (H.sentenceSize (H.target (H.witnessIndex C1 i)) + 1)
          < S.length p) ∧
    (∀ M : Nat, ∃ I : Nat, ∀ i : Nat, I ≤ i →
      ∀ r : S.Proof (H.reflection (H.witnessIndex C1 i)), M < S.length r) :=
  ⟨H.witness_increasing C1, H.shortest_proof_separation C1,
    H.witness_reflection_lengths_diverge C1⟩

end SeparationHypotheses
end MAISO11
MAIS_FILE_0_END

cat > 'Audit.lean' <<'MAIS_FILE_1_END'
import FirstPass

set_option warningAsError true

/- These declarations show the hypotheses that still need concrete instances. -/
#print MAISO11.FiniteDiagonal
#print MAISO11.LobConditions
#print MAISO11.SeparationHypotheses

/- This displays the precise conditional conclusion, not just a theorem name. -/
#check MAISO11.SeparationHypotheses.conditional_main

/- No project-specific axioms or unfinished-proof axioms should appear here. -/
#print axioms MAISO11.finite_diagonal_lower_bound
#print axioms MAISO11.lob_rule
#print axioms MAISO11.SeparationHypotheses.direct_lower_bound
#print axioms MAISO11.SeparationHypotheses.witness_large_enough
#print axioms MAISO11.SeparationHypotheses.conditional_main
MAIS_FILE_1_END

cat > 'lean-toolchain' <<'MAIS_FILE_2_END'
leanprover/lean4:v4.19.0
MAIS_FILE_2_END

cat > 'lakefile.toml' <<'MAIS_FILE_3_END'
name = "mais_o11_first_pass"
version = "0.1.0"
defaultTargets = ["FirstPass"]

[[lean_lib]]
name = "FirstPass"
MAIS_FILE_3_END

cat > 'README.md' <<'MAIS_FILE_4_END'
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
MAIS_FILE_4_END

cat > 'checked-output.txt' <<'MAIS_FILE_5_END'
$ lake env lean --version
Lean (version 4.19.0, x86_64-unknown-linux-gnu, commit 6caaee842e94, Release)

$ lake build
✔ [2/3] Built FirstPass
Build completed successfully.

$ lake env lean -DwarningAsError=true Audit.lean
structure MAISO11.FiniteDiagonal {F : Type} (B : MAISO11.ProofSystem F) : Type
number of parameters: 2
fields:
  MAISO11.FiniteDiagonal.sentence : Nat → F
  MAISO11.FiniteDiagonal.guard : Nat → F
  MAISO11.FiniteDiagonal.neg : F → F
  MAISO11.FiniteDiagonal.consistent : ∀ (A : F), B.Proof A → B.Proof (self.neg A) → False
  MAISO11.FiniteDiagonal.toGuard : (n : Nat) → B.Proof (self.sentence n) → B.Proof (self.guard n)
  MAISO11.FiniteDiagonal.refuteShort : (n : Nat) →
      (p : B.Proof (self.sentence n)) → B.length p ≤ n → B.Proof (self.neg (self.guard n))
constructor:
  MAISO11.FiniteDiagonal.mk {F : Type} {B : MAISO11.ProofSystem F} (sentence guard : Nat → F) (neg : F → F)
    (consistent : ∀ (A : F), B.Proof A → B.Proof (neg A) → False)
    (toGuard : (n : Nat) → B.Proof (sentence n) → B.Proof (guard n))
    (refuteShort : (n : Nat) → (p : B.Proof (sentence n)) → B.length p ≤ n → B.Proof (neg (guard n))) :
    MAISO11.FiniteDiagonal B
structure MAISO11.LobConditions {F : Type} (S : MAISO11.ProofSystem F) : Type
number of parameters: 2
fields:
  MAISO11.LobConditions.imp : F → F → F
  MAISO11.LobConditions.box : F → F
  MAISO11.LobConditions.mp : ∀ (A B : F),
      MAISO11.Provable S (self.imp A B) → MAISO11.Provable S A → MAISO11.Provable S B
  MAISO11.LobConditions.chain : ∀ (A B C : F),
      MAISO11.Provable S (self.imp A B) → MAISO11.Provable S (self.imp B C) → MAISO11.Provable S (self.imp A C)
  MAISO11.LobConditions.underMP : ∀ (A B C : F),
      MAISO11.Provable S (self.imp A (self.imp B C)) →
        MAISO11.Provable S (self.imp A B) → MAISO11.Provable S (self.imp A C)
  MAISO11.LobConditions.necessitate : ∀ (A : F), MAISO11.Provable S A → MAISO11.Provable S (self.box A)
  MAISO11.LobConditions.boxMP : ∀ (A B : F),
      MAISO11.Provable S (self.imp (self.box (self.imp A B)) (self.imp (self.box A) (self.box B)))
  MAISO11.LobConditions.boxBox : ∀ (A : F), MAISO11.Provable S (self.imp (self.box A) (self.box (self.box A)))
  MAISO11.LobConditions.fixedPoint : ∀ (A : F),
      ∃ G,
        MAISO11.Provable S (self.imp G (self.imp (self.box G) A)) ∧
          MAISO11.Provable S (self.imp (self.imp (self.box G) A) G)
constructor:
  MAISO11.LobConditions.mk {F : Type} {S : MAISO11.ProofSystem F} (imp : F → F → F) (box : F → F)
    (mp : ∀ (A B : F), MAISO11.Provable S (imp A B) → MAISO11.Provable S A → MAISO11.Provable S B)
    (chain : ∀ (A B C : F), MAISO11.Provable S (imp A B) → MAISO11.Provable S (imp B C) → MAISO11.Provable S (imp A C))
    (underMP :
      ∀ (A B C : F), MAISO11.Provable S (imp A (imp B C)) → MAISO11.Provable S (imp A B) → MAISO11.Provable S (imp A C))
    (necessitate : ∀ (A : F), MAISO11.Provable S A → MAISO11.Provable S (box A))
    (boxMP : ∀ (A B : F), MAISO11.Provable S (imp (box (imp A B)) (imp (box A) (box B))))
    (boxBox : ∀ (A : F), MAISO11.Provable S (imp (box A) (box (box A))))
    (fixedPoint :
      ∀ (A : F), ∃ G, MAISO11.Provable S (imp G (imp (box G) A)) ∧ MAISO11.Provable S (imp (imp (box G) A) G)) :
    MAISO11.LobConditions S
structure MAISO11.SeparationHypotheses {F G : Type} (B : MAISO11.ProofSystem F) (S : MAISO11.ProofSystem G) : Type
number of parameters: 4
fields:
  MAISO11.SeparationHypotheses.diagonal : MAISO11.FiniteDiagonal B
  MAISO11.SeparationHypotheses.logic : MAISO11.LobConditions S
  MAISO11.SeparationHypotheses.target : Nat → G
  MAISO11.SeparationHypotheses.sentenceSize : G → Nat
  MAISO11.SeparationHypotheses.C : Nat
  MAISO11.SeparationHypotheses.C_pos : 0 < self.C
  MAISO11.SeparationHypotheses.a : Nat
  MAISO11.SeparationHypotheses.b : Nat
  MAISO11.SeparationHypotheses.translate : (n : Nat) → S.Proof (self.target n) → B.Proof (self.diagonal.sentence n)
  MAISO11.SeparationHypotheses.translationBound : ∀ (n : Nat) (p : S.Proof (self.target n)),
      B.length (self.translate n p) ≤ self.C * (S.length p + 1)
  MAISO11.SeparationHypotheses.reflectionProof : (n : Nat) →
      S.Proof (self.logic.imp (self.logic.box (self.target n)) (self.target n))
  MAISO11.SeparationHypotheses.reflectionBound : ∀ (n : Nat),
      S.length (self.reflectionProof n) ≤ self.a * MAISO11.logSize n
  MAISO11.SeparationHypotheses.sizeBound : ∀ (n : Nat),
      self.sentenceSize (self.target n) + 1 ≤ self.b * MAISO11.logSize n
  MAISO11.SeparationHypotheses.reflectionDistinct : ∀ (i j : Nat),
      self.logic.imp (self.logic.box (self.target i)) (self.target i) =
          self.logic.imp (self.logic.box (self.target j)) (self.target j) →
        i = j
  MAISO11.SeparationHypotheses.shortConclusions : Nat → List G
  MAISO11.SeparationHypotheses.shortConclusionsComplete : ∀ (M : Nat) (A : G) (p : S.Proof A),
      S.length p ≤ M → A ∈ self.shortConclusions M
constructor:
  MAISO11.SeparationHypotheses.mk {F G : Type} {B : MAISO11.ProofSystem F} {S : MAISO11.ProofSystem G}
    (diagonal : MAISO11.FiniteDiagonal B) (logic : MAISO11.LobConditions S) (target : Nat → G) (sentenceSize : G → Nat)
    (C : Nat) (C_pos : 0 < C) (a b : Nat) (translate : (n : Nat) → S.Proof (target n) → B.Proof (diagonal.sentence n))
    (translationBound : ∀ (n : Nat) (p : S.Proof (target n)), B.length (translate n p) ≤ C * (S.length p + 1))
    (reflectionProof : (n : Nat) → S.Proof (logic.imp (logic.box (target n)) (target n)))
    (reflectionBound : ∀ (n : Nat), S.length (reflectionProof n) ≤ a * MAISO11.logSize n)
    (sizeBound : ∀ (n : Nat), sentenceSize (target n) + 1 ≤ b * MAISO11.logSize n)
    (reflectionDistinct :
      ∀ (i j : Nat), logic.imp (logic.box (target i)) (target i) = logic.imp (logic.box (target j)) (target j) → i = j)
    (shortConclusions : Nat → List G)
    (shortConclusionsComplete : ∀ (M : Nat) (A : G) (p : S.Proof A), S.length p ≤ M → A ∈ shortConclusions M) :
    MAISO11.SeparationHypotheses B S
MAISO11.SeparationHypotheses.conditional_main {F G : Type} {B : MAISO11.ProofSystem F} {S : MAISO11.ProofSystem G}
  (H : MAISO11.SeparationHypotheses B S) (C1 : Nat) :
  (∀ (i j : Nat), i < j → H.witnessIndex C1 i < H.witnessIndex C1 j) ∧
    (∀ (i : Nat),
        ∃ p r,
          MAISO11.IsShortest S p ∧
            MAISO11.IsShortest S r ∧
              2 * S.length r + C1 * (H.sentenceSize (H.target (H.witnessIndex C1 i)) + 1) < S.length p) ∧
      ∀ (M : Nat), ∃ I, ∀ (i : Nat), I ≤ i → ∀ (r : S.Proof (H.reflection (H.witnessIndex C1 i))), M < S.length r
'MAISO11.finite_diagonal_lower_bound' depends on axioms: [propext, Quot.sound]
'MAISO11.lob_rule' does not depend on any axioms
'MAISO11.SeparationHypotheses.direct_lower_bound' depends on axioms: [propext, Quot.sound]
'MAISO11.SeparationHypotheses.witness_large_enough' depends on axioms: [propext, Classical.choice, Quot.sound]
'MAISO11.SeparationHypotheses.conditional_main' depends on axioms: [propext, Classical.choice, Quot.sound]
MAIS_FILE_5_END

cat > 'SHA256SUMS' <<'MAIS_FILE_6_END'
2bb51161d580c93654eb0394ded6048a3f8b66d261f02177a9a62cf8f3916efa  FirstPass.lean
d04a2223577c94b09c41b959331796f13e485fb240192b82a712f861c3d6fcbc  Audit.lean
55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea  lean-toolchain
2189e211dd38ad6402c35debb46b5e11edd8bad0b32cc084d7bd68b7105abc7f  lakefile.toml
5c9504a1da22d380fa8f25c67dc7562d65ab596f86d4a93429f0750cbea81556  README.md
a16eaca41ac74a56644bfe6e4a961562d62af9da8f2e9fcb33d38d16198f708a  checked-output.txt
MAIS_FILE_6_END

# Check that the embedded project matches the tested source.
if command -v shasum >/dev/null 2>&1; then
  shasum -a 256 -c SHA256SUMS
elif command -v sha256sum >/dev/null 2>&1; then
  sha256sum -c SHA256SUMS
fi

printf '\nSelecting the pinned Lean toolchain. This may download Lean once.\n'
"$mais_elan" toolchain install "$mais_toolchain"
"$mais_elan" run "$mais_toolchain" lake env lean --version | tee verification.log
"$mais_elan" run "$mais_toolchain" lake build 2>&1 | tee -a verification.log
"$mais_elan" run "$mais_toolchain" lake env lean -DwarningAsError=true Audit.lean 2>&1 | tee -a verification.log

if grep -Eq 'sorryAx|Lean\.ofReduceBool' verification.log; then
  printf '\nFAILED: an unfinished-proof or native-evaluation axiom appeared.\n' >&2
  exit 1
fi

printf '\nPASS: conditional first-pass theorem verified with Lean 4.19.0.\n'
printf 'The concrete PA/checker hypotheses remain to be proved.\n'
printf 'Project folder: %s\n' "$mais_project"
printf 'Audit transcript: %s/verification.log\n' "$mais_project"
printf 'In VS Code, use File > Open Folder and select this project folder.\n'

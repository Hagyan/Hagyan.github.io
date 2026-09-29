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

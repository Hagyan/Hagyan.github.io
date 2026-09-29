import Std

/-!
Arithmetic core for the padded-system Part 1 construction.

This file verifies the only asymptotic estimate used in the construction:
quadratic raw padding eventually dominates every fixed linear reflection
length bound and the fixed sentence-size toll.  It does not formalize the
Kleene fixed-point construction of the self-referential proof checker or
Löb's theorem for that checker; those remain in the accompanying note.
-/

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.PaddingLoophole

/-- If the reflection proof length is at most affine in sentence size,
quadratic padding eventually pays for twice that length and the fixed toll. -/
theorem quadratic_padding_dominates
    (a b c s : Nat)
    (large : 2 * a + c + 2 * b ≤ s) :
    2 * (a * (s + 1) + b) + c * (s + 1) ≤ (s + 1) ^ 2 := by
  let x := s + 1
  have hx : 1 ≤ x := by omega
  have hbx : 2 * b ≤ (2 * b) * x := by
    simpa using Nat.mul_le_mul_left (2 * b) hx
  have h1 : 2 * (a * x + b) + c * x ≤ (2 * a + c) * x + 2 * b := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc]
    omega
  have h2 : (2 * a + c) * x + 2 * b ≤ (2 * a + c + 2 * b) * x := by
    calc
      (2 * a + c) * x + 2 * b ≤ (2 * a + c) * x + (2 * b) * x :=
        Nat.add_le_add_left hbx _
      _ = (2 * a + c + 2 * b) * x := by simp [Nat.add_mul, Nat.mul_assoc]
  have h3 : (2 * a + c + 2 * b) * x ≤ s * x :=
    Nat.mul_le_mul_right x large
  have h4 : s * x ≤ x * x :=
    Nat.mul_le_mul_right x (by omega)
  calc
    2 * (a * (s + 1) + b) + c * (s + 1) =
        2 * (a * x + b) + c * x := by rfl
    _ ≤ (2 * a + c) * x + 2 * b := h1
    _ ≤ (2 * a + c + 2 * b) * x := h2
    _ ≤ s * x := h3
    _ ≤ x * x := h4
    _ = (s + 1) ^ 2 := by simp [x, Nat.pow_two]


/-- The useful form, with the actual reflection length in place of its bound. -/
theorem padded_sentence_separation
    (a b c s r d : Nat)
    (reflection_bound : r ≤ a * (s + 1) + b)
    (padding_bound : (s + 1) ^ 2 ≤ d)
    (large : 2 * a + c + 2 * b ≤ s) :
    2 * r + c * (s + 1) ≤ d := by
  have h := quadratic_padding_dominates a b c s large
  omega

/-- A family with eventually growing sentence and reflection lengths, a linear
upper bound on its designated reflection proofs, and quadratic mandatory
padding has a cofinal factor-two separation with the fixed linear toll. -/
theorem cofinal_factor_two_speedup
    (s r d : Nat → Nat) (a b c : Nat)
    (size_tends : ∀ N, ∃ I, ∀ i, I ≤ i → N ≤ s i)
    (reflection_tends : ∀ N, ∃ I, ∀ i, I ≤ i → N ≤ r i)
    (reflection_bound : ∀ i, r i ≤ a * (s i + 1) + b)
    (padding_bound : ∀ i, (s i + 1) ^ 2 ≤ d i) :
    ∃ I, (∀ i, I ≤ i → 2 * r i + c * (s i + 1) ≤ d i) ∧
      (∀ N, ∃ I', ∀ i, I' ≤ i → N ≤ r i) := by
  obtain ⟨I, hI⟩ := size_tends (2 * a + c + 2 * b)
  refine ⟨I, ?_, reflection_tends⟩
  intro i hi
  exact padded_sentence_separation a b c (s i) (r i) (d i)
    (reflection_bound i) (padding_bound i) (hI i hi)

end MAISO11.PaddingLoophole

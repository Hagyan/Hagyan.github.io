import Std

set_option autoImplicit false
set_option warningAsError true

/-!
An abstract transfer from superlinear Loeb overhead to arbitrarily strong
Part 1 witnesses. The eligible-sentence type contains only sentences with
finite direct and reflection proof lengths. `attained` and `boundedFiber`
are explicit hypotheses: this module does not formalize a full PA checker.

The accompanying SPEC-SECOND-AUDIT.md proves why finite proof syntax and
Loeb's rule supply those hypotheses for the agenda's overhead definition.
-/

namespace MAISO11.SpecTransfer

theorem numericGap
    (d k n r s i a c : Nat)
    (hgap : i * (k + n + 1) < d)
    (hr : r ≤ k) (hs : s ≤ n) (ha : a ≤ i) (hc : c ≤ i) :
    a * r + c * (s + 1) < d := by
  have h1 : a * r ≤ i * k := Nat.mul_le_mul ha hr
  have h2 : c * (s + 1) ≤ i * (n + 1) :=
    Nat.mul_le_mul hc (Nat.succ_le_succ hs)
  have h3 : a * r + c * (s + 1) ≤ i * (k + n + 1) := by
    calc
      a * r + c * (s + 1) ≤ i * k + i * (n + 1) := Nat.add_le_add h1 h2
      _ = i * (k + n + 1) := by simp [Nat.mul_add, Nat.add_assoc]
  exact Nat.lt_of_le_of_lt h3 hgap

/-- Finite proof alphabets plus Loeb's rule imply `boundedFiber`; positivity
ensures a nonempty maximum, hence `attained`. No uniform constructive bound
on the witnesses in these two hypotheses is asserted here. -/
theorem unboundedOverheadGivesWitness
    {Sentence : Type}
    (direct reflection size : Sentence → Nat) (F : Nat → Nat → Nat)
    (attained : ∀ k n, 0 < F k n →
      ∃ p, reflection p ≤ k ∧ size p ≤ n ∧ direct p = F k n)
    (boundedFiber : ∀ R, ∃ M, ∀ p, reflection p ≤ R → direct p ≤ M)
    (unboundedRatio : ∀ i, ∃ k n, i * (k + n + 1) < F k n)
    (a c R : Nat) :
    ∃ p, R < reflection p ∧
      a * reflection p + c * (size p + 1) < direct p := by
  obtain ⟨M, hM⟩ := boundedFiber R
  let i := a + c + M + 1
  obtain ⟨k, n, hF⟩ := unboundedRatio i
  have hpos : 0 < F k n := Nat.lt_of_le_of_lt (Nat.zero_le _) hF
  obtain ⟨p, hr, hs, hd⟩ := attained k n hpos
  have hi : i ≤ i * (k + n + 1) := by
    calc
      i = i * 1 := by simp
      _ ≤ i * (k + n + 1) := Nat.mul_le_mul_left i (by omega)
  have hMd : M < direct p := by
    rw [hd]
    have hMi : M < i := by simp only [i]; omega
    exact Nat.lt_trans hMi (Nat.lt_of_le_of_lt hi hF)
  refine ⟨p, ?_, ?_⟩
  · by_cases hp : reflection p ≤ R
    · have hbound := hM p hp
      omega
    · omega
  · apply numericGap (direct p) k n (reflection p) (size p) i a c
    · simpa only [hd] using hF
    · exact hr
    · exact hs
    · simp only [i]; omega
    · simp only [i]; omega

/-- The convergence requirement in Part 1 follows from finite bounded
reflection fibers, even for arbitrary choices among maximizing sentences. -/
theorem reflectionLengthsTendToInfinity
    (direct reflection : Nat → Nat)
    (grows : ∀ i, i < direct i)
    (boundedFiber : ∀ R, ∃ M, ∀ i, reflection i ≤ R → direct i ≤ M) :
    ∀ R, ∃ I, ∀ i, I ≤ i → R < reflection i := by
  intro R
  obtain ⟨M, hM⟩ := boundedFiber R
  refine ⟨M, ?_⟩
  intro i hi
  by_cases hp : reflection i ≤ R
  · have hbound := hM i hp
    have hlarge := grows i
    omega
  · omega

#print axioms numericGap
#print axioms unboundedOverheadGivesWitness
#print axioms reflectionLengthsTendToInfinity

end MAISO11.SpecTransfer

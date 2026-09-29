import Std

/-!
Finite-budget maxima and the relationship between the two parts of MAIS-O11.

The objects in `Lengths` are provable targets with finite direct and reflection
lengths. The `short` lists enumerate exactly the targets with reflection length
at most a budget. No PA checker, internalization estimate, or asymptotic bound
is postulated or implemented here.

All ratios are expressed with natural-number inequalities and positive integer
denominators. This avoids any dependency on Mathlib or floating-point arithmetic.
-/

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Envelope

def maxList : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maxList xs)

theorem le_maxList {x : Nat} {xs : List Nat} (h : x ∈ xs) :
    x ≤ maxList xs := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    simp only [List.mem_cons] at h
    simp only [maxList]
    rcases h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem maxList_le {xs : List Nat} {b : Nat}
    (h : ∀ x ∈ xs, x ≤ b) : maxList xs ≤ b := by
  induction xs with
  | nil => simp [maxList]
  | cons a xs ih =>
    have ha := h a (by simp)
    have hx := ih (by intro x hx; exact h x (by simp [hx]))
    simp only [maxList]
    omega

theorem maxList_zero_or_attained (xs : List Nat) :
    maxList xs = 0 ∨ maxList xs ∈ xs := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons a xs ih =>
    by_cases ha : maxList xs ≤ a
    · right
      simp [maxList, Nat.max_eq_left ha]
    · have he : maxList (a :: xs) = maxList xs := by
        simp [maxList, Nat.max_eq_right (by omega : a ≤ maxList xs)]
      rw [he]
      rcases ih with ih | ih
      · exact Or.inl ih
      · exact Or.inr (by simp [ih])

structure Lengths (α : Type) where
  direct : α → Nat
  reflection : α → Nat
  size : α → Nat
  tollCoefficient : Nat
  short : Nat → List α
  mem_short : ∀ p k, p ∈ short k ↔ reflection p ≤ k

namespace Lengths

variable {α : Type} (M : Lengths α)

def toll (p : α) : Nat := M.tollCoefficient * (M.size p + 1)

/-- Truncated excess above reflection length plus the fixed sentence-size toll. -/
def excess (p : α) : Nat := M.direct p - (M.reflection p + M.toll p)

/-- The finite maximum, with the empty maximum defined to be zero. -/
def envelope (k : Nat) : Nat := maxList ((M.short k).map M.excess)

theorem excess_le_envelope (p : α) (k : Nat)
    (h : M.reflection p ≤ k) : M.excess p ≤ M.envelope k := by
  apply le_maxList
  exact List.mem_map.mpr ⟨p, (M.mem_short p k).mpr h, rfl⟩

theorem envelope_zero_or_attained (k : Nat) :
    M.envelope k = 0 ∨
    ∃ p, M.reflection p ≤ k ∧ M.excess p = M.envelope k := by
  rcases maxList_zero_or_attained ((M.short k).map M.excess) with h | h
  · exact Or.inl h
  · right
    rcases List.mem_map.mp h with ⟨p, hp, he⟩
    exact ⟨p, (M.mem_short p k).mp hp, he⟩

theorem envelope_mono (k l : Nat) (h : k ≤ l) :
    M.envelope k ≤ M.envelope l := by
  apply maxList_le
  intro e he
  rcases List.mem_map.mp he with ⟨p, hp, rfl⟩
  exact M.excess_le_envelope p l (Nat.le_trans ((M.mem_short p k).mp hp) h)

theorem direct_le_base_add_excess (p : α) :
    M.direct p ≤ M.reflection p + M.toll p + M.excess p := by
  unfold excess
  omega

theorem direct_le_envelope_bound (p : α) :
    M.direct p ≤ M.reflection p + M.toll p + M.envelope (M.reflection p) := by
  have h := M.direct_le_base_add_excess p
  have he := M.excess_le_envelope p (M.reflection p) (Nat.le_refl _)
  omega

/-- The exact separation inequality for delta = 1/q. -/
def Separated (q : Nat) (p : α) : Prop :=
  (q + 1) * M.reflection p + q * M.toll p ≤ q * M.direct p

theorem separated_iff_excess (q : Nat) (p : α)
    (hq : 0 < q) (hr : 0 < M.reflection p) :
    M.Separated q p ↔ M.reflection p ≤ q * M.excess p := by
  by_cases hb : M.reflection p + M.toll p ≤ M.direct p
  · have he : M.direct p = M.reflection p + M.toll p + M.excess p := by
      unfold excess
      omega
    unfold Separated
    rw [he]
    simp only [Nat.add_mul, Nat.one_mul, Nat.mul_add]
    omega
  · have he : M.excess p = 0 := by unfold excess; omega
    have hh : q * M.direct p < q * (M.reflection p + M.toll p) :=
      Nat.mul_lt_mul_of_pos_left (by omega) hq
    unfold Separated
    rw [he]
    simp only [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_zero] at *
    omega

/-- A witness exists at arbitrarily large reflection lengths for one fixed q. -/
def HasSpeedup : Prop :=
  ∃ q, 0 < q ∧ ∀ K, ∃ p, K ≤ M.reflection p ∧ M.Separated q p

theorem hasSpeedup_iff_witness_sequence : M.HasSpeedup ↔
    ∃ q, 0 < q ∧ ∃ p : Nat → α,
      ∀ i, i ≤ M.reflection (p i) ∧ M.Separated q (p i) := by
  classical
  constructor
  · rintro ⟨q, hq, hw⟩
    exact ⟨q, hq, fun i => Classical.choose (hw i),
      fun i => Classical.choose_spec (hw i)⟩
  · rintro ⟨q, hq, p, hp⟩
    exact ⟨q, hq, fun K => ⟨p K, hp K⟩⟩

/-- Exact absence of fixed-factor excess at large reflection lengths. -/
def NoSpeedup : Prop :=
  ∀ q, 0 < q → ∃ K, ∀ p, K ≤ M.reflection p → q * M.excess p < M.reflection p

/-- Natural-number form of h(k)/k tending to zero. -/
def Sublinear (h : Nat → Nat) : Prop :=
  ∀ q, 0 < q → ∃ K, ∀ k, K ≤ k → q * h k < k

theorem noSpeedup_iff_not_hasSpeedup : M.NoSpeedup ↔ ¬ M.HasSpeedup := by
  classical
  constructor
  · intro hn ⟨q, hq, hw⟩
    obtain ⟨K, hK⟩ := hn q hq
    obtain ⟨p, hp, hs⟩ := hw (K + 1)
    have he := (M.separated_iff_excess q p hq (by omega)).mp hs
    have hn' := hK p (by omega)
    omega
  · intro hn q hq
    by_cases h : ∃ K, ∀ p, K ≤ M.reflection p → q * M.excess p < M.reflection p
    · exact h
    · exfalso
      apply hn
      refine ⟨q, hq, ?_⟩
      intro K
      have hx : ∃ p, K + 1 ≤ M.reflection p ∧ M.reflection p ≤ q * M.excess p := by
        have h' : ¬ (∀ p, K + 1 ≤ M.reflection p →
            q * M.excess p < M.reflection p) := by
          intro hc
          exact h ⟨K + 1, hc⟩
        obtain ⟨p, hp⟩ := Classical.not_forall.mp h'
        have hp' := Classical.not_imp.mp hp
        exact ⟨p, hp'.1, by omega⟩
      obtain ⟨p, hp, he⟩ := hx
      exact ⟨p, by omega, (M.separated_iff_excess q p hq (by omega)).mpr he⟩

theorem noSpeedup_iff_sublinear_envelope :
    M.NoSpeedup ↔ Sublinear M.envelope := by
  constructor
  · intro hn q hq
    obtain ⟨K, hK⟩ := hn q hq
    refine ⟨q * M.envelope K + 1, ?_⟩
    intro k hk
    rcases M.envelope_zero_or_attained k with hz | ⟨p, hp, he⟩
    · rw [hz, Nat.mul_zero]
      omega
    · rw [← he]
      by_cases hlarge : K ≤ M.reflection p
      · exact Nat.lt_of_lt_of_le (hK p hlarge) hp
      · have he' := M.excess_le_envelope p K (by omega)
        have hh := Nat.mul_le_mul_left q he'
        omega
  · intro hh q hq
    obtain ⟨K, hK⟩ := hh q hq
    refine ⟨K, ?_⟩
    intro p hp
    exact Nat.lt_of_le_of_lt
      (Nat.mul_le_mul_left q (M.excess_le_envelope p (M.reflection p) (Nat.le_refl _)))
      (hK (M.reflection p) hp)

theorem hasSpeedup_iff_not_sublinear_envelope :
    M.HasSpeedup ↔ ¬ Sublinear M.envelope := by
  classical
  have h := M.noSpeedup_iff_not_hasSpeedup
  have h' := M.noSpeedup_iff_sublinear_envelope
  constructor
  · intro hs hl
    exact h.mp (h'.mpr hl) hs
  · intro hn
    by_cases hs : M.HasSpeedup
    · exact hs
    · exact False.elim (hn (h'.mp (h.mpr hs)))

/-- A sublinear envelope is not merely sufficient: it is the exact negative condition. -/
theorem noSpeedup_iff_sublinear_converter :
    M.NoSpeedup ↔ ∃ h : Nat → Nat, Sublinear h ∧
      ∀ p, M.direct p ≤ M.reflection p + M.toll p + h (M.reflection p) := by
  constructor
  · intro hn
    exact ⟨M.envelope, M.noSpeedup_iff_sublinear_envelope.mp hn,
      M.direct_le_envelope_bound⟩
  · rintro ⟨h, hh, hb⟩ q hq
    obtain ⟨K, hK⟩ := hh q hq
    refine ⟨K, ?_⟩
    intro p hp
    have he : M.excess p ≤ h (M.reflection p) := by
      have hbp := hb p
      unfold excess
      omega
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left q he) (hK (M.reflection p) hp)

/-- A negative part 1 gives a global coefficient 1+1/q, with a constant exception toll. -/
theorem noSpeedup_near_unit_affine (hn : M.NoSpeedup) (q : Nat) (hq : 0 < q) :
    ∃ B, ∀ p, q * M.direct p ≤
      (q + 1) * M.reflection p + q * M.toll p + B := by
  obtain ⟨K, hK⟩ := hn q hq
  refine ⟨q * M.envelope K, ?_⟩
  intro p
  have he : q * M.excess p ≤ M.reflection p + q * M.envelope K := by
    by_cases hp : K ≤ M.reflection p
    · have h := hK p hp
      omega
    · have h := Nat.mul_le_mul_left q (M.excess_le_envelope p K (by omega))
      omega
  have hd := Nat.mul_le_mul_left q (M.direct_le_base_add_excess p)
  simp only [Nat.add_mul, Nat.one_mul, Nat.mul_add] at hd ⊢
  omega

def overhead (k n : Nat) : Nat :=
  maxList (((M.short k).filter (fun p => decide (M.size p ≤ n))).map M.direct)

theorem direct_le_overhead (p : α) (k n : Nat)
    (hr : M.reflection p ≤ k) (hs : M.size p ≤ n) : M.direct p ≤ M.overhead k n := by
  apply le_maxList
  apply List.mem_map.mpr
  refine ⟨p, ?_, rfl⟩
  simpa only [List.mem_filter, decide_eq_true_eq] using
    And.intro ((M.mem_short p k).mpr hr) hs

/-- With no speedup, F(k,n) <= 2k + C1(n+1) + B. -/
theorem noSpeedup_overhead_affine (hn : M.NoSpeedup) :
    ∃ B, ∀ k n, M.overhead k n ≤ 2 * k + M.tollCoefficient * (n + 1) + B := by
  obtain ⟨B, hB⟩ := M.noSpeedup_near_unit_affine hn 1 (by decide)
  refine ⟨B, ?_⟩
  intro k n
  apply maxList_le
  intro d hd
  rcases List.mem_map.mp hd with ⟨p, hp, rfl⟩
  simp only [List.mem_filter, decide_eq_true_eq] at hp
  have hr := (M.mem_short p k).mp hp.1
  have hs := Nat.mul_le_mul_left M.tollCoefficient (Nat.add_le_add_right hp.2 1)
  have hb := hB p
  simp only [Nat.one_mul] at hb
  unfold toll at hb
  omega

def LinearOverhead : Prop := ∃ C, ∀ k n, M.overhead k n ≤ C * (k + n + 1)

theorem noSpeedup_implies_linear_overhead (hn : M.NoSpeedup) : M.LinearOverhead := by
  obtain ⟨B, hB⟩ := M.noSpeedup_overhead_affine hn
  refine ⟨2 + M.tollCoefficient + B, ?_⟩
  intro k n
  have hb := hB k n
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at hb ⊢
  omega

/-- Any failure of a linear joint bound already implies part 1. -/
theorem not_linear_overhead_implies_speedup (h : ¬ M.LinearOverhead) : M.HasSpeedup := by
  classical
  by_cases hs : M.HasSpeedup
  · exact hs
  · exact False.elim (h (M.noSpeedup_implies_linear_overhead
      (M.noSpeedup_iff_not_hasSpeedup.mpr hs)))

/-- Failure of a linear joint bound gives arbitrarily large reflection lengths
with any prescribed integer factor, not just one fixed factor. -/
theorem not_linear_overhead_arbitrary_factor (h : ¬ M.LinearOverhead)
    (a : Nat) (ha : 1 ≤ a) (K : Nat) :
    ∃ p, K ≤ M.reflection p ∧ a * M.reflection p + M.toll p ≤ M.direct p := by
  classical
  by_cases hw : ∃ p, K ≤ M.reflection p ∧
      a * M.reflection p + M.toll p ≤ M.direct p
  · exact hw
  · exfalso
    apply h
    refine ⟨a + M.tollCoefficient + M.envelope K, ?_⟩
    intro k n
    apply maxList_le
    intro d hd
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hd
    simp only [List.mem_filter, decide_eq_true_eq] at hp
    have hr := (M.mem_short p k).mp hp.1
    have ht := Nat.mul_le_mul_left M.tollCoefficient (Nat.add_le_add_right hp.2 1)
    have har := Nat.mul_le_mul_left a hr
    have hb : M.direct p ≤ a * M.reflection p + M.toll p + M.envelope K := by
      by_cases hk : K ≤ M.reflection p
      · have hx : ¬ (a * M.reflection p + M.toll p ≤ M.direct p) := by
          intro hx
          exact hw ⟨p, hk, hx⟩
        omega
      · have he := M.excess_le_envelope p K (by omega)
        have hd' := M.direct_le_base_add_excess p
        have ha' := Nat.mul_le_mul_right (M.reflection p) ha
        simp only [Nat.one_mul] at ha'
        omega
    unfold toll at hb
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at ht hb ⊢
    omega

end Lengths

end MAISO11.Envelope

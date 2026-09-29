import Std

/-!
An obstruction to a proposed MAIS-O11 witness, including logarithmic
proof-assembly costs. The input inequalities are explicit hypotheses.
This file is not an implementation of PA or its proof-length function.
-/

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Obstruction

def logBudget (r : Nat) : Nat := Nat.log2 (r + 2) + 1

theorem logBudget_mono (x y : Nat) (h : x ≤ y) : logBudget x ≤ logBudget y := by
  have hp : 2 ^ Nat.log2 (x + 2) ≤ y + 2 :=
    Nat.le_trans (Nat.log2_self_le (by omega)) (by omega)
  have hl := (Nat.le_log2 (by omega : y + 2 ≠ 0)).mpr hp
  unfold logBudget
  omega

theorem logBudget_add (x y : Nat) :
    logBudget (x + y + 1) ≤ logBudget x + logBudget (y + 1) := by
  have hsum : x + y + 3 ≤ (x + 2) * (y + 3) := by
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  have hx : x + 2 < 2 ^ logBudget x := Nat.lt_log2_self
  have hy : y + 3 < 2 ^ logBudget (y + 1) := Nat.lt_log2_self
  have hp : x + y + 3 < 2 ^ (logBudget x + logBudget (y + 1)) := by
    rw [Nat.pow_add]
    exact Nat.lt_of_le_of_lt hsum (Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_right hx (by omega : 0 < y + 3))
      (Nat.mul_le_mul_left _ (Nat.le_of_lt hy)))
  have hl := (Nat.log2_lt (by omega : x + y + 3 ≠ 0)).mpr hp
  unfold logBudget at *
  have he : x + y + 1 + 2 = x + y + 3 := by omega
  rw [he]
  omega

def assemblyCoeff (boxLength sentenceLength : Nat) : Nat :=
  (boxLength + sentenceLength + 7) * (2 * logBudget (boxLength + 1) + 5)

theorem normalize_suffix_cost (cost r b s N m : Nat)
    (hN : N ≤ r) (hm : m ≤ b)
    (hcost : cost ≤ (b + s + 7) * (2 * logBudget (N + m + 1) + 3)) :
    cost ≤ assemblyCoeff b s * logBudget r := by
  have hl := Nat.le_trans (logBudget_mono (N + m + 1) (r + b + 1) (by omega))
    (logBudget_add r b)
  have hr : 1 ≤ logBudget r := by simp [logBudget]
  have haux := Nat.mul_le_mul_left (2 * logBudget (b + 1) + 3) hr
  have hfactor : 2 * logBudget (N + m + 1) + 3 ≤
      (2 * logBudget (b + 1) + 5) * logBudget r := by
    simp only [Nat.mul_one, Nat.add_mul] at haux ⊢
    omega
  calc
    cost ≤ (b + s + 7) * (2 * logBudget (N + m + 1) + 3) := hcost
    _ ≤ (b + s + 7) * ((2 * logBudget (b + 1) + 5) * logBudget r) :=
      Nat.mul_le_mul_left _ hfactor
    _ = assemblyCoeff b s * logBudget r := by simp [assemblyCoeff, Nat.mul_assoc]

theorem square_le_four_two_pow (m : Nat) :
    (m + 1) ^ 2 ≤ 4 * 2 ^ m := by
  induction m with
  | zero => decide
  | succ m ih =>
    by_cases hm : m < 2
    · have hm' : m = 0 ∨ m = 1 := by omega
      rcases hm' with rfl | rfl <;> decide
    · have hm2 : 2 ≤ m := by omega
      have hs : 4 ≤ m * m := Nat.mul_le_mul hm2 hm2
      have step : (m + 2) ^ 2 ≤ 2 * (m + 1) ^ 2 := by
        simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul,
          Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
        omega
      calc
        (m + 1 + 1) ^ 2 = (m + 2) ^ 2 := by rw [Nat.add_assoc]
        _ ≤ 2 * (m + 1) ^ 2 := step
        _ ≤ 2 * (4 * 2 ^ m) := Nat.mul_le_mul_left 2 ih
        _ = 4 * 2 ^ (m + 1) := by
          rw [Nat.pow_succ]
          simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem logBudget_square (r : Nat) :
    logBudget r ^ 2 ≤ 4 * (r + 2) := by
  calc
    _ ≤ 4 * 2 ^ Nat.log2 (r + 2) := square_le_four_two_pow _
    _ ≤ 4 * (r + 2) := Nat.mul_le_mul_left 4 (Nat.log2_self_le (by omega))

/-- An explicit inversion of r <= K(log_2(r+2)+1). -/
theorem linear_log_bound (r K : Nat)
    (h : r ≤ K * logBudget r) : r ≤ 8 * K ^ 2 + 1 := by
  by_cases hr : r < 2
  · omega
  · have hr2 : r + 2 ≤ 2 * r := by omega
    have hsq : r ^ 2 ≤ 8 * K ^ 2 * r := by
      calc
        _ ≤ (K * logBudget r) ^ 2 := Nat.pow_le_pow_left h 2
        _ = K ^ 2 * logBudget r ^ 2 := Nat.mul_pow _ _ _
        _ ≤ K ^ 2 * (4 * (r + 2)) := Nat.mul_le_mul_left _ (logBudget_square r)
        _ ≤ K ^ 2 * (4 * (2 * r)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 4 hr2)
        _ = 8 * K ^ 2 * r := by
          simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have hc : r ≤ 8 * K ^ 2 := by
      apply Nat.le_of_mul_le_mul_right _ (by omega : 0 < r)
      simpa [Nat.pow_succ, Nat.pow_zero] using hsq
    omega

/-- Integer form of a factor 1+1/q separation, including a nonnegative toll. -/
def Separation (q direct reflection toll : Nat) : Prop :=
  (q + 1) * reflection + q * toll ≤ q * direct

/-- If a plain proof of Box P gives this assembly bound, a separation
forces its overhead coefficient to be large. No cost hypothesis is hidden. -/
theorem separation_requires_expensive_assembly
    (q direct reflection toll a : Nat)
    (assemble : direct ≤ reflection + a * logBudget reflection)
    (gap : Separation q direct reflection toll) :
    reflection + q * toll ≤ (q * a) * logBudget reflection := by
  have h := Nat.mul_le_mul_left q assemble
  simp only [Nat.mul_add, ← Nat.mul_assoc] at h
  unfold Separation at gap
  rw [Nat.add_mul, Nat.one_mul] at gap
  omega

theorem separation_reflection_bound
    (q direct reflection toll a : Nat)
    (assemble : direct ≤ reflection + a * logBudget reflection)
    (gap : Separation q direct reflection toll) :
    reflection ≤ 8 * (q * a) ^ 2 + 1 := by
  apply linear_log_bound
  have h := separation_requires_expensive_assembly
    q direct reflection toll a assemble gap
  omega

/-- A coarse explicit bound on direct length whenever the proposed gap holds. -/
theorem separation_direct_bound
    (q direct reflection toll a : Nat)
    (assemble : direct ≤ reflection + a * logBudget reflection)
    (gap : Separation q direct reflection toll) :
    direct ≤ (a + 1) * (8 * (q * a) ^ 2 + 4) := by
  have hr := separation_reflection_bound q direct reflection toll a assemble gap
  have hl : logBudget reflection ≤ reflection + 3 := by
    have h := Nat.log2_le_self (reflection + 2)
    unfold logBudget
    omega
  have hml := Nat.mul_le_mul_left a hl
  have hmr := Nat.mul_le_mul_left (a + 1) (by omega :
    reflection + 3 ≤ 8 * (q * a) ^ 2 + 4)
  calc
    direct ≤ reflection + a * (reflection + 3) := by omega
    _ ≤ (a + 1) * (reflection + 3) := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    _ ≤ (a + 1) * (8 * (q * a) ^ 2 + 4) := hmr

/-- All sufficiently large indices, not just an unbounded subsequence. -/
theorem polynomial_lt_exponential (C d n : Nat)
    (large : 8 * (C + d) ^ 2 + 1 < n) :
    C * (n + 1) ^ d < 2 ^ n := by
  have hlin : (C + d) * logBudget n < n := by
    by_cases hn : (C + d) * logBudget n < n
    · exact hn
    · have hb := linear_log_bound n (C + d) (by omega)
      omega
  have hL : 1 ≤ logBudget n := by simp [logBudget]
  have hC : C ≤ 2 ^ C := Nat.le_of_lt Nat.lt_two_pow_self
  have hn : n + 1 ≤ 2 ^ logBudget n := by
    have hh : n + 2 < 2 ^ logBudget n := Nat.lt_log2_self
    omega
  have hCe : C ≤ C * logBudget n := by
    simpa using Nat.mul_le_mul_left C hL
  have he : C + logBudget n * d < n := by
    rw [Nat.add_mul] at hlin
    have hcomm : d * logBudget n = logBudget n * d := Nat.mul_comm _ _
    omega
  calc
    C * (n + 1) ^ d ≤ 2 ^ C * (2 ^ logBudget n) ^ d :=
      Nat.mul_le_mul hC (Nat.pow_le_pow_left hn d)
    _ = 2 ^ (C + logBudget n * d) := by rw [← Nat.pow_mul, ← Nat.pow_add]
    _ < 2 ^ n := Nat.pow_lt_pow_of_lt (by decide) he

def obstructionCoeff (q A : Nat) : Nat :=
  (A + 1) * (8 * (q * A) ^ 2 + 4)

theorem direct_bound_polynomial
    (q direct reflection toll a A e n : Nat)
    (assemble : direct ≤ reflection + a * logBudget reflection)
    (cheap : a ≤ A * (n + 1) ^ e)
    (gap : Separation q direct reflection toll) :
    direct ≤ obstructionCoeff q A * (n + 1) ^ (3 * e) := by
  have hp : 1 ≤ (n + 1) ^ e := Nat.pow_pos (by omega)
  have hp2 : 1 ≤ ((n + 1) ^ e) ^ 2 := Nat.pow_pos hp
  have h1 : a + 1 ≤ (A + 1) * (n + 1) ^ e := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hq := Nat.mul_le_mul_left q cheap
  have hsq := Nat.pow_le_pow_left hq 2
  have hsq' : (q * a) ^ 2 ≤ (q * A) ^ 2 * ((n + 1) ^ e) ^ 2 := by
    simpa [← Nat.mul_assoc, Nat.mul_pow] using hsq
  have h2 : 8 * (q * a) ^ 2 + 4 ≤
      (8 * (q * A) ^ 2 + 4) * ((n + 1) ^ e) ^ 2 := by
    have hh := Nat.mul_le_mul_left 8 hsq'
    have h4 := Nat.mul_le_mul_left 4 hp2
    simp only [Nat.add_mul, Nat.mul_assoc] at *
    omega
  calc
    direct ≤ (a + 1) * (8 * (q * a) ^ 2 + 4) :=
      separation_direct_bound q direct reflection toll a assemble gap
    _ ≤ ((A + 1) * (n + 1) ^ e) *
        ((8 * (q * A) ^ 2 + 4) * ((n + 1) ^ e) ^ 2) := Nat.mul_le_mul h1 h2
    _ = obstructionCoeff q A * (n + 1) ^ (3 * e) := by
      unfold obstructionCoeff
      rw [← Nat.pow_mul]
      have he : 3 * e = e + e * 2 := by omega
      rw [he, Nat.pow_add]
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Explicitly excludes EVERY sufficiently late member of an exponential
lower-bound family with polynomial cheap-box assembly cost. This is a
conditional numerical theorem, not an asserted PA-bin instantiation. -/
theorem no_separation_after
    (direct reflection toll a : Nat → Nat) (q A e n : Nat)
    (assemble : ∀ i, direct i ≤ reflection i + a i * logBudget (reflection i))
    (cheap : ∀ i, a i ≤ A * (i + 1) ^ e)
    (hard : ∀ i, 2 ^ i < direct i)
    (large : 8 * (obstructionCoeff q A + 3 * e) ^ 2 + 1 < n) :
    ¬ Separation q (direct n) (reflection n) (toll n) := by
  intro gap
  have hu := direct_bound_polynomial q (direct n) (reflection n)
    (toll n) (a n) A e n (assemble n) (cheap n) gap
  have hp := polynomial_lt_exponential (obstructionCoeff q A) (3 * e) n large
  have hh := hard n
  omega

end MAISO11.Obstruction

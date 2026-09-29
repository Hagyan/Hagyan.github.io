import Std

/-!
Quantitative consequences used in the mathematical construction.

These theorems assume the displayed numerical bounds. They do not assert
that PA, or PA-bin, satisfies those bounds. The concrete guard syntax is
formalized separately in TaggedSyntax.lean.
-/

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Tagged

/-- Explicit elementary proof that exponentials beat each fixed polynomial. -/
theorem exponential_exceeds_polynomial (C d : Nat) :
    ∃ n : Nat, C * (n + 1) ^ d < 2 ^ n := by
  let t := 2 * d + C + 2
  let n := 2 ^ (2 * t)
  have hCd : C + d < t := by dsimp [t]; omega
  have hdt : 2 * d + 1 ≤ t := by dsimp [t]; omega
  have hlinear : C + (2 * t + 1) * d < (2 * d + 1) * t := by
    simp only [Nat.add_mul, Nat.one_mul]
    have heq : 2 * t * d = 2 * d * t := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [heq]
    omega
  have hsquare : (2 * d + 1) * t ≤ t * t :=
    Nat.mul_le_mul_right t hdt
  have htpow : t ≤ 2 ^ t := Nat.le_of_lt Nat.lt_two_pow_self
  have hnlarge : C + (2 * t + 1) * d < n := by
    calc
      _ < (2 * d + 1) * t := hlinear
      _ ≤ t * t := hsquare
      _ ≤ 2 ^ t * 2 ^ t := Nat.mul_le_mul htpow htpow
      _ = n := by dsimp [n]; rw [← Nat.pow_add]; congr 1; omega
  have hnpos : 0 < n := Nat.pow_pos (by decide)
  have hsucc : n + 1 ≤ 2 ^ (2 * t + 1) := by
    rw [Nat.pow_succ]
    change n + 1 ≤ n * 2
    omega
  have hCpow : C ≤ 2 ^ C := Nat.le_of_lt Nat.lt_two_pow_self
  refine ⟨n, ?_⟩
  calc
    C * (n + 1) ^ d ≤ 2 ^ C * (2 ^ (2 * t + 1)) ^ d :=
      Nat.mul_le_mul hCpow (Nat.pow_le_pow_left hsucc d)
    _ = 2 ^ (C + (2 * t + 1) * d) := by rw [← Nat.pow_mul, ← Nat.pow_add]
    _ < 2 ^ n := Nat.pow_lt_pow_of_lt (by decide) hnlarge

/-- The exponential comparison can be made beyond any prescribed index. -/
theorem exponential_exceeds_polynomial_after (C d start : Nat) :
    ∃ n : Nat, start ≤ n ∧ C * (n + 1) ^ d < 2 ^ n := by
  obtain ⟨j, hj⟩ := exponential_exceeds_polynomial
    (C * (start + 1) ^ d) d
  refine ⟨start + j, by omega, ?_⟩
  have hbase : start + j + 1 ≤ (start + 1) * (j + 1) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  calc
    C * (start + j + 1) ^ d ≤ C * ((start + 1) * (j + 1)) ^ d :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase d)
    _ = (C * (start + 1) ^ d) * (j + 1) ^ d := by
      rw [Nat.mul_pow, Nat.mul_assoc]
    _ < 2 ^ j := hj
    _ ≤ 2 ^ (start + j) := Nat.pow_le_pow_right (by decide) (by omega)

/-- Part 1's factor-two inequality follows from the proposed family's bounds.
`direct` and `reflection` are intended to be MINIMUM object-proof lengths;
the theorem does not define them or infer the hypotheses for any calculus. -/
theorem factor_two_after
    (direct reflection sentenceSize : Nat → Nat) (a b d : Nat)
    (hard : ∀ n, 2 ^ n < direct n)
    (shortReflection : ∀ n, reflection n ≤ a * (n + 1) ^ d)
    (smallSentence : ∀ n, sentenceSize n + 1 ≤ b * (n + 1) ^ d)
    (C1 start : Nat) :
    ∃ n, start ≤ n ∧
      2 * reflection n + C1 * (sentenceSize n + 1) < direct n := by
  obtain ⟨n, hn, hpow⟩ :=
    exponential_exceeds_polynomial_after (2 * a + C1 * b) d start
  refine ⟨n, hn, ?_⟩
  have hsum : 2 * reflection n + C1 * (sentenceSize n + 1)
      ≤ (2 * a + C1 * b) * (n + 1) ^ d := by
    calc
      _ ≤ 2 * (a * (n + 1) ^ d) + C1 * (b * (n + 1) ^ d) :=
        Nat.add_le_add (Nat.mul_le_mul_left 2 (shortReflection n))
          (Nat.mul_le_mul_left C1 (smallSentence n))
      _ = _ := by simp [Nat.add_mul, Nat.mul_assoc]
  exact Nat.lt_trans (Nat.lt_of_le_of_lt hsum hpow) (hard n)

/-- Exponential direct lower bounds and polynomial-size inputs preclude
every polynomial overhead bound for that family. -/
theorem no_polynomial_overhead
    (direct reflection sentenceSize : Nat → Nat) (a d : Nat)
    (hard : ∀ n, 2 ^ n < direct n)
    (inputBound : ∀ n,
      reflection n + sentenceSize n + 1 ≤ a * (n + 1) ^ d) :
    ¬ ∃ C e : Nat, ∀ n,
      direct n ≤ C * (reflection n + sentenceSize n + 1) ^ e := by
  rintro ⟨C, e, upper⟩
  obtain ⟨n, hn⟩ := exponential_exceeds_polynomial (C * a ^ e) (d * e)
  have hle : direct n ≤ (C * a ^ e) * (n + 1) ^ (d * e) := by
    calc
      _ ≤ C * (reflection n + sentenceSize n + 1) ^ e := upper n
      _ ≤ C * (a * (n + 1) ^ d) ^ e :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_left (inputBound n) e)
      _ = _ := by rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc]
  have hhard := hard n
  omega

/-- Abstract arithmetic at the end of the bridge argument. If every bridge
proof plus polynomial overhead exceeds 2^n, the bridges have no polynomial
size bound. The proof-file composition establishing `bridgeLower` remains
an explicit hypothesis here. -/
theorem no_polynomial_bridges (bridgeLength : Nat → Nat) (Q d : Nat)
    (bridgeLower : ∀ n, 2 ^ n < bridgeLength n + Q * (n + 1) ^ d) :
    ¬ ∃ C e : Nat, ∀ n, bridgeLength n ≤ C * (n + 1) ^ e := by
  rintro ⟨C, e, upper⟩
  let D := max d e
  obtain ⟨n, hn⟩ := exponential_exceeds_polynomial (C + Q) D
  have he : (n + 1) ^ e ≤ (n + 1) ^ D :=
    Nat.pow_le_pow_right (by omega) (Nat.le_max_right d e)
  have hd : (n + 1) ^ d ≤ (n + 1) ^ D :=
    Nat.pow_le_pow_right (by omega) (Nat.le_max_left d e)
  have hsum : bridgeLength n + Q * (n + 1) ^ d ≤ (C + Q) * (n + 1) ^ D := by
    calc
      _ ≤ C * (n + 1) ^ e + Q * (n + 1) ^ d :=
        Nat.add_le_add_right (upper n) _
      _ ≤ C * (n + 1) ^ D + Q * (n + 1) ^ D :=
        Nat.add_le_add (Nat.mul_le_mul_left C he) (Nat.mul_le_mul_left Q hd)
      _ = _ := by rw [Nat.add_mul]
  have hlow := bridgeLower n
  omega

end MAISO11.Tagged

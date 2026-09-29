import FirstPass

/-!
MAIS-O11: audit of the proposed transition to the fixed PA_bin problem.

This file does not instantiate a PA proof checker. It proves that the previous
separation hypotheses contradict polynomial Loeb overhead, and it gives a
quantitative conversion theorem with all proof-operation costs explicit.
Neither PA_bin(1) nor PA_bin(2) is asserted here.
-/

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11

/-- A polynomial upper bound for converting arbitrary reflection certificates. -/
def PolynomialLobBound {F : Type} (S : ProofSystem F)
    (imp : F → F → F) (box : F → F) (size : F → Nat) : Prop :=
  ∃ C d : Nat, ∀ (A : F) (r : S.Proof (imp (box A) A)),
    ∃ p : S.Proof A, S.length p ≤ C * (S.length r + size A + 1) ^ d

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

theorem exponential_exceeds_shifted_polynomial (C d : Nat) :
    ∃ n : Nat, C * (n + 2) ^ d < 2 ^ n := by
  obtain ⟨n, hn⟩ := exponential_exceeds_polynomial (C * 2 ^ d) d
  refine ⟨n, ?_⟩
  have hshift : n + 2 ≤ 2 * (n + 1) := by omega
  calc
    C * (n + 2) ^ d ≤ C * (2 * (n + 1)) ^ d :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left hshift d)
    _ = (C * 2 ^ d) * (n + 1) ^ d := by rw [Nat.mul_pow, Nat.mul_assoc]
    _ < 2 ^ n := hn

/--
The first-pass interface already implies superpolynomial Loeb overhead.
Consequently it cannot instantiate PA_bin if the polynomial conjecture holds.
This is an incompatibility theorem, not a decision of that conjecture.
-/
theorem first_pass_excludes_polynomial_overhead {F G : Type}
    {B : ProofSystem F} {S : ProofSystem G} (H : SeparationHypotheses B S) :
    ¬ PolynomialLobBound S H.logic.imp H.logic.box H.sentenceSize := by
  rintro ⟨Q, d, hpoly⟩
  let K := Q * (H.a + H.b) ^ d
  obtain ⟨j, hj⟩ := exponential_exceeds_shifted_polynomial (H.C * (K + 1)) d
  let n := 2 ^ j
  obtain ⟨p, hp⟩ := hpoly (H.target n) (H.reflectionProof n)
  have hlog : logSize n = j + 2 := by simp [n, logSize, Nat.log2_two_pow]
  have hr := H.reflectionBound n
  have hs := H.sizeBound n
  rw [hlog] at hr hs
  have hinput : S.length (H.reflectionProof n) + H.sentenceSize (H.target n) + 1
      ≤ (H.a + H.b) * (j + 2) := by
    rw [Nat.add_mul]
    omega
  have hp' : S.length p ≤ K * (j + 2) ^ d := by
    calc
      _ ≤ Q * (S.length (H.reflectionProof n) + H.sentenceSize (H.target n) + 1) ^ d := hp
      _ ≤ Q * ((H.a + H.b) * (j + 2)) ^ d :=
        Nat.mul_le_mul_left Q (Nat.pow_le_pow_left hinput d)
      _ = K * (j + 2) ^ d := by rw [Nat.mul_pow]; simp [K, Nat.mul_assoc]
  have hpowpos : 1 ≤ (j + 2) ^ d := Nat.pow_pos (by omega)
  have hp1 : S.length p + 1 ≤ (K + 1) * (j + 2) ^ d := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hupper : H.C * (S.length p + 1) < n := by
    calc
      _ ≤ H.C * ((K + 1) * (j + 2) ^ d) := Nat.mul_le_mul_left H.C hp1
      _ = (H.C * (K + 1)) * (j + 2) ^ d := by rw [Nat.mul_assoc]
      _ < n := hj
  have hlower := H.direct_lower_bound n p
  omega

/-- Internal Loeb's axiom from HBL, diagonalization and propositional reasoning. -/
theorem internal_lob_axiom {F : Type} {S : ProofSystem F}
    (L : LobConditions S)
    (precompose : ∀ A B C : F, Provable S (L.imp A B) →
      Provable S (L.imp (L.imp B C) (L.imp A C))) (A : F) :
    Provable S (L.imp (L.box (L.imp (L.box A) A)) (L.box A)) := by
  obtain ⟨G, hForward, hBackward⟩ := L.fixedPoint A
  have h1 := L.necessitate _ hForward
  have h2 := L.mp _ _ (L.boxMP G (L.imp (L.box G) A)) h1
  have h3 := L.chain _ _ _ h2 (L.boxMP (L.box G) A)
  have h4 := L.underMP _ _ _ h3 (L.boxBox G)
  have h5 := precompose (L.box G) (L.box A) A h4
  have hRG := L.chain _ _ _ h5 hBackward
  have h6 := L.mp _ _ (L.boxMP (L.imp (L.box A) A) G) (L.necessitate _ hRG)
  exact L.chain _ _ _ h6 h4

/--
Primitive proof operations and their costs. No concrete PA instance is supplied.
`notice` and `lob` are certificate-producing functions, with separate bounds.
-/
structure QuantitativeLobTools {F : Type} (S : ProofSystem F)
    (imp : F → F → F) (box : F → F) (size : F → Nat) where
  mp : ∀ A B : F, S.Proof (imp A B) → S.Proof A → S.Proof B
  mpCost : Nat
  mp_bound : ∀ (A B : F) (p : S.Proof (imp A B)) (q : S.Proof A),
    S.length (mp A B p q) ≤ S.length p + S.length q + mpCost * (size A + size B + 1)
  notice : ∀ (A : F), S.Proof (imp (box A) A) → S.Proof (box (imp (box A) A))
  noticeCoeff : Nat
  noticeDegree : Nat
  notice_bound : ∀ (A : F) (r : S.Proof (imp (box A) A)),
    S.length (notice A r) ≤ noticeCoeff * (S.length r + size A + 1) ^ noticeDegree
  lob : ∀ A : F, S.Proof (imp (box (imp (box A) A)) (box A))
  lobCoeff : Nat
  lobDegree : Nat
  lob_bound : ∀ A : F, S.length (lob A) ≤ lobCoeff * (size A + 1) ^ lobDegree
  boxCoeff : Nat
  box_bound : ∀ A : F, size (box A) ≤ boxCoeff * (size A + 1)
  reflectionCoeff : Nat
  reflection_bound : ∀ A : F, size (imp (box A) A) ≤ reflectionCoeff * (size A + 1)

namespace QuantitativeLobTools

variable {F : Type} {S : ProofSystem F}
  {imp : F → F → F} {box : F → F} {size : F → Nat}

/-- Construct the direct certificate, rather than assume a conversion exists. -/
def convert (T : QuantitativeLobTools S imp box size) (A : F)
    (r : S.Proof (imp (box A) A)) : S.Proof A :=
  T.mp (box A) A r
    (T.mp (box (imp (box A) A)) (box A) (T.lob A) (T.notice A r))

theorem exact_cost (T : QuantitativeLobTools S imp box size) (A : F)
    (r : S.Proof (imp (box A) A)) :
    S.length (T.convert A r) ≤
      S.length r + S.length (T.lob A) + S.length (T.notice A r) +
      T.mpCost * (size (box (imp (box A) A)) + size (box A) + 1) +
      T.mpCost * (size (box A) + size A + 1) := by
  have h1 := T.mp_bound (box (imp (box A) A)) (box A) (T.lob A) (T.notice A r)
  have h2 := T.mp_bound (box A) A r
    (T.mp (box (imp (box A) A)) (box A) (T.lob A) (T.notice A r))
  change S.length (T.convert A r) ≤ _ at h2
  omega

def assemblyCoeff (T : QuantitativeLobTools S imp box size) : Nat :=
  T.mpCost * (T.boxCoeff * (T.reflectionCoeff + 3) + 2)

theorem assembly_bound (T : QuantitativeLobTools S imp box size) (A : F) :
    T.mpCost * (size (box (imp (box A) A)) + size (box A) + 1) +
      T.mpCost * (size (box A) + size A + 1)
    ≤ T.assemblyCoeff * (size A + 1) := by
  let t := size A + 1
  have hsize : size (imp (box A) A) + 1 ≤ (T.reflectionCoeff + 1) * t := by
    have h := T.reflection_bound A
    dsimp [t]
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hbR : size (box (imp (box A) A)) ≤ T.boxCoeff * ((T.reflectionCoeff + 1) * t) :=
    Nat.le_trans (T.box_bound _) (Nat.mul_le_mul_left T.boxCoeff hsize)
  have hb : size (box A) ≤ T.boxCoeff * t := T.box_bound A
  have htotal : size (box (imp (box A) A)) + size (box A) + 1 +
      (size (box A) + size A + 1)
      ≤ (T.boxCoeff * (T.reflectionCoeff + 3) + 2) * t := by
    have hunit : size A + 2 ≤ 2 * t := by dsimp [t]; omega
    calc
      _ ≤ T.boxCoeff * ((T.reflectionCoeff + 1) * t) +
          (T.boxCoeff * t + T.boxCoeff * t) + 2 * t := by omega
      _ = (T.boxCoeff * (T.reflectionCoeff + 3) + 2) * t := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_succ, Nat.succ_mul,
          Nat.mul_zero, Nat.zero_mul, Nat.one_mul, Nat.mul_one, Nat.mul_assoc]
        omega
  calc
    _ = T.mpCost * (size (box (imp (box A) A)) + size (box A) + 1 +
        (size (box A) + size A + 1)) := by simp only [Nat.mul_add]
    _ ≤ T.mpCost * ((T.boxCoeff * (T.reflectionCoeff + 3) + 2) * t) :=
      Nat.mul_le_mul_left T.mpCost htotal
    _ = T.assemblyCoeff * (size A + 1) := by simp [assemblyCoeff, t, Nat.mul_assoc]

theorem budget (T : QuantitativeLobTools S imp box size) (A : F)
    (r : S.Proof (imp (box A) A)) :
    S.length (T.convert A r) ≤ S.length r +
      T.noticeCoeff * (S.length r + size A + 1) ^ T.noticeDegree +
      T.lobCoeff * (size A + 1) ^ T.lobDegree +
      T.assemblyCoeff * (size A + 1) := by
  have h := T.exact_cost A r
  have hn := T.notice_bound A r
  have hl := T.lob_bound A
  have ha := T.assembly_bound A
  omega

def degree (T : QuantitativeLobTools S imp box size) : Nat :=
  max (max T.noticeDegree T.lobDegree) 1

def coefficient (T : QuantitativeLobTools S imp box size) : Nat :=
  1 + T.noticeCoeff + T.lobCoeff + T.assemblyCoeff

/-- A proved polynomial bound for the constructed conversion, under the fields. -/
theorem convert_polynomial_bound (T : QuantitativeLobTools S imp box size)
    (A : F) (r : S.Proof (imp (box A) A)) :
    S.length (T.convert A r) ≤
      T.coefficient * (S.length r + size A + 1) ^ T.degree := by
  let z := S.length r + size A + 1
  have hz : 0 < z := by dsimp [z]; omega
  have hd1 : 1 ≤ T.degree := Nat.le_max_right _ _
  have hdn : T.noticeDegree ≤ T.degree :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hdl : T.lobDegree ≤ T.degree :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hzpow : z ≤ z ^ T.degree := Nat.le_pow (by omega)
  have hk : S.length r ≤ z ^ T.degree := Nat.le_trans (by dsimp [z]; omega) hzpow
  have hn : z ^ T.noticeDegree ≤ z ^ T.degree := Nat.pow_le_pow_right hz hdn
  have hl : (size A + 1) ^ T.lobDegree ≤ z ^ T.degree :=
    Nat.le_trans (Nat.pow_le_pow_left (by dsimp [z]; omega) T.lobDegree)
      (Nat.pow_le_pow_right hz hdl)
  have ha : size A + 1 ≤ z ^ T.degree :=
    Nat.le_trans (by dsimp [z]; omega) hzpow
  calc
    _ ≤ S.length r + T.noticeCoeff * z ^ T.noticeDegree +
        T.lobCoeff * (size A + 1) ^ T.lobDegree + T.assemblyCoeff * (size A + 1) :=
      T.budget A r
    _ ≤ z ^ T.degree + T.noticeCoeff * z ^ T.degree +
        T.lobCoeff * z ^ T.degree + T.assemblyCoeff * z ^ T.degree :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hk
        (Nat.mul_le_mul_left T.noticeCoeff hn)) (Nat.mul_le_mul_left T.lobCoeff hl))
        (Nat.mul_le_mul_left T.assemblyCoeff ha)
    _ = T.coefficient * z ^ T.degree := by simp [coefficient, Nat.add_mul]

theorem polynomial_overhead (T : QuantitativeLobTools S imp box size) :
    PolynomialLobBound S imp box size :=
  ⟨T.coefficient, T.degree, fun A r => ⟨T.convert A r, T.convert_polynomial_bound A r⟩⟩

/-- The two-parameter form needed to bound the maximum defining F_S(k,n). -/
theorem uniform_budget (T : QuantitativeLobTools S imp box size)
    (k n : Nat) (A : F) (r : S.Proof (imp (box A) A))
    (hr : S.length r ≤ k) (hA : size A ≤ n) :
    ∃ p : S.Proof A, S.length p ≤ T.coefficient * (k + n + 1) ^ T.degree := by
  refine ⟨T.convert A r, ?_⟩
  exact Nat.le_trans (T.convert_polynomial_bound A r)
    (Nat.mul_le_mul_left T.coefficient
      (Nat.pow_le_pow_left (by omega) T.degree))

/-- Linear noticing yields a bound linear in the supplied premise-proof length. -/
theorem linear_premise_bound (T : QuantitativeLobTools S imp box size)
    (hdegree : T.noticeDegree ≤ 1) (A : F) (r : S.Proof (imp (box A) A)) :
    S.length (T.convert A r) ≤
      (T.noticeCoeff + 1) * S.length r +
      (T.noticeCoeff + T.lobCoeff + T.assemblyCoeff) *
        (size A + 1) ^ (max T.lobDegree 1) := by
  let t := size A + 1
  let d := max T.lobDegree 1
  have hd : 0 < d := by have h := Nat.le_max_right T.lobDegree 1; dsimp [d]; omega
  have ht : 0 < t := by dsimp [t]; omega
  have htpow : t ≤ t ^ d := Nat.le_pow hd
  have hnotice : (S.length r + size A + 1) ^ T.noticeDegree
      ≤ S.length r + t := by
    have h := Nat.pow_le_pow_right (by omega : 0 < S.length r + size A + 1) hdegree
    simpa [t] using h
  have hlob : t ^ T.lobDegree ≤ t ^ d :=
    Nat.pow_le_pow_right ht (Nat.le_max_left _ _)
  have h := T.budget A r
  have hn := Nat.mul_le_mul_left T.noticeCoeff hnotice
  have hl := Nat.mul_le_mul_left T.lobCoeff hlob
  have ha := Nat.mul_le_mul_left T.assemblyCoeff htpow
  have ht' := Nat.mul_le_mul_left T.noticeCoeff htpow
  change S.length (T.convert A r) ≤
    (T.noticeCoeff + 1) * S.length r +
      (T.noticeCoeff + T.lobCoeff + T.assemblyCoeff) * t ^ d
  change S.length (T.convert A r) ≤ S.length r +
    T.noticeCoeff * (S.length r + size A + 1) ^ T.noticeDegree +
    T.lobCoeff * t ^ T.lobDegree + T.assemblyCoeff * t at h
  simp only [Nat.mul_add] at hn
  simp only [Nat.add_mul, Nat.one_mul]
  omega

end QuantitativeLobTools

theorem first_pass_and_polynomial_tools_incompatible {F G : Type}
    {B : ProofSystem F} {S : ProofSystem G} (H : SeparationHypotheses B S)
    (T : QuantitativeLobTools S H.logic.imp H.logic.box H.sentenceSize) : False :=
  first_pass_excludes_polynomial_overhead H T.polynomial_overhead

end MAISO11

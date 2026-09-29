import PadBounds

/-!
A quadratic terminal fee for a family of conclusions is incompatible with
constant-cost modus ponens when a fixed cheaply provable antecedent has
affine-size implications into those conclusions.  The theorem isolates the
exact numerical obligations; the accompanying note explains their source
in the proposed artificial proof presentation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.PaddingLoophole

/-- `s` is the size of the chosen conclusion; `imp` is a proof length for an
implication from a fixed theorem into that conclusion; `d` is the shortest
direct proof length.  The last hypothesis is what a constant-cost MP assembly
operation would provide. -/
theorem quadratic_fee_excludes_constant_mp
    (s imp d : Nat → Nat) (a b antecedentCost mpCost : Nat)
    (sizes_cofinal : ∀ N, ∃ i, N ≤ s i)
    (imp_affine : ∀ i, imp i ≤ a * (s i + 1) + b)
    (terminal_fee : ∀ i, (s i + 1)^2 ≤ d i)
    (mp_assembly : ∀ i, d i ≤ antecedentCost + imp i + mpCost) : False := by
  obtain ⟨i, hi⟩ := sizes_cofinal
    (2*a + (antecedentCost+mpCost+1) + 2*b)
  have hq := quadratic_padding_dominates a b (antecedentCost+mpCost+1)
    (s i) hi
  have hx : 1 ≤ s i + 1 := by omega
  have hm : antecedentCost+mpCost+1 ≤
      (antecedentCost+mpCost+1)*(s i+1) := by
    simpa using Nat.mul_le_mul_left (antecedentCost+mpCost+1) hx
  have hd := terminal_fee i
  have hp := imp_affine i
  have ha := mp_assembly i
  omega

#print axioms quadratic_fee_excludes_constant_mp

end MAISO11.PaddingLoophole

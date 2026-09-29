import Std

/-!
The logical obstruction for a finite Goedel sentence, with every required
object-theory fact visible as a hypothesis. This is an abstract object logic,
not Lean's own implication and not a PA arithmetization.
-/

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Obstruction

structure ClassicalProvability (F : Type) where
  proves : F → Prop
  imp : F → F → F
  neg : F → F
  box : F → F
  mp : ∀ {A B}, proves (imp A B) → proves A → proves B
  chain : ∀ {A B C}, proves (imp A B) → proves (imp B C) → proves (imp A C)
  cases : ∀ {A B}, proves (imp A B) → proves (imp (neg A) B) → proves B
  necessitate : ∀ {A}, proves A → proves (box A)
  distribute : ∀ A B, proves (imp (box (imp A B)) (imp (box A) (box B)))

/-- B is the bounded assertion that P has a short proof. The reverse
diagonal implication is (not B) -> P. Completeness for (not B), together
with dropping the proof-length bound, proves Box P in BOTH cases.
No consistency assumption and no proof of P is an input. -/
theorem finite_diagonal_box {F : Type} (L : ClassicalProvability F) (B P : F)
    (diagonalReverse : L.proves (L.imp (L.neg B) P))
    (boundedCompleteness : L.proves (L.imp (L.neg B) (L.box (L.neg B))))
    (dropBound : L.proves (L.imp B (L.box P))) :
    L.proves (L.box P) := by
  have boxedReverse := L.necessitate diagonalReverse
  have boxMap : L.proves (L.imp (L.box (L.neg B)) (L.box P)) :=
    L.mp (L.distribute (L.neg B) P) boxedReverse
  exact L.cases dropBound (L.chain boundedCompleteness boxMap)

/-- Once Box P is available, the reflection instance is equivalent to P
over this object theory. This theorem asserts derivability, not a size bound. -/
theorem reflection_iff_target_of_box {F : Type} (L : ClassicalProvability F) (P : F)
    (boxed : L.proves (L.box P))
    (weaken : L.proves P → L.proves (L.imp (L.box P) P)) :
    L.proves (L.imp (L.box P) P) ↔ L.proves P := by
  constructor
  · intro reflected
    exact L.mp reflected boxed
  · exact weaken

/-- Pointwise conversion using an internal Loeb axiom. This syntax has
no object-level quantifier, so this is NOT a formalization of a uniform
PA theorem with a free numerical parameter. -/
theorem boxed_reflection_to_box_target {F : Type} (L : ClassicalProvability F)
    (P : F)
    (internalLob : L.proves (L.imp (L.box (L.imp (L.box P) P)) (L.box P)))
    (boxedReflection : L.proves (L.box (L.imp (L.box P) P))) :
    L.proves (L.box P) := by
  exact L.mp internalLob boxedReflection

end MAISO11.Obstruction

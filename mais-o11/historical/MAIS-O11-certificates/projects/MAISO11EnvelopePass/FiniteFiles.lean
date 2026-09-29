import Envelope

/-!
Derive the finite-budget lists from proof files over a finite alphabet.
The decoder is a parameter, so this applies to compressed and uncompressed
formats alike. No claim is made to implement PA-bin's decoder here.
-/

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Envelope.FiniteFiles

def words (a : Nat) : Nat → List (List (Fin a))
  | 0 => [[]]
  | k + 1 => [] :: (List.finRange a).flatMap
      (fun c => (words a k).map (fun w => c :: w))

theorem mem_words (a k : Nat) (w : List (Fin a)) :
    w ∈ words a k ↔ w.length ≤ k := by
  induction k generalizing w with
  | zero => simp [words, List.length_eq_zero_iff]
  | succ k ih =>
    cases w with
    | nil => simp [words]
    | cons c w =>
      constructor
      · intro h
        simp only [words, List.mem_cons, List.cons_ne_nil, false_or,
          List.mem_flatMap, List.mem_map] at h
        obtain ⟨c', _, w', hw', he⟩ := h
        have he' : w' = w := (List.cons.inj he).2
        subst w'
        have hl := (ih w).mp hw'
        simp only [List.length_cons]
        omega
      · intro h
        have hw : w ∈ words a k := (ih w).mpr (by simpa using h)
        apply List.mem_cons_of_mem
        apply List.mem_flatMap.mpr
        refine ⟨c, ?_, List.mem_map.mpr ⟨w, hw, rfl⟩⟩
        simp [List.finRange, List.mem_ofFn]

def targets {α : Type} (a : Nat) (decode : List (Fin a) → Option α) (k : Nat) : List α :=
  (words a k).filterMap decode

theorem mem_targets {α : Type} (a : Nat) (decode : List (Fin a) → Option α)
    (k : Nat) (p : α) :
    p ∈ targets a decode k ↔
      ∃ w, w.length ≤ k ∧ decode w = some p := by
  simp only [targets, List.mem_filterMap, mem_words]

/-- `minimum_spec` is the defining property of shortest reflection length.
It is not an asymptotic or internalization hypothesis. -/
def toLengths {α : Type} (a : Nat) (decode : List (Fin a) → Option α)
    (direct reflection size : α → Nat) (c : Nat)
    (minimum_spec : ∀ p k, reflection p ≤ k ↔
      ∃ w, w.length ≤ k ∧ decode w = some p) : Lengths α where
  direct := direct
  reflection := reflection
  size := size
  tollCoefficient := c
  short := targets a decode
  mem_short := fun p k => (mem_targets a decode k p).trans (minimum_spec p k).symm

end MAISO11.Envelope.FiniteFiles

import LocalCertificates

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Quotation

/-- The first definition is the incomplete prefix `(>`, not a term or formula. -/
def boundaryExample : Grammar 128 3 :=
  .snoc
    (.snoc
      (.snoc .nil [.char ⟨40, by decide⟩, .char ⟨62, by decide⟩])
      [.char ⟨40, by decide⟩, .char ⟨61, by decide⟩, .char ⟨48, by decide⟩,
       .char ⟨48, by decide⟩, .char ⟨41, by decide⟩])
    [.use (Fin.castSucc (Fin.last 0)), .use (Fin.last 1), .use (Fin.last 1), .char ⟨41, by decide⟩]

theorem boundaryExample_expansion :
    (boundaryExample.words (Fin.last 2)).map Fin.val =
      [40, 62, 40, 61, 48, 48, 41, 40, 61, 48, 48, 41, 41] := by
  simp only [boundaryExample, Grammar.words, expandFragment, Atom.expand,
    Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem boundaryExample_mass : boundaryExample.mass = 14 := by decide

def doubling {b : Nat} (a : Fin b) : (n : Nat) → Grammar b (n + 1)
  | 0 => .snoc .nil [.char a]
  | n + 1 => .snoc (doubling a n) [.use (Fin.last n), .use (Fin.last n)]

theorem doubling_length {b : Nat} (a : Fin b) (n : Nat) :
    ((doubling a n).words (Fin.last n)).length = 2 ^ n := by
  induction n with
  | zero =>
    simp only [doubling, Grammar.words, expandFragment, Atom.expand,
      Fin.lastCases_last, List.append_nil, List.length_cons, List.length_nil, Nat.pow_zero]
  | succ n ih =>
    simp only [doubling, Grammar.words, Fin.lastCases_last, expandFragment,
      Atom.expand, List.append_nil, List.length_append, ih, Nat.pow_succ]
    omega

theorem doubling_mass {b : Nat} (a : Fin b) (n : Nat) :
    (doubling a n).mass = 3 * n + 2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [doubling, Grammar.mass, ih]; omega

theorem doubling_quoted_length {b : Nat} (a : Fin b) (n : Nat) :
    ((compile (doubling a n)).eval (Fin.last n)).len = 2 ^ n := by
  rw [compile_length, doubling_length]

end MAISO11.Quotation

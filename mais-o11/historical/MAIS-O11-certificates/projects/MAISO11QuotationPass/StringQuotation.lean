import Std

/-!
Quotation of arbitrary string-fragment abbreviations into arithmetic terms.
There is no restriction that a fragment be a term, formula, or subtree.

This is NOT a formalization of the PA proof predicate Bew. Theorems below are
about the compiler, its denotation, and its size. See LocalCertificates for
the small object-language proof segment generated from its definitions.
-/

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Quotation

abbrev Word (b : Nat) := List (Fin b)

/-- Unmarked big-endian base-b value. Length is retained separately. -/
def rawCode (b : Nat) : Word b → Nat
  | [] => 0
  | a :: w => a.val * b ^ w.length + rawCode b w

theorem rawCode_append (b : Nat) (x y : Word b) :
    rawCode b (x ++ y) = rawCode b x * b ^ y.length + rawCode b y := by
  induction x with
  | nil => simp [rawCode]
  | cons a x ih =>
    simp only [List.cons_append, rawCode, List.length_append, Nat.pow_add, ih]
    simp [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

theorem rawCode_lt_scale (b : Nat) (w : Word b) : rawCode b w < b ^ w.length := by
  induction w with
  | nil => simp [rawCode]
  | cons a w ih =>
    have h₁ := Nat.add_lt_add_left ih (a.val * b ^ w.length)
    have h₂ := Nat.mul_le_mul_right (b ^ w.length) (Nat.succ_le_of_lt a.isLt)
    simp only [rawCode, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_comm (b ^ w.length) b]
    have hh : a.val * b ^ w.length + b ^ w.length = (a.val + 1) * b ^ w.length := by
      simp [Nat.add_mul]
    rw [hh] at h₁
    exact Nat.lt_of_lt_of_le h₁ h₂

structure Value where
  len : Nat
  scale : Nat
  payload : Nat
  deriving DecidableEq, Repr

def quoteWord (b : Nat) (w : Word b) : Value :=
  ⟨w.length, b ^ w.length, rawCode b w⟩

def Value.append (x y : Value) : Value :=
  ⟨x.len + y.len, x.scale * y.scale, x.payload * y.scale + y.payload⟩

@[simp] theorem quoteWord_append (b : Nat) (x y : Word b) :
    quoteWord b (x ++ y) = (quoteWord b x).append (quoteWord b y) := by
  simp [quoteWord, Value.append, List.length_append, Nat.pow_add, rawCode_append]

inductive Atom (b n : Nat) where
  | char : Fin b → Atom b n
  | use : Fin n → Atom b n
  deriving DecidableEq, Repr

abbrev Fragment (b n : Nat) := List (Atom b n)

def Atom.expand {b n : Nat} (ρ : Fin n → Word b) : Atom b n → Word b
  | .char a => [a]
  | .use i => ρ i

def expandFragment {b n : Nat} (ρ : Fin n → Word b) : Fragment b n → Word b
  | [] => []
  | a :: r => a.expand ρ ++ expandFragment ρ r

/-- Fresh definitions in order. References can only name earlier definitions. -/
inductive Grammar (b : Nat) : Nat → Type where
  | nil : Grammar b 0
  | snoc {n : Nat} : Grammar b n → Fragment b n → Grammar b (n + 1)
  deriving Repr

def Grammar.words {b n : Nat} : Grammar b n → Fin n → Word b
  | .nil => Fin.elim0
  | .snoc g r => Fin.lastCases (expandFragment g.words r) g.words

/-- Every atom and every definition costs at least one written character. -/
def Grammar.mass {b n : Nat} : Grammar b n → Nat
  | .nil => 0
  | .snoc g r => g.mass + r.length + 1

theorem Grammar.count_le_mass {b n : Nat} (g : Grammar b n) : n ≤ g.mass := by
  induction g with
  | nil => exact Nat.le_refl 0
  | snoc g r ih => simp only [mass]; omega

inductive Slot where
  | len | scale | payload
  deriving DecidableEq, Repr

def Slot.offset : Slot → Nat
  | .len => 0
  | .scale => 1
  | .payload => 2

theorem Slot.offset_le_two (s : Slot) : s.offset ≤ 2 := by cases s <;> decide

def Value.get (v : Value) : Slot → Nat
  | .len => v.len
  | .scale => v.scale
  | .payload => v.payload

/-- Arithmetic terms with references to previously defined triples only. -/
inductive Expr (n : Nat) where
  | num : Nat → Expr n
  | ref : Fin n → Slot → Expr n
  | add : Expr n → Expr n → Expr n
  | mul : Expr n → Expr n → Expr n
  deriving DecidableEq, Repr

def Expr.eval {n : Nat} (ρ : Fin n → Value) : Expr n → Nat
  | .num k => k
  | .ref i s => (ρ i).get s
  | .add x y => x.eval ρ + y.eval ρ
  | .mul x y => x.eval ρ * y.eval ρ

/-- Deliberately coarse weight, including the numeric values of small constants.
The compiler only uses 0, 1, b and alphabet digits less than b. -/
def Expr.weight {n : Nat} : Expr n → Nat
  | .num k => k + 1
  | .ref _ _ => 1
  | .add x y => 1 + x.weight + y.weight
  | .mul x y => 1 + x.weight + y.weight

structure Triple (n : Nat) where
  len : Expr n
  scale : Expr n
  payload : Expr n
  deriving DecidableEq, Repr

def Triple.eval {n : Nat} (ρ : Fin n → Value) (t : Triple n) : Value :=
  ⟨t.len.eval ρ, t.scale.eval ρ, t.payload.eval ρ⟩

def Triple.weight {n : Nat} (t : Triple n) : Nat :=
  t.len.weight + t.scale.weight + t.payload.weight

def emptyTriple (n : Nat) : Triple n := ⟨.num 0, .num 1, .num 0⟩

def quoteAtom {b n : Nat} : Atom b n → Triple n
  | .char a => ⟨.num 1, .num b, .num a.val⟩
  | .use i => ⟨.ref i .len, .ref i .scale, .ref i .payload⟩

def Triple.cat {n : Nat} (x y : Triple n) : Triple n :=
  ⟨.add x.len y.len, .mul x.scale y.scale,
   .add (.mul x.payload y.scale) y.payload⟩

def quoteFragment {b n : Nat} : Fragment b n → Triple n
  | [] => emptyTriple n
  | a :: r => (quoteAtom a).cat (quoteFragment r)

theorem quoteAtom_correct {b n : Nat} (ρ : Fin n → Word b) (a : Atom b n) :
    (quoteAtom a).eval (fun i => quoteWord b (ρ i)) = quoteWord b (a.expand ρ) := by
  cases a <;> simp [quoteAtom, Triple.eval, Expr.eval, Atom.expand, quoteWord,
    rawCode, Value.get]

theorem Triple.eval_cat {n : Nat} (ρ : Fin n → Value) (x y : Triple n) :
    (x.cat y).eval ρ = (x.eval ρ).append (y.eval ρ) := rfl

theorem quoteFragment_correct {b n : Nat} (ρ : Fin n → Word b) (r : Fragment b n) :
    (quoteFragment r).eval (fun i => quoteWord b (ρ i)) =
      quoteWord b (expandFragment ρ r) := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    simp only [quoteFragment, expandFragment, Triple.eval_cat,
      quoteAtom_correct, ih, quoteWord_append]

inductive Program : Nat → Type where
  | nil : Program 0
  | snoc {n : Nat} : Program n → Triple n → Program (n + 1)
  deriving Repr

def Program.eval {n : Nat} : Program n → Fin n → Value
  | .nil => Fin.elim0
  | .snoc p t => Fin.lastCases (t.eval p.eval) p.eval

def compile {b n : Nat} : Grammar b n → Program n
  | .nil => .nil
  | .snoc g r => .snoc (compile g) (quoteFragment r)

/-- Every previously defined raw fragment, not only a selected output, is quoted. -/
theorem compile_correct {b n : Nat} (g : Grammar b n) :
    (compile g).eval = fun i => quoteWord b (g.words i) := by
  induction g with
  | nil => funext i; exact Fin.elim0 i
  | snoc g r ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [compile, Program.eval, Grammar.words, Fin.lastCases_last, ih]
      exact quoteFragment_correct g.words r
    · simp only [compile, Program.eval, Grammar.words, Fin.lastCases_castSucc, ih]

theorem compile_length {b n : Nat} (g : Grammar b n) (i : Fin n) :
    ((compile g).eval i).len = (g.words i).length := by
  rw [compile_correct]; rfl

theorem compile_scale {b n : Nat} (g : Grammar b n) (i : Fin n) :
    ((compile g).eval i).scale = b ^ (g.words i).length := by
  rw [compile_correct]; rfl

theorem compile_payload {b n : Nat} (g : Grammar b n) (i : Fin n) :
    ((compile g).eval i).payload = rawCode b (g.words i) := by
  rw [compile_correct]; rfl

/-- The common injective base-b convention with a leading marker digit 1. -/
def markedCode (b : Nat) (w : Word b) : Nat := b ^ w.length + rawCode b w

theorem compile_markedCode {b n : Nat} (g : Grammar b n) (i : Fin n) :
    ((compile g).eval i).scale + ((compile g).eval i).payload =
      markedCode b (g.words i) := by
  rw [compile_correct]; rfl

theorem quoteAtom_weight {b n : Nat} (a : Atom b n) :
    (quoteAtom a).weight ≤ 2 * (b + 4) := by
  cases a with
  | char c => simp only [quoteAtom, Triple.weight, Expr.weight]; have := c.isLt; omega
  | use i => simp [quoteAtom, Triple.weight, Expr.weight]; omega

theorem quoteAtom_scale_weight {b n : Nat} (a : Atom b n) :
    (quoteAtom a).scale.weight ≤ b + 2 := by
  cases a <;> simp [quoteAtom, Expr.weight] <;> omega

theorem quoteFragment_scale_weight {b n : Nat} (r : Fragment b n) :
    (quoteFragment r).scale.weight ≤ (b + 4) * (r.length + 1) := by
  induction r with
  | nil => simp [quoteFragment, emptyTriple, Expr.weight]
  | cons a r ih =>
    have ha := quoteAtom_scale_weight a
    simp only [quoteFragment, Triple.cat, Expr.weight, List.length_cons]
    simp only [Nat.mul_add, Nat.mul_one] at *
    omega

theorem Triple.cat_weight {n : Nat} (x y : Triple n) :
    (x.cat y).weight = x.weight + y.weight + y.scale.weight + 4 := by
  simp [Triple.weight, Triple.cat, Expr.weight]; omega

/-- Cubic end-to-end bounds below use this quadratic bound per raw RHS.
No conversion from string grammars to tree DAGs is used. -/
theorem quoteFragment_weight {b n : Nat} (r : Fragment b n) :
    (quoteFragment r).weight ≤ 4 * (b + 4) * (r.length + 1) ^ 2 := by
  induction r with
  | nil => simp [quoteFragment, emptyTriple, Triple.weight, Expr.weight]; omega
  | cons a r ih =>
    have ha := quoteAtom_weight a
    have hs := quoteFragment_scale_weight r
    rw [quoteFragment, Triple.cat_weight]
    simp only [List.length_cons]
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_add, Nat.add_mul,
      Nat.mul_one, Nat.mul_assoc] at *
    omega

def Program.weight {n : Nat} : Program n → Nat
  | .nil => 0
  | .snoc p t => p.weight + t.weight

theorem square_sum_le (x y : Nat) : x ^ 2 + y ^ 2 ≤ (x + y) ^ 2 := by
  simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul]
  omega

theorem compile_weight {b n : Nat} (g : Grammar b n) :
    (compile g).weight ≤ 4 * (b + 4) * g.mass ^ 2 := by
  induction g with
  | nil => simp [compile, Program.weight, Grammar.mass]
  | snoc g r ih =>
    have hr := quoteFragment_weight r
    have hs := Nat.mul_le_mul_left (4 * (b + 4)) (square_sum_le g.mass (r.length + 1))
    simp only [compile, Program.weight, Grammar.mass]
    rw [Nat.mul_add] at hs
    have hh : g.mass + r.length + 1 = g.mass + (r.length + 1) := by omega
    rw [hh]
    omega

end MAISO11.Quotation

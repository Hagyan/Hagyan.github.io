import ArithmeticTrace

/-!
Compact arithmetic terms for the entire encoded witness trace. Original
quotation registers use names 0..3*n-1; new packing definitions use names
3*n, 3*n+1, ... . No intermediate natural number is converted into a numeral.
-/

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Quotation

inductive PackExpr (n m : Nat) where
  | num : Nat → PackExpr n m
  | source : Fin n → Slot → PackExpr n m
  | saved : Fin m → PackExpr n m
  | add : PackExpr n m → PackExpr n m → PackExpr n m
  | mul : PackExpr n m → PackExpr n m → PackExpr n m
  deriving DecidableEq, Repr

def PackExpr.eval {n m : Nat} (ρ : Fin n → Value) (σ : Fin m → Nat) : PackExpr n m → Nat
  | .num k => k
  | .source i s => (ρ i).get s
  | .saved i => σ i
  | .add x y => x.eval ρ σ + y.eval ρ σ
  | .mul x y => x.eval ρ σ * y.eval ρ σ

def PackExpr.weight {n m : Nat} : PackExpr n m → Nat
  | .num k => k + 1
  | .source _ _ => 1
  | .saved _ => 1
  | .add x y => 1 + x.weight + y.weight
  | .mul x y => 1 + x.weight + y.weight

def pairExpr {n m : Nat} (x y : PackExpr n m) : PackExpr n m :=
  .add (.add (.mul (.add x y) (.add x y)) x) (.num 1)

theorem pairExpr_eval {n m : Nat} (ρ : Fin n → Value) (σ : Fin m → Nat)
    (x y : PackExpr n m) :
    (pairExpr x y).eval ρ σ = arithPair (x.eval ρ σ) (y.eval ρ σ) := rfl

theorem pairExpr_weight {n m : Nat} (x y : PackExpr n m) :
    (pairExpr x y).weight = 7 + 3 * x.weight + 2 * y.weight := by
  simp [pairExpr, PackExpr.weight]
  omega

def valueExpr {n m : Nat} (i : Fin n) : PackExpr n m :=
  pairExpr (.source i .len) (pairExpr (.source i .scale) (.source i .payload))

theorem valueExpr_eval {n m : Nat} (ρ : Fin n → Value) (σ : Fin m → Nat) (i : Fin n) :
    (valueExpr i).eval ρ σ = encodeValue (ρ i) := rfl

theorem valueExpr_weight {n m : Nat} (i : Fin n) : (valueExpr (m := m) i).weight = 34 := rfl

def lastExpr (n : Nat) : (m : Nat) → PackExpr n m
  | 0 => .num 0
  | m + 1 => .saved (Fin.last m)

def lastOrZero : (m : Nat) → (Fin m → Nat) → Nat
  | 0, _ => 0
  | m + 1, σ => σ (Fin.last m)

theorem lastExpr_eval {n m : Nat} (ρ : Fin n → Value) (σ : Fin m → Nat) :
    (lastExpr n m).eval ρ σ = lastOrZero m σ := by cases m <;> rfl

theorem lastExpr_weight (n m : Nat) : (lastExpr n m).weight = 1 := by cases m <;> rfl

inductive PackingProgram (n : Nat) : Nat → Type where
  | nil : PackingProgram n 0
  | snoc {m : Nat} : PackingProgram n m → PackExpr n m → PackingProgram n (m + 1)
  deriving Repr

def PackingProgram.eval {n m : Nat} (ρ : Fin n → Value) : PackingProgram n m → Fin m → Nat
  | .nil => Fin.elim0
  | .snoc p e => Fin.lastCases (e.eval ρ (p.eval ρ)) (p.eval ρ)

def PackingProgram.root {n m : Nat} (p : PackingProgram n m) (ρ : Fin n → Value) : Nat :=
  lastOrZero m (p.eval ρ)

/-- Build the tail first, so each new definition references only earlier ones. -/
def packRefs {n : Nat} : (is : List (Fin n)) → PackingProgram n is.length
  | [] => .nil
  | i :: is => .snoc (packRefs is) (pairExpr (valueExpr i) (lastExpr n is.length))

theorem packRefs_correct {n : Nat} (ρ : Fin n → Value) (is : List (Fin n)) :
    (packRefs is).root ρ = encodeValues (is.map ρ) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [packRefs, PackingProgram.root, List.length_cons, lastOrZero,
      PackingProgram.eval, Fin.lastCases_last, pairExpr_eval, valueExpr_eval, lastExpr_eval,
      List.map_cons, encodeValues]
    change arithPair (encodeValue (ρ i)) ((packRefs is).root ρ) = _
    rw [ih]

def PackingProgram.weight {n m : Nat} : PackingProgram n m → Nat
  | .nil => 0
  | .snoc p e => p.weight + e.weight

theorem packRefs_weight {n : Nat} (is : List (Fin n)) :
    (packRefs is).weight = 111 * is.length := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp [packRefs, PackingProgram.weight, pairExpr_weight, valueExpr_weight,
      lastExpr_weight, ih]
    omega

def PackExpr.wire {n m : Nat} : PackExpr n m → List Char
  | .num k => numeral k
  | .source i s => identifier (3 * i.val + s.offset)
  | .saved i => identifier (3 * n + i.val)
  | .add x y => ['(', '+'] ++ x.wire ++ y.wire ++ [')']
  | .mul x y => ['(', '*'] ++ x.wire ++ y.wire ++ [')']

theorem PackExpr.wire_length {n m : Nat} (e : PackExpr n m) :
    e.wire.length ≤ (6 * n + 2 * m + 7) * e.weight := by
  induction e with
  | num k =>
    have h := numeral_length_le k
    simp only [wire, weight]
    have hn : 3 ≤ 6 * n + 2 * m + 7 := by omega
    have hh := Nat.mul_le_mul_right (k + 1) hn
    omega
  | source i s =>
    have h := identifier_length_le (3 * i.val + s.offset)
    have hs := s.offset_le_two
    have hi := i.isLt
    simp only [wire, weight, Nat.mul_one]
    omega
  | saved i =>
    have h := identifier_length_le (3 * n + i.val)
    have hi := i.isLt
    simp only [wire, weight, Nat.mul_one]
    omega
  | add x y hx hy =>
    simp only [wire, List.length_append, List.length_cons, List.length_nil, weight,
      Nat.mul_add, Nat.mul_one]
    omega
  | mul x y hx hy =>
    simp only [wire, List.length_append, List.length_cons, List.length_nil, weight,
      Nat.mul_add, Nat.mul_one]
    omega

def packingDefinition {n m : Nat} (e : PackExpr n m) : List Char :=
  "def ".toList ++ identifier (3 * n + m) ++ " := ".toList ++ e.wire ++ ['\n']

theorem packingDefinition_length {n m : Nat} (e : PackExpr n m) :
    (packingDefinition e).length ≤ (6 * n + 2 * m + 20) * (e.weight + 1) := by
  have he := e.wire_length
  have hn := identifier_length_le (3 * n + m)
  have hm := Nat.mul_le_mul_right e.weight
    (show 6 * n + 2 * m + 7 ≤ 6 * n + 2 * m + 20 by omega)
  simp only [packingDefinition, List.length_append, List.length_cons, List.length_nil]
  change 4 + (identifier (3 * n + m)).length + 4 + e.wire.length + (1 + 0) ≤ _
  simp only [Nat.mul_add, Nat.mul_one]
  omega

def PackingProgram.wire {n m : Nat} : PackingProgram n m → List Char
  | .nil => []
  | .snoc p e => p.wire ++ packingDefinition e

theorem PackingProgram.wire_length {n m : Nat} (p : PackingProgram n m) :
    p.wire.length ≤ (6 * n + 2 * m + 20) * (p.weight + m) := by
  induction p with
  | nil => simp [wire, weight]
  | @snoc m p e ih =>
    have he := packingDefinition_length e
    have hs := Nat.mul_le_mul_right (p.weight + e.weight + m + 1)
      (show 6 * n + 2 * m + 20 ≤ 6 * n + 2 * (m + 1) + 20 by omega)
    simp only [wire, List.length_append, weight]
    have h : p.wire.length + (packingDefinition e).length ≤
        (6 * n + 2 * m + 20) * (p.weight + e.weight + m + 1) := by
      simp only [Nat.mul_add, Nat.mul_one] at *
      omega
    calc
      _ ≤ (6 * n + 2 * m + 20) * (p.weight + e.weight + m + 1) := h
      _ ≤ (6 * n + 2 * (m + 1) + 20) * (p.weight + e.weight + m + 1) := hs
      _ = _ := by congr 1

theorem map_finRange {α : Type} {n : Nat} (f : Fin n → α) :
    (List.finRange n).map f = List.ofFn f := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [List.finRange]

def tracePacking (n : Nat) : PackingProgram n (List.finRange n).length :=
  packRefs (List.finRange n)

def packedWitness {n : Nat} (p : Program n) : Nat := (tracePacking n).root p.eval

theorem packedWitness_eq_traceCode {n : Nat} (p : Program n) :
    packedWitness p = p.traceCode := by
  simp [packedWitness, tracePacking, packRefs_correct, map_finRange, Program.traceCode]

/-- This witness is supplied by short arithmetic definitions, not a huge numeral. -/
theorem packedWitness_checked {n : Nat} (p : Program n) :
    checkTrace p (packedWitness p) = true := by
  rw [packedWitness_eq_traceCode]
  exact checkTrace_complete p

theorem packedWitness_lookup {b n : Nat} (g : Grammar b n) (i : Fin n) :
    readValue (packedWitness (compile g)) i.val = some (quoteWord b (g.words i)) :=
  compiled_trace_sound g _ (packedWitness_checked _) i

def PackExpr.expand {n m : Nat} (ρ : Fin n → TermTriple) (σ : Fin m → ClosedTerm) :
    PackExpr n m → ClosedTerm
  | .num k => numeralTerm k
  | .source i s => (ρ i).get s
  | .saved i => σ i
  | .add x y => .add (x.expand ρ σ) (y.expand ρ σ)
  | .mul x y => .mul (x.expand ρ σ) (y.expand ρ σ)

theorem PackExpr.expand_eval {n m : Nat} (ρ : Fin n → TermTriple) (σ : Fin m → ClosedTerm)
    (e : PackExpr n m) :
    (e.expand ρ σ).eval = e.eval (fun i => (ρ i).eval) (fun j => (σ j).eval) := by
  induction e with
  | num k => exact numeralTerm_eval k
  | source i s => exact TermTriple.get_eval (ρ i) s
  | saved i => rfl
  | add x y hx hy => simp [expand, ClosedTerm.eval, PackExpr.eval, hx, hy]
  | mul x y hx hy => simp [expand, ClosedTerm.eval, PackExpr.eval, hx, hy]

def PackingProgram.expansion {n m : Nat} (ρ : Fin n → TermTriple) :
    PackingProgram n m → Fin m → ClosedTerm
  | .nil => Fin.elim0
  | .snoc p e => Fin.lastCases (e.expand ρ (p.expansion ρ)) (p.expansion ρ)

theorem PackingProgram.expansion_eval {n m : Nat} (ρ : Fin n → TermTriple)
    (p : PackingProgram n m) :
    (fun i => (p.expansion ρ i).eval) = p.eval (fun j => (ρ j).eval) := by
  induction p with
  | nil => funext i; exact Fin.elim0 i
  | snoc p e ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [expansion, PackingProgram.eval, Fin.lastCases_last, PackExpr.expand_eval, ih]
    · simp only [expansion, PackingProgram.eval, Fin.lastCases_castSucc]
      exact congrFun ih j

theorem packing_source_fresh {n m : Nat} (i : Fin n) (s : Slot) :
    identifier (3 * i.val + s.offset) ≠ identifier (3 * n + m) := by
  intro h
  have he := identifier_injective h
  have hl := register_lt i s
  omega

theorem packing_saved_fresh {n m : Nat} (i : Fin m) :
    identifier (3 * n + i.val) ≠ identifier (3 * n + m) := by
  intro h
  have he := identifier_injective h
  have hi := i.isLt
  omega

/-- Extra definitions for the entire witness trace have a quadratic character bound. -/
theorem tracePacking_characters (n : Nat) :
    (tracePacking n).wire.length ≤ (8 * n + 20) * (112 * n) := by
  have h := (tracePacking n).wire_length
  simp only [tracePacking, packRefs_weight, List.length_finRange] at h
  have h₁ : 6 * n + 2 * n + 20 = 8 * n + 20 := by omega
  have h₂ : 111 * n + n = 112 * n := by omega
  simpa only [h₁, h₂] using h

theorem compiled_bundle_characters {b n : Nat} (g : Grammar b n) :
    ((compile g).certifiedWire ++ (tracePacking n).wire).length ≤
      20 + (40 * g.mass + 100) * (4 * (b + 4) * g.mass ^ 2 + 3 * g.mass) +
        (8 * g.mass + 20) * (112 * g.mass) := by
  have hq := compile_certificate_characters g
  have hp := tracePacking_characters n
  have hn := g.count_le_mass
  have h₁ : 8 * n + 20 ≤ 8 * g.mass + 20 := by omega
  have h₂ : 112 * n ≤ 112 * g.mass := by omega
  have hh := Nat.mul_le_mul h₁ h₂
  rw [List.length_append]
  omega

end MAISO11.Quotation

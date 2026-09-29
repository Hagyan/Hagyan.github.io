import CompactChecker
import DagEquality

/-!
The first integration boundary for checking compact proof files without
expanding both sides of every modus-ponens comparison.  The caller supplies
a Boolean equality procedure on compact terms, together with its correctness
proof.  The axiom branch still uses the previous arithmetic axiom checker.
-/
set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Wire
open MAISO11.Arithmetic MAISO11.Quotation

/-- Compare two formulas by structure; the only external operation compares
terms with the same variable context. -/
def formulaEqual {r n : Nat}
    (termEqual : (m : Nat) → CTerm r m → CTerm r m → Bool) :
    CFormula r n → CFormula r n → Bool
  | .eq s t, .eq u v => termEqual n s u && termEqual n t v
  | .neg f, .neg g => formulaEqual termEqual f g
  | .imp f h, .imp g i => formulaEqual termEqual f g && formulaEqual termEqual h i
  | .all f, .all g => formulaEqual termEqual f g
  | _, _ => false

/-- A correct term comparator lifts to arbitrary formulas, including nested
quantifiers. The proof only uses that abbreviation references are closed. -/
theorem formulaEqual_iff {r n : Nat} (δ : Fin r → ClosedTerm)
    (termEqual : (m : Nat) → CTerm r m → CTerm r m → Bool)
    (correct : ∀ (m : Nat) (s t : CTerm r m),
      termEqual m s t = true ↔ s.expand δ = t.expand δ)
    (f g : CFormula r n) :
    formulaEqual termEqual f g = true ↔ f.expand δ = g.expand δ := by
  induction f with
  | eq s t =>
    cases g <;> simp [formulaEqual, CFormula.expand, correct]
  | neg f ih =>
    cases g <;> simp [formulaEqual, CFormula.expand, ih]
  | imp f h hf hh =>
    cases g <;> simp [formulaEqual, CFormula.expand, hf, hh]
  | all f ih =>
    cases g <;> simp [formulaEqual, CFormula.expand, ih]

/-- Modus ponens can inspect the compact outer constructor before asking
about subformula equality; no expansion is needed to identify implication. -/
def mpEqual {r : Nat}
    (termEqual : (m : Nat) → CTerm r m → CTerm r m → Bool)
    (antecedent implication conclusion : CFormula r 0) : Bool :=
  match implication with
  | .imp a b => formulaEqual termEqual antecedent a && formulaEqual termEqual conclusion b
  | _ => false

theorem mpEqual_iff {r : Nat} (δ : Fin r → ClosedTerm)
    (termEqual : (m : Nat) → CTerm r m → CTerm r m → Bool)
    (correct : ∀ (m : Nat) (s t : CTerm r m),
      termEqual m s t = true ↔ s.expand δ = t.expand δ)
    (antecedent implication conclusion : CFormula r 0) :
    mpEqual termEqual antecedent implication conclusion = true ↔
      implication.expand δ =
        Formula.imp (antecedent.expand δ) (conclusion.expand δ) := by
  cases implication <;> simp [mpEqual,CFormula.expand,
    formulaEqual_iff δ termEqual correct]
  case imp =>
    constructor <;> intro h <;> exact ⟨h.1.symm,h.2.symm⟩

def Record.checkWithTermEqual {r k : Nat} (δ : Fin r → ClosedTerm)
    (termEqual : (m : Nat) → CTerm r m → CTerm r m → Bool)
    (fs : Records r k) : Record r k → Bool
  | .axiom f => axiomCheck (f.expand δ)
  | .mp a b f => mpEqual termEqual (fs.get a) (fs.get b) f

theorem Record.checkWithTermEqual_iff {r k : Nat} (δ : Fin r → ClosedTerm)
    (termEqual : (m : Nat) → CTerm r m → CTerm r m → Bool)
    (correct : ∀ (m : Nat) (s t : CTerm r m),
      termEqual m s t = true ↔ s.expand δ = t.expand δ)
    (fs : Records r k) (f : Record r k) :
    f.checkWithTermEqual δ termEqual fs = true ↔ f.valid δ fs := by
  cases f <;> simp [Record.checkWithTermEqual, Record.valid,
    axiomCheck_iff, mpEqual_iff δ termEqual correct]

def Records.checkWithTermEqual {r k : Nat} (δ : Fin r → ClosedTerm)
    (termEqual : (m : Nat) → CTerm r m → CTerm r m → Bool) :
    Records r k → Bool
  | .nil => true
  | .snoc fs f => fs.checkWithTermEqual δ termEqual &&
      f.checkWithTermEqual δ termEqual fs

theorem Records.checkWithTermEqual_iff {r k : Nat} (δ : Fin r → ClosedTerm)
    (termEqual : (m : Nat) → CTerm r m → CTerm r m → Bool)
    (correct : ∀ (m : Nat) (s t : CTerm r m),
      termEqual m s t = true ↔ s.expand δ = t.expand δ)
    (fs : Records r k) :
    fs.checkWithTermEqual δ termEqual = true ↔ fs.valid δ := by
  induction fs with
  | nil => simp [checkWithTermEqual, Records.valid]
  | snoc fs f ih =>
    simp [checkWithTermEqual, Records.valid, ih,
      Record.checkWithTermEqual_iff δ termEqual correct]

theorem Records.checkWithTermEqual_derivable {r k : Nat}
    (δ : Fin r → ClosedTerm)
    (termEqual : (m : Nat) → CTerm r m → CTerm r m → Bool)
    (correct : ∀ (m : Nat) (s t : CTerm r m),
      termEqual m s t = true ↔ s.expand δ = t.expand δ)
    (fs : Records r k) (h : fs.checkWithTermEqual δ termEqual = true)
    (i : Fin k) : Nonempty (Derivation ((fs.get i).expand δ)) :=
  fs.valid_derivable δ ((fs.checkWithTermEqual_iff δ termEqual correct).mp h) i

/-- A reference implementation pins down the interface. It expands terms,
so its purpose is extensional comparison with the existing checker. -/
def expandedTermEqual {r : Nat} (δ : Fin r → ClosedTerm)
    (n : Nat) (s t : CTerm r n) : Bool :=
  decide (s.expand δ = t.expand δ)

theorem expandedTermEqual_correct {r : Nat} (δ : Fin r → ClosedTerm)
    (n : Nat) (s t : CTerm r n) :
    expandedTermEqual δ n s t = true ↔ s.expand δ = t.expand δ := by
  simp [expandedTermEqual]

/-- The new structural MP checker accepts exactly the same structured proof
records as the previous expansion-based checker. -/
theorem checkWithTermEqual_agrees {r k : Nat} (δ : Fin r → ClosedTerm)
    (fs : Records r k) :
    fs.checkWithTermEqual δ (expandedTermEqual δ) = fs.check δ := by
  have h : fs.checkWithTermEqual δ (expandedTermEqual δ) = true ↔
      fs.check δ = true :=
    (fs.checkWithTermEqual_iff δ (expandedTermEqual δ)
      (expandedTermEqual_correct δ)).trans (fs.check_iff δ).symm
  cases hx : fs.checkWithTermEqual δ (expandedTermEqual δ) <;>
    cases hy : fs.check δ <;> simp_all

/-- Embedding a closed term into a term context loses no syntax. -/
theorem ofClosed_injective (n : Nat) :
    ∀ (a b : ClosedTerm),
      (Term.ofClosed a : Term n) = Term.ofClosed b → a = b := by
  intro a b h
  induction a generalizing b with
  | zero => cases b <;> cases h; rfl
  | bit0 a ih =>
    cases b with
    | bit0 b =>
      simp only [Term.ofClosed, Term.bit0.injEq] at h
      exact congrArg ClosedTerm.bit0 (ih b h)
    | zero => cases h
    | bit1 _ => cases h
    | add _ _ => cases h
    | mul _ _ => cases h
  | bit1 a ih =>
    cases b with
    | bit1 b =>
      simp only [Term.ofClosed, Term.bit1.injEq] at h
      exact congrArg ClosedTerm.bit1 (ih b h)
    | zero => cases h
    | bit0 _ => cases h
    | add _ _ => cases h
    | mul _ _ => cases h
  | add a c ihA ihC =>
    cases b with
    | add b d =>
      simp only [Term.ofClosed, Term.add.injEq] at h
      cases ihA b h.1
      cases ihC d h.2
      rfl
    | zero => cases h
    | bit0 _ => cases h
    | bit1 _ => cases h
    | mul _ _ => cases h
  | mul a c ihA ihC =>
    cases b with
    | mul b d =>
      simp only [Term.ofClosed, Term.mul.injEq] at h
      cases ihA b h.1
      cases ihC d h.2
      rfl
    | zero => cases h
    | bit0 _ => cases h
    | bit1 _ => cases h
    | add _ _ => cases h

/-- On bare abbreviation references, consult the graph's equality table.
The general branch is intentionally the reference implementation; later
work must compile every compact term into the shared graph. -/
def graphReferenceEqual {r : Nat} (g : Shared.Graph r)
    (δ : Fin r → ClosedTerm) (n : Nat)
    (s t : CTerm r n) : Bool :=
  match s,t with
  | .ref i,.ref j => g.table[i][j]
  | _,_ => expandedTermEqual δ n s t

theorem graphReferenceEqual_correct {r : Nat} (g : Shared.Graph r)
    (δ : Fin r → ClosedTerm) (hδ : g.expand = δ)
    (n : Nat) (s t : CTerm r n) :
    graphReferenceEqual g δ n s t = true ↔ s.expand δ = t.expand δ := by
  cases s <;> cases t <;>
    try simp [graphReferenceEqual, expandedTermEqual]
  case ref.ref i j =>
    change g.table[i][j] = true ↔
      (Term.ofClosed (δ i) : Term n) = Term.ofClosed (δ j)
    rw [g.table_iff, hδ]
    constructor
    · intro h; exact congrArg Term.ofClosed h
    · intro h; exact ofClosed_injective n (δ i) (δ j) h

end MAISO11.Wire

import OpenGraph
set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Wire
def CTerm.hasVar {r n : Nat} : CTerm r n → Bool
  | .var _ => true
  | .ref _ | .zero => false
  | .bit0 t | .bit1 t => t.hasVar
  | .add s t | .mul s t => s.hasVar || t.hasVar

def CTerm.eraseVars {r n : Nat} : CTerm r n → CTerm r 0
  | .var _ => .zero
  | .ref i => .ref i
  | .zero => .zero
  | .bit0 t => .bit0 t.eraseVars
  | .bit1 t => .bit1 t.eraseVars
  | .add s t => .add s.eraseVars t.eraseVars
  | .mul s t => .mul s.eraseVars t.eraseVars

end MAISO11.Wire

namespace MAISO11.Arithmetic
open MAISO11.Quotation
def Term.hasVar {n : Nat} : Term n → Bool
  | .var _ => true
  | .zero => false
  | .bit0 t | .bit1 t => t.hasVar
  | .add s t | .mul s t => s.hasVar || t.hasVar

theorem Term.hasVar_ofClosed {n : Nat} (a : ClosedTerm) :
    (Term.ofClosed a : Term n).hasVar = false := by
  induction a <;> simp_all [Term.ofClosed,Term.hasVar]

end MAISO11.Arithmetic

namespace MAISO11.Wire
open MAISO11.Arithmetic MAISO11.Quotation

theorem CTerm.expand_hasVar {r n : Nat} (δ : Fin r → ClosedTerm)
    (t : CTerm r n) : (t.expand δ).hasVar = t.hasVar := by
  induction t with
  | var i => rfl
  | ref i => exact Term.hasVar_ofClosed (δ i)
  | zero => rfl
  | bit0 t ih => simp [CTerm.expand,CTerm.hasVar,Term.hasVar,ih]
  | bit1 t ih => simp [CTerm.expand,CTerm.hasVar,Term.hasVar,ih]
  | add s t hs ht => simp [CTerm.expand,CTerm.hasVar,Term.hasVar,hs,ht]
  | mul s t hs ht => simp [CTerm.expand,CTerm.hasVar,Term.hasVar,hs,ht]

theorem CTerm.expand_closed_of_hasVar_eq_false {r n : Nat}
    (δ : Fin r → ClosedTerm) {t : CTerm r n} (h : t.hasVar = false) :
    (Term.ofClosed (t.eraseVars.close δ) : Term n) = t.expand δ := by
  induction t with
  | var i => simp [CTerm.hasVar] at h
  | ref i => rfl
  | zero => rfl
  | bit0 t ih =>
    have ht : t.hasVar = false := by simpa [CTerm.hasVar] using h
    simp only [CTerm.eraseVars,CTerm.expand,CTerm.close,Term.ofClosed]
    rw [ih ht]
  | bit1 t ih =>
    have ht : t.hasVar = false := by simpa [CTerm.hasVar] using h
    simp only [CTerm.eraseVars,CTerm.expand,CTerm.close,Term.ofClosed]
    rw [ih ht]
  | add s t hs ht =>
    have hs' : s.hasVar = false := by simp [CTerm.hasVar] at h ⊢; exact h.1
    have ht' : t.hasVar = false := by simp [CTerm.hasVar] at h ⊢; exact h.2
    simp only [CTerm.eraseVars,CTerm.expand,CTerm.close,Term.ofClosed]
    rw [hs hs',ht ht']
  | mul s t hs ht =>
    have hs' : s.hasVar = false := by simp [CTerm.hasVar] at h ⊢; exact h.1
    have ht' : t.hasVar = false := by simp [CTerm.hasVar] at h ⊢; exact h.2
    simp only [CTerm.eraseVars,CTerm.expand,CTerm.close,Term.ofClosed]
    rw [hs hs',ht ht']

end MAISO11.Wire

namespace MAISO11.Shared
open MAISO11.Wire MAISO11.Arithmetic MAISO11.Quotation

def sharedClosedEqual {r n : Nat} (g : Graph n) (refs : Fin r → Fin n)
    (s t : CTerm r 0) : Bool :=
  let a := compileTerm g refs s
  let b := compileTerm a.graph (fun i => a.lift (refs i)) t
  b.graph.table[(b.lift a.root)][b.root]

theorem sharedClosedEqual_correct {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (δ : Fin r → ClosedTerm)
    (hδ : ∀ i, g.expand (refs i) = δ i) (s t : CTerm r 0) :
    sharedClosedEqual g refs s t = true ↔ s.close δ = t.close δ := by
  unfold sharedClosedEqual
  let a := compileTerm g refs s
  let b := compileTerm a.graph (fun i => a.lift (refs i)) t
  have hAroot := compileTerm_root g refs s
  have hBroot := compileTerm_root a.graph (fun i => a.lift (refs i)) t
  have hBprev := compileTerm_preserves a.graph (fun i => a.lift (refs i)) t a.root
  have hrefs : (fun i => a.graph.expand (a.lift (refs i))) = δ := by
    funext i
    rw [compileTerm_preserves]
    exact hδ i
  have hδfun : (fun i => g.expand (refs i)) = δ := funext hδ
  rw [Graph.table_iff]
  rw [hBprev,hBroot,hAroot]
  rw [hrefs,hδfun]

theorem closedExpand_eq_iff {r : Nat} (δ : Fin r → ClosedTerm)
    (s t : CTerm r 0) :
    s.close δ = t.close δ ↔ s.expand δ = t.expand δ := by
  constructor
  · intro h
    have hs : (Term.ofClosed (s.close δ) : Term 0) = s.expand δ :=
      CTerm.close_expand δ s
    have ht : (Term.ofClosed (t.close δ) : Term 0) = t.expand δ :=
      CTerm.close_expand δ t
    rw [← hs, ← ht]
    exact congrArg Term.ofClosed h
  · intro h
    have hs : (Term.ofClosed (s.close δ) : Term 0) = s.expand δ :=
      CTerm.close_expand δ s
    have ht : (Term.ofClosed (t.close δ) : Term 0) = t.expand δ :=
      CTerm.close_expand δ t
    have hterm : (Term.ofClosed (s.close δ) : Term 0) =
        (Term.ofClosed (t.close δ) : Term 0) := by
      rw [hs, ht]
      exact h
    exact ofClosed_injective 0 _ _ hterm

/-- Closed terms use the compact closed-graph comparator. Under binders, the
variable-labelled graph compiler keeps bound variables as leaves and still
reuses the closed abbreviation graph. -/
def compiledTermEqual {r n : Nat} (g : Graph n) (refs : Fin r → Fin n)
    (m : Nat) (s t : CTerm r m) : Bool :=
  match m with
  | 0 => sharedClosedEqual g refs s t
  | _ => sharedOpenEqual g refs s t

theorem compiledTermEqual_correct {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) :
    ∀ (m : Nat) (s t : CTerm r m),
      compiledTermEqual g refs m s t = true ↔
        s.expand (fun i => g.expand (refs i)) =
          t.expand (fun i => g.expand (refs i)) := by
  intro m
  cases m with
  | zero =>
    intro s t
    rw [compiledTermEqual, sharedClosedEqual_correct g refs
      (fun i => g.expand (refs i)) (by intro i; rfl), closedExpand_eq_iff]
  | succ m =>
    intro s t
    exact sharedOpenEqual_correct g refs s t

/-- Lift the compiled term comparison to formulas, including terms beneath
nested quantifiers. -/
def compiledFormulaEqual {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (f h : CFormula r 0) : Bool :=
  MAISO11.Wire.formulaEqual (compiledTermEqual g refs) f h

theorem compiledFormulaEqual_correct {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (f h : CFormula r 0) :
    compiledFormulaEqual g refs f h = true ↔
      f.expand (fun i => g.expand (refs i)) =
        h.expand (fun i => g.expand (refs i)) := by
  exact MAISO11.Wire.formulaEqual_iff
    (fun i => g.expand (refs i)) (compiledTermEqual g refs)
    (compiledTermEqual_correct g refs) f h

/-- Graph shortcut for the contrapositive tautology shape. -/
def compiledContrapShortcut {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (f : CFormula r 0) : Bool :=
  match f with
  | .imp (.imp a (.neg b)) c =>
      compiledFormulaEqual g refs c (.imp b (.neg a))
  | _ => false

theorem compiledContrapShortcut_sound {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (δ : Fin r → ClosedTerm)
    (hδ : ∀ i, g.expand (refs i) = δ i) {f : CFormula r 0}
    (h : compiledContrapShortcut g refs f = true) :
    IsAxiom (f.expand δ) := by
  cases f with
  | eq s t => simp [compiledContrapShortcut] at h
  | neg q => simp [compiledContrapShortcut] at h
  | all q => simp [compiledContrapShortcut] at h
  | imp a c =>
    cases a with
    | eq s t => simp [compiledContrapShortcut] at h
    | neg q => simp [compiledContrapShortcut] at h
    | all q => simp [compiledContrapShortcut] at h
    | imp a b =>
      cases b with
      | eq s t => simp [compiledContrapShortcut] at h
      | imp b c => simp [compiledContrapShortcut] at h
      | all b => simp [compiledContrapShortcut] at h
      | neg b =>
        have hc0 : c.expand (fun i => g.expand (refs i)) =
            (CFormula.imp b (CFormula.neg a)).expand (fun i => g.expand (refs i)) :=
          (compiledFormulaEqual_correct g refs c (.imp b (.neg a))).mp h
        have henv : (fun i => g.expand (refs i)) = δ := funext hδ
        rw [henv] at hc0
        have hc := hc0
        change IsAxiom (.imp (.imp (a.expand δ) (.neg (b.expand δ))) (c.expand δ))
        rw [hc]
        exact IsAxiom.contrap (a.expand δ) (b.expand δ)

/-- Graph shortcut for the conjunction-introduction tautology shape. -/
def compiledConjShortcut {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (f : CFormula r 0) : Bool :=
  match f with
  | .imp a (.imp b c) =>
      compiledFormulaEqual g refs c (CFormula.conj a b)
  | _ => false

theorem compiledConjShortcut_sound {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (δ : Fin r → ClosedTerm)
    (hδ : ∀ i, g.expand (refs i) = δ i) {f : CFormula r 0}
    (h : compiledConjShortcut g refs f = true) :
    IsAxiom (f.expand δ) := by
  cases f with
  | eq s t => simp [compiledConjShortcut] at h
  | neg q => simp [compiledConjShortcut] at h
  | all q => simp [compiledConjShortcut] at h
  | imp a c =>
    cases c with
    | eq s t => simp [compiledConjShortcut] at h
    | neg q => simp [compiledConjShortcut] at h
    | all q => simp [compiledConjShortcut] at h
    | imp b c =>
      have hc0 : c.expand (fun i => g.expand (refs i)) =
          (CFormula.conj a b).expand (fun i => g.expand (refs i)) :=
        (compiledFormulaEqual_correct g refs c (CFormula.conj a b)).mp h
      have henv : (fun i => g.expand (refs i)) = δ := funext hδ
      rw [henv] at hc0
      have hc := hc0
      change IsAxiom (.imp (a.expand δ) (.imp (b.expand δ) (c.expand δ)))
      rw [hc]
      exact IsAxiom.conjIntro (a.expand δ) (b.expand δ)

/-- A common universal-instantiation case: from `∀x, x=x` infer an
equality of two terms with the same expanded syntax. The terms may use
different compact definitions. -/
def compiledReflInstShortcut {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (f : CFormula r 0) : Bool :=
  match f with
  | .imp (.all (.eq (.var _) (.var _))) (.eq s t) =>
      compiledTermEqual g refs 0 s t
  | _ => false

theorem compiledReflInstShortcut_sound {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (δ : Fin r → ClosedTerm)
    (hδ : ∀ i, g.expand (refs i) = δ i) {f : CFormula r 0}
    (h : compiledReflInstShortcut g refs f = true) :
    IsAxiom (f.expand δ) := by
  cases f with
  | eq s t => simp [compiledReflInstShortcut] at h
  | neg q => simp [compiledReflInstShortcut] at h
  | all q => simp [compiledReflInstShortcut] at h
  | imp antecedent consequent =>
    cases antecedent with
    | eq s t => simp [compiledReflInstShortcut] at h
    | neg q => simp [compiledReflInstShortcut] at h
    | imp a b => simp [compiledReflInstShortcut] at h
    | all body =>
      cases body with
      | neg q => simp [compiledReflInstShortcut] at h
      | imp a b => simp [compiledReflInstShortcut] at h
      | all q => simp [compiledReflInstShortcut] at h
      | eq a b =>
        cases a with
        | zero => simp [compiledReflInstShortcut] at h
        | ref i => simp [compiledReflInstShortcut] at h
        | bit0 q => simp [compiledReflInstShortcut] at h
        | bit1 q => simp [compiledReflInstShortcut] at h
        | add q v => simp [compiledReflInstShortcut] at h
        | mul q v => simp [compiledReflInstShortcut] at h
        | var i =>
          cases b with
          | zero => simp [compiledReflInstShortcut] at h
          | ref j => simp [compiledReflInstShortcut] at h
          | bit0 q => simp [compiledReflInstShortcut] at h
          | bit1 q => simp [compiledReflInstShortcut] at h
          | add q v => simp [compiledReflInstShortcut] at h
          | mul q v => simp [compiledReflInstShortcut] at h
          | var j =>
            cases consequent with
            | neg q => simp [compiledReflInstShortcut] at h
            | imp q v => simp [compiledReflInstShortcut] at h
            | all q => simp [compiledReflInstShortcut] at h
            | eq s t =>
              have hi : i = 0 := by apply Fin.ext; omega
              have hj : j = 0 := by apply Fin.ext; omega
              subst i
              subst j
              have ht0 := (compiledTermEqual_correct g refs 0 s t).mp h
              have henv : (fun x => g.expand (refs x)) = δ := funext hδ
              rw [henv] at ht0
              change IsAxiom (.imp (.all (.eq (.var 0) (.var 0)))
                (.eq (s.expand δ) (t.expand δ)))
              rw [← ht0]
              simpa [Formula.instantiate,Formula.subst,Term.subst,instanceSubst]
                using (IsAxiom.inst (.eq (.var 0) (.var 0)) (s.expand δ))

def compiledAxiomShortcut {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (f : CFormula r 0) : Bool :=
  compiledContrapShortcut g refs f || compiledConjShortcut g refs f ||
    compiledReflInstShortcut g refs f

theorem compiledAxiomShortcut_sound {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (δ : Fin r → ClosedTerm)
    (hδ : ∀ i, g.expand (refs i) = δ i) {f : CFormula r 0}
    (h : compiledAxiomShortcut g refs f = true) : IsAxiom (f.expand δ) := by
  simp only [compiledAxiomShortcut, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact compiledContrapShortcut_sound g refs δ hδ h
  · exact compiledConjShortcut_sound g refs δ hδ h
  · exact compiledReflInstShortcut_sound g refs δ hδ h

/-- Preserve the old exact axiom relation, but try graph comparisons for the
two propositional schemes and the reflexivity-instantiation case first. Other
universal instantiations and unsuccessful shortcuts still use the expansion-based
reference checker.
-/
def compiledAxiomCheck {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (δ : Fin r → ClosedTerm)
    (f : CFormula r 0) : Bool :=
  compiledAxiomShortcut g refs f || axiomCheck (f.expand δ)

theorem compiledAxiomCheck_eq_reference {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (δ : Fin r → ClosedTerm)
    (hδ : ∀ i, g.expand (refs i) = δ i) (f : CFormula r 0) :
    compiledAxiomCheck g refs δ f = axiomCheck (f.expand δ) := by
  unfold compiledAxiomCheck
  cases hs : compiledAxiomShortcut g refs f <;> simp [hs]
  have ha := axiomCheck_complete (compiledAxiomShortcut_sound g refs δ hδ hs)
  simp [ha]

def checkRecordCompiled {r k n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (δ : Fin r → ClosedTerm)
    (termEqual : (m : Nat) → CTerm r m → CTerm r m → Bool)
    (rec : Record r k) (fs : Records r k) : Bool :=
  match rec with
  | .axiom f => compiledAxiomCheck g refs δ f
  | .mp a b f => mpEqual termEqual (fs.get a) (fs.get b) f

theorem checkRecordCompiled_iff {r k n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (δ : Fin r → ClosedTerm)
    (termEqual : (m : Nat) → CTerm r m → CTerm r m → Bool)
    (correct : ∀ (m : Nat) (s t : CTerm r m),
      termEqual m s t = true ↔ s.expand δ = t.expand δ)
    (hδ : ∀ i, g.expand (refs i) = δ i)
    (fs : Records r k) (rec : Record r k) :
    checkRecordCompiled g refs δ termEqual rec fs = true ↔ rec.valid δ fs := by
  cases rec with
  | «axiom» f =>
    simp [checkRecordCompiled, Record.valid, compiledAxiomCheck_eq_reference g refs δ hδ,
      axiomCheck_iff]
  | mp a b f =>
    simp [checkRecordCompiled, Record.valid, mpEqual_iff δ termEqual correct]

def checkRecordsCompiled {r k n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (δ : Fin r → ClosedTerm)
    (termEqual : (m : Nat) → CTerm r m → CTerm r m → Bool)
    (hδ : ∀ i, g.expand (refs i) = δ i) : Records r k → Bool
  | .nil => true
  | .snoc fs rec => checkRecordsCompiled g refs δ termEqual hδ fs &&
      checkRecordCompiled g refs δ termEqual rec fs

theorem checkRecordsCompiled_iff {r k n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (δ : Fin r → ClosedTerm)
    (termEqual : (m : Nat) → CTerm r m → CTerm r m → Bool)
    (correct : ∀ (m : Nat) (s t : CTerm r m),
      termEqual m s t = true ↔ s.expand δ = t.expand δ)
    (hδ : ∀ i, g.expand (refs i) = δ i) (fs : Records r k) :
    checkRecordsCompiled g refs δ termEqual hδ fs = true ↔ fs.valid δ := by
  induction fs with
  | nil => simp [checkRecordsCompiled, Records.valid]
  | @snoc k fs rec ih =>
    simp [checkRecordsCompiled, Records.valid, ih,
      checkRecordCompiled_iff g refs δ termEqual correct hδ]

/-- Existing records use graph comparison for MP at all binder depths and
graph shortcuts for two propositional axiom schemes and the reflexivity
instantiation case. Other instantiations retain the expansion-based fallback. -/
def checkRecordsCompiledTerms {r k n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (fs : Records r k) : Bool :=
  checkRecordsCompiled g refs (fun i => g.expand (refs i))
    (compiledTermEqual g refs) (by intro i; rfl) fs

theorem checkRecordsCompiledTerms_iff {r k n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (fs : Records r k) :
    checkRecordsCompiledTerms g refs fs = true ↔
      fs.valid (fun i => g.expand (refs i)) :=
  checkRecordsCompiled_iff g refs (fun i => g.expand (refs i))
    (compiledTermEqual g refs) (compiledTermEqual_correct g refs) (by intro i; rfl) fs

theorem checkRecordsCompiledTerms_derivable {r k n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (fs : Records r k)
    (h : checkRecordsCompiledTerms g refs fs = true) (i : Fin k) :
    Nonempty (Derivation ((fs.get i).expand (fun j => g.expand (refs j)))) :=
  fs.valid_derivable _ ((checkRecordsCompiledTerms_iff g refs fs).mp h) i

end MAISO11.Shared

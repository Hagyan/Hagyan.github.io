import SharedOracle
import GraphSubterms

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Wire
open MAISO11.Arithmetic MAISO11.Quotation

/-- Replace the variable bound by an outer universal quantifier with a new
closed abbreviation reference. `m` variables bound by inner quantifiers are
retained. -/
def CTerm.replaceOuter {r m : Nat} : CTerm r (m+1) → CTerm (r+1) m
  | .var i => Fin.lastCases (.ref (Fin.last r)) (fun j => .var j) i
  | .ref i => .ref i.castSucc
  | .zero => .zero
  | .bit0 t => .bit0 t.replaceOuter
  | .bit1 t => .bit1 t.replaceOuter
  | .add s t => .add s.replaceOuter t.replaceOuter
  | .mul s t => .mul s.replaceOuter t.replaceOuter

def CFormula.replaceOuter {r m : Nat} : CFormula r (m+1) → CFormula (r+1) m
  | .eq s t => .eq s.replaceOuter t.replaceOuter
  | .neg f => .neg f.replaceOuter
  | .imp f g => .imp f.replaceOuter g.replaceOuter
  | .all f => .all f.replaceOuter

def CTerm.mapRefs {r s m : Nat} (ρ : Fin r → Fin s) :
    CTerm r m → CTerm s m
  | .var i => .var i
  | .ref i => .ref (ρ i)
  | .zero => .zero
  | .bit0 t => .bit0 (t.mapRefs ρ)
  | .bit1 t => .bit1 (t.mapRefs ρ)
  | .add a b => .add (a.mapRefs ρ) (b.mapRefs ρ)
  | .mul a b => .mul (a.mapRefs ρ) (b.mapRefs ρ)

def CFormula.mapRefs {r s m : Nat} (ρ : Fin r → Fin s) :
    CFormula r m → CFormula s m
  | .eq a b => .eq (a.mapRefs ρ) (b.mapRefs ρ)
  | .neg f => .neg (f.mapRefs ρ)
  | .imp f h => .imp (f.mapRefs ρ) (h.mapRefs ρ)
  | .all f => .all (f.mapRefs ρ)

theorem CTerm.mapRefs_correct {r s m : Nat} (δ : Fin s → ClosedTerm)
    (ρ : Fin r → Fin s) (t : CTerm r m) :
    (t.mapRefs ρ).expand δ = t.expand (δ ∘ ρ) := by
  induction t <;> simp [mapRefs,expand, *]

theorem CFormula.mapRefs_correct {r s m : Nat} (δ : Fin s → ClosedTerm)
    (ρ : Fin r → Fin s) (f : CFormula r m) :
    (f.mapRefs ρ).expand δ = f.expand (δ ∘ ρ) := by
  induction f <;> simp [mapRefs,expand,CTerm.mapRefs_correct, *]

/-- At depth `m`, replace only the outer variable, index `m`. -/
def outerSubst (m : Nat) (w : ClosedTerm) : Fin (m+1) → Term m :=
  Fin.lastCases (Term.ofClosed w) Term.var

theorem outerSubst_lift (m : Nat) (w : ClosedTerm) :
    liftSubst (outerSubst m w) = outerSubst (m+1) w := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hr : outerSubst (m+1) w (Fin.last (m+1)) = Term.ofClosed w := by
      simp [outerSubst]
    rw [hr]
    calc
      liftSubst (outerSubst m w) (Fin.last (m+1)) =
          liftSubst (outerSubst m w) (Fin.last m).succ := by rw [Fin.succ_last]
      _ = (outerSubst m w (Fin.last m)).up := rfl
      _ = Term.ofClosed w := by simp [outerSubst,Term.up,ofClosed_subst]
  · refine Fin.cases ?_ (fun k => ?_) j
    · change liftSubst (outerSubst m w) 0 =
        outerSubst (m+1) w (Fin.castSucc (0 : Fin (m+1)))
      simp only [liftSubst,Fin.cases_zero,outerSubst,Fin.lastCases_castSucc]
    · change liftSubst (outerSubst m w) (Fin.castSucc k).succ =
        outerSubst (m+1) w (Fin.castSucc (k.succ))
      simp only [liftSubst,Fin.cases_succ,outerSubst,
        Fin.lastCases_castSucc,Term.up,Term.subst]

theorem CTerm.replaceOuter_correct {r m : Nat} (δ : Fin r → ClosedTerm)
    (w : ClosedTerm) (t : CTerm r (m+1)) :
    t.replaceOuter.expand (Fin.lastCases w δ) =
      (t.expand δ).subst (outerSubst m w) := by
  induction t with
  | var i =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [CTerm.replaceOuter,CTerm.expand,Term.subst,outerSubst]
    · simp [CTerm.replaceOuter,CTerm.expand,Term.subst,outerSubst]
  | ref i => simp [CTerm.replaceOuter,CTerm.expand,Term.subst,ofClosed_subst]
  | zero => rfl
  | bit0 t ih => simp [CTerm.replaceOuter,CTerm.expand,Term.subst,ih]
  | bit1 t ih => simp [CTerm.replaceOuter,CTerm.expand,Term.subst,ih]
  | add s t hs ht => simp [CTerm.replaceOuter,CTerm.expand,Term.subst,hs,ht]
  | mul s t hs ht => simp [CTerm.replaceOuter,CTerm.expand,Term.subst,hs,ht]

theorem CFormula.replaceOuter_correct {r m : Nat} (δ : Fin r → ClosedTerm)
    (w : ClosedTerm) (f : CFormula r (m+1)) :
    f.replaceOuter.expand (Fin.lastCases w δ) =
      (f.expand δ).subst (outerSubst m w) := by
  cases f with
  | eq s t =>
    simp [CFormula.replaceOuter,CFormula.expand,Formula.subst,
      CTerm.replaceOuter_correct]
  | neg f =>
    simp [CFormula.replaceOuter,CFormula.expand,Formula.subst,
      CFormula.replaceOuter_correct δ w f]
  | imp f g =>
    simp [CFormula.replaceOuter,CFormula.expand,Formula.subst,
      CFormula.replaceOuter_correct δ w f,
      CFormula.replaceOuter_correct δ w g]
  | all f =>
    simp only [CFormula.replaceOuter,CFormula.expand,Formula.subst]
    rw [CFormula.replaceOuter_correct δ w f,outerSubst_lift]
termination_by sizeOf f

theorem CFormula.replaceOuter_instantiate {r : Nat}
    (δ : Fin r → ClosedTerm) (w : ClosedTerm) (f : CFormula r 1) :
    f.replaceOuter.expand (Fin.lastCases w δ) =
      (f.expand δ).instantiate (Term.ofClosed w) := by
  rw [CFormula.replaceOuter_correct]
  change (f.expand δ).subst (outerSubst 0 w) =
    (f.expand δ).subst (instanceSubst (Term.ofClosed w))
  congr 1
  funext i
  have hi : i = 0 := Fin.fin_one_eq_zero i
  subst i
  change outerSubst 0 w (Fin.last 0) = instanceSubst (Term.ofClosed w) 0
  simp only [outerSubst,Fin.lastCases_last,instanceSubst,Fin.cases_zero]

end MAISO11.Wire

namespace MAISO11.Shared
open MAISO11.Wire MAISO11.Arithmetic MAISO11.Quotation

theorem closeTerm_ofClosed {m : Nat} (t : ClosedTerm) :
    closeTerm (Term.ofClosed t : Term m) = Term.ofClosed t := by
  induction t <;> simp [closeTerm,Term.ofClosed, *]

theorem erasedTerm_close {r m : Nat} (δ : Fin r → ClosedTerm)
    (t : CTerm r m) :
    Term.ofClosed (t.eraseVars.close δ) = closeTerm (t.expand δ) := by
  induction t with
  | var i => rfl
  | ref i => exact (closeTerm_ofClosed (δ i)).symm
  | zero => rfl
  | bit0 t ih => simp [CTerm.eraseVars,CTerm.close,CTerm.expand,
      Term.ofClosed,closeTerm,ih]
  | bit1 t ih => simp [CTerm.eraseVars,CTerm.close,CTerm.expand,
      Term.ofClosed,closeTerm,ih]
  | add s t hs ht => simp [CTerm.eraseVars,CTerm.close,CTerm.expand,
      Term.ofClosed,closeTerm,hs,ht]
  | mul s t hs ht => simp [CTerm.eraseVars,CTerm.close,CTerm.expand,
      Term.ofClosed,closeTerm,hs,ht]

def closedTermCandidates : ClosedTerm → List ClosedTerm
  | .zero => [.zero]
  | .bit0 t => .bit0 t :: closedTermCandidates t
  | .bit1 t => .bit1 t :: closedTermCandidates t
  | .add s t => .add s t :: (closedTermCandidates s ++ closedTermCandidates t)
  | .mul s t => .mul s t :: (closedTermCandidates s ++ closedTermCandidates t)

theorem closedTermCandidates_termCandidates {m : Nat} (t : ClosedTerm) :
    (closedTermCandidates t).map (fun u => (Term.ofClosed u : Term 0)) =
      termCandidates (Term.ofClosed t : Term m) := by
  induction t with
  | zero => rfl
  | bit0 t ih => simp [closedTermCandidates,termCandidates,
      Term.ofClosed,closeTerm,closeTerm_ofClosed,ih]
  | bit1 t ih => simp [closedTermCandidates,termCandidates,
      Term.ofClosed,closeTerm,closeTerm_ofClosed,ih]
  | add s t hs ht => simp [closedTermCandidates,termCandidates,
      Term.ofClosed,closeTerm,closeTerm_ofClosed,hs,ht]
  | mul s t hs ht => simp [closedTermCandidates,termCandidates,
      Term.ofClosed,closeTerm,closeTerm_ofClosed,hs,ht]

theorem closedTermCandidates_subterm {s t : ClosedTerm}
    (h : s ∈ closedTermCandidates t) : IsSubterm s t := by
  induction t with
  | zero => simp only [closedTermCandidates,List.mem_singleton] at h; subst s; exact .self
  | bit0 t ih =>
    rcases List.mem_cons.mp h with h | h
    · subst s; exact .self
    · exact .bit0 (ih h)
  | bit1 t ih =>
    rcases List.mem_cons.mp h with h | h
    · subst s; exact .self
    · exact .bit1 (ih h)
  | add a b ha hb =>
    rcases List.mem_cons.mp h with h | h
    · subst s; exact .self
    · rcases List.mem_append.mp h with h | h
      · exact .addLeft (ha h)
      · exact .addRight (hb h)
  | mul a b ha hb =>
    rcases List.mem_cons.mp h with h | h
    · subst s; exact .self
    · rcases List.mem_append.mp h with h | h
      · exact .mulLeft (ha h)
      · exact .mulRight (hb h)

/-- An expanded subterm inside a closed definition is represented by a
preexisting graph node, even when the compact formula mentions only its
outer abbreviation. -/
theorem reference_candidate_graph {r n m : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (δ : Fin r → ClosedTerm)
    (hδ : ∀ i, g.expand (refs i) = δ i) (i : Fin r)
    (u : Term 0) (h : u ∈ termCandidates ((CTerm.ref i : CTerm r m).expand δ)) :
    ∃ j : Fin n, Term.ofClosed (g.expand j) = u := by
  have he := closedTermCandidates_termCandidates (m:=m) (δ i)
  simp only [CTerm.expand] at h
  rw [← he] at h
  obtain ⟨v,hv,hu⟩ := List.mem_map.mp h
  obtain ⟨j,hj⟩ := g.subterm_has_node (refs i) v (by
    rw [hδ i]
    exact closedTermCandidates_subterm hv)
  exact ⟨j,by rw [hj,hu]⟩

def writtenTermCandidates {r m : Nat} (t : CTerm r m) : List (CTerm r 0) :=
  t.eraseVars :: match t with
  | .var _ | .ref _ | .zero => []
  | .bit0 s | .bit1 s => writtenTermCandidates s
  | .add s u | .mul s u => writtenTermCandidates s ++ writtenTermCandidates u

def writtenFormulaCandidates {r m : Nat} : CFormula r m → List (CTerm r 0)
  | .eq s t => writtenTermCandidates s ++ writtenTermCandidates t
  | .neg f => writtenFormulaCandidates f
  | .imp f h => writtenFormulaCandidates f ++ writtenFormulaCandidates h
  | .all f => writtenFormulaCandidates f

theorem writtenTermCandidates_length_le_weight {r m : Nat} (t : CTerm r m) :
    (writtenTermCandidates t).length ≤ t.weight := by
  induction t with
  | var i => simp [writtenTermCandidates,CTerm.weight]
  | ref i => simp [writtenTermCandidates,CTerm.weight]
  | zero => simp [writtenTermCandidates,CTerm.weight]
  | bit0 t ih => simp [writtenTermCandidates,CTerm.weight] at *; omega
  | bit1 t ih => simp [writtenTermCandidates,CTerm.weight] at *; omega
  | add s t hs ht => simp [writtenTermCandidates,CTerm.weight] at *; omega
  | mul s t hs ht => simp [writtenTermCandidates,CTerm.weight] at *; omega

theorem writtenFormulaCandidates_length_le_weight {r m : Nat}
    (f : CFormula r m) :
    (writtenFormulaCandidates f).length ≤ f.weight := by
  induction f with
  | eq s t =>
    have hs := writtenTermCandidates_length_le_weight s
    have ht := writtenTermCandidates_length_le_weight t
    simp [writtenFormulaCandidates,CFormula.weight] at *; omega
  | neg f ih => simp [writtenFormulaCandidates,CFormula.weight] at *; omega
  | imp f h hf hh =>
    simp [writtenFormulaCandidates,CFormula.weight] at *; omega
  | all f ih => simp [writtenFormulaCandidates,CFormula.weight] at *; omega

theorem writtenTermCandidates_cover {r n m : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (δ : Fin r → ClosedTerm)
    (hδ : ∀ i, g.expand (refs i) = δ i) (t : CTerm r m) :
    ∀ u : Term 0, u ∈ termCandidates (t.expand δ) →
      (∃ j : Fin n, Term.ofClosed (g.expand j) = u) ∨
      (∃ c ∈ writtenTermCandidates t, Term.ofClosed (c.close δ) = u) := by
  induction t with
  | var i =>
    intro u hu
    right
    refine ⟨.zero,by simp [writtenTermCandidates,CTerm.eraseVars],?_⟩
    have he : u = Term.zero := by simpa [termCandidates,CTerm.expand,closeTerm] using hu
    simp [CTerm.close,Term.ofClosed,he]
  | ref i =>
    intro u hu
    exact Or.inl (reference_candidate_graph g refs δ hδ i u hu)
  | zero =>
    intro u hu
    right
    refine ⟨.zero,by simp [writtenTermCandidates,CTerm.eraseVars],?_⟩
    have he : u = Term.zero := by simpa [termCandidates,CTerm.expand,closeTerm] using hu
    simp [CTerm.close,Term.ofClosed,he]
  | bit0 s ih =>
    intro u hu
    rcases List.mem_cons.mp hu with he | ht
    · right
      exact ⟨(CTerm.bit0 s).eraseVars,by simp [writtenTermCandidates],
        by rw [erasedTerm_close]; exact he.symm⟩
    · rcases ih u ht with ⟨j,hj⟩ | ⟨c,hc,he⟩
      · exact Or.inl ⟨j,hj⟩
      · exact Or.inr ⟨c,by simp [writtenTermCandidates,hc],he⟩
  | bit1 s ih =>
    intro u hu
    rcases List.mem_cons.mp hu with he | ht
    · right
      exact ⟨(CTerm.bit1 s).eraseVars,by simp [writtenTermCandidates],
        by rw [erasedTerm_close]; exact he.symm⟩
    · rcases ih u ht with ⟨j,hj⟩ | ⟨c,hc,he⟩
      · exact Or.inl ⟨j,hj⟩
      · exact Or.inr ⟨c,by simp [writtenTermCandidates,hc],he⟩
  | add s t hs ht =>
    intro u hu
    rcases List.mem_cons.mp hu with he | hu
    · right
      exact ⟨(CTerm.add s t).eraseVars,by simp [writtenTermCandidates],
        by rw [erasedTerm_close]; exact he.symm⟩
    · rcases List.mem_append.mp hu with hu | hu
      · rcases hs u hu with ⟨j,hj⟩ | ⟨c,hc,he⟩
        · exact Or.inl ⟨j,hj⟩
        · exact Or.inr ⟨c,by simp [writtenTermCandidates,hc],he⟩

      · rcases ht u hu with ⟨j,hj⟩ | ⟨c,hc,he⟩
        · exact Or.inl ⟨j,hj⟩
        · exact Or.inr ⟨c,by simp [writtenTermCandidates,hc],he⟩
  | mul s t hs ht =>
    intro u hu
    rcases List.mem_cons.mp hu with he | hu
    · right
      exact ⟨(CTerm.mul s t).eraseVars,by simp [writtenTermCandidates],
        by rw [erasedTerm_close]; exact he.symm⟩
    · rcases List.mem_append.mp hu with hu | hu
      · rcases hs u hu with ⟨j,hj⟩ | ⟨c,hc,he⟩
        · exact Or.inl ⟨j,hj⟩
        · exact Or.inr ⟨c,by simp [writtenTermCandidates,hc],he⟩
      · rcases ht u hu with ⟨j,hj⟩ | ⟨c,hc,he⟩
        · exact Or.inl ⟨j,hj⟩
        · exact Or.inr ⟨c,by simp [writtenTermCandidates,hc],he⟩

theorem writtenFormulaCandidates_cover {r n m : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (δ : Fin r → ClosedTerm)
    (hδ : ∀ i, g.expand (refs i) = δ i) (f : CFormula r m) :
    ∀ u : Term 0, u ∈ formulaCandidates (f.expand δ) →
      (∃ j : Fin n, Term.ofClosed (g.expand j) = u) ∨
      (∃ c ∈ writtenFormulaCandidates f, Term.ofClosed (c.close δ) = u) := by
  induction f with
  | eq s t =>
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · rcases writtenTermCandidates_cover g refs δ hδ s u hu with
        ⟨j,hj⟩ | ⟨c,hc,he⟩
      · exact Or.inl ⟨j,hj⟩
      · exact Or.inr ⟨c,by simp [writtenFormulaCandidates,hc],he⟩
    · rcases writtenTermCandidates_cover g refs δ hδ t u hu with
        ⟨j,hj⟩ | ⟨c,hc,he⟩
      · exact Or.inl ⟨j,hj⟩
      · exact Or.inr ⟨c,by simp [writtenFormulaCandidates,hc],he⟩
  | neg f ih =>
    intro u hu
    rcases ih u hu with ⟨j,hj⟩ | ⟨c,hc,he⟩
    · exact Or.inl ⟨j,hj⟩
    · exact Or.inr ⟨c,by simpa [writtenFormulaCandidates] using hc,he⟩
  | imp f h hf hh =>
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · rcases hf u hu with ⟨j,hj⟩ | ⟨c,hc,he⟩
      · exact Or.inl ⟨j,hj⟩
      · exact Or.inr ⟨c,by simp [writtenFormulaCandidates,hc],he⟩
    · rcases hh u hu with ⟨j,hj⟩ | ⟨c,hc,he⟩
      · exact Or.inl ⟨j,hj⟩
      · exact Or.inr ⟨c,by simp [writtenFormulaCandidates,hc],he⟩
  | all f ih =>
    intro u hu
    rcases ih u hu with ⟨j,hj⟩ | ⟨c,hc,he⟩
    · exact Or.inl ⟨j,hj⟩
    · exact Or.inr ⟨c,by simpa [writtenFormulaCandidates] using hc,he⟩

/-- Test a particular internal graph node as the closed witness. The graph's
existing equality engine compares terms below arbitrarily nested binders. -/
def compiledInstAtRoot {r n : Nat} (g : Graph n) (refs : Fin r → Fin n)
    (body : CFormula r 1) (target : CFormula r 0) (candidate : Fin n) : Bool :=
  compiledFormulaEqual g
    (Fin.lastCases candidate refs) body.replaceOuter
    (target.mapRefs Fin.castSucc)

theorem compiledInstAtRoot_correct {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (body : CFormula r 1)
    (target : CFormula r 0) (candidate : Fin n) :
    compiledInstAtRoot g refs body target candidate = true ↔
      (body.expand (fun i => g.expand (refs i))).instantiate
          (Term.ofClosed (g.expand candidate)) =
        target.expand (fun i => g.expand (refs i)) := by
  unfold compiledInstAtRoot
  rw [compiledFormulaEqual_correct]
  have href : (fun i => g.expand (Fin.lastCases candidate refs i)) =
      Fin.lastCases (g.expand candidate) (fun i => g.expand (refs i)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [href,CFormula.replaceOuter_instantiate,CFormula.mapRefs_correct]
  have he : ((Fin.lastCases (g.expand candidate) (fun i => g.expand (refs i))) ∘
      Fin.castSucc) = (fun i => g.expand (refs i)) := by
    funext i
    simp
  rw [he]

/-- Every written subterm becomes a candidate even if it contains a free
variable: erasing those variables supplies a closed term. A witness that
actually occurs in the conclusion loses no information under this erasure. -/
def compiledInstWithTerm {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (body : CFormula r 1)
    (target : CFormula r 0) (witness : CTerm r 0) : Bool :=
  let a := compileTerm g refs witness
  compiledInstAtRoot a.graph (fun i => a.lift (refs i)) body target a.root

theorem compiledInstWithTerm_correct {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (body : CFormula r 1)
    (target : CFormula r 0) (witness : CTerm r 0) :
    compiledInstWithTerm g refs body target witness = true ↔
      (body.expand (fun i => g.expand (refs i))).instantiate
          (Term.ofClosed (witness.close (fun i => g.expand (refs i)))) =
        target.expand (fun i => g.expand (refs i)) := by
  unfold compiledInstWithTerm
  rw [compiledInstAtRoot_correct]
  have hp := compileTerm_preserves g refs witness
  have hr := compileTerm_root g refs witness
  simp only [hr]
  have he : (fun i => (compileTerm g refs witness).graph.expand
      ((compileTerm g refs witness).lift (refs i))) =
      (fun i => g.expand (refs i)) := funext (fun i => hp (refs i))
  rw [he]

/-- This candidate set is finite in the compact input: existing nodes,
written subterms, and zero for vacuous substitution. -/
def compiledInstCandidates {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (body : CFormula r 1)
    (target : CFormula r 0) : Bool :=
  ((List.finRange n).any (compiledInstAtRoot g refs body target)) ||
    ((CTerm.zero :: writtenFormulaCandidates target).any
      (compiledInstWithTerm g refs body target))

theorem compiledInstCandidate_count_bound {r n : Nat}
    (target : CFormula r 0) :
    (List.finRange n).length +
      (CTerm.zero :: writtenFormulaCandidates target).length ≤
        n + 1 + target.weight := by
  have h := writtenFormulaCandidates_length_le_weight target
  simp only [List.length_finRange,List.length_cons]
  omega

theorem compiledInstCandidates_sound {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (body : CFormula r 1)
    (target : CFormula r 0)
    (h : compiledInstCandidates g refs body target = true) :
    IsAxiom (.imp (.all (body.expand (fun i => g.expand (refs i))))
      (target.expand (fun i => g.expand (refs i)))) := by
  simp only [compiledInstCandidates,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨i,_,hi⟩ | ⟨t,_,ht⟩
  · have he := (compiledInstAtRoot_correct g refs body target i).mp hi
    rw [← he]
    exact IsAxiom.inst _ _
  · have he := (compiledInstWithTerm_correct g refs body target t).mp ht
    rw [← he]
    exact IsAxiom.inst _ _

theorem compiledInstCandidates_complete {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (body : CFormula r 1)
    (target : CFormula r 0)
    (h : ∃ w : Term 0,
      (body.expand (fun i => g.expand (refs i))).instantiate w =
        target.expand (fun i => g.expand (refs i))) :
    compiledInstCandidates g refs body target = true := by
  let δ : Fin r → ClosedTerm := fun i => g.expand (refs i)
  obtain ⟨w,hw⟩ := h
  obtain ⟨u,hu,he⟩ := instance_candidate (body.expand δ) w
  have hin : (body.expand δ).instantiate u = target.expand δ := he.trans hw
  simp only [compiledInstCandidates,Bool.or_eq_true,List.any_eq_true]
  rcases List.mem_cons.mp hu with hz | ht
  · have hzero : u = Term.zero := hz
    have hi : compiledInstWithTerm g refs body target .zero = true := by
      rw [compiledInstWithTerm_correct]
      simpa [δ,CTerm.close,Term.ofClosed,hzero] using hin
    exact Or.inr ⟨.zero,by simp,hi⟩
  · rcases writtenFormulaCandidates_cover g refs δ (by intro i; rfl)
      target u (by rw [← hw]; exact ht) with ⟨j,hj⟩ | ⟨c,hc,hcval⟩
    · have hi : compiledInstAtRoot g refs body target j = true := by
        rw [compiledInstAtRoot_correct]
        simpa [δ,hj] using hin
      exact Or.inl ⟨j,by exact List.mem_ofFn.mpr ⟨j,rfl⟩,hi⟩
    · have hi : compiledInstWithTerm g refs body target c = true := by
        rw [compiledInstWithTerm_correct]
        simpa [δ,hcval] using hin
      exact Or.inr ⟨c,by simp [hc],hi⟩

/-- Exact graph decision procedure for arbitrary universal instantiation in
the restricted abbreviation grammar, including buried abbreviation subterms
and nested quantifiers in the quantified body. -/
theorem compiledInstCandidates_iff {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (body : CFormula r 1)
    (target : CFormula r 0) :
    compiledInstCandidates g refs body target = true ↔
      ∃ w : Term 0,
        (body.expand (fun i => g.expand (refs i))).instantiate w =
          target.expand (fun i => g.expand (refs i)) := by
  constructor
  · intro h
    simp only [compiledInstCandidates,Bool.or_eq_true,List.any_eq_true] at h
    rcases h with ⟨j,_,hj⟩ | ⟨c,_,hc⟩
    · exact ⟨Term.ofClosed (g.expand j),
        (compiledInstAtRoot_correct g refs body target j).mp hj⟩
    · exact ⟨Term.ofClosed (c.close (fun i => g.expand (refs i))),
        (compiledInstWithTerm_correct g refs body target c).mp hc⟩
  · exact compiledInstCandidates_complete g refs body target

/-- The complete compact replacement for the expanding `instCheck` branch. -/
def compiledInstShortcut {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) : CFormula r 0 → Bool
  | .imp (.all body) target => compiledInstCandidates g refs body target
  | _ => false

theorem instCheck_imp_all_iff (body : Formula 1) (target : Formula 0) :
    instCheck (.imp (.all body) target) = true ↔
      ∃ w : Term 0, body.instantiate w = target := by
  constructor
  · intro h
    obtain ⟨w,_,hw⟩ := List.any_eq_true.mp h
    exact ⟨w,of_decide_eq_true hw⟩
  · rintro ⟨w,hw⟩
    rw [← hw]
    exact instCheck_complete body w

theorem compiledInstShortcut_eq_instCheck {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (f : CFormula r 0) :
    compiledInstShortcut g refs f =
      instCheck (f.expand (fun i => g.expand (refs i))) := by
  cases f with
  | eq s t => rfl
  | neg q => rfl
  | all q => rfl
  | imp a b =>
    cases a with
    | eq s t => rfl
    | neg q => rfl
    | imp q v => rfl
    | all body =>
      have hi := compiledInstCandidates_iff g refs body b
      have hj := instCheck_imp_all_iff
        (body.expand (fun i => g.expand (refs i)))
        (b.expand (fun i => g.expand (refs i)))
      have he : compiledInstCandidates g refs body b =
          instCheck (Formula.imp (.all (body.expand (fun i => g.expand (refs i))))
            (b.expand (fun i => g.expand (refs i)))) := by
        cases hc : compiledInstCandidates g refs body b <;>
          cases hd : instCheck (Formula.imp (.all
            (body.expand (fun i => g.expand (refs i))))
            (b.expand (fun i => g.expand (refs i)))) <;>
          simp_all [hi,hj]
      exact he

/-- Axiom recognition now has a complete, graph-based early branch for the
universal-instantiation family. Remaining failed cases pass to the existing
exact axiom checker. -/
def compiledAxiomCheckInst {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (δ : Fin r → ClosedTerm)
    (f : CFormula r 0) : Bool :=
  compiledInstShortcut g refs f || compiledAxiomCheck g refs δ f

theorem compiledAxiomCheckInst_eq_reference {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (δ : Fin r → ClosedTerm)
    (hδ : ∀ i, g.expand (refs i) = δ i) (f : CFormula r 0) :
    compiledAxiomCheckInst g refs δ f = axiomCheck (f.expand δ) := by
  have henv : (fun i => g.expand (refs i)) = δ := funext hδ
  unfold compiledAxiomCheckInst
  rw [compiledInstShortcut_eq_instCheck,henv,
    compiledAxiomCheck_eq_reference g refs δ hδ]
  cases hi : instCheck (f.expand δ) <;> simp [MAISO11.Wire.axiomCheck,hi]

private def hiddenGraph : Graph 3 :=
  .snoc (.snoc (.snoc .nil .zero) (.bit1 (Fin.last 0)))
    (.add (Fin.last 1) (Fin.castSucc (Fin.last 0)))

private def hiddenRefs : Fin 1 → Fin 3 := fun _ => Fin.last 2

private def hiddenCompactBody : CFormula 1 1 :=
  .eq (.add (.var 0) .zero) (.add (.var 0) .zero)

private def hiddenCompactConclusion : CFormula 1 0 := .eq (.ref 0) (.ref 0)

/-- A concrete witness occurs only inside the definition of `u₀`. -/
theorem hiddenInternalNodeAccepted :
    compiledInstAtRoot hiddenGraph hiddenRefs hiddenCompactBody
      hiddenCompactConclusion (Fin.castSucc (Fin.last 1)) = true := by
  rw [compiledInstAtRoot_correct]
  simp only [hiddenGraph,hiddenRefs,Graph.expand,Fin.lastCases_last,
    Fin.lastCases_castSucc,Node.expand]
  simp [hiddenCompactBody,hiddenCompactConclusion,CFormula.expand,CTerm.expand,
    Formula.instantiate,Formula.subst,Term.subst,Term.ofClosed,instanceSubst]

theorem hiddenInstShortcutAccepted :
    compiledInstShortcut hiddenGraph hiddenRefs
      (.imp (.all hiddenCompactBody) hiddenCompactConclusion) = true := by
  simp only [compiledInstShortcut,compiledInstCandidates,
    Bool.or_eq_true,List.any_eq_true]
  exact Or.inl ⟨Fin.castSucc (Fin.last 1),
    List.mem_ofFn.mpr ⟨_,rfl⟩,hiddenInternalNodeAccepted⟩

#print axioms CFormula.replaceOuter_instantiate
#print axioms compiledInstCandidates_iff
#print axioms compiledInstShortcut_eq_instCheck
#print axioms compiledAxiomCheckInst_eq_reference
#print axioms hiddenInstShortcutAccepted

end MAISO11.Shared

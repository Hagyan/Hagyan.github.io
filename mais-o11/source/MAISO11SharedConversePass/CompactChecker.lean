import CompactParser
set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Wire
open Arithmetic

/-- Erase free variables; this recovers a closed instance term even under binders. -/
def closeTerm {n : Nat} : Term n → Term 0
  | .var _ => .zero
  | .zero => .zero
  | .bit0 t => .bit0 (closeTerm t)
  | .bit1 t => .bit1 (closeTerm t)
  | .add s t => .add (closeTerm s) (closeTerm t)
  | .mul s t => .mul (closeTerm s) (closeTerm t)

def termCandidates {n : Nat} (t : Term n) : List (Term 0) :=
  closeTerm t :: match t with
  | .var _ | .zero => []
  | .bit0 s | .bit1 s => termCandidates s
  | .add s u | .mul s u => termCandidates s ++ termCandidates u

theorem closeTerm_mem {n : Nat} (t : Term n) : closeTerm t ∈ termCandidates t := by
  cases t <;> simp [termCandidates]

def formulaCandidates {n : Nat} : Formula n → List (Term 0)
  | .eq s t => termCandidates s ++ termCandidates t
  | .neg f => formulaCandidates f
  | .imp f g => formulaCandidates f ++ formulaCandidates g
  | .all f => formulaCandidates f

theorem closeTerm_rename {n m : Nat} (t : Term n) (ρ : Fin n → Fin m) :
    closeTerm (t.subst (fun i => .var (ρ i))) = closeTerm t := by
  induction t <;> simp_all [Term.subst,closeTerm]

theorem closeTerm_closed (t : Term 0) : closeTerm t = t := by
  induction t with
  | var i => exact Fin.elim0 i
  | zero => rfl
  | bit0 t ih => simp [closeTerm,ih]
  | bit1 t ih => simp [closeTerm,ih]
  | add s t hs ht => simp [closeTerm,hs,ht]
  | mul s t hs ht => simp [closeTerm,hs,ht]

/-- If a changed substitution entry is not among the resulting subterms,
then it cannot affect the expression. -/
theorem term_subst_unchanged {n m : Nat} (s : Term n)
    (σ τ : Fin n → Term m) (t : Term 0)
    (hd : ∀ i, σ i ≠ τ i → closeTerm (σ i) = t)
    (hn : t ∉ termCandidates (s.subst σ)) : s.subst σ = s.subst τ := by
  induction s with
  | var i =>
    by_cases h : σ i = τ i
    · exact h
    · have he := hd i h
      apply False.elim
      apply hn
      simpa only [Term.subst,he] using closeTerm_mem (σ i)
  | zero => rfl
  | bit0 s ih =>
    have hs : t ∉ termCandidates (s.subst σ) := by
      intro h; exact hn (by simp [Term.subst,termCandidates,h])
    simp [Term.subst,ih hs]
  | bit1 s ih =>
    have hs : t ∉ termCandidates (s.subst σ) := by
      intro h; exact hn (by simp [Term.subst,termCandidates,h])
    simp [Term.subst,ih hs]
  | add s u hs hu =>
    have h₁ : t ∉ termCandidates (s.subst σ) := by
      intro h; exact hn (by simp [Term.subst,termCandidates,h])
    have h₂ : t ∉ termCandidates (u.subst σ) := by
      intro h; exact hn (by simp [Term.subst,termCandidates,h])
    simp [Term.subst,hs h₁,hu h₂]
  | mul s u hs hu =>
    have h₁ : t ∉ termCandidates (s.subst σ) := by
      intro h; exact hn (by simp [Term.subst,termCandidates,h])
    have h₂ : t ∉ termCandidates (u.subst σ) := by
      intro h; exact hn (by simp [Term.subst,termCandidates,h])
    simp [Term.subst,hs h₁,hu h₂]

theorem formula_subst_unchanged {n m : Nat} (f : Formula n)
    (σ τ : Fin n → Term m) (t : Term 0)
    (hd : ∀ i, σ i ≠ τ i → closeTerm (σ i) = t)
    (hn : t ∉ formulaCandidates (f.subst σ)) : f.subst σ = f.subst τ := by
  induction f generalizing m with
  | eq s u =>
    have h₁ : t ∉ termCandidates (s.subst σ) := by
      intro h; exact hn (by simp [Formula.subst,formulaCandidates,h])
    have h₂ : t ∉ termCandidates (u.subst σ) := by
      intro h; exact hn (by simp [Formula.subst,formulaCandidates,h])
    simp [Formula.subst,term_subst_unchanged s σ τ t hd h₁,
      term_subst_unchanged u σ τ t hd h₂]
  | neg f ih =>
    simpa only [Formula.subst] using congrArg Formula.neg (ih σ τ hd hn)
  | imp f g hf hg =>
    have h₁ : t ∉ formulaCandidates (f.subst σ) := by
      intro h; exact hn (by simp [Formula.subst,formulaCandidates,h])
    have h₂ : t ∉ formulaCandidates (g.subst σ) := by
      intro h; exact hn (by simp [Formula.subst,formulaCandidates,h])
    simp [Formula.subst,hf σ τ hd h₁,hg σ τ hd h₂]
  | all f ih =>
    have hl : ∀ i, liftSubst σ i ≠ liftSubst τ i →
        closeTerm (liftSubst σ i) = t := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [liftSubst]
      · intro h
        have hj : σ j ≠ τ j := by
          intro he
          exact h (by simp [liftSubst,he])
        simpa [liftSubst,closeTerm_rename] using hd j hj
    simpa only [Formula.subst] using
      congrArg Formula.all (ih (liftSubst σ) (liftSubst τ) hl hn)

theorem instance_candidate (f : Formula 1) (t : Term 0) :
    ∃ u ∈ (Term.zero :: formulaCandidates (f.instantiate t)),
      f.instantiate u = f.instantiate t := by
  by_cases ht : t ∈ formulaCandidates (f.instantiate t)
  · exact ⟨t,by simp [ht],rfl⟩
  · refine ⟨.zero,by simp,?_⟩
    apply Eq.symm
    apply formula_subst_unchanged f (instanceSubst t) (instanceSubst .zero) t
    · intro i _
      have hi : i = 0 := by apply Fin.ext; omega
      subst i
      exact closeTerm_closed t
    · exact ht

/-- Search witnesses in the result itself, with zero for vacuous substitution. -/
def instCheck : Formula 0 → Bool
  | .imp (.all f) g => (.zero :: formulaCandidates g).any
      (fun t => decide (f.instantiate t = g))
  | _ => false

def contrapCheck : Formula 0 → Bool
  | .imp (.imp a (.neg b)) g => decide (g = .imp b (.neg a))
  | _ => false

def conjCheck : Formula 0 → Bool
  | .imp a (.imp b c) => decide (c = a.conj b)
  | _ => false

def axiomCheck (f : Formula 0) : Bool :=
  decide (f = .all (.eq (.var 0) (.var 0))) ||
    instCheck f || contrapCheck f || conjCheck f

theorem instCheck_sound {f : Formula 0} (h : instCheck f = true) : IsAxiom f := by
  unfold instCheck at h
  split at h
  next a b =>
    obtain ⟨t,_,ht⟩ := List.any_eq_true.mp h
    have he : a.instantiate t = b := of_decide_eq_true ht
    rw [← he]
    exact .inst a t
  next => contradiction

theorem contrapCheck_sound {f : Formula 0} (h : contrapCheck f = true) : IsAxiom f := by
  unfold contrapCheck at h
  split at h
  next a b c =>
    have he : c = .imp b (.neg a) := of_decide_eq_true h
    rw [he]
    exact .contrap a b
  next => contradiction

theorem conjCheck_sound {f : Formula 0} (h : conjCheck f = true) : IsAxiom f := by
  unfold conjCheck at h
  split at h
  next a b c =>
    have he : c = a.conj b := of_decide_eq_true h
    rw [he]
    exact .conjIntro a b
  next => contradiction

theorem axiomCheck_sound {f : Formula 0} (h : axiomCheck f = true) : IsAxiom f := by
  simp only [axiomCheck,Bool.or_eq_true,decide_eq_true_eq] at h
  rcases h with ((h | h) | h) | h
  · rw [h]; exact .universalRefl
  · exact instCheck_sound h
  · exact contrapCheck_sound h
  · exact conjCheck_sound h

theorem instCheck_complete (f : Formula 1) (t : Term 0) :
    instCheck (.imp (.all f) (f.instantiate t)) = true := by
  obtain ⟨u,hu,he⟩ := instance_candidate f t
  exact List.any_eq_true.mpr ⟨u,hu,by simp [he]⟩

theorem axiomCheck_complete {f : Formula 0} (h : IsAxiom f) : axiomCheck f = true := by
  cases h with
  | universalRefl => simp [axiomCheck]
  | inst f t => simp [axiomCheck,instCheck_complete]
  | contrap a b => simp [axiomCheck,contrapCheck]
  | conjIntro a b => simp [axiomCheck,conjCheck]

theorem axiomCheck_iff (f : Formula 0) : axiomCheck f = true ↔ IsAxiom f :=
  ⟨axiomCheck_sound,axiomCheck_complete⟩

def Record.check {r k : Nat} (δ : Fin r → Quotation.ClosedTerm) (fs : Records r k) :
    Record r k → Bool
  | .axiom f => axiomCheck (f.expand δ)
  | .mp a b f => decide ((fs.get b).expand δ =
      Formula.imp ((fs.get a).expand δ) (f.expand δ))

def Records.check {r k : Nat} (δ : Fin r → Quotation.ClosedTerm) : Records r k → Bool
  | .nil => true
  | .snoc fs f => fs.check δ && f.check δ fs

theorem Record.check_iff {r k : Nat} (δ : Fin r → Quotation.ClosedTerm)
    (fs : Records r k) (f : Record r k) : f.check δ fs = true ↔ f.valid δ fs := by
  cases f <;> simp [check,valid,axiomCheck_iff]

theorem Records.check_iff {r k : Nat} (δ : Fin r → Quotation.ClosedTerm)
    (fs : Records r k) : fs.check δ = true ↔ fs.valid δ := by
  induction fs with
  | nil => simp [check,valid]
  | snoc fs f ih => simp [check,valid,Record.check_iff,ih]


theorem Records.check_derivable {r k : Nat} (δ : Fin r → Quotation.ClosedTerm)
    (fs : Records r k) (h : fs.check δ = true) (i : Fin k) :
    Nonempty (Derivation ((fs.get i).expand δ)) :=
  fs.valid_derivable δ ((fs.check_iff δ).mp h) i

/-- Lookup in the environment actually returned by the definition parser. -/
def envDictionary {r : Nat} (env : List Quotation.ClosedTerm)
    (h : env.length = r) (i : Fin r) : Quotation.ClosedTerm :=
  env[i.val]'(by rw [h]; exact i.isLt)

@[simp] theorem envDictionary_ofFn {r : Nat} (δ : Fin r → Quotation.ClosedTerm)
    (h : (List.ofFn δ).length = r) : envDictionary (List.ofFn δ) h = δ := by
  funext i
  simp [envDictionary]

/-- Return the final expanded formula only after checking every proof record. -/
def checkDecoded {r k : Nat} (env : List Quotation.ClosedTerm)
    (fs : Records r k) : Option (Formula 0) :=
  if h : env.length = r then
    let δ := envDictionary env h
    if fs.check δ then
      if hk : 0 < k then some ((fs.get ⟨k-1,by omega⟩).expand δ) else none
    else none
  else none

def checkWhole (r count : Nat) (cs : List Char) : Option (Formula 0) := do
  let ⟨env,_k,fs⟩ ← decodeWhole r count cs
  checkDecoded env fs

theorem checkDecoded_sound {r k : Nat} {env : List Quotation.ClosedTerm}
    {fs : Records r k} {f : Formula 0} (h : checkDecoded env fs = some f) :
    Nonempty (Derivation f) := by
  unfold checkDecoded at h
  split at h
  next hlen =>
    dsimp at h
    split at h
    next hc =>
      split at h
      next hk =>
        have he := Option.some.inj h
        rw [← he]
        exact fs.check_derivable (envDictionary env hlen) hc ⟨k-1,by omega⟩
      next => contradiction
    next => contradiction
  next => contradiction

theorem checkWhole_sound {r count : Nat} {cs : List Char} {f : Formula 0}
    (h : checkWhole r count cs = some f) : Nonempty (Derivation f) := by
  unfold checkWhole at h
  cases hd : decodeWhole r count cs with
  | none => simp [hd] at h
  | some result =>
    obtain ⟨env,k,fs⟩ := result
    simp only [hd,Option.bind_some] at h
    exact checkDecoded_sound h

theorem checkWhole_complete {n k : Nat} (p : Quotation.Program n)
    (fs : Records (3*n+n) k) (last : Fin k) (hl : last.val+1=k)
    (hv : fs.valid (dictionary p)) :
    checkWhole (3*n+n) k (definitionPrelude p ++ fs.wire) =
      some ((fs.get last).expand (dictionary p)) := by
  have hc := (fs.check_iff (dictionary p)).mpr hv
  have hk : 0 < k := by omega
  have hi : (⟨k-1,by omega⟩ : Fin k) = last := by
    apply Fin.ext; dsimp; omega
  simp [checkWhole,decodeWhole_compiled,checkDecoded,hc,hk,hi]

/-- The previously bounded serialized trace now passes the executable checker. -/
theorem compiled_trace_checked {b n : Nat} (g : Quotation.Grammar b n) :
    ∃ (k : Nat) (fs : Records (3*n+n) k),
      k ≤ traceN n ∧
      checkWhole (3*n+n) k (definitionPrelude (Quotation.compile g) ++ fs.wire) =
        some ((trace n).expand (dictionary (Quotation.compile g))) ∧
      (definitionPrelude (Quotation.compile g) ++ fs.wire).length ≤
        fullCharacters b g.mass g.mass := by
  obtain ⟨k,fs,last,hk,hl,hf,_,hv,hc⟩ := compiled_trace_whole g
  refine ⟨k,fs,hk,?_,hc⟩
  rw [checkWhole_complete (Quotation.compile g) fs last hl hv,hf]
end MAISO11.Wire

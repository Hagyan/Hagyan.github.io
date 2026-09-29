import TracePacking

/-! Literal first-order arithmetic syntax and a small Hilbert fragment.
No arithmetic truth rule is provided. Existential introduction is derived
from universal instantiation, a propositional tautology, and modus ponens.
This is not a full PA-bin file checker or a proof of polynomial Bew costs. -/
set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Arithmetic

inductive Term (n : Nat) where
  | var : Fin n → Term n
  | zero : Term n
  | bit0 : Term n → Term n
  | bit1 : Term n → Term n
  | add : Term n → Term n → Term n
  | mul : Term n → Term n → Term n
  deriving DecidableEq, Repr

def Term.eval {n : Nat} (ρ : Fin n → Nat) : Term n → Nat
  | .var i => ρ i
  | .zero => 0
  | .bit0 t => 2 * t.eval ρ
  | .bit1 t => 2 * t.eval ρ + 1
  | .add s t => s.eval ρ + t.eval ρ
  | .mul s t => s.eval ρ * t.eval ρ

def Term.subst {n m : Nat} (σ : Fin n → Term m) : Term n → Term m
  | .var i => σ i
  | .zero => .zero
  | .bit0 t => .bit0 (t.subst σ)
  | .bit1 t => .bit1 (t.subst σ)
  | .add s t => .add (s.subst σ) (t.subst σ)
  | .mul s t => .mul (s.subst σ) (t.subst σ)

theorem Term.eval_subst {n m : Nat} (σ : Fin n → Term m) (ρ : Fin m → Nat)
    (t : Term n) : (t.subst σ).eval ρ = t.eval (fun i => (σ i).eval ρ) := by
  induction t <;> simp_all [subst, eval]

def extend {n : Nat} (a : Nat) (ρ : Fin n → Nat) : Fin (n + 1) → Nat :=
  Fin.cases a ρ

@[simp] theorem fin_cases_one {α : Type} {n : Nat} (a : α) (f : Fin (n+1) → α) :
    Fin.cases a f (1 : Fin (n+2)) = f 0 := rfl

def liftSubst {n m : Nat} (σ : Fin n → Term m) : Fin (n + 1) → Term (m + 1) :=
  Fin.cases (.var 0) (fun i => (σ i).subst (fun j => .var j.succ))

theorem liftSubst_eval {n m : Nat} (σ : Fin n → Term m)
    (ρ : Fin m → Nat) (a : Nat) :
    (fun i => (liftSubst σ i).eval (extend a ρ)) =
      extend a (fun i => (σ i).eval ρ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [liftSubst, extend, Term.eval_subst, Term.eval]

inductive Formula : Nat → Type where
  | eq {n : Nat} : Term n → Term n → Formula n
  | neg {n : Nat} : Formula n → Formula n
  | imp {n : Nat} : Formula n → Formula n → Formula n
  | all {n : Nat} : Formula (n + 1) → Formula n
  deriving DecidableEq, Repr

def Formula.realize {n : Nat} (ρ : Fin n → Nat) : Formula n → Prop
  | .eq s t => s.eval ρ = t.eval ρ
  | .neg f => ¬ f.realize ρ
  | .imp f g => f.realize ρ → g.realize ρ
  | .all f => ∀ a, f.realize (extend a ρ)

def Formula.subst {n m : Nat} (σ : Fin n → Term m) : Formula n → Formula m
  | .eq s t => .eq (s.subst σ) (t.subst σ)
  | .neg f => .neg (f.subst σ)
  | .imp f g => .imp (f.subst σ) (g.subst σ)
  | .all f => .all (f.subst (liftSubst σ))

theorem Formula.realize_subst {n m : Nat} (f : Formula n)
    (σ : Fin n → Term m) (ρ : Fin m → Nat) :
    (f.subst σ).realize ρ ↔ f.realize (fun i => (σ i).eval ρ) := by
  induction f generalizing m with
  | eq s t => simp [subst, realize, Term.eval_subst]
  | neg f ih => simp [subst, realize, ih]
  | imp f g hf hg => simp [subst, realize, hf, hg]
  | all f ih =>
    simp only [subst, realize]
    apply forall_congr'
    intro a
    rw [ih, liftSubst_eval]

def Formula.ex {n : Nat} (f : Formula (n + 1)) : Formula n := .neg (.all (.neg f))
def Formula.conj {n : Nat} (f g : Formula n) : Formula n := .neg (.imp f (.neg g))

theorem Formula.realize_ex {n : Nat} (f : Formula (n + 1)) (ρ : Fin n → Nat) :
    f.ex.realize ρ ↔ ∃ a, f.realize (extend a ρ) := by
  classical
  simp [ex, realize]

theorem Formula.realize_conj {n : Nat} (f g : Formula n) (ρ : Fin n → Nat) :
    (f.conj g).realize ρ ↔ f.realize ρ ∧ g.realize ρ := by
  classical
  simp [conj, realize, not_imp]

def instanceSubst {n : Nat} (t : Term n) : Fin (n + 1) → Term n :=
  Fin.cases t Term.var

def Formula.instantiate {n : Nat} (f : Formula (n + 1)) (t : Term n) : Formula n :=
  f.subst (instanceSubst t)

theorem Formula.realize_instantiate {n : Nat} (f : Formula (n + 1))
    (t : Term n) (ρ : Fin n → Nat) :
    (f.instantiate t).realize ρ ↔ f.realize (extend (t.eval ρ) ρ) := by
  rw [instantiate, realize_subst]
  have he : (fun i => (instanceSubst t i).eval ρ) = extend (t.eval ρ) ρ := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [he]

/-- A restricted ordinary Hilbert calculus: all four axiom families below
are instances of equality, quantifier, or propositional Enderton axioms.
In particular, semantic truth is not an axiom or inference rule. -/
inductive Derivation {n : Nat} : Formula n → Type where
  | universalRefl : Derivation (.all (.eq (.var 0) (.var 0)))
  | inst (f : Formula (n + 1)) (t : Term n) :
      Derivation (.imp (.all f) (f.instantiate t))
  | contrap (a b : Formula n) :
      Derivation (.imp (.imp a (.neg b)) (.imp b (.neg a)))
  | conjIntro (a b : Formula n) : Derivation (.imp a (.imp b (a.conj b)))
  | mp {a b : Formula n} : Derivation a → Derivation (.imp a b) → Derivation b

theorem Derivation.sound {n : Nat} {f : Formula n} (d : Derivation f)
    (ρ : Fin n → Nat) : f.realize ρ := by
  induction d with
  | universalRefl => intro a; rfl
  | inst f t =>
    intro h
    exact (Formula.realize_instantiate f t ρ).mpr (h (t.eval ρ))
  | contrap a b => exact fun hab hb ha => hab ha hb
  | conjIntro a b =>
    intro ha hb
    exact (Formula.realize_conj a b ρ).mpr ⟨ha, hb⟩
  | mp da dab ha hab => exact hab ha

/-- Term reflexivity is derived from the universally closed variable axiom;
it is not silently added as a new Enderton axiom family. -/
def Derivation.refl {n : Nat} (t : Term n) : Derivation (.eq t t) :=
  .mp .universalRefl (.inst (.eq (.var 0) (.var 0)) t)

def Derivation.conjunction {n : Nat} {a b : Formula n}
    (da : Derivation a) (db : Derivation b) : Derivation (a.conj b) :=
  .mp db (.mp da (.conjIntro a b))

/-- Existential introduction is derived, not postulated as a new axiom. -/
def Derivation.existsIntro {n : Nat} (f : Formula (n + 1)) (t : Term n)
    (d : Derivation (f.instantiate t)) : Derivation f.ex :=
  .mp d (.mp (.inst (.neg f) t) (.contrap (.all (.neg f)) (f.instantiate t)))

def Term.ofClosed {n : Nat} : Quotation.ClosedTerm → Term n
  | .zero => .zero
  | .bit0 t => .bit0 (ofClosed t)
  | .bit1 t => .bit1 (ofClosed t)
  | .add s t => .add (ofClosed s) (ofClosed t)
  | .mul s t => .mul (ofClosed s) (ofClosed t)

theorem Term.eval_ofClosed {n : Nat} (t : Quotation.ClosedTerm) (ρ : Fin n → Nat) :
    (ofClosed t).eval ρ = t.eval := by
  induction t <;> simp_all [ofClosed, eval, Quotation.ClosedTerm.eval]

def Term.pair {n : Nat} (a b : Term n) : Term n :=
  .add (.add (.mul (.add a b) (.add a b)) a) (.bit1 .zero)

theorem Term.eval_pair {n : Nat} (a b : Term n) (ρ : Fin n → Nat) :
    (a.pair b).eval ρ = Quotation.arithPair (a.eval ρ) (b.eval ρ) := by
  simp [pair, eval, Quotation.arithPair]

theorem Term.subst_pair {n m : Nat} (a b : Term n) (σ : Fin n → Term m) :
    (a.pair b).subst σ = (a.subst σ).pair (b.subst σ) := rfl

theorem Term.subst_comp {n m k : Nat} (t : Term n)
    (σ : Fin n → Term m) (τ : Fin m → Term k) :
    (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) := by
  induction t <;> simp_all [subst]

@[simp] theorem Term.subst_id {n : Nat} (t : Term n) : t.subst Term.var = t := by
  induction t <;> simp_all [subst]

def Term.up {n : Nat} (t : Term n) : Term (n + 1) := t.subst (fun i => .var i.succ)

@[simp] theorem Term.eval_up {n : Nat} (t : Term n) (a : Nat) (ρ : Fin n → Nat) :
    t.up.eval (extend a ρ) = t.eval ρ := by
  simp [up, eval_subst, eval, extend]

@[simp] theorem Term.subst_up_instance {n : Nat} (t w : Term n) :
    t.up.subst (instanceSubst w) = t := by
  simp [up, subst_comp, subst, instanceSubst]

theorem Term.subst_up_lift {n m : Nat} (t : Term n) (σ : Fin n → Term m) :
    t.up.subst (liftSubst σ) = (t.subst σ).up := by
  simp [up, subst_comp, subst, liftSubst]

def Derivation.nodes {n : Nat} {f : Formula n} : Derivation f → Nat
  | .universalRefl => 1
  | .inst _ _ => 1
  | .contrap _ _ => 1
  | .conjIntro _ _ => 1
  | .mp d e => d.nodes + e.nodes + 1

theorem Derivation.existsIntro_nodes {n : Nat} (f : Formula (n + 1)) (t : Term n)
    (d : Derivation (f.instantiate t)) : (existsIntro f t d).nodes = d.nodes + 4 := by
  simp [existsIntro, nodes, Nat.add_assoc]

def Within {n : Nat} (f : Formula n) (k : Nat) : Prop :=
  ∃ d : Derivation f, d.nodes ≤ k

theorem Within.refl {n : Nat} (t : Term n) : Within (.eq t t) 3 :=
  ⟨.refl t, Nat.le_refl 3⟩

theorem Within.existsIntro {n : Nat} (f : Formula (n+1)) (t : Term n) (k : Nat)
    (h : Within (f.instantiate t) k) : Within f.ex (k+4) := by
  obtain ⟨d,hd⟩ := h
  exact ⟨d.existsIntro f t, by rw [Derivation.existsIntro_nodes]; omega⟩

theorem Within.conjunction {n : Nat} (a b : Formula n) (ka kb : Nat)
    (ha : Within a ka) (hb : Within b kb) : Within (a.conj b) (ka+kb+3) := by
  obtain ⟨da,hda⟩ := ha
  obtain ⟨db,hdb⟩ := hb
  refine ⟨da.conjunction db, ?_⟩
  simp only [Derivation.conjunction, Derivation.nodes]
  omega

end MAISO11.Arithmetic

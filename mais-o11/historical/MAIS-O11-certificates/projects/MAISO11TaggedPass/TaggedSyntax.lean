import Std

/-!
Concrete syntax certificate for the connective-tagged checker.

This module implements terms, capture-avoiding substitution, formulas, tags,
and the guard predicate. It does not implement PA's axioms, arithmetic
coding, the diagonal lemma, or the complete proof-file checker.

`conj` is a PRIMITIVE connective. It is not expanded to negation/implication.
The core arithmetic fragment uses only eq, neg, imp, and all.
-/

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Tagged

inductive Term where
  | var : Nat → Term
  | zero : Term
  | succ : Term → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
  | bit0 : Term → Term
  | bit1 : Term → Term
  deriving DecidableEq, Repr

def Term.rename (ρ : Nat → Nat) : Term → Term
  | .var n => .var (ρ n)
  | .zero => .zero
  | .succ t => .succ (t.rename ρ)
  | .add s t => .add (s.rename ρ) (t.rename ρ)
  | .mul s t => .mul (s.rename ρ) (t.rename ρ)
  | .bit0 t => .bit0 (t.rename ρ)
  | .bit1 t => .bit1 (t.rename ρ)

def Term.subst (σ : Nat → Term) : Term → Term
  | .var n => σ n
  | .zero => .zero
  | .succ t => .succ (t.subst σ)
  | .add s t => .add (s.subst σ) (t.subst σ)
  | .mul s t => .mul (s.subst σ) (t.subst σ)
  | .bit0 t => .bit0 (t.subst σ)
  | .bit1 t => .bit1 (t.subst σ)

/-- Lift a simultaneous substitution underneath a de Bruijn binder. -/
def liftSubst (σ : Nat → Term) : Nat → Term
  | 0 => .var 0
  | n + 1 => (σ n).rename Nat.succ

inductive Formula where
  | eq : Term → Term → Formula
  | neg : Formula → Formula
  | imp : Formula → Formula → Formula
  | all : Formula → Formula
  | conj : Formula → Formula → Formula
  deriving DecidableEq, Repr

def Formula.subst (σ : Nat → Term) : Formula → Formula
  | .eq s t => .eq (s.subst σ) (t.subst σ)
  | .neg A => .neg (A.subst σ)
  | .imp A B => .imp (A.subst σ) (B.subst σ)
  | .all A => .all (A.subst (liftSubst σ))
  | .conj A B => .conj (A.subst σ) (B.subst σ)

inductive Shape where
  | atom : Shape
  | neg : Shape → Shape
  | imp : Shape → Shape → Shape
  | all : Shape → Shape
  | conj : Shape → Shape → Shape
  deriving DecidableEq, Repr

def Formula.shape : Formula → Shape
  | .eq _ _ => .atom
  | .neg A => .neg A.shape
  | .imp A B => .imp A.shape B.shape
  | .all A => .all A.shape
  | .conj A B => .conj A.shape B.shape

@[simp] theorem shape_subst (A : Formula) (σ : Nat → Term) :
    (A.subst σ).shape = A.shape := by
  induction A generalizing σ <;> simp_all [Formula.subst, Formula.shape]

/-- Decode the length of a conjunction chain whose left children are atomic.
Terms and the truth values of the atoms play no role in recognition. -/
def decodeTag : Shape → Option Nat
  | .atom => some 0
  | .conj .atom t => (decodeTag t).map Nat.succ
  | _ => none

/-- Every conjunction whose left operand decodes to j incurs guard H(j). -/
def guardIndices : Shape → List Nat
  | .atom => []
  | .neg A => guardIndices A
  | .imp A B => guardIndices A ++ guardIndices B
  | .all A => guardIndices A
  | .conj A B => (decodeTag A).toList ++ guardIndices A ++ guardIndices B

def Guarded (H : Nat → Prop) (A : Formula) : Prop :=
  ∀ j ∈ guardIndices A.shape, H j

@[simp] theorem guarded_subst (H : Nat → Prop) (A : Formula) (σ : Nat → Term) :
    Guarded H (A.subst σ) ↔ Guarded H A := by
  simp [Guarded]

def top : Formula := .eq .zero .zero

def tag : Nat → Formula
  | 0 => top
  | n + 1 => .conj top (tag n)

def target (D : Nat → Formula) (n : Nat) : Formula := .conj (tag n) (D n)

@[simp] theorem decode_tag (n : Nat) : decodeTag (tag n).shape = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tag, top, Formula.shape, decodeTag, ih]

theorem tag_injective : ∀ m n, tag m = tag n → m = n := by
  intro m n h
  have hh := congrArg (fun A : Formula => decodeTag A.shape) h
  simpa using hh

theorem target_injective (D : Nat → Formula) :
    ∀ m n, target D m = target D n → m = n := by
  intro m n h
  have ht : tag m = tag n := (Formula.conj.inj h).1
  exact tag_injective m n ht

theorem index_in_target (D : Nat → Formula) (n : Nat) :
    n ∈ guardIndices (target D n).shape := by
  simp [target, Formula.shape, guardIndices]

/-- This is the structural reason accepted proofs of P_n must pass H(n). -/
theorem target_guard (H : Nat → Prop) (D : Nat → Formula) (n : Nat)
    (h : Guarded H (target D n)) : H n :=
  h n (index_in_target D n)

theorem guarded_imp (H : Nat → Prop) (A B : Formula) :
    Guarded H (.imp A B) ↔ Guarded H A ∧ Guarded H B := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (List.mem_append_left _ hj),
      fun j hj => h j (List.mem_append_right _ hj)⟩
  · intro h j hj
    cases List.mem_append.mp hj with
    | inl ha => exact h.1 j ha
    | inr hb => exact h.2 j hb

theorem guarded_all (H : Nat → Prop) (A : Formula) :
    Guarded H (.all A) ↔ Guarded H A := Iff.rfl

theorem guarded_mp (H : Nat → Prop) (A B : Formula)
    (h : Guarded H (.imp A B)) : Guarded H B :=
  ((guarded_imp H A B).mp h).2

/-- Universal instantiation introduces no new guard index, even in its axiom. -/
theorem guarded_instantiation_axiom (H : Nat → Prop) (A : Formula)
    (σ : Nat → Term) (h : Guarded H (.all A)) :
    Guarded H (.imp (.all A) (A.subst σ)) := by
  apply (guarded_imp H _ _).mpr
  exact ⟨h, (guarded_subst H A σ).mpr ((guarded_all H A).mp h)⟩

def Core : Formula → Prop
  | .eq _ _ => True
  | .neg A => Core A
  | .imp A B => Core A ∧ Core B
  | .all A => Core A
  | .conj _ _ => False

theorem core_indices_empty (A : Formula) (h : Core A) :
    guardIndices A.shape = [] := by
  induction A with
  | eq s t => rfl
  | neg A ih => exact ih h
  | imp A B ihA ihB =>
      simp only [Core] at h
      simp [Formula.shape, guardIndices, ihA h.1, ihB h.2]
  | all A ih => exact ih h
  | conj A B ihA ihB => exact False.elim h

theorem core_guarded (H : Nat → Prop) (A : Formula) (h : Core A) :
    Guarded H A := by
  simp [Guarded, core_indices_empty A h]

/-- A trace here is a list of ALREADY EXPANDED formulas. Parsing, ordered
abbreviations, and ordinary Hilbert correctness belong to `ordinaryCheck`.
There is no assertion that this arbitrary argument implements PA. -/
def guardedCheck (ordinaryCheck : List Formula → Bool) (H : Nat → Prop)
    (trace : List Formula) : Prop :=
  ordinaryCheck trace = true ∧ ∀ A ∈ trace, Guarded H A

/-- Executable guard test, with the finite arithmetic guard supplied as a
Boolean function. Its runtime is deliberately left unrestricted here. -/
def guardsPass (guardTest : Nat → Bool) (A : Formula) : Bool :=
  (guardIndices A.shape).all guardTest

def checkedTrace (ordinaryCheck : List Formula → Bool)
    (guardTest : Nat → Bool) (trace : List Formula) : Bool :=
  ordinaryCheck trace && trace.all (guardsPass guardTest)

theorem guardsPass_correct (guardTest : Nat → Bool) (A : Formula) :
    guardsPass guardTest A = true ↔ Guarded (fun n => guardTest n = true) A := by
  simp [guardsPass, Guarded]

theorem checkedTrace_correct (ordinaryCheck : List Formula → Bool)
    (guardTest : Nat → Bool) (trace : List Formula) :
    checkedTrace ordinaryCheck guardTest trace = true ↔
      guardedCheck ordinaryCheck (fun n => guardTest n = true) trace := by
  simp [checkedTrace, guardedCheck, guardsPass_correct]

theorem same_accepted_traces (ordinaryCheck : List Formula → Bool)
    (H : Nat → Prop) (allH : ∀ n, H n) (trace : List Formula) :
    guardedCheck ordinaryCheck H trace ↔ ordinaryCheck trace = true := by
  constructor
  · exact And.left
  · intro h
    exact ⟨h, fun _ _ n _ => allH n⟩

/-- Core proofs need no assumption that all guards hold. This is the
syntactic fact used for the core inclusion in the human D3 argument. -/
theorem core_trace_acceptance (ordinaryCheck : List Formula → Bool)
    (H : Nat → Prop) (trace : List Formula)
    (coreTrace : ∀ A ∈ trace, Core A) :
    guardedCheck ordinaryCheck H trace ↔ ordinaryCheck trace = true := by
  constructor
  · exact And.left
  · intro h
    exact ⟨h, fun A hA => core_guarded H A (coreTrace A hA)⟩

theorem accepted_target_guard (ordinaryCheck : List Formula → Bool)
    (H : Nat → Prop) (D : Nat → Formula) (trace : List Formula) (n : Nat)
    (accepted : guardedCheck ordinaryCheck H trace)
    (lastOccurs : target D n ∈ trace) : H n :=
  target_guard H D n (accepted.2 _ lastOccurs)

/-- Node count only; this is NOT the PA-bin character metric. The tag uses
one fixed atom and one fixed connective, so its printed size is linear too. -/
def Formula.nodes : Formula → Nat
  | .eq _ _ => 1
  | .neg A => A.nodes + 1
  | .imp A B => A.nodes + B.nodes + 1
  | .all A => A.nodes + 1
  | .conj A B => A.nodes + B.nodes + 1

theorem tag_nodes (n : Nat) : (tag n).nodes = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tag, top, Formula.nodes, ih]; omega

def Term.eval (v : Nat → Nat) : Term → Nat
  | .var n => v n
  | .zero => 0
  | .succ t => t.eval v + 1
  | .add s t => s.eval v + t.eval v
  | .mul s t => s.eval v * t.eval v
  | .bit0 t => 2 * t.eval v
  | .bit1 t => 2 * t.eval v + 1

def Formula.eval (v : Nat → Nat) : Formula → Prop
  | .eq s t => s.eval v = t.eval v
  | .neg A => ¬ A.eval v
  | .imp A B => A.eval v → B.eval v
  | .all A => ∀ n, A.eval (fun i => match i with | 0 => n | j + 1 => v j)
  | .conj A B => A.eval v ∧ B.eval v

theorem tag_true (n : Nat) (v : Nat → Nat) : (tag n).eval v := by
  induction n with
  | zero => rfl
  | succ n ih => exact ⟨rfl, ih⟩

theorem target_truth (D : Nat → Formula) (n : Nat) (v : Nat → Nat) :
    (target D n).eval v ↔ (D n).eval v := by
  exact ⟨And.right, fun h => ⟨tag_true n v, h⟩⟩

end MAISO11.Tagged

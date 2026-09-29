import PairingGraph
set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Wire
open Arithmetic Quotation

/-- References name closed arithmetic terms, so binder descent cannot capture them. -/
inductive CTerm (r n : Nat) where
  | var : Fin n → CTerm r n
  | ref : Fin r → CTerm r n
  | zero : CTerm r n
  | bit0 : CTerm r n → CTerm r n
  | bit1 : CTerm r n → CTerm r n
  | add : CTerm r n → CTerm r n → CTerm r n
  | mul : CTerm r n → CTerm r n → CTerm r n
  deriving DecidableEq, Repr

def CTerm.expand {r n : Nat} (δ : Fin r → ClosedTerm) : CTerm r n → Arithmetic.Term n
  | .var i => .var i
  | .ref i => Arithmetic.Term.ofClosed (δ i)
  | .zero => .zero
  | .bit0 t => .bit0 (t.expand δ)
  | .bit1 t => .bit1 (t.expand δ)
  | .add s t => .add (s.expand δ) (t.expand δ)
  | .mul s t => .mul (s.expand δ) (t.expand δ)

def CTerm.weight {r n : Nat} : CTerm r n → Nat
  | .var _ | .ref _ | .zero => 1
  | .bit0 t | .bit1 t => 1+t.weight
  | .add s t | .mul s t => 1+s.weight+t.weight

def CTerm.rename {r n m : Nat} (σ : Fin n → Fin m) : CTerm r n → CTerm r m
  | .var i => .var (σ i)
  | .ref i => .ref i
  | .zero => .zero
  | .bit0 t => .bit0 (t.rename σ)
  | .bit1 t => .bit1 (t.rename σ)
  | .add s t => .add (s.rename σ) (t.rename σ)
  | .mul s t => .mul (s.rename σ) (t.rename σ)

@[simp] theorem CTerm.weight_rename {r n m : Nat} (t : CTerm r n) (σ : Fin n → Fin m) :
    (t.rename σ).weight = t.weight := by induction t <;> simp_all [rename,weight]

def CTerm.up {r n : Nat} (t : CTerm r n) : CTerm r (n+1) := t.rename Fin.succ

theorem ofClosed_subst {n m : Nat} (t : ClosedTerm) (σ : Fin n → Arithmetic.Term m) :
    (Arithmetic.Term.ofClosed t).subst σ = Arithmetic.Term.ofClosed t := by
  induction t <;> simp_all [Arithmetic.Term.ofClosed, Arithmetic.Term.subst]

theorem CTerm.expand_rename {r n m : Nat} (t : CTerm r n)
    (δ : Fin r → ClosedTerm) (σ : Fin n → Fin m) :
    (t.rename σ).expand δ = (t.expand δ).subst (fun i => .var (σ i)) := by
  induction t <;> simp_all [rename,expand,Arithmetic.Term.subst,ofClosed_subst]

@[simp] theorem CTerm.expand_up {r n : Nat} (t : CTerm r n) (δ : Fin r → ClosedTerm) :
    t.up.expand δ = (t.expand δ).up := CTerm.expand_rename t δ Fin.succ

def CTerm.pair {r n : Nat} (a b : CTerm r n) : CTerm r n :=
  .add (.add (.mul (.add a b) (.add a b)) a) (.bit1 .zero)

@[simp] theorem CTerm.expand_pair {r n : Nat} (a b : CTerm r n) (δ : Fin r → ClosedTerm) :
    (a.pair b).expand δ = (a.expand δ).pair (b.expand δ) := rfl

@[simp] theorem CTerm.weight_pair {r n : Nat} (a b : CTerm r n) :
    (a.pair b).weight = 7+3*a.weight+2*b.weight := by
  simp [pair,weight]; omega

inductive CFormula (r : Nat) : Nat → Type where
  | eq {n : Nat} : CTerm r n → CTerm r n → CFormula r n
  | neg {n : Nat} : CFormula r n → CFormula r n
  | imp {n : Nat} : CFormula r n → CFormula r n → CFormula r n
  | all {n : Nat} : CFormula r (n+1) → CFormula r n
  deriving DecidableEq, Repr

def CFormula.expand {r n : Nat} (δ : Fin r → ClosedTerm) : CFormula r n → Arithmetic.Formula n
  | .eq s t => .eq (s.expand δ) (t.expand δ)
  | .neg f => .neg (f.expand δ)
  | .imp f g => .imp (f.expand δ) (g.expand δ)
  | .all f => .all (f.expand δ)

def CFormula.weight {r n : Nat} : CFormula r n → Nat
  | .eq s t => 1+s.weight+t.weight
  | .neg f | .all f => 1+f.weight
  | .imp f g => 1+f.weight+g.weight

def CFormula.depth {r n : Nat} : CFormula r n → Nat
  | .eq _ _ => 0
  | .neg f => f.depth
  | .imp f g => max f.depth g.depth
  | .all f => f.depth+1

def CFormula.ex {r n : Nat} (f : CFormula r (n+1)) : CFormula r n := .neg (.all (.neg f))
def CFormula.conj {r n : Nat} (f g : CFormula r n) : CFormula r n := .neg (.imp f (.neg g))

def lookup : (i : Nat) → {r n : Nat} → CTerm r n → CTerm r n → CTerm r n → CTerm r n → CFormula r n
  | 0, _, _, z,l,s,v => (CFormula.eq z.up ((l.up.pair (s.up.pair v.up)).pair (.var 0))).ex
  | i+1, _, _, z,l,s,v =>
      ((CFormula.eq z.up.up ((CTerm.var (Fin.succ 0)).pair (.var 0))).conj
        (lookup i (.var 0) l.up.up s.up.up v.up.up)).ex.ex

theorem lookup_expand (i : Nat) {r n : Nat} (z l s v : CTerm r n) (δ : Fin r → ClosedTerm) :
    (lookup i z l s v).expand δ =
      Arithmetic.lookup i (z.expand δ) (l.expand δ) (s.expand δ) (v.expand δ) := by
  induction i generalizing n with
  | zero => simp [lookup,Arithmetic.lookup,CFormula.ex,CFormula.expand,Arithmetic.Formula.ex,CTerm.expand]
  | succ i ih => simp [lookup,Arithmetic.lookup,CFormula.ex,CFormula.conj,CFormula.expand,
      Arithmetic.Formula.ex,Arithmetic.Formula.conj,ih,CTerm.expand]

theorem lookup_weight (i : Nat) {r n : Nat} (z l s v : CTerm r n) :
    (lookup i z l s v).weight = 23*i+76+z.weight+9*l.weight+18*s.weight+12*v.weight := by
  induction i generalizing n with
  | zero => simp [lookup,CFormula.ex,CFormula.weight,CTerm.up,CTerm.weight]; omega
  | succ i ih =>
    simp [lookup,CFormula.ex,CFormula.conj,CFormula.weight,ih,CTerm.up,CTerm.weight]
    omega

theorem lookup_depth (i : Nat) {r n : Nat} (z l s v : CTerm r n) :
    (lookup i z l s v).depth = 2*i+1 := by
  induction i generalizing n with
  | zero => simp [lookup,CFormula.ex,CFormula.depth]
  | succ i ih => simp [lookup,CFormula.ex,CFormula.conj,CFormula.depth,ih]; omega

/-- Same self-delimiting binary indices as the existing abbreviation names,
but a disjoint prefix for variables. -/
def variableName (i : Nat) : List Char := ['v'] ++ (identifier i).drop 1

theorem variable_length (i : Nat) : (variableName i).length = (identifier i).length := by
  have h := identifier_length i
  simp [variableName]; omega

theorem variable_length_le (i : Nat) : (variableName i).length ≤ 2*i+4 := by
  rw [variable_length]; exact identifier_length_le i

/-- De Bruijn indices are printed as levels. The next binder is named n;
every variable already in scope has a strictly smaller level. -/
def level {n : Nat} (i : Fin n) : Nat := n-1-i.val

theorem level_lt {n : Nat} (i : Fin n) : level i < n := by
  have hi := i.isLt
  unfold level; omega

theorem level_succ {n : Nat} (i : Fin n) : level i.succ = level i := by
  have hi := i.isLt
  simp only [level,Fin.val_succ]; omega

theorem level_zero (n : Nat) : level (0 : Fin (n+1)) = n := by simp [level]

theorem level_injective {n : Nat} {i j : Fin n} (h : level i = level j) : i=j := by
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  unfold level at h; omega

def CTerm.wire {r n : Nat} : CTerm r n → List Char
  | .var i => variableName (level i)
  | .ref i => identifier i.val
  | .zero => ['0']
  | .bit0 t => ['(','D'] ++ t.wire ++ [')']
  | .bit1 t => ['(','E'] ++ t.wire ++ [')']
  | .add s t => ['(','+'] ++ s.wire ++ t.wire ++ [')']
  | .mul s t => ['(','*'] ++ s.wire ++ t.wire ++ [')']

theorem CTerm.wire_bound {r n : Nat} (t : CTerm r n) (B : Nat)
    (hb : 2*r+2*n+4 ≤ B) : t.wire.length ≤ B*t.weight := by
  induction t with
  | var i =>
    have h := variable_length_le (level i)
    have hi := level_lt i
    simp only [wire,weight,Nat.mul_one]; omega
  | ref i =>
    have h := identifier_length_le i.val
    have hi := i.isLt
    simp only [wire,weight,Nat.mul_one]; omega
  | zero => simp [wire,weight]; omega
  | bit0 t ih => simp [wire,weight,Nat.mul_add] at *; omega
  | bit1 t ih => simp [wire,weight,Nat.mul_add] at *; omega
  | add s t hs ht => simp [wire,weight,Nat.mul_add] at *; omega
  | mul s t hs ht => simp [wire,weight,Nat.mul_add] at *; omega

def CFormula.wire {r n : Nat} : CFormula r n → List Char
  | .eq s t => ['(','='] ++ s.wire ++ t.wire ++ [')']
  | .neg f => ['(','~'] ++ f.wire ++ [')']
  | .imp f g => ['(','>'] ++ f.wire ++ g.wire ++ [')']
  | @CFormula.all _ n f => ['(','A'] ++ variableName n ++ f.wire ++ [')']

theorem CFormula.wire_bound {r n : Nat} (f : CFormula r n) (D B : Nat)
    (hd : n+f.depth ≤ D) (hb : 2*r+2*D+7 ≤ B) : f.wire.length ≤ B*f.weight := by
  induction f with
  | eq s t =>
    have hs := s.wire_bound B (by simp only [depth] at hd; omega)
    have ht := t.wire_bound B (by simp only [depth] at hd; omega)
    simp [wire,weight,Nat.mul_add] at *; omega
  | neg f ih =>
    have h := ih (by simpa [depth] using hd)
    simp [wire,weight,Nat.mul_add] at *; omega
  | imp f g hf hg =>
    have hdf := Nat.le_max_left f.depth g.depth
    have hdg := Nat.le_max_right f.depth g.depth
    have h1 := hf (by simp only [depth] at hd; omega)
    have h2 := hg (by simp only [depth] at hd; omega)
    simp [wire,weight,Nat.mul_add] at *; omega
  | @all n f ih =>
    have h := ih (by simp only [depth] at hd; omega)
    have hv := variable_length_le n
    simp only [wire,weight,List.length_append,List.length_cons,List.length_nil,Nat.mul_add,Nat.mul_one]
    simp only [depth] at hd
    omega

theorem lookup_wire_bound (i : Nat) {r n : Nat} (z l s v : CTerm r n) :
    (lookup i z l s v).wire.length ≤
      (2*r+2*(n+2*i+1)+7) *
        (23*i+76+z.weight+9*l.weight+18*s.weight+12*v.weight) := by
  have h := (lookup i z l s v).wire_bound (n+2*i+1)
    (2*r+2*(n+2*i+1)+7) (by rw [lookup_depth]; omega) (Nat.le_refl _)
  simpa [lookup_weight] using h

def readVariable : List Char → Option (Nat × List Char)
  | 'v' :: cs => readIdentifier ('u' :: cs)
  | _ => none

theorem readVariable_encode (i : Nat) (tail : List Char) :
    readVariable (variableName i ++ tail) = some (i,tail) := by
  have h : readVariable (variableName i ++ tail) = readIdentifier (identifier i ++ tail) := by
    simp [readVariable,variableName,identifier]
  rw [h,readIdentifier_encode]

def sourceIndex {n : Nat} (i : Fin n) (s : Slot) : Fin (3*n+n) :=
  ⟨3*i.val+s.offset, by have hi := i.isLt; have hs := s.offset_le_two; omega⟩

def slotOfNat (k : Nat) : Slot := if k=0 then .len else if k=1 then .scale else .payload

@[simp] theorem slotOfNat_offset (s : Slot) : slotOfNat s.offset = s := by
  cases s <;> decide

/-- Precisely the expanded register terms in the old quotation-plus-packing
prelude: 3*n source slots, followed by n packed tails. -/
def dictionary {n : Nat} (p : Program n) (j : Fin (3*n+n)) : ClosedTerm :=
  if h : j.val < 3*n then
    (p.expansion ⟨j.val/3, by omega⟩).get (slotOfNat (j.val%3))
  else
    ((tracePacking n).expansion p.expansion)
      ⟨j.val-3*n, by have hj := j.isLt; simp; omega⟩

theorem dictionary_source {n : Nat} (p : Program n) (i : Fin n) (s : Slot) :
    dictionary p (sourceIndex i s) = (p.expansion i).get s := by
  have hi := i.isLt
  have hs := s.offset_le_two
  have hlt : 3*i.val+s.offset < 3*n := by omega
  have hd : (3*i.val+s.offset)/3 = i.val := by omega
  have hm : (3*i.val+s.offset)%3 = s.offset := by omega
  simp [dictionary,sourceIndex,hlt,hd,hm]

def rootRef : (n : Nat) → CTerm (3*n+n) 0
  | 0 => .zero
  | n+1 => .ref ⟨3*(n+1)+n, by omega⟩

theorem rootRef_expand {n : Nat} (p : Program n) :
    (rootRef n).expand (dictionary p) = Arithmetic.Term.ofClosed (packedRoot p) := by
  cases n with
  | zero =>
    have hz : ∀ (m : Nat) (σ : Fin m → ClosedTerm), m = 0 → lastTerm m σ = .zero := by
      intro m σ hm; subst m; rfl
    simp only [rootRef,CTerm.expand,packedRoot]
    rw [hz _ _ List.length_finRange]
    rfl
  | succ n =>
    have h : ¬ 3*(n+1)+n < 3*(n+1) := by omega
    have hp : ∀ (m : Nat) (σ : Fin m → ClosedTerm) (hm : 0 < m),
        lastTerm m σ = σ ⟨m-1, by omega⟩ := by
      intro m σ hm
      cases m with
      | zero => omega
      | succ m => rfl
    simp only [rootRef,CTerm.expand,dictionary,h,dif_neg,packedRoot]
    rw [hp _ _ (by simp only [List.length_finRange]; omega)]
    simp only [dite_false]
    congr 2
    apply Fin.ext
    simp only [List.length_finRange]
    omega

def allConj {r n : Nat} : List (CFormula r n) → CFormula r n
  | [] => .eq .zero .zero
  | f :: fs => f.conj (allConj fs)

theorem allConj_expand {r n : Nat} (fs : List (CFormula r n)) (δ : Fin r → ClosedTerm) :
    (allConj fs).expand δ = Arithmetic.allConj (fs.map (fun f => f.expand δ)) := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [allConj,CFormula.conj,CFormula.expand,Arithmetic.allConj,
      Arithmetic.Formula.conj,ih]

theorem allConj_weight {r n : Nat} (fs : List (CFormula r n)) (W : Nat)
    (h : ∀ f ∈ fs, f.weight ≤ W) : (allConj fs).weight ≤ fs.length*(W+3)+3 := by
  induction fs with
  | nil => simp [allConj,CFormula.weight,CTerm.weight]
  | cons f fs ih =>
    have hf := h f (by simp)
    have ht := ih (fun g hg => h g (by simp [hg]))
    simp [allConj,CFormula.conj,CFormula.weight,Nat.add_mul] at *; omega

theorem allConj_depth {r n : Nat} (fs : List (CFormula r n)) (D : Nat)
    (h : ∀ f ∈ fs, f.depth ≤ D) : (allConj fs).depth ≤ D := by
  induction fs with
  | nil => simp [allConj,CFormula.depth]
  | cons f fs ih =>
    have hf := h f (by simp)
    have ht := ih (fun g hg => h g (by simp [hg]))
    simp only [allConj,CFormula.conj,CFormula.depth]
    exact Nat.max_le.mpr ⟨hf,ht⟩

def entry {n : Nat} (i : Fin n) : CFormula (3*n+n) 0 :=
  lookup i.val (rootRef n) (.ref (sourceIndex i .len))
    (.ref (sourceIndex i .scale)) (.ref (sourceIndex i .payload))

def trace (n : Nat) : CFormula (3*n+n) 0 := allConj (List.ofFn (entry (n:=n)))

theorem entry_expand {n : Nat} (p : Program n) (i : Fin n) :
    (entry i).expand (dictionary p) =
      programEntry p (Arithmetic.Term.ofClosed (packedRoot p)) i := by
  simp [entry,lookup_expand,rootRef_expand,CTerm.expand,dictionary_source,
    programEntry,TermTriple.get]

theorem trace_expand {n : Nat} (p : Program n) :
    (trace n).expand (dictionary p) =
      traceFormula p (Arithmetic.Term.ofClosed (packedRoot p)) := by
  simp [trace,allConj_expand,Arithmetic.map_ofFn,entry_expand,traceFormula]

theorem trace_provable {n : Nat} (p : Program n) :
    Within ((trace n).expand (dictionary p)) (n*(14*n+10)+3) := by
  rw [trace_expand]
  exact traceFormula_within p

theorem rootRef_weight (n : Nat) : (rootRef n).weight = 1 := by cases n <;> rfl

theorem trace_weight (n : Nat) : (trace n).weight ≤ n*(23*n+119)+3 := by
  have h : ∀ f ∈ List.ofFn (entry (n:=n)), f.weight ≤ 23*n+116 := by
    intro f hf
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
    have hi := i.isLt
    simp [entry,lookup_weight,CTerm.weight,rootRef_weight]; omega
  simpa [trace,Nat.add_assoc] using allConj_weight _ (23*n+116) h

theorem trace_depth (n : Nat) : (trace n).depth ≤ 2*n+1 := by
  apply allConj_depth
  intro f hf
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
  have hi := i.isLt
  simp [entry,lookup_depth]; omega

/-- A character bound for the compressed CONCLUSION, not the entire proof. -/
theorem trace_characters (n : Nat) :
    (trace n).wire.length ≤ (12*n+9)*(n*(23*n+119)+3) := by
  have h := (trace n).wire_bound (2*n+1) (12*n+9)
    (by simpa using trace_depth n) (by omega)
  exact Nat.le_trans h (Nat.mul_le_mul_left _ (trace_weight n))

/-- Record syntax only: backward references are enforced, but logical validity
of axiom labels and modus ponens is deliberately not asserted here. -/
inductive Record (r k : Nat) where
  | axiom : CFormula r 0 → Record r k
  | mp : Fin k → Fin k → CFormula r 0 → Record r k

def Record.formula {r k : Nat} : Record r k → CFormula r 0
  | .axiom f => f
  | .mp _ _ f => f

def Record.wire {r k : Nat} : Record r k → List Char
  | .axiom f => ['A',' '] ++ f.wire ++ ['\n']
  | .mp a b f => ['M','['] ++ identifier a.val ++ [','] ++
      identifier b.val ++ [']',' '] ++ f.wire ++ ['\n']

theorem Record.wire_bound {r k : Nat} (a : Record r k) (D W N : Nat)
    (hk : k ≤ N) (hd : a.formula.depth ≤ D) (hw : a.formula.weight ≤ W) :
    a.wire.length ≤ (2*r+2*D+7)*W + 4*N+14 := by
  have hf := a.formula.wire_bound D (2*r+2*D+7) (by simpa using hd) (by omega)
  have hfw := Nat.le_trans hf (Nat.mul_le_mul_left (2*r+2*D+7) hw)
  cases a with
  | «axiom» f => simp [wire,formula] at *; omega
  | mp a b f =>
    have ha := identifier_length_le a.val
    have hb := identifier_length_le b.val
    have hai := a.isLt
    have hbi := b.isLt
    simp [wire,formula] at *; omega

inductive Records (r : Nat) : Nat → Type where
  | nil : Records r 0
  | snoc {k : Nat} : Records r k → Record r k → Records r (k+1)

def Records.wire {r k : Nat} : Records r k → List Char
  | .nil => []
  | .snoc fs f => fs.wire ++ f.wire

def Records.bounded {r k : Nat} (D W : Nat) : Records r k → Prop
  | .nil => True
  | .snoc fs f => fs.bounded D W ∧ f.formula.depth ≤ D ∧ f.formula.weight ≤ W

/-- This is a conditional character ledger, not a proof-generator theorem. -/
theorem Records.wire_bound {r k : Nat} (fs : Records r k) (D W N : Nat)
    (hk : k ≤ N) (h : fs.bounded D W) :
    fs.wire.length ≤ k*((2*r+2*D+7)*W+4*N+14) := by
  induction fs with
  | nil => simp [wire]
  | @snoc k fs f ih =>
    have hp := ih (by omega) h.1
    have hf := f.wire_bound D W N (by omega) h.2.1 h.2.2
    simpa only [wire,List.length_append,Nat.succ_mul] using Nat.add_le_add hp hf

end MAISO11.Wire

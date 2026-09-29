import LocalCertificates

/-!
A concrete arithmetic encoding of the witness vector and an executable checker
of its local arithmetic recurrences. The program is still a typed syntax tree;
this module does not give a PA formula or a PA derivation of its acceptance.

The deliberately simple decoder uses bounded search. Certificates will use
symbolic pairing terms, not a transcript of that potentially enormous search.
-/

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Quotation

/-- Positive, injective pairing expressed using only addition and multiplication. -/
def arithPair (a b : Nat) : Nat := (a + b) * (a + b) + a + 1

theorem le_square (a : Nat) : a ≤ a * a := by
  cases a with
  | zero => exact Nat.le_refl 0
  | succ n =>
    have h := Nat.mul_le_mul_left (n + 1) (show 1 ≤ n + 1 by omega)
    simpa using h

theorem arithPair_bounds (a b : Nat) : a < arithPair a b ∧ b < arithPair a b := by
  have h := le_square (a + b)
  unfold arithPair
  omega

theorem square_gap (s t : Nat) (h : s < t) : s * s + s < t * t := by
  have ht : s + 1 ≤ t := by omega
  have hh := Nat.mul_le_mul ht ht
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul] at hh
  omega

theorem arithPair_injective {a b c d : Nat} (h : arithPair a b = arithPair c d) :
    a = c ∧ b = d := by
  have hsum : a + b = c + d := by
    by_cases hl : a + b < c + d
    · have hs := square_gap (a + b) (c + d) hl
      unfold arithPair at h
      omega
    · by_cases hg : c + d < a + b
      · have hs := square_gap (c + d) (a + b) hg
        unfold arithPair at h
        omega
      · omega
  unfold arithPair at h
  rw [hsum] at h
  omega

def pairCandidates (z : Nat) : List (Nat × Nat) :=
  (List.range z).flatMap (fun a => (List.range z).map (fun b => (a, b)))

def arithUnpair (z : Nat) : Option (Nat × Nat) :=
  (pairCandidates z).find? (fun ab => decide (arithPair ab.1 ab.2 = z))

theorem find_unique {α : Type} (xs : List α) (p : α → Bool) (a : α)
    (ha : a ∈ xs) (hp : p a = true)
    (hu : ∀ x ∈ xs, p x = true → x = a) : xs.find? p = some a := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    by_cases hx : p x = true
    · have hxa := hu x (by simp) hx
      subst x
      simp [hp]
    · have hat : a ∈ xs := by
        simp only [List.mem_cons] at ha
        rcases ha with he | ht
        · subst x; exact False.elim (hx hp)
        · exact ht
      have hpf : p x = false := by cases he : p x <;> simp_all
      have hut : ∀ y ∈ xs, p y = true → y = a :=
        fun y hy hpy => hu y (by simp [hy]) hpy
      simp [hpf, ih hat hut]

@[simp] theorem arithUnpair_zero : arithUnpair 0 = none := rfl

@[simp] theorem arithUnpair_pair (a b : Nat) : arithUnpair (arithPair a b) = some (a, b) := by
  apply find_unique
  · have hab := arithPair_bounds a b
    simp [pairCandidates, hab.1, hab.2]
  · simp
  · intro x hx hp
    have he : arithPair x.1 x.2 = arithPair a b := of_decide_eq_true hp
    have hh := arithPair_injective he
    exact Prod.ext hh.1 hh.2

def encodeValue (v : Value) : Nat := arithPair v.len (arithPair v.scale v.payload)

def decodeValue (z : Nat) : Option Value := do
  let (l, rest) ← arithUnpair z
  let (s, v) ← arithUnpair rest
  pure ⟨l, s, v⟩

@[simp] theorem decode_encodeValue (v : Value) : decodeValue (encodeValue v) = some v := by
  cases v
  simp [decodeValue, encodeValue]

def encodeValues : List Value → Nat
  | [] => 0
  | v :: vs => arithPair (encodeValue v) (encodeValues vs)

def readValue : Nat → Nat → Option Value
  | z, 0 => do
    let (v, _) ← arithUnpair z
    decodeValue v
  | z, i + 1 => do
    let (_, tail) ← arithUnpair z
    readValue tail i

@[simp] theorem readValue_zero (i : Nat) : readValue 0 i = none := by
  cases i <;> simp [readValue]

theorem readValue_encode (vs : List Value) (i : Nat) :
    readValue (encodeValues vs) i = vs[i]? := by
  induction vs generalizing i with
  | nil => cases i <;> simp [encodeValues, readValue]
  | cons v vs ih => cases i <;> simp [encodeValues, readValue, ih]

def Program.traceCode {n : Nat} (p : Program n) : Nat := encodeValues (List.ofFn p.eval)

theorem Program.traceCode_lookup {n : Nat} (p : Program n) (i : Fin n) :
    readValue p.traceCode i.val = some (p.eval i) := by
  rw [traceCode, readValue_encode]
  simp [List.getElem?_eq_getElem, i.isLt]

def zeroValue : Value := ⟨0, 0, 0⟩

def traceEnv (n z : Nat) : Fin n → Value := fun i => (readValue z i.val).getD zeroValue

/-- Verify each register against the arithmetic recurrence for that register.
The same coded vector is used throughout; earlier registers are checked first.
Extra entries beyond the program's register count are irrelevant. -/
def checkTrace {n : Nat} : Program n → Nat → Bool
  | .nil, _ => true
  | @Program.snoc n p t, z =>
    checkTrace p z && decide (readValue z n = some (t.eval (traceEnv n z)))

theorem checkTrace_rejects_missing {n : Nat} (p : Program n) (t : Triple n) :
    checkTrace (.snoc p t) 0 = false := by simp [checkTrace]

theorem checkTrace_sound {n : Nat} (p : Program n) (z : Nat) (h : checkTrace p z = true) :
    ∀ i : Fin n, readValue z i.val = some (p.eval i) := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @snoc n p t ih =>
    have hh : checkTrace p z = true ∧ readValue z n = some (t.eval (traceEnv n z)) := by
      simpa [checkTrace] using h
    have hp := ih hh.1
    have he : traceEnv n z = p.eval := by
      funext i
      simp [traceEnv, hp i]
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.val_last, Program.eval, Fin.lastCases_last]
      simpa [he] using hh.2
    · simpa only [Program.eval, Fin.lastCases_castSucc] using hp j

theorem checkTrace_of_lookup {n : Nat} (p : Program n) (z : Nat)
    (h : ∀ i : Fin n, readValue z i.val = some (p.eval i)) : checkTrace p z = true := by
  induction p with
  | nil => rfl
  | @snoc n p t ih =>
    have hp : ∀ i : Fin n, readValue z i.val = some (p.eval i) := by
      intro i
      simpa only [Program.eval, Fin.lastCases_castSucc] using h i.castSucc
    have he : traceEnv n z = p.eval := by
      funext i
      simp [traceEnv, hp i]
    have hl : readValue z n = some (t.eval p.eval) := by
      simpa only [Fin.val_last, Program.eval, Fin.lastCases_last] using h (Fin.last n)
    simp [checkTrace, ih hp, he, hl]

theorem checkTrace_complete {n : Nat} (p : Program n) : checkTrace p p.traceCode = true :=
  checkTrace_of_lookup p p.traceCode p.traceCode_lookup

theorem compiled_trace_sound {b n : Nat} (g : Grammar b n) (z : Nat)
    (h : checkTrace (compile g) z = true) (i : Fin n) :
    readValue z i.val = some (quoteWord b (g.words i)) := by
  have hh := checkTrace_sound (compile g) z h i
  rw [compile_correct] at hh
  exact hh

end MAISO11.Quotation

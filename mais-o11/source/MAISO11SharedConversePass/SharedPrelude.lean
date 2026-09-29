import CompactEquality
set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Wire
open MAISO11.Quotation MAISO11.Arithmetic

/-- A closed term whose references name earlier abbreviation definitions.
The compact syntax is the same `CTerm` already used by proof records. -/
def CTerm.close {r : Nat} (δ : Fin r → ClosedTerm) : CTerm r 0 → ClosedTerm
  | .var i => Fin.elim0 i
  | .ref i => δ i
  | .zero => .zero
  | .bit0 t => .bit0 (t.close δ)
  | .bit1 t => .bit1 (t.close δ)
  | .add s t => .add (s.close δ) (t.close δ)
  | .mul s t => .mul (s.close δ) (t.close δ)

theorem CTerm.close_expand {r : Nat} (δ : Fin r → ClosedTerm) (t : CTerm r 0) :
    Term.ofClosed (t.close δ) = t.expand δ := by
  induction t with
  | var i => exact Fin.elim0 i
  | ref i => rfl
  | zero => rfl
  | bit0 t ih => simp [CTerm.close,CTerm.expand,Term.ofClosed,ih]
  | bit1 t ih => simp [CTerm.close,CTerm.expand,Term.ofClosed,ih]
  | add s t hs ht => simp [CTerm.close,CTerm.expand,Term.ofClosed,hs,ht]
  | mul s t hs ht => simp [CTerm.close,CTerm.expand,Term.ofClosed,hs,ht]

/-- Each definition refers only to the preceding entries by construction. -/
inductive CDefs : Nat → Type where
  | nil : CDefs 0
  | snoc {r : Nat} : CDefs r → CTerm r 0 → CDefs (r+1)
  deriving Repr

def CDefs.expand {r : Nat} : CDefs r → Fin r → ClosedTerm
  | .nil => Fin.elim0
  | .snoc p t => Fin.lastCases (t.close p.expand) p.expand

def CDefs.terms {r : Nat} : CDefs r → List ClosedTerm
  | .nil => []
  | .snoc p t => p.terms ++ [t.close p.expand]

theorem CDefs.terms_length {r : Nat} (p : CDefs r) : p.terms.length = r := by
  induction p with
  | nil => rfl
  | snoc p t ih => simp [terms,ih]

theorem CDefs.terms_get {r : Nat} (p : CDefs r) (i : Fin r) :
    p.terms[i.val]? = some (p.expand i) := by
  induction p with
  | nil => exact Fin.elim0 i
  | @snoc n p t ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [terms,expand,Fin.lastCases_last,p.terms_length]
    · have hj : j.val < p.terms.length := by rw [p.terms_length]; exact j.isLt
      simp only [terms,expand,Fin.lastCases_castSucc,Fin.coe_castSucc]
      rw [List.getElem?_append_left hj]
      exact ih j

/-- The old reader and the new compact term parser assign the same expanded
value to every canonically serialized closed compact term. -/
theorem readEnvTermFuel_cterm {r : Nat} (env : List ClosedTerm)
    (δ : Fin r → ClosedTerm)
    (he : ∀ i : Fin r, env[i.val]? = some (δ i))
    (t : CTerm r 0) (tail : List Char) (fuel : Nat)
    (hf : t.wire.length ≤ fuel) :
    readEnvTermFuel env fuel (t.wire ++ tail) = some (t.close δ,tail) := by
  induction t generalizing fuel tail with
  | var i => exact Fin.elim0 i
  | ref i =>
    cases fuel with
    | zero =>
      have hi := identifier_length i.val
      simp only [CTerm.wire] at hf
      omega
    | succ fuel =>
      have hi := readCanonicalIdentifier_wire i.val tail
      simp [CTerm.wire,readEnvTermFuel,identifier,he,CTerm.close,hi]
      have hr : readCanonicalIdentifier ('u' ::
          (List.replicate (bits (i.val+1)).length '1' ++
          '0' :: (((bits (i.val+1)).map bitChar).reverse ++ tail))) =
          some (i.val,tail) := by
        simpa only [identifier,List.map_reverse,List.append_assoc,List.cons_append,
          List.nil_append] using hi
      rw [hr]
      simp [he]
  | zero =>
    cases fuel with
    | zero => simp [CTerm.wire] at hf
    | succ fuel => rfl
  | bit0 t ih =>
    cases fuel with
    | zero => simp [CTerm.wire] at hf
    | succ fuel =>
      have ht : t.wire.length ≤ fuel := by simp [CTerm.wire] at hf; omega
      simp [CTerm.wire,readEnvTermFuel,CTerm.close,ih (')'::tail) fuel ht,close]
  | bit1 t ih =>
    cases fuel with
    | zero => simp [CTerm.wire] at hf
    | succ fuel =>
      have ht : t.wire.length ≤ fuel := by simp [CTerm.wire] at hf; omega
      simp [CTerm.wire,readEnvTermFuel,CTerm.close,ih (')'::tail) fuel ht,close]
  | add s t hs ht =>
    cases fuel with
    | zero => simp [CTerm.wire] at hf
    | succ fuel =>
      have h₁ : s.wire.length ≤ fuel := by simp [CTerm.wire] at hf; omega
      have h₂ : t.wire.length ≤ fuel := by simp [CTerm.wire] at hf; omega
      simp [CTerm.wire,readEnvTermFuel,CTerm.close,
        hs (t.wire ++ ')'::tail) fuel h₁,ht (')'::tail) fuel h₂,
        close,List.append_assoc]
  | mul s t hs ht =>
    cases fuel with
    | zero => simp [CTerm.wire] at hf
    | succ fuel =>
      have h₁ : s.wire.length ≤ fuel := by simp [CTerm.wire] at hf; omega
      have h₂ : t.wire.length ≤ fuel := by simp [CTerm.wire] at hf; omega
      simp [CTerm.wire,readEnvTermFuel,CTerm.close,
        hs (t.wire ++ ')'::tail) fuel h₁,ht (')'::tail) fuel h₂,
        close,List.append_assoc]

theorem readEnvTerm_cterm {r : Nat} (env : List ClosedTerm)
    (δ : Fin r → ClosedTerm)
    (he : ∀ i : Fin r, env[i.val]? = some (δ i))
    (t : CTerm r 0) (tail : List Char) :
    readEnvTerm env (t.wire ++ tail) = some (t.close δ,tail) := by
  exact readEnvTermFuel_cterm env δ he t tail _ (by simp)

def sharedDefinition {r : Nat} (t : CTerm r 0) : List Char :=
  "def ".toList ++ identifier r ++ " := ".toList ++ t.wire ++ ['\n']

def CDefs.wire {r : Nat} : CDefs r → List Char
  | .nil => []
  | .snoc p t => p.wire ++ sharedDefinition t

theorem CTerm.weight_le_wire {r : Nat} (t : CTerm r 0) :
    t.weight ≤ t.wire.length := by
  induction t with
  | var i => exact Fin.elim0 i
  | ref i =>
    simp [CTerm.weight,CTerm.wire,identifier_length]
  | zero => simp [CTerm.weight,CTerm.wire]
  | bit0 t ih => simp [CTerm.weight,CTerm.wire] at *; omega
  | bit1 t ih => simp [CTerm.weight,CTerm.wire] at *; omega
  | add s t hs ht => simp [CTerm.weight,CTerm.wire] at *; omega
  | mul s t hs ht => simp [CTerm.weight,CTerm.wire] at *; omega

def CDefs.mass {r : Nat} : CDefs r → Nat
  | .nil => 0
  | .snoc p t => p.mass + t.weight + 1

/-- This parser's result has at most one syntax node per written character.
The bound is about the retained syntax; it does not assert a CPU-time bound. -/
theorem CDefs.mass_le_wire {r : Nat} (p : CDefs r) :
    p.mass ≤ p.wire.length := by
  induction p with
  | nil => simp [mass,wire]
  | snoc p t ih =>
    have ht := CTerm.weight_le_wire t
    simp [mass,wire,sharedDefinition] at *
    omega

/-- Unlike `readDefinition`, this parser returns a compact syntax tree;
reading an abbreviation does not construct its expanded value. -/
def parseSharedDefinition (r : Nat) (cs : List Char) :
    Option (CTerm r 0 × List Char) :=
  match cs with
  | 'd' :: 'e' :: 'f' :: ' ' :: body => do
      let (i,rest) ← readCanonicalIdentifier body
      if i != r then none else do
        let ' ' :: ':' :: '=' :: ' ' :: rest := rest | none
        let (t,rest) ← parseTerm r 0 rest
        let rest ← newline rest
        pure (t,rest)
  | _ => none

theorem parseSharedDefinition_wire {r : Nat} (t : CTerm r 0)
    (tail : List Char) :
    parseSharedDefinition r (sharedDefinition t ++ tail) = some (t,tail) := by
  simp [parseSharedDefinition,sharedDefinition,readCanonicalIdentifier_wire,
    parseTerm_wire,newline,List.append_assoc]

theorem readCanonicalIdentifier_sound {cs : List Char} {i : Nat}
    {tail : List Char}
    (h : readCanonicalIdentifier cs = some (i,tail)) :
    cs = identifier i ++ tail := by
  unfold readCanonicalIdentifier at h
  cases hr : readIdentifier cs with
  | none => simp [hr] at h
  | some result =>
    obtain ⟨j,rest⟩ := result
    by_cases hc : identifier j ++ rest = cs
    · simp [hr,hc] at h
      obtain ⟨rfl,rfl⟩ := h
      exact hc.symm
    · simp [hr,hc] at h

theorem newline_sound {cs tail : List Char} (h : newline cs = some tail) :
    cs = '\n' :: tail := by
  cases cs with
  | nil => simp [newline] at h
  | cons c rest =>
    by_cases hc : c = '\n'
    · subst c
      simp only [newline,Option.some.injEq] at h
      subst rest
      rfl
    · simp [newline,hc] at h

theorem parseSharedDefinition_sound {r : Nat} {cs : List Char}
    {t : CTerm r 0} {tail : List Char}
    (h : parseSharedDefinition r cs = some (t,tail)) :
    cs = sharedDefinition t ++ tail := by
  unfold parseSharedDefinition at h
  split at h
  · rename_i body
    cases hi : readCanonicalIdentifier body with
    | none => simp [hi] at h
    | some result =>
      obtain ⟨j,rest⟩ := result
      by_cases hj : j = r
      · subst j
        simp [hi] at h
        split at h
        · rename_i termBytes
          cases ht : parseTerm r 0 termBytes with
          | none => simp [ht] at h
          | some result =>
            obtain ⟨u,restTerm⟩ := result
            cases hn : newline restTerm with
            | none => simp [ht,hn] at h
            | some remaining =>
              simp [ht,hn] at h
              rcases h with ⟨rfl,rfl⟩
              have hid := readCanonicalIdentifier_sound hi
              have hterm := parseTerm_sound ht
              have hnl := newline_sound hn
              rw [hid,hterm,hnl]
              simp [sharedDefinition,List.append_assoc]
        · simp at h
      · simp [hi,hj] at h
  · simp at h

theorem readDefinition_cterm {r : Nat} (p : CDefs r)
    (t : CTerm r 0) (tail : List Char) :
    readDefinition p.terms (sharedDefinition t ++ tail) =
      some (p.terms ++ [t.close p.expand],tail) := by
  simp [readDefinition,sharedDefinition,readCanonicalIdentifier_wire,
    readEnvTerm_cterm p.terms p.expand p.terms_get t ('\n'::tail),
    newline,p.terms_length,List.append_assoc]

theorem parseSharedDefinition_refines_old {r : Nat} (p : CDefs r)
    {cs : List Char} {t : CTerm r 0} {tail : List Char}
    (h : parseSharedDefinition r cs = some (t,tail)) :
    readDefinition p.terms cs =
      some (p.terms ++ [t.close p.expand],tail) := by
  rw [parseSharedDefinition_sound h]
  exact readDefinition_cterm p t tail

theorem readDefinitionsCount_wire {r : Nat} (p : CDefs r) (tail : List Char) :
    readDefinitionsCount r [] (p.wire ++ tail) = some (p.terms,tail) := by
  induction p generalizing tail with
  | nil => simp [CDefs.wire,CDefs.terms,readDefinitionsCount]
  | @snoc r p t ih =>
    simp only [CDefs.wire,List.append_assoc]
    rw [readDefinitionsCount_comp r 1 []
      (p.wire ++ (sharedDefinition t ++ tail))]
    rw [ih (sharedDefinition t ++ tail)]
    simp [readDefinitionsCount,readDefinition_cterm,CDefs.terms]

theorem readDefinitionPrelude_wire {r : Nat} (p : CDefs r) :
    readDefinitionPrelude r p.wire = some p.terms := by
  have h := readDefinitionsCount_wire p []
  simp only [List.append_nil] at h
  simp [readDefinitionPrelude,h,p.terms_length]

def parseSharedCount : (k r : Nat) → CDefs r → List Char →
    Option ((m : Nat) × CDefs m × List Char)
  | 0, r, p, cs => some ⟨r,p,cs⟩
  | k+1, r, p, cs => do
      let (t,rest) ← parseSharedDefinition r cs
      parseSharedCount k (r+1) (.snoc p t) rest

theorem parseSharedCount_refines_old (k : Nat) {r : Nat} (p : CDefs r)
    {cs : List Char} {m : Nat} {q : CDefs m} {tail : List Char}
    (h : parseSharedCount k r p cs = some ⟨m,q,tail⟩) :
    readDefinitionsCount k p.terms cs = some (q.terms,tail) := by
  induction k generalizing r p cs m q tail with
  | zero =>
    simp [parseSharedCount] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    rfl
  | succ k ih =>
    cases hs : parseSharedDefinition r cs with
    | none => simp [parseSharedCount,hs] at h
    | some result =>
      obtain ⟨t,rest⟩ := result
      have hstep := parseSharedDefinition_refines_old p hs
      have hnext : parseSharedCount k (r+1) (.snoc p t) rest =
          some ⟨m,q,tail⟩ := by simpa [parseSharedCount,hs] using h
      have hind := ih (p.snoc t) hnext
      simpa [readDefinitionsCount,hstep,CDefs.terms] using hind

theorem parseSharedCount_sound_wire (k : Nat) {r : Nat} (p : CDefs r)
    {cs : List Char} {m : Nat} {q : CDefs m} {tail : List Char}
    (h : parseSharedCount k r p cs = some ⟨m,q,tail⟩) :
    p.wire ++ cs = q.wire ++ tail := by
  induction k generalizing r p cs m q tail with
  | zero =>
    simp [parseSharedCount] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    rfl
  | succ k ih =>
    cases hs : parseSharedDefinition r cs with
    | none => simp [parseSharedCount,hs] at h
    | some result =>
      obtain ⟨t,rest⟩ := result
      have hnext : parseSharedCount k (r+1) (.snoc p t) rest =
          some ⟨m,q,tail⟩ := by simpa [parseSharedCount,hs] using h
      have hw := parseSharedDefinition_sound hs
      have hc := ih (p.snoc t) hnext
      simpa [hw,CDefs.wire,List.append_assoc] using hc

theorem parseSharedCount_comp (a b r : Nat) (p : CDefs r)
    (cs : List Char) :
    parseSharedCount (a+b) r p cs =
      (parseSharedCount a r p cs).bind
        (fun ⟨m,q,rest⟩ => parseSharedCount b m q rest) := by
  induction a generalizing r p cs with
  | zero => simp [parseSharedCount]
  | succ a ih =>
    simp only [Nat.succ_add,parseSharedCount]
    cases hp : parseSharedDefinition r cs with
    | none => simp [hp]
    | some result =>
      obtain ⟨t,rest⟩ := result
      simp [hp,ih]

theorem parseSharedCount_wire {r : Nat} (p : CDefs r) (tail : List Char) :
    parseSharedCount r 0 .nil (p.wire ++ tail) = some ⟨r,p,tail⟩ := by
  induction p generalizing tail with
  | nil => simp [CDefs.wire,parseSharedCount]
  | @snoc r p t ih =>
    simp only [CDefs.wire,List.append_assoc]
    rw [parseSharedCount_comp r 1 0 .nil
      (p.wire ++ (sharedDefinition t ++ tail))]
    rw [ih (sharedDefinition t ++ tail)]
    simp [parseSharedCount,parseSharedDefinition_wire]

/-- Exactly `r` closed definitions, consuming all bytes. -/
def parseSharedPrelude (r : Nat) (cs : List Char) : Option (CDefs r) := do
  let ⟨m,p,rest⟩ ← parseSharedCount r 0 .nil cs
  if h : m = r then
    if rest.isEmpty then some (h ▸ p) else none
  else none

theorem parseSharedPrelude_wire {r : Nat} (p : CDefs r) :
    parseSharedPrelude r p.wire = some p := by
  have h := parseSharedCount_wire p []
  simp only [List.append_nil] at h
  simp [parseSharedPrelude,h]

theorem parseSharedPrelude_refines_old {r : Nat} {cs : List Char}
    {p : CDefs r} (h : parseSharedPrelude r cs = some p) :
    readDefinitionPrelude r cs = some p.terms := by
  unfold parseSharedPrelude at h
  cases hp : parseSharedCount r 0 .nil cs with
  | none => simp [hp] at h
  | some result =>
    obtain ⟨m,q,rest⟩ := result
    by_cases hm : m = r
    · simp [hp,hm] at h
      subst m
      rcases h with ⟨rfl,rfl⟩
      have hOld := parseSharedCount_refines_old r CDefs.nil hp
      change readDefinitionsCount r [] cs = some (q.terms,[]) at hOld
      unfold readDefinitionPrelude
      rw [hOld]
      simp [q.terms_length]
    · simp [hp,hm] at h

theorem parseSharedPrelude_sound_wire {r : Nat} {cs : List Char}
    {p : CDefs r} (h : parseSharedPrelude r cs = some p) :
    cs = p.wire := by
  unfold parseSharedPrelude at h
  cases hp : parseSharedCount r 0 .nil cs with
  | none => simp [hp] at h
  | some result =>
    obtain ⟨m,q,rest⟩ := result
    by_cases hm : m = r
    · simp [hp,hm] at h
      subst m
      rcases h with ⟨rfl,rfl⟩
      have hw := parseSharedCount_sound_wire r CDefs.nil hp
      simpa [CDefs.wire] using hw
    · simp [hp,hm] at h

theorem parseSharedPrelude_mass_le_input {r : Nat} {cs : List Char}
    {p : CDefs r} (h : parseSharedPrelude r cs = some p) :
    p.mass ≤ cs.length := by
  rw [parseSharedPrelude_sound_wire h]
  exact p.mass_le_wire

theorem two_definition_readers_agree_on_wire {r : Nat} (p : CDefs r) :
    parseSharedPrelude r p.wire = some p ∧
      readDefinitionPrelude r p.wire = some p.terms :=
  ⟨parseSharedPrelude_wire p, readDefinitionPrelude_wire p⟩

end MAISO11.Wire

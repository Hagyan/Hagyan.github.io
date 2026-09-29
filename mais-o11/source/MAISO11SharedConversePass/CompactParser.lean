import CompactProof

/-! An executable parser for the compact trace proof's fully parenthesized
term/formula/record syntax. Parsing is checked against canonical serialization. -/
set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Wire
open Arithmetic Quotation

def parseLevel (n level : Nat) : Option (Fin n) :=
  if h : level < n then some ⟨n-1-level,by omega⟩ else none

theorem parseLevel_level {n : Nat} (i : Fin n) :
    parseLevel n (level i) = some i := by
  simp only [parseLevel,level_lt,dite_true]
  congr 1
  apply Fin.ext
  have hi := i.isLt
  simp only [level]
  omega

def close : List Char → Option (List Char)
  | ')' :: cs => some cs
  | _ => none

def parseTermFuel (r n : Nat) : Nat → List Char → Option (CTerm r n × List Char)
  | 0, _ => none
  | fuel+1, cs =>
    match cs with
    | '0' :: tail => some (.zero,tail)
    | 'v' :: _ => do
        let (x,tail) ← readVariable cs
        let i ← parseLevel n x
        pure (.var i,tail)
    | 'u' :: _ => do
        let (x,tail) ← readIdentifier cs
        if h : x < r then pure (.ref ⟨x,h⟩,tail) else none
    | '(' :: 'D' :: tail => do
        let (t,rest) ← parseTermFuel r n fuel tail
        let rest ← close rest
        pure (.bit0 t,rest)
    | '(' :: 'E' :: tail => do
        let (t,rest) ← parseTermFuel r n fuel tail
        let rest ← close rest
        pure (.bit1 t,rest)
    | '(' :: '+' :: tail => do
        let (s,rest) ← parseTermFuel r n fuel tail
        let (t,rest) ← parseTermFuel r n fuel rest
        let rest ← close rest
        pure (.add s t,rest)
    | '(' :: '*' :: tail => do
        let (s,rest) ← parseTermFuel r n fuel tail
        let (t,rest) ← parseTermFuel r n fuel rest
        let rest ← close rest
        pure (.mul s t,rest)
    | _ => none

/-- A canonical checked parser: noncanonical identifier spellings are rejected
by comparing the reconstructed serialization with the entire consumed prefix. -/
def parseTerm (r n : Nat) (cs : List Char) : Option (CTerm r n × List Char) := do
  let (t,tail) ← parseTermFuel r n cs.length cs
  if t.wire ++ tail = cs then pure (t,tail) else none

theorem parseTerm_sound {r n : Nat} {cs : List Char} {t : CTerm r n} {tail : List Char}
    (h : parseTerm r n cs = some (t,tail)) : cs = t.wire ++ tail := by
  simp only [parseTerm] at h
  cases he : parseTermFuel r n cs.length cs with
  | none => simp [he] at h
  | some result =>
    obtain ⟨u,rest⟩ := result
    by_cases hc : u.wire ++ rest = cs
    · simp [he,hc] at h
      obtain ⟨rfl,rfl⟩ := h
      exact hc.symm
    · simp [he,hc] at h

theorem parseTermFuel_wire {r n : Nat} (t : CTerm r n) (tail : List Char)
    (fuel : Nat) (h : t.wire.length ≤ fuel) :
    parseTermFuel r n fuel (t.wire ++ tail) = some (t,tail) := by
  induction t generalizing fuel tail with
  | var i =>
    cases fuel with
    | zero =>
      have hv := variable_length (level i)
      simp only [CTerm.wire] at h
      have hi := identifier_length (level i)
      omega
    | succ fuel =>
      have hi : readIdentifier ('u' ::
          (List.replicate (bits (level i+1)).length '1' ++
          '0' :: ((bits (level i+1)).reverse.map bitChar ++ tail))) =
          some (level i,tail) := by
        simpa [identifier,List.map_reverse] using readIdentifier_encode (level i) tail
      simp [parseTermFuel,variableName,identifier,readVariable,
        hi,parseLevel_level,CTerm.wire]
      simp only [List.map_reverse] at hi
      rw [hi]
      simp [parseLevel_level]
  | ref i =>
    cases fuel with
    | zero =>
      have hi := identifier_length i.val
      simp only [CTerm.wire] at h
      omega
    | succ fuel =>
      have hi : readIdentifier ('u' ::
          (List.replicate (bits (i.val+1)).length '1' ++
          '0' :: ((bits (i.val+1)).reverse.map bitChar ++ tail))) =
          some (i.val,tail) := by
        simpa [identifier,List.map_reverse] using readIdentifier_encode i.val tail
      simp [CTerm.wire,parseTermFuel,identifier,hi,i.isLt]
      simp only [List.map_reverse] at hi
      rw [hi]
      simp [i.isLt]
  | zero =>
    cases fuel with
    | zero => simp [CTerm.wire] at h
    | succ fuel => rfl
  | bit0 t ih =>
    cases fuel with
    | zero => simp [CTerm.wire] at h
    | succ fuel =>
      have ht : t.wire.length ≤ fuel := by simp [CTerm.wire] at h; omega
      simp [CTerm.wire,parseTermFuel,ih (')'::tail) fuel ht,close]
  | bit1 t ih =>
    cases fuel with
    | zero => simp [CTerm.wire] at h
    | succ fuel =>
      have ht : t.wire.length ≤ fuel := by simp [CTerm.wire] at h; omega
      simp [CTerm.wire,parseTermFuel,ih (')'::tail) fuel ht,close]
  | add s t hs ht =>
    cases fuel with
    | zero => simp [CTerm.wire] at h
    | succ fuel =>
      have h₁ : s.wire.length ≤ fuel := by simp [CTerm.wire] at h; omega
      have h₂ : t.wire.length ≤ fuel := by simp [CTerm.wire] at h; omega
      simp [CTerm.wire,parseTermFuel,hs _ fuel h₁,ht _ fuel h₂,close,
        List.append_assoc]
  | mul s t hs ht =>
    cases fuel with
    | zero => simp [CTerm.wire] at h
    | succ fuel =>
      have h₁ : s.wire.length ≤ fuel := by simp [CTerm.wire] at h; omega
      have h₂ : t.wire.length ≤ fuel := by simp [CTerm.wire] at h; omega
      simp [CTerm.wire,parseTermFuel,hs _ fuel h₁,ht _ fuel h₂,close,
        List.append_assoc]

theorem parseTerm_wire {r n : Nat} (t : CTerm r n) (tail : List Char) :
    parseTerm r n (t.wire ++ tail) = some (t,tail) := by
  simp only [parseTerm,List.length_append]
  rw [parseTermFuel_wire t tail (t.wire.length+tail.length) (by omega)]
  simp

def parseFormulaFuel (r n : Nat) : Nat → List Char → Option (CFormula r n × List Char)
  | 0, _ => none
  | fuel+1, cs =>
    match cs with
    | '(' :: '=' :: body => do
        let (s,rest) ← parseTerm r n body
        let (t,rest) ← parseTerm r n rest
        let rest ← close rest
        pure (.eq s t,rest)
    | '(' :: '~' :: body => do
        let (f,rest) ← parseFormulaFuel r n fuel body
        let rest ← close rest
        pure (.neg f,rest)
    | '(' :: '>' :: body => do
        let (f,rest) ← parseFormulaFuel r n fuel body
        let (g,rest) ← parseFormulaFuel r n fuel rest
        let rest ← close rest
        pure (.imp f g,rest)
    | '(' :: 'A' :: body => do
        let (x,rest) ← readVariable body
        if x ≠ n then none else do
          let (f,rest) ← parseFormulaFuel r (n+1) fuel rest
          let rest ← close rest
          pure (.all f,rest)
    | _ => none

def parseFormula (r n : Nat) (cs : List Char) : Option (CFormula r n × List Char) := do
  let (f,tail) ← parseFormulaFuel r n cs.length cs
  if f.wire ++ tail = cs then pure (f,tail) else none

theorem parseFormula_sound {r n : Nat} {cs : List Char} {f : CFormula r n}
    {tail : List Char} (h : parseFormula r n cs = some (f,tail)) :
    cs = f.wire ++ tail := by
  unfold parseFormula at h
  cases he : parseFormulaFuel r n cs.length cs with
  | none => simp [he] at h
  | some result =>
    obtain ⟨u,rest⟩ := result
    by_cases hc : u.wire ++ rest = cs
    · simp [he,hc] at h
      obtain ⟨rfl,rfl⟩ := h
      exact hc.symm
    · simp [he,hc] at h

theorem parseFormulaFuel_wire {r n : Nat} (f : CFormula r n)
    (tail : List Char) (fuel : Nat) (h : f.wire.length ≤ fuel) :
    parseFormulaFuel r n fuel (f.wire ++ tail) = some (f,tail) := by
  induction f generalizing fuel tail with
  | eq s t =>
    cases fuel with
    | zero => simp [CFormula.wire] at h
    | succ fuel =>
      simp only [CFormula.wire,List.cons_append]
      simp [parseFormulaFuel,parseTerm_wire,close,List.append_assoc]
  | neg f ih =>
    cases fuel with
    | zero => simp [CFormula.wire] at h
    | succ fuel =>
      have hf : f.wire.length ≤ fuel := by simp [CFormula.wire] at h; omega
      simp [CFormula.wire,parseFormulaFuel,ih (')'::tail) fuel hf,close]
  | imp f g hf hg =>
    cases fuel with
    | zero => simp [CFormula.wire] at h
    | succ fuel =>
      have h₁ : f.wire.length ≤ fuel := by simp [CFormula.wire] at h; omega
      have h₂ : g.wire.length ≤ fuel := by simp [CFormula.wire] at h; omega
      simp [CFormula.wire,parseFormulaFuel,hf _ fuel h₁,hg _ fuel h₂,close,
        List.append_assoc]
  | @all n f ih =>
    cases fuel with
    | zero => simp [CFormula.wire] at h
    | succ fuel =>
      have hf : f.wire.length ≤ fuel := by simp [CFormula.wire] at h; omega
      simp [CFormula.wire,parseFormulaFuel,readVariable_encode,
        ih (')'::tail) fuel hf,close,List.append_assoc]

theorem parseFormula_wire {r n : Nat} (f : CFormula r n) (tail : List Char) :
    parseFormula r n (f.wire ++ tail) = some (f,tail) := by
  simp only [parseFormula,List.length_append]
  rw [parseFormulaFuel_wire f tail (f.wire.length+tail.length) (by omega)]
  simp

def newline : List Char → Option (List Char)
  | '\n' :: cs => some cs
  | _ => none

def parseRecordRaw (r k : Nat) (cs : List Char) : Option (Record r k × List Char) :=
  match cs with
  | 'A' :: ' ' :: body => do
      let (f,rest) ← parseFormula r 0 body
      let tail ← newline rest
      pure (.axiom f,tail)
  | 'M' :: '[' :: body => do
      let (a,rest) ← readIdentifier body
      let ',' :: rest := rest | none
      let (b,rest) ← readIdentifier rest
      let ']' :: ' ' :: rest := rest | none
      let (f,rest) ← parseFormula r 0 rest
      let tail ← newline rest
      if ha : a < k then
        if hb : b < k then pure (.mp ⟨a,ha⟩ ⟨b,hb⟩ f,tail) else none
      else none
  | _ => none

def parseRecord (r k : Nat) (cs : List Char) : Option (Record r k × List Char) := do
  let (a,tail) ← parseRecordRaw r k cs
  if a.wire ++ tail = cs then pure (a,tail) else none

theorem parseRecord_sound {r k : Nat} {cs : List Char} {a : Record r k}
    {tail : List Char} (h : parseRecord r k cs = some (a,tail)) :
    cs = a.wire ++ tail := by
  unfold parseRecord at h
  cases he : parseRecordRaw r k cs with
  | none => simp [he] at h
  | some result =>
    obtain ⟨u,rest⟩ := result
    by_cases hc : u.wire ++ rest = cs
    · simp [he,hc] at h
      obtain ⟨rfl,rfl⟩ := h
      exact hc.symm
    · simp [he,hc] at h

theorem parseRecordRaw_wire {r k : Nat} (a : Record r k) (tail : List Char) :
    parseRecordRaw r k (a.wire ++ tail) = some (a,tail) := by
  cases a with
  | «axiom» f => simp [parseRecordRaw,Record.wire,parseFormula_wire,newline]
  | mp a b f =>
    simp [parseRecordRaw,Record.wire,readIdentifier_encode,parseFormula_wire,
      newline,a.isLt,b.isLt,List.append_assoc]

theorem parseRecord_wire {r k : Nat} (a : Record r k) (tail : List Char) :
    parseRecord r k (a.wire ++ tail) = some (a,tail) := by
  simp [parseRecord,parseRecordRaw_wire]

/-- A bounded parser for exactly `remaining` consecutive formula records.
The record count is explicit so a proof containing zero records is unambiguous. -/
def parseRecordsCount (r : Nat) : (remaining : Nat) → {k : Nat} →
    Records r k → List Char → Option ((l : Nat) × Records r l × List Char)
  | 0, _, fs, cs => some ⟨_,fs,cs⟩
  | remaining+1, _, fs, cs => do
      let (record,rest) ← parseRecord r _ cs
      parseRecordsCount r remaining (fs.snoc record) rest

def parseFile (r count : Nat) (cs : List Char) : Option ((k : Nat) × Records r k) := do
  let ⟨k,fs,rest⟩ ← parseRecordsCount r count .nil cs
  if rest.isEmpty then pure ⟨k,fs⟩ else none

theorem parseRecordsCount_sound {r remaining k l : Nat} (fs : Records r k)
    (cs tail : List Char) (gs : Records r l)
    (h : parseRecordsCount r remaining fs cs = some ⟨l,gs,tail⟩) :
    ∃ suffix, gs.wire = fs.wire ++ suffix ∧ cs = suffix ++ tail ∧
      l = k+remaining := by
  induction remaining generalizing k fs cs with
  | zero =>
    simp only [parseRecordsCount] at h
    cases h
    exact ⟨[],by simp,by simp,by omega⟩
  | succ remaining ih =>
    simp only [parseRecordsCount] at h
    cases hr : parseRecord r k cs with
    | none => simp [hr] at h
    | some result =>
      obtain ⟨a,rest⟩ := result
      have hc := parseRecord_sound hr
      simp only [hr,Option.bind_some] at h
      obtain ⟨suffix,hwire,hinput,hcount⟩ := ih (fs.snoc a) rest h
      refine ⟨a.wire ++ suffix,?_,?_,by omega⟩
      · simp only [Records.wire,List.append_assoc] at hwire ⊢
        exact hwire
      · rw [hc,hinput]
        simp [List.append_assoc]

theorem parseFile_sound {r count k : Nat} {cs : List Char} {fs : Records r k}
    (h : parseFile r count cs = some ⟨k,fs⟩) :
    cs = fs.wire ∧ k = count := by
  unfold parseFile at h
  cases hp : parseRecordsCount r count (.nil : Records r 0) cs with
  | none => simp [hp] at h
  | some result =>
    obtain ⟨l,gs,rest⟩ := result
    by_cases he : rest.isEmpty
    · simp [hp,he] at h
      obtain ⟨hre,hl,hgs⟩ := h
      subst l
      cases hgs
      obtain ⟨suffix,hw,hi,hc⟩ := parseRecordsCount_sound .nil cs rest fs hp
      subst rest
      simp only [Records.wire,List.nil_append,List.append_nil] at hw hi
      exact ⟨hi.trans hw.symm,by simpa using hc⟩
    · simp [hp,he] at h
      exact (he (by simp [h.1])).elim

theorem parseRecordsCount_comp (r a b : Nat) {k : Nat}
    (base : Records r k) (cs : List Char) :
    parseRecordsCount r (a+b) base cs =
      (parseRecordsCount r a base cs).bind
        (fun ⟨_,ys,rest⟩ => parseRecordsCount r b ys rest) := by
  induction a generalizing k base cs with
  | zero => simp [parseRecordsCount]
  | succ a ih =>
    simp only [Nat.succ_add,parseRecordsCount]
    cases hp : parseRecord r k cs with
    | none => simp [hp]
    | some result =>
      obtain ⟨f,rest⟩ := result
      simp [hp]
      exact ih (base.snoc f) rest

theorem parseRecordsCount_wire {r k : Nat} (fs : Records r k) (tail : List Char) :
    parseRecordsCount r k .nil (fs.wire ++ tail) = some ⟨k,fs,tail⟩ := by
  induction fs generalizing tail with
  | nil => simp [Records.wire,parseRecordsCount]
  | @snoc k fs f ih =>
    simp only [Records.wire]
    simp only [List.append_assoc]
    apply Eq.trans (parseRecordsCount_comp r k 1 .nil (fs.wire ++ (f.wire ++ tail)))
    rw [ih (f.wire ++ tail)]
    simp [parseRecordsCount,parseRecord_wire]

theorem parseFile_wire {r k : Nat} (fs : Records r k) :
    parseFile r k fs.wire = some ⟨k,fs⟩ := by
  unfold parseFile
  have h := parseRecordsCount_wire fs []
  simp only [List.append_nil] at h
  rw [h]
  rfl

/-- The polynomially bounded trace proof from the preceding certificate has
an actual written string accepted by the executable parser, with exactly the
same structured records on return. Logical validity still refers to the
concrete dictionary; the parser does not decide axiom membership by itself. -/
theorem compiled_trace_file_parsed {b n : Nat} (g : Grammar b n) :
    ∃ (k : Nat) (fs : Records (3*n+n) k) (last : Fin k),
      k ≤ traceN n ∧ last.val+1=k ∧ fs.get last = trace n ∧
      parseFile (3*n+n) k fs.wire = some ⟨k,fs⟩ ∧
      fs.valid (dictionary (compile g)) ∧
      (definitionPrelude (compile g) ++ fs.wire).length ≤ fullCharacters b g.mass g.mass := by
  obtain ⟨k,fs,last,hk,hl,hf,hv,hc⟩ := compiled_trace_file_mass g
  exact ⟨k,fs,last,hk,hl,hf,parseFile_wire fs,hv,hc⟩

def readCanonicalIdentifier (cs : List Char) : Option (Nat × List Char) := do
  let (i,rest) ← readIdentifier cs
  if identifier i ++ rest = cs then pure (i,rest) else none

theorem readCanonicalIdentifier_wire (i : Nat) (tail : List Char) :
    readCanonicalIdentifier (identifier i ++ tail) = some (i,tail) := by
  simp [readCanonicalIdentifier,readIdentifier_encode]

def readEnvTermFuel (env : List ClosedTerm) : Nat → List Char → Option (ClosedTerm × List Char)
  | 0, _ => none
  | fuel+1, cs =>
    match cs with
    | '0' :: tail => some (.zero,tail)
    | 'u' :: _ => do
        let (i,rest) ← readCanonicalIdentifier cs
        let t ← env[i]?
        pure (t,rest)
    | '(' :: 'D' :: body => do
        let (t,rest) ← readEnvTermFuel env fuel body
        let rest ← close rest
        pure (.bit0 t,rest)
    | '(' :: 'E' :: body => do
        let (t,rest) ← readEnvTermFuel env fuel body
        let rest ← close rest
        pure (.bit1 t,rest)
    | '(' :: '+' :: body => do
        let (s,rest) ← readEnvTermFuel env fuel body
        let (t,rest) ← readEnvTermFuel env fuel rest
        let rest ← close rest
        pure (.add s t,rest)
    | '(' :: '*' :: body => do
        let (s,rest) ← readEnvTermFuel env fuel body
        let (t,rest) ← readEnvTermFuel env fuel rest
        let rest ← close rest
        pure (.mul s t,rest)
    | _ => none

def readEnvTerm (env : List ClosedTerm) (cs : List Char) : Option (ClosedTerm × List Char) :=
  readEnvTermFuel env cs.length cs

/-- Parse the next `def u_i := term` line. The exact next index is enforced,
and each referenced register must already be present in the environment. -/
def readDefinition (env : List ClosedTerm) (cs : List Char) :
    Option (List ClosedTerm × List Char) :=
  match cs with
  | 'd' :: 'e' :: 'f' :: ' ' :: body => do
      let (i,rest) ← readCanonicalIdentifier body
      if i ≠ env.length then none else do
        let ' ' :: ':' :: '=' :: ' ' :: rest := rest | none
        let (t,rest) ← readEnvTerm env rest
        let rest ← newline rest
        pure (env ++ [t],rest)
  | _ => none

def readDefinitionsCount : Nat → List ClosedTerm → List Char →
    Option (List ClosedTerm × List Char)
  | 0, env, cs => some (env,cs)
  | k+1, env, cs => do
      let (next,rest) ← readDefinition env cs
      readDefinitionsCount k next rest

def readDefinitionPrelude (r : Nat) (cs : List Char) : Option (List ClosedTerm) := do
  let (env,rest) ← readDefinitionsCount r [] cs
  if rest.isEmpty && env.length = r then pure env else none

/-- The parsed definitions supply the dictionary used to check the parsed
records. This is an executable check on both sections of the byte string. -/
def decodeSections (r recordCount : Nat) (prelude records : List Char) :
    Option (List ClosedTerm × ((k : Nat) × Records r k)) := do
  let env ← readDefinitionPrelude r prelude
  let ⟨k,fs⟩ ← parseFile r recordCount records
  pure ⟨env,k,fs⟩

theorem readDefinitionPrelude_length {r : Nat} {cs : List Char} {env : List ClosedTerm}
    (h : readDefinitionPrelude r cs = some env) : env.length = r := by
  unfold readDefinitionPrelude at h
  cases hp : readDefinitionsCount r [] cs with
  | none => simp [hp] at h
  | some result =>
    obtain ⟨out,rest⟩ := result
    by_cases hc : rest.isEmpty && out.length = r
    · simp [hp,hc] at h
      obtain ⟨⟨_,hlen⟩,rfl⟩ := h
      exact hlen
    · simp [hp,hc] at h
      have hlen := h.1.2
      have hempty := h.1.1
      simp [hempty,hlen] at hc

theorem decodeSections_sound {r count k : Nat} {prelude records : List Char}
    {env : List ClosedTerm} {fs : Records r k}
    (h : decodeSections r count prelude records = some ⟨env,k,fs⟩) :
    env.length = r ∧ records = fs.wire ∧ k = count := by
  unfold decodeSections at h
  cases he : readDefinitionPrelude r prelude with
  | none => simp [he] at h
  | some out =>
    cases hf : parseFile r count records with
    | none => simp [he,hf] at h
    | some result =>
      obtain ⟨j,gs⟩ := result
      simp [he,hf] at h
      obtain ⟨rfl,rfl,hgs⟩ := h
      cases hgs
      exact ⟨readDefinitionPrelude_length he,(parseFile_sound hf).1,(parseFile_sound hf).2⟩

theorem readEnvTermFuel_numeralBits (env : List ClosedTerm) (bs : List Bool)
    (tail : List Char) (fuel : Nat) (h : (numeralBits bs).length ≤ fuel) :
    readEnvTermFuel env fuel (numeralBits bs ++ tail) =
      some (numeralTermBits bs,tail) := by
  induction bs generalizing fuel tail with
  | nil =>
    cases fuel with
    | zero => simp [numeralBits] at h
    | succ fuel => rfl
  | cons b bs ih =>
    cases fuel with
    | zero => simp [numeralBits] at h
    | succ fuel =>
      have hb : (numeralBits bs).length ≤ fuel := by
        simp [numeralBits] at h
        omega
      cases b <;> simp [numeralBits,numeralTermBits,readEnvTermFuel,
        ih (')'::tail) fuel hb,close]

theorem readEnvTermFuel_expr {n : Nat} (env : List ClosedTerm)
    (ρ : Fin n → TermTriple)
    (he : ∀ (i : Fin n) (s : Slot), env[3*i.val+s.offset]? = some ((ρ i).get s))
    (e : Expr n) (tail : List Char) (fuel : Nat) (hf : e.wire.length ≤ fuel) :
    readEnvTermFuel env fuel (e.wire ++ tail) = some (e.expand ρ,tail) := by
  induction e generalizing fuel tail with
  | num v =>
    simpa only [Expr.wire,numeral,Expr.expand,numeralTerm] using
      readEnvTermFuel_numeralBits env (bits v) tail fuel hf
  | ref i s =>
    cases fuel with
    | zero =>
      have hi := identifier_length (3*i.val+s.offset)
      simp only [Expr.wire] at hf
      omega
    | succ fuel =>
      have hi := readCanonicalIdentifier_wire (3*i.val+s.offset) tail
      simp [Expr.wire,readEnvTermFuel,identifier,he,Expr.expand,hi]
      have hr : readCanonicalIdentifier ('u' ::
          (List.replicate (bits (3*i.val+s.offset+1)).length '1' ++
          '0' :: (((bits (3*i.val+s.offset+1)).map bitChar).reverse ++ tail))) =
          some (3*i.val+s.offset,tail) := by
        simpa only [identifier,List.map_reverse,List.append_assoc,List.cons_append,
          List.nil_append] using hi
      rw [hr]
      simp [he]
  | add x y hx hy =>
    cases fuel with
    | zero => simp [Expr.wire] at hf
    | succ fuel =>
      have h₁ : x.wire.length ≤ fuel := by simp [Expr.wire] at hf; omega
      have h₂ : y.wire.length ≤ fuel := by simp [Expr.wire] at hf; omega
      simp [Expr.wire,readEnvTermFuel,Expr.expand,
        hx (y.wire ++ ')'::tail) fuel h₁,hy (')'::tail) fuel h₂,
        close,List.append_assoc]
  | mul x y hx hy =>
    cases fuel with
    | zero => simp [Expr.wire] at hf
    | succ fuel =>
      have h₁ : x.wire.length ≤ fuel := by simp [Expr.wire] at hf; omega
      have h₂ : y.wire.length ≤ fuel := by simp [Expr.wire] at hf; omega
      simp [Expr.wire,readEnvTermFuel,Expr.expand,
        hx (y.wire ++ ')'::tail) fuel h₁,hy (')'::tail) fuel h₂,
        close,List.append_assoc]

theorem readEnvTermFuel_pack {n m : Nat} (env : List ClosedTerm)
    (ρ : Fin n → TermTriple) (σ : Fin m → ClosedTerm)
    (hs : ∀ (i : Fin n) (s : Slot), env[3*i.val+s.offset]? = some ((ρ i).get s))
    (ht : ∀ j : Fin m, env[3*n+j.val]? = some (σ j))
    (e : PackExpr n m) (tail : List Char) (fuel : Nat) (hf : e.wire.length ≤ fuel) :
    readEnvTermFuel env fuel (e.wire ++ tail) = some (e.expand ρ σ,tail) := by
  induction e generalizing fuel tail with
  | num v =>
    simpa only [PackExpr.wire,numeral,PackExpr.expand,numeralTerm] using
      readEnvTermFuel_numeralBits env (bits v) tail fuel hf
  | source i s =>
    cases fuel with
    | zero =>
      have hi := identifier_length (3*i.val+s.offset)
      simp only [PackExpr.wire] at hf
      omega
    | succ fuel =>
      have hi := readCanonicalIdentifier_wire (3*i.val+s.offset) tail
      simp [PackExpr.wire,readEnvTermFuel,identifier,hs,PackExpr.expand,hi]
      have hr : readCanonicalIdentifier ('u' ::
          (List.replicate (bits (3*i.val+s.offset+1)).length '1' ++
          '0' :: (((bits (3*i.val+s.offset+1)).map bitChar).reverse ++ tail))) =
          some (3*i.val+s.offset,tail) := by
        simpa only [identifier,List.map_reverse,List.append_assoc,List.cons_append,
          List.nil_append] using hi
      rw [hr]
      simp [hs]
  | saved j =>
    cases fuel with
    | zero =>
      have hi := identifier_length (3*n+j.val)
      simp only [PackExpr.wire] at hf
      omega
    | succ fuel =>
      have hi := readCanonicalIdentifier_wire (3*n+j.val) tail
      simp [PackExpr.wire,readEnvTermFuel,identifier,ht,PackExpr.expand,hi]
      have hr : readCanonicalIdentifier ('u' ::
          (List.replicate (bits (3*n+j.val+1)).length '1' ++
          '0' :: (((bits (3*n+j.val+1)).map bitChar).reverse ++ tail))) =
          some (3*n+j.val,tail) := by
        simpa only [identifier,List.map_reverse,List.append_assoc,List.cons_append,
          List.nil_append] using hi
      rw [hr]
      simp [ht]
  | add x y hx hy =>
    cases fuel with
    | zero => simp [PackExpr.wire] at hf
    | succ fuel =>
      have h₁ : x.wire.length ≤ fuel := by simp [PackExpr.wire] at hf; omega
      have h₂ : y.wire.length ≤ fuel := by simp [PackExpr.wire] at hf; omega
      simp [PackExpr.wire,readEnvTermFuel,PackExpr.expand,
        hx (y.wire ++ ')'::tail) fuel h₁,hy (')'::tail) fuel h₂,
        close,List.append_assoc]
  | mul x y hx hy =>
    cases fuel with
    | zero => simp [PackExpr.wire] at hf
    | succ fuel =>
      have h₁ : x.wire.length ≤ fuel := by simp [PackExpr.wire] at hf; omega
      have h₂ : y.wire.length ≤ fuel := by simp [PackExpr.wire] at hf; omega
      simp [PackExpr.wire,readEnvTermFuel,PackExpr.expand,
        hx (y.wire ++ ')'::tail) fuel h₁,hy (')'::tail) fuel h₂,
        close,List.append_assoc]

theorem readEnvTerm_expr {n : Nat} (env : List ClosedTerm)
    (ρ : Fin n → TermTriple)
    (he : ∀ (i : Fin n) (s : Slot), env[3*i.val+s.offset]? = some ((ρ i).get s))
    (e : Expr n) (tail : List Char) :
    readEnvTerm env (e.wire ++ tail) = some (e.expand ρ,tail) := by
  unfold readEnvTerm
  exact readEnvTermFuel_expr env ρ he e tail _ (by simp)

theorem readEnvTerm_pack {n m : Nat} (env : List ClosedTerm)
    (ρ : Fin n → TermTriple) (σ : Fin m → ClosedTerm)
    (hs : ∀ (i : Fin n) (s : Slot), env[3*i.val+s.offset]? = some ((ρ i).get s))
    (ht : ∀ j : Fin m, env[3*n+j.val]? = some (σ j))
    (e : PackExpr n m) (tail : List Char) :
    readEnvTerm env (e.wire ++ tail) = some (e.expand ρ σ,tail) := by
  unfold readEnvTerm
  exact readEnvTermFuel_pack env ρ σ hs ht e tail _ (by simp)

theorem readDefinition_expr {n : Nat} (env : List ClosedTerm)
    (ρ : Fin n → TermTriple) (he : ∀ (i : Fin n) (s : Slot),
      env[3*i.val+s.offset]? = some ((ρ i).get s))
    (s : Slot) (e : Expr n) (tail : List Char)
    (hl : env.length = 3*n+s.offset) :
    readDefinition env (definition n s e ++ tail) =
      some (env ++ [e.expand ρ],tail) := by
  simp [readDefinition,definition,readCanonicalIdentifier_wire,
    readEnvTerm_expr env ρ he e ('\n'::tail),newline,hl,List.append_assoc]

theorem readDefinition_pack {n m : Nat} (env : List ClosedTerm)
    (ρ : Fin n → TermTriple) (σ : Fin m → ClosedTerm)
    (hs : ∀ (i : Fin n) (s : Slot), env[3*i.val+s.offset]? = some ((ρ i).get s))
    (ht : ∀ j : Fin m, env[3*n+j.val]? = some (σ j))
    (e : PackExpr n m) (tail : List Char)
    (hl : env.length = 3*n+m) :
    readDefinition env (packingDefinition e ++ tail) =
      some (env ++ [e.expand ρ σ],tail) := by
  simp [readDefinition,packingDefinition,readCanonicalIdentifier_wire,
    readEnvTerm_pack env ρ σ hs ht e ('\n'::tail),newline,hl,List.append_assoc]

theorem Program.terms_source {n : Nat} (p : Program n) (i : Fin n) (s : Slot) :
    p.terms[3*i.val+s.offset]? = some ((p.expansion i).get s) := by
  induction p with
  | nil => exact Fin.elim0 i
  | @snoc n p t ih =>
    let v := t.expand p.expansion
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hp := p.terms_length
      have hindex : 3*n+s.offset - p.terms.length = s.offset := by omega
      simp only [Program.terms,Program.expansion,Fin.lastCases_last,Fin.val_last]
      rw [List.getElem?_append_right (by omega)]
      rw [hindex]
      cases s <;> rfl
    · have hj := j.isLt
      have hs := s.offset_le_two
      have hp := p.terms_length
      have hlt : 3*j.val+s.offset < p.terms.length := by omega
      simp only [Program.terms,Program.expansion,Fin.lastCases_castSucc,
        Fin.coe_castSucc,List.getElem?_append_left hlt]
      exact ih j

theorem source_index_stable {n : Nat} (env extra : List ClosedTerm)
    (ρ : Fin n → TermTriple) (hl : 3*n ≤ env.length)
    (he : ∀ (i : Fin n) (s : Slot), env[3*i.val+s.offset]? = some ((ρ i).get s)) :
    ∀ (i : Fin n) (s : Slot), (env ++ extra)[3*i.val+s.offset]? = some ((ρ i).get s) := by
  intro i s
  have hi := i.isLt
  have hs := s.offset_le_two
  rw [List.getElem?_append_left (by omega)]
  exact he i s

theorem readDefinitionsCount_comp (a b : Nat) (env : List ClosedTerm) (cs : List Char) :
    readDefinitionsCount (a+b) env cs =
      (readDefinitionsCount a env cs).bind
        (fun ⟨env',rest⟩ => readDefinitionsCount b env' rest) := by
  induction a generalizing env cs with
  | zero => simp [readDefinitionsCount]
  | succ a ih =>
    simp only [Nat.succ_add,readDefinitionsCount]
    cases h : readDefinition env cs with
    | none => simp [h]
    | some result =>
      obtain ⟨next,rest⟩ := result
      simp [h]
      exact ih next rest

theorem readTripleDefinitions {n : Nat} (env : List ClosedTerm)
    (ρ : Fin n → TermTriple)
    (he : ∀ (i : Fin n) (s : Slot), env[3*i.val+s.offset]? = some ((ρ i).get s))
    (hl : env.length = 3*n)
    (t : Triple n) (tail : List Char) :
    readDefinitionsCount 3 env (t.wire ++ tail) =
      some (env ++ [t.len.expand ρ,t.scale.expand ρ,t.payload.expand ρ],tail) := by
  have h₁ := readDefinition_expr env ρ he .len t.len
    (definition n .scale t.scale ++ definition n .payload t.payload ++ tail)
    (by simpa [Slot.offset] using hl)
  have he₁ := source_index_stable env [t.len.expand ρ] ρ (by omega) he
  have h₂ := readDefinition_expr (env ++ [t.len.expand ρ]) ρ he₁ .scale t.scale
    (definition n .payload t.payload ++ tail) (by simp [hl,Slot.offset])
  have he₂ := source_index_stable env [t.len.expand ρ,t.scale.expand ρ] ρ
    (by omega) he
  have h₃ := readDefinition_expr (env ++ [t.len.expand ρ,t.scale.expand ρ])
    ρ he₂ .payload t.payload tail (by simp [hl,Slot.offset])
  simp only [Triple.wire,List.append_assoc,readDefinitionsCount]
  simp only [List.append_assoc] at h₁ h₂ h₃
  rw [h₁]
  dsimp
  rw [h₂]
  dsimp
  rw [h₃]
  simp [List.append_assoc]

theorem Program.wire_parses {n : Nat} (p : Program n) (tail : List Char) :
    readDefinitionsCount (3*n) [] (p.wire ++ tail) = some (p.terms,tail) := by
  induction p generalizing tail with
  | nil => rfl
  | @snoc n p t ih =>
    have hh : 3*(n+1) = 3*n+3 := by omega
    rw [hh]
    simp only [Program.wire,List.append_assoc]
    apply Eq.trans (readDefinitionsCount_comp (3*n) 3 [] (p.wire ++ (t.wire ++ tail)))
    rw [ih (t.wire ++ tail)]
    dsimp
    rw [readTripleDefinitions p.terms p.expansion
      (fun i s => Program.terms_source p i s) p.terms_length t tail]
    rfl

def _root_.MAISO11.Quotation.PackingProgram.terms {n : Nat} (ρ : Fin n → TermTriple) :
    {m : Nat} → PackingProgram n m → List ClosedTerm
  | _, .nil => []
  | _, .snoc q e => q.terms ρ ++ [e.expand ρ (q.expansion ρ)]

theorem _root_.MAISO11.Quotation.PackingProgram.terms_length {n m : Nat} (ρ : Fin n → TermTriple)
    (q : PackingProgram n m) : (q.terms ρ).length = m := by
  induction q with
  | nil => rfl
  | snoc q e ih => simp [PackingProgram.terms,ih]

theorem _root_.MAISO11.Quotation.PackingProgram.terms_saved {n m : Nat} (ρ : Fin n → TermTriple)
    (q : PackingProgram n m) (j : Fin m) :
    (q.terms ρ)[j.val]? = some (q.expansion ρ j) := by
  induction q with
  | nil => exact Fin.elim0 j
  | @snoc m q e ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · have hl := q.terms_length ρ
      simp only [PackingProgram.terms,PackingProgram.expansion,Fin.lastCases_last,Fin.val_last]
      rw [List.getElem?_append_right (by omega)]
      simp [hl]
    · have hi := i.isLt
      have hl := q.terms_length ρ
      have hlt : i.val < (q.terms ρ).length := by omega
      simp only [PackingProgram.terms,PackingProgram.expansion,Fin.lastCases_castSucc,Fin.coe_castSucc,
        List.getElem?_append_left hlt]
      exact ih i

theorem source_and_saved {n m : Nat} (p : Program n) (q : PackingProgram n m)
    (i : Fin n) (s : Slot) :
    (p.terms ++ q.terms p.expansion)[3*i.val+s.offset]? =
      some ((p.expansion i).get s) := by
  have hi := i.isLt
  have hs := s.offset_le_two
  have hl := p.terms_length
  rw [List.getElem?_append_left (by omega)]
  exact Program.terms_source p i s

theorem saved_after_source {n m : Nat} (p : Program n) (q : PackingProgram n m)
    (j : Fin m) :
    (p.terms ++ q.terms p.expansion)[3*n+j.val]? =
      some (q.expansion p.expansion j) := by
  have hl := p.terms_length
  rw [List.getElem?_append_right (by omega)]
  rw [show 3*n+j.val-p.terms.length = j.val by omega]
  exact q.terms_saved p.expansion j

theorem PackingProgram.wire_parses {n m : Nat} (p : Program n)
    (q : PackingProgram n m) (tail : List Char) :
    readDefinitionsCount m p.terms (q.wire ++ tail) =
      some (p.terms ++ q.terms p.expansion,tail) := by
  induction q generalizing tail with
  | nil => simp [PackingProgram.wire,PackingProgram.terms,readDefinitionsCount]
  | @snoc m q e ih =>
    simp only [PackingProgram.wire,List.append_assoc]
    apply Eq.trans (readDefinitionsCount_comp m 1 p.terms
      (q.wire ++ (packingDefinition e ++ tail)))
    rw [ih (packingDefinition e ++ tail)]
    dsimp
    have hlen : (p.terms ++ q.terms p.expansion).length = 3*n+m := by
      simp [p.terms_length,q.terms_length]
    rw [show readDefinitionsCount 1 (p.terms ++ q.terms p.expansion)
      (packingDefinition e ++ tail) =
      some ((p.terms ++ q.terms p.expansion) ++
        [e.expand p.expansion (q.expansion p.expansion)],tail) from by
        simp only [readDefinitionsCount]
        rw [readDefinition_pack (p.terms ++ q.terms p.expansion)
          p.expansion (q.expansion p.expansion)
          (source_and_saved p q) (saved_after_source p q) e tail hlen]
        rfl]
    simp [PackingProgram.terms,List.append_assoc]

theorem definitionPrelude_parses {n : Nat} (p : Program n) :
    readDefinitionPrelude (3*n+n) (definitionPrelude p) =
      some (p.terms ++ (tracePacking n).terms p.expansion) := by
  let q := tracePacking n
  have hcount : 3*n+n = 3*n+(List.finRange n).length := by
    simp only [List.length_finRange]
  have hs := Program.wire_parses p q.wire
  have ht := PackingProgram.wire_parses p q []
  unfold readDefinitionPrelude definitionPrelude
  rw [hcount]
  rw [readDefinitionsCount_comp (3*n) (List.finRange n).length [] (p.wire ++ q.wire)]
  rw [hs]
  dsimp
  simp only [List.append_nil] at ht
  rw [ht]
  simp [q,p.terms_length,PackingProgram.terms_length,List.length_finRange]

theorem slotOfNat_mod_three (j : Nat) :
    (slotOfNat (j%3)).offset = j%3 := by
  have h := Nat.mod_lt j (by decide : 0<3)
  by_cases h0 : j%3=0
  · simp [slotOfNat,h0,Slot.offset]
  by_cases h1 : j%3=1
  · simp [slotOfNat,h0,h1,Slot.offset]
  have h2 : j%3=2 := by omega
  simp [slotOfNat,h0,h1,h2,Slot.offset]

theorem dictionary_terms {n : Nat} (p : Program n) (j : Fin (3*n+n)) :
    (p.terms ++ (tracePacking n).terms p.expansion)[j.val]? =
      some (dictionary p j) := by
  have hj := j.isLt
  by_cases h : j.val < 3*n
  · have hi : j.val/3 < n := by omega
    have hr : j.val%3 < 3 := Nat.mod_lt _ (by decide)
    have hd : 3*(j.val/3)+(slotOfNat (j.val%3)).offset = j.val := by
      rw [slotOfNat_mod_three]
      omega
    rw [List.getElem?_append_left (by rw [p.terms_length]; exact h)]
    have hs := Program.terms_source p ⟨j.val/3,hi⟩ (slotOfNat (j.val%3))
    rw [hd] at hs
    simpa only [dictionary,dif_pos h] using hs
  · have hi : j.val-3*n < (List.finRange n).length := by
      simp only [List.length_finRange]
      omega
    rw [List.getElem?_append_right (by rw [p.terms_length]; omega)]
    have hs := (tracePacking n).terms_saved p.expansion ⟨j.val-3*n,hi⟩
    rw [show j.val-p.terms.length = j.val-3*n by rw [p.terms_length]]
    simpa only [dictionary,dif_neg h] using hs

theorem dictionary_list {n : Nat} (p : Program n) :
    p.terms ++ (tracePacking n).terms p.expansion =
      List.ofFn (dictionary p) := by
  apply List.ext_getElem?
  intro i
  have hl : (p.terms ++ (tracePacking n).terms p.expansion).length = 3*n+n := by
    simp [p.terms_length,PackingProgram.terms_length,List.length_finRange]
  by_cases hi : i < 3*n+n
  · have hd := dictionary_terms p ⟨i,hi⟩
    simpa [List.getElem?_ofFn,hi] using hd
  · simp [List.getElem?_ofFn,hi,hl]

theorem definitionPrelude_dictionary {n : Nat} (p : Program n) :
    readDefinitionPrelude (3*n+n) (definitionPrelude p) =
      some (List.ofFn (dictionary p)) := by
  rw [definitionPrelude_parses,dictionary_list]

/-- Read the definition prefix of a single combined byte stream. -/
def decodeWhole (r recordCount : Nat) (cs : List Char) :
    Option (List ClosedTerm × ((k : Nat) × Records r k)) := do
  let (env,rest) ← readDefinitionsCount r [] cs
  if env.length != r then none else
  let ⟨k,fs⟩ ← parseFile r recordCount rest
  pure ⟨env,k,fs⟩

theorem definitionPrelude_dictionary_tail {n : Nat} (p : Program n)
    (tail : List Char) :
    readDefinitionsCount (3*n+n) [] (definitionPrelude p ++ tail) =
      some (List.ofFn (dictionary p),tail) := by
  let q := tracePacking n
  have hs := Program.wire_parses p (q.wire ++ tail)
  have ht := PackingProgram.wire_parses p q tail
  change readDefinitionsCount (3*n+n) [] ((p.wire ++ q.wire) ++ tail) = _
  rw [List.append_assoc,readDefinitionsCount_comp,hs]
  dsimp
  have htn : readDefinitionsCount n p.terms (q.wire ++ tail) =
      some (p.terms ++ q.terms p.expansion,tail) := by
    simpa only [List.length_finRange] using ht
  rw [htn,dictionary_list]

theorem decodeWhole_compiled {n k : Nat} (p : Program n)
    (fs : Records (3*n+n) k) :
    decodeWhole (3*n+n) k (definitionPrelude p ++ fs.wire) =
      some ⟨List.ofFn (dictionary p),k,fs⟩ := by
  simp [decodeWhole,definitionPrelude_dictionary_tail,
    List.length_ofFn,parseFile_wire]

theorem compiled_trace_sections {b n : Nat} (g : Grammar b n) :
    ∃ (k : Nat) (fs : Records (3*n+n) k) (last : Fin k),
      k ≤ traceN n ∧ last.val+1=k ∧ fs.get last = trace n ∧
      decodeSections (3*n+n) k (definitionPrelude (compile g)) fs.wire =
        some ⟨List.ofFn (dictionary (compile g)),k,fs⟩ ∧
      fs.valid (dictionary (compile g)) ∧
      (definitionPrelude (compile g) ++ fs.wire).length ≤ fullCharacters b g.mass g.mass := by
  obtain ⟨k,fs,last,hk,hl,hf,hr,hv,hc⟩ := compiled_trace_file_parsed g
  refine ⟨k,fs,last,hk,hl,hf,?_,hv,hc⟩
  simp [decodeSections,definitionPrelude_dictionary,hr]

/-- The complete combined byte stream is accepted and its decoded proof
is valid in the dictionary decoded from the same stream. -/
theorem compiled_trace_whole {b n : Nat} (g : Grammar b n) :
    ∃ (k : Nat) (fs : Records (3*n+n) k) (last : Fin k),
      k ≤ traceN n ∧ last.val+1=k ∧ fs.get last = trace n ∧
      decodeWhole (3*n+n) k
        (definitionPrelude (compile g) ++ fs.wire) =
        some ⟨List.ofFn (dictionary (compile g)),k,fs⟩ ∧
      fs.valid (dictionary (compile g)) ∧
      (definitionPrelude (compile g) ++ fs.wire).length ≤
        fullCharacters b g.mass g.mass := by
  obtain ⟨k,fs,last,hk,hl,hf,_,hv,hc⟩ := compiled_trace_sections g
  exact ⟨k,fs,last,hk,hl,hf,decodeWhole_compiled (compile g) fs,hv,hc⟩
end MAISO11.Wire

import ObstructionBounds

/-!
Concrete binary line-reference encoding and relocation of a plain Hilbert
proof suffix. The past is represented by its expanded formula history.
The source parser, abbreviation expansion, PA axioms, and Bew remain outside
this module. No correctness property of a PA checker is assumed here.
-/

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Obstruction.Suffix

def bits : Nat → List Bool
  | 0 => []
  | n + 1 => decide ((n + 1) % 2 = 1) :: bits ((n + 1) / 2)
termination_by n => n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

theorem bits_length_of_lt (n k : Nat) (h : n < 2 ^ k) :
    (bits n).length ≤ k := by
  induction k generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    subst n
    simp [bits]
  | succ k ih =>
    cases n with
    | zero => simp [bits]
    | succ n =>
      have hd : (n + 1) / 2 < 2 ^ k := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
        simpa [Nat.pow_succ] using h
      have hh := ih ((n + 1) / 2) hd
      simp only [bits, List.length_cons]
      omega

def bitChar (b : Bool) : Char := if b then '1' else '0'

/-- A letter r, unary bit-length header, separator 0, then index+1 in binary. -/
def reference (i : Nat) : List Char :=
  ['r'] ++ List.replicate (bits (i + 1)).length '1' ++ ['0'] ++
    ((bits (i + 1)).reverse.map bitChar)

theorem reference_length (i : Nat) :
    (reference i).length = 2 * (bits (i + 1)).length + 2 := by
  simp [reference]; omega

theorem reference_length_bounded (i limit : Nat) (h : i < limit) :
    (reference i).length ≤ 2 * logBudget limit + 2 := by
  have hp : i + 1 < 2 ^ logBudget limit := by
    have hh : limit + 2 < 2 ^ logBudget limit := Nat.lt_log2_self
    omega
  have hb := bits_length_of_lt (i + 1) (logBudget limit) hp
  rw [reference_length]
  omega

structure Rules (F : Type) where
  imp : F → F → F
  all : Nat → F → F
  isAxiom : F → Prop

inductive Step (F : Type) where
  | ax (A : F)
  | mp (A B : F) (implication antecedent : Nat)
  | gen (varIndex : Nat) (A : F) (premise : Nat)

def Step.conclusion {F : Type} (L : Rules F) : Step F → F
  | .ax A => A
  | .mp _ B _ _ => B
  | .gen x A _ => L.all x A

def Step.refs {F : Type} : Step F → List Nat
  | .ax _ => []
  | .mp _ _ i j => [i, j]
  | .gen _ _ i => [i]

def Step.shift {F : Type} (offset : Nat) : Step F → Step F
  | .ax A => .ax A
  | .mp A B i j => .mp A B (offset + i) (offset + j)
  | .gen x A i => .gen x A (offset + i)

def Step.Checked {F : Type} (L : Rules F) (history : List F) : Step F → Prop
  | .ax A => L.isAxiom A
  | .mp A B i j => history[i]? = some (L.imp A B) ∧ history[j]? = some A
  | .gen _ A i => history[i]? = some A

def ValidTrace {F : Type} (L : Rules F) : List F → List (Step F) → Prop
  | _, [] => True
  | history, s :: ss => s.Checked L history ∧
      ValidTrace L (history ++ [s.conclusion L]) ss

theorem shift_conclusion {F : Type} (L : Rules F) (s : Step F) (n : Nat) :
    (s.shift n).conclusion L = s.conclusion L := by cases s <;> rfl

theorem shifted_lookup {F : Type} (past history : List F) (i : Nat) :
    (past ++ history)[past.length + i]? = history[i]? := by
  rw [List.getElem?_append_right (by omega)]
  rw [Nat.add_sub_cancel_left]

theorem shift_checked {F : Type} (L : Rules F) (past history : List F)
    (s : Step F) (h : s.Checked L history) :
    (s.shift past.length).Checked L (past ++ history) := by
  cases s <;> simp only [Step.Checked, Step.shift, shifted_lookup] at * <;> exact h

/-- Relocating references preserves every axiom, MP and generalization step. -/
theorem shift_valid {F : Type} (L : Rules F) (past history : List F)
    (proof : List (Step F)) (h : ValidTrace L history proof) :
    ValidTrace L (past ++ history) (proof.map (Step.shift past.length)) := by
  induction proof generalizing history with
  | nil => trivial
  | cons s ss ih =>
    rcases h with ⟨hs, hss⟩
    refine ⟨shift_checked L past history s hs, ?_⟩
    simpa [shift_conclusion, List.append_assoc] using ih _ hss

theorem lookup_bound {F : Type} (history : List F) (i : Nat) (A : F)
    (h : history[i]? = some A) : i < history.length := by
  by_cases hi : i < history.length
  · exact hi
  · have hn : history[i]? = none := List.getElem?_eq_none (by omega)
    rw [hn] at h
    contradiction

theorem checked_ref_bound {F : Type} (L : Rules F) (history : List F)
    (s : Step F) (h : s.Checked L history) (i : Nat) (hi : i ∈ s.refs) :
    i < history.length := by
  cases s with
  | ax A => simp [Step.refs] at hi
  | mp A B j k =>
    simp only [Step.refs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases h with ⟨hj, hk⟩
    rcases hi with rfl | rfl
    · exact lookup_bound _ _ _ hj
    · exact lookup_bound _ _ _ hk
  | gen x A j =>
    have he : i = j := by simpa [Step.refs] using hi
    subst i
    exact lookup_bound _ _ _ h

theorem valid_ref_bound {F : Type} (L : Rules F) (history : List F)
    (proof : List (Step F)) (h : ValidTrace L history proof) :
    ∀ s ∈ proof, ∀ i ∈ s.refs, i < history.length + proof.length := by
  induction proof generalizing history with
  | nil => simp
  | cons s ss ih =>
    rcases h with ⟨hs, hss⟩
    intro t ht i hi
    rcases List.mem_cons.mp ht with he | ht
    · subst t
      have hb := checked_ref_bound L history s hs i hi
      simp only [List.length_cons]
      omega
    · have hb := ih _ hss t ht i hi
      simp only [List.length_append, List.length_cons, List.length_nil] at *
      omega

theorem validTrace_append {F : Type} (L : Rules F) (history : List F)
    (xs ys : List (Step F)) :
    ValidTrace L history (xs ++ ys) ↔
      ValidTrace L history xs ∧
        ValidTrace L (history ++ xs.map (Step.conclusion L)) ys := by
  induction xs generalizing history with
  | nil => simp [ValidTrace]
  | cons s ss ih =>
    simp [ValidTrace, ih, List.append_assoc, and_assoc]

/-- The suffix leaves the old proof text intact, relocates a plain Box P
proof, and adds the single MP step deriving P. -/
def appendBoxSuffix {F : Type} (past : List F) (proof : List (Step F))
    (boxP P : F) (reflectionLine boxLine : Nat) : List (Step F) :=
  proof.map (Step.shift past.length) ++
    [.mp boxP P reflectionLine (past.length + boxLine)]

theorem appendBoxSuffix_valid {F : Type} (L : Rules F) (past : List F)
    (proof : List (Step F)) (boxP P : F) (i j : Nat)
    (reflection : past[i]? = some (L.imp boxP P))
    (boxProof : ValidTrace L [] proof)
    (conclusion : (proof.map (Step.conclusion L))[j]? = some boxP) :
    ValidTrace L past (appendBoxSuffix past proof boxP P i j) := by
  unfold appendBoxSuffix
  rw [validTrace_append]
  constructor
  · simpa using shift_valid L past [] proof boxProof
  · have hi := lookup_bound _ _ _ reflection
    have hc : (proof.map (Step.shift past.length)).map (Step.conclusion L) =
        proof.map (Step.conclusion L) := by
      simp [List.map_map, Function.comp_def, shift_conclusion]
    rw [hc]
    refine ⟨?_, trivial⟩
    change _ ∧ _
    constructor
    · rw [List.getElem?_append_left hi]
      exact reflection
    · rw [shifted_lookup]
      exact conclusion

def Step.wire {F : Type} (L : Rules F) (formula : F → List Char) : Step F → List Char
  | .ax A => ['a', ' '] ++ formula A ++ ['\n']
  | .mp _ B i j => ['m', ' '] ++ formula B ++ [' '] ++ reference i ++
      [' '] ++ reference j ++ ['\n']
  | .gen x A i => ['g', ' '] ++ formula (L.all x A) ++ [' '] ++ reference x ++
      [' '] ++ reference i ++ ['\n']

def Step.payload {F : Type} (L : Rules F) (formula : F → List Char) : Step F → Nat
  | .ax A => (formula A).length + 3
  | .mp _ B _ _ => (formula B).length + 5
  | .gen x A _ => (formula (L.all x A)).length + (reference x).length + 5

def Step.mass {F : Type} (L : Rules F) (formula : F → List Char) (s : Step F) : Nat :=
  s.payload L formula + s.refs.length

theorem wire_length {F : Type} (L : Rules F) (formula : F → List Char) (s : Step F) :
    (s.wire L formula).length =
      s.payload L formula + (s.refs.map (fun i => (reference i).length)).sum := by
  cases s <;> simp [Step.wire, Step.payload, Step.refs] <;> omega

theorem shifted_wire_bound {F : Type} (L : Rules F) (formula : F → List Char)
    (s : Step F) (offset limit : Nat) (scope : ∀ i ∈ s.refs, offset + i < limit) :
    ((s.shift offset).wire L formula).length ≤
      s.mass L formula * (2 * logBudget limit + 3) := by
  cases s with
  | ax A =>
    have hf : (formula A).length + 3 ≤
        ((formula A).length + 3) * (2 * logBudget limit + 3) := by
      have h := Nat.mul_le_mul_left ((formula A).length + 3)
        (show 1 ≤ 2 * logBudget limit + 3 by omega)
      simpa using h
    simpa [Step.shift, Step.mass, Step.payload, Step.refs, Step.wire] using hf
  | mp A B i j =>
    have hi := reference_length_bounded (offset + i) limit (scope i (by simp [Step.refs]))
    have hj := reference_length_bounded (offset + j) limit (scope j (by simp [Step.refs]))
    have hf := Nat.mul_le_mul_left ((formula B).length + 5)
      (show 1 ≤ 2 * logBudget limit + 3 by omega)
    simp only [Nat.mul_one] at hf
    simp [Step.shift, Step.wire, Step.mass, Step.payload, Step.refs,
      Nat.add_mul, Nat.mul_add]
    omega
  | gen x A i =>
    have hi := reference_length_bounded (offset + i) limit (scope i (by simp [Step.refs]))
    have hf := Nat.mul_le_mul_left ((formula (L.all x A)).length + (reference x).length + 5)
      (show 1 ≤ 2 * logBudget limit + 3 by omega)
    simp only [Nat.mul_one] at hf
    simp [Step.shift, Step.wire, Step.mass, Step.payload, Step.refs,
      Nat.add_mul, Nat.mul_add]
    omega

def traceWire {F : Type} (L : Rules F) (formula : F → List Char)
    (proof : List (Step F)) : List Char :=
  (proof.map (Step.wire L formula)).flatten

def traceMass {F : Type} (L : Rules F) (formula : F → List Char)
    (proof : List (Step F)) : Nat := (proof.map (Step.mass L formula)).sum

theorem mass_le_wire {F : Type} (L : Rules F) (formula : F → List Char) (s : Step F) :
    s.mass L formula ≤ (s.wire L formula).length := by
  have hr : ∀ i, 2 ≤ (reference i).length := by intro i; rw [reference_length]; omega
  cases s with
  | ax A => simp [Step.mass, Step.payload, Step.refs, Step.wire]
  | mp A B i j =>
    have hi := hr i
    have hj := hr j
    simp [Step.mass, Step.payload, Step.refs, Step.wire]
    omega
  | gen x A i =>
    have hi := hr i
    simp [Step.mass, Step.payload, Step.refs, Step.wire]
    omega

theorem traceMass_le_wire {F : Type} (L : Rules F) (formula : F → List Char)
    (proof : List (Step F)) : traceMass L formula proof ≤ (traceWire L formula proof).length := by
  induction proof with
  | nil => simp [traceMass, traceWire]
  | cons s ss ih =>
    simpa [traceMass, traceWire] using Nat.add_le_add (mass_le_wire L formula s) ih

theorem length_le_traceMass {F : Type} (L : Rules F) (formula : F → List Char)
    (proof : List (Step F)) : proof.length ≤ traceMass L formula proof := by
  induction proof with
  | nil => simp [traceMass]
  | cons s ss ih =>
    have hs : 1 ≤ s.mass L formula := by
      cases s <;> simp [Step.mass, Step.payload, Step.refs] <;> omega
    simpa [traceMass, Nat.add_comm] using Nat.add_le_add hs ih

/-- Exact serialized suffix cost; every line reference and record header is charged. -/
theorem shifted_trace_characters {F : Type} (L : Rules F) (formula : F → List Char)
    (proof : List (Step F)) (offset limit : Nat)
    (scope : ∀ s ∈ proof, ∀ i ∈ s.refs, offset + i < limit) :
    (traceWire L formula (proof.map (Step.shift offset))).length ≤
      traceMass L formula proof * (2 * logBudget limit + 3) := by
  induction proof with
  | nil => simp [traceWire, traceMass]
  | cons s ss ih =>
    have hs := shifted_wire_bound L formula s offset limit (scope s (by simp))
    have ht := ih (fun t ht i hi => scope t (by simp [ht]) i hi)
    simpa [traceWire, traceMass, Nat.add_mul] using Nat.add_le_add hs ht

/-- Character bound for the complete constructed suffix, including final MP. -/
theorem appendBoxSuffix_characters {F : Type} (L : Rules F) (formula : F → List Char)
    (past : List F) (proof : List (Step F)) (boxP P : F) (i j : Nat)
    (reflection : past[i]? = some (L.imp boxP P))
    (boxProof : ValidTrace L [] proof)
    (conclusion : (proof.map (Step.conclusion L))[j]? = some boxP) :
    (traceWire L formula (appendBoxSuffix past proof boxP P i j)).length ≤
      (traceMass L formula proof + (formula P).length + 7) *
        (2 * logBudget (past.length + proof.length + 1) + 3) := by
  let limit := past.length + proof.length + 1
  have hp := shifted_trace_characters L formula proof past.length limit (by
    intro s hs k hk
    have h := valid_ref_bound L [] proof boxProof s hs k hk
    simp only [List.length_nil, Nat.zero_add] at h
    dsimp [limit]
    omega)
  have hi := lookup_bound _ _ _ reflection
  have hj := lookup_bound _ _ _ conclusion
  simp only [List.length_map] at hj
  have hm := shifted_wire_bound L formula (.mp boxP P i (past.length + j)) 0 limit (by
    intro k hk
    simp only [Step.refs, List.mem_cons, List.not_mem_nil, or_false] at hk
    dsimp [limit]
    omega)
  simp only [Step.shift, Nat.zero_add, Step.mass, Step.payload, Step.refs,
    List.length_cons, List.length_nil] at hm
  have hh := Nat.add_le_add hp hm
  simpa [appendBoxSuffix, traceWire, Nat.add_mul, limit, Nat.add_assoc] using hh

/-- The complete relocation/MP bound in terms of the original plain Box P
file's character count b and an arbitrary prefix character budget r.
Only the link from parsed PA files to this structured model is external. -/
theorem appendBoxSuffix_normalized {F : Type} (L : Rules F) (formula : F → List Char)
    (past : List F) (proof : List (Step F)) (boxP P : F) (i j r : Nat)
    (prefixBudget : past.length ≤ r)
    (reflection : past[i]? = some (L.imp boxP P))
    (boxProof : ValidTrace L [] proof)
    (conclusion : (proof.map (Step.conclusion L))[j]? = some boxP) :
    (traceWire L formula (appendBoxSuffix past proof boxP P i j)).length ≤
      assemblyCoeff (traceWire L formula proof).length (formula P).length * logBudget r := by
  have hc := appendBoxSuffix_characters L formula past proof boxP P i j
    reflection boxProof conclusion
  have hm := traceMass_le_wire L formula proof
  have hn := Nat.le_trans (length_le_traceMass L formula proof) hm
  apply normalize_suffix_cost _ r _ _ past.length proof.length prefixBudget hn
  exact Nat.le_trans hc (Nat.mul_le_mul_right _ (by omega))

end MAISO11.Obstruction.Suffix

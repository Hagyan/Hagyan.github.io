import ChosenSystemSerialization

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.ChosenSystem
open MAISO11.Quotation

/-- A stream of output fragments and fresh definitions. A definition can occur
after earlier output; its body can refer only to definitions already in scope.
Output fragments can refer to the definitions in scope at their position. -/
inductive InterleavedProgram (b : Nat) : Nat → Type where
  | nil : InterleavedProgram b 0
  | define {n : Nat} (prior : InterleavedProgram b n)
      (rhs : Fragment b n) : InterleavedProgram b (n + 1)
  | emit {n : Nat} (prior : InterleavedProgram b n)
      (fragment : Fragment b n) : InterleavedProgram b n

/-- Lift a fragment into the next scope without changing its references. -/
def weakenAtom {b n : Nat} : Atom b n → Atom b (n + 1)
  | .char c => .char c
  | .use i => .use i.castSucc

def weakenFragment {b n : Nat} : Fragment b n → Fragment b (n + 1)
  | [] => []
  | atom :: rest => weakenAtom atom :: weakenFragment rest

@[simp] theorem weakenFragment_length {b n : Nat} (fragment : Fragment b n) :
    (weakenFragment fragment).length = fragment.length := by
  induction fragment with
  | nil => rfl
  | cons atom rest ih => simp [weakenFragment, ih]

theorem grammar_snoc_words_castSucc {b n : Nat} (g : Grammar b n)
    (rhs : Fragment b n) (i : Fin n) :
    (Grammar.snoc g rhs).words i.castSucc = g.words i := by
  simp [Grammar.words]

theorem expandFragment_weaken {b n : Nat} (g : Grammar b n)
    (rhs fragment : Fragment b n) :
    expandFragment (Grammar.snoc g rhs).words (weakenFragment fragment) =
      expandFragment g.words fragment := by
  induction fragment with
  | nil => rfl
  | cons atom rest ih =>
      cases atom with
      | char c =>
          simp only [weakenFragment, weakenAtom, Atom.expand,
            expandFragment]
          rw [ih]
      | use i =>
          simp only [weakenFragment, weakenAtom, Atom.expand,
            expandFragment, grammar_snoc_words_castSucc]
          rw [ih]

@[simp] theorem expandFragment_append {b n : Nat} (env : Fin n → Word b)
    (left right : Fragment b n) :
    expandFragment env (left ++ right) =
      expandFragment env left ++ expandFragment env right := by
  induction left with
  | nil => rfl
  | cons atom rest ih =>
      simp [expandFragment, ih, List.append_assoc]

/-- Compile a sequential declaration/output stream into the equivalent
topologically ordered grammar and one concatenated root fragment. -/
def interleavedGrammar {b : Nat} : {n : Nat} →
    InterleavedProgram b n → Grammar b n
  | _, .nil => .nil
  | _, .define prior rhs => .snoc (interleavedGrammar prior) rhs
  | _, .emit prior _ => interleavedGrammar prior

def interleavedRoot {b : Nat} : {n : Nat} →
    InterleavedProgram b n → Fragment b n
  | _, .nil => []
  | _, .define prior _ => weakenFragment (interleavedRoot prior)
  | _, .emit prior fragment => interleavedRoot prior ++ fragment

/-- Count fragment atoms and one unit for every directive. -/
def interleavedCost {b : Nat} : {n : Nat} →
    InterleavedProgram b n → Nat
  | _, .nil => 0
  | _, .define prior rhs => interleavedCost prior + rhs.length + 1
  | _, .emit prior fragment => interleavedCost prior + fragment.length + 1

theorem interleavedGrammar_mass_le_cost {b n : Nat}
    (program : InterleavedProgram b n) :
    (interleavedGrammar program).mass ≤ interleavedCost program := by
  induction program with
  | nil => simp [interleavedGrammar, interleavedCost, Grammar.mass]
  | @define n prior rhs ih =>
      simpa [interleavedGrammar, interleavedCost, Grammar.mass] using
        Nat.add_le_add_right ih (rhs.length + 1)
  | @emit n prior fragment ih =>
      simp only [interleavedGrammar, interleavedCost]
      omega

theorem interleavedRoot_length_le_cost {b n : Nat}
    (program : InterleavedProgram b n) :
    (interleavedRoot program).length ≤ interleavedCost program := by
  induction program with
  | nil => simp [interleavedRoot, interleavedCost]
  | @define n prior rhs ih =>
      simp only [interleavedRoot, interleavedCost, weakenFragment_length]
      omega
  | @emit n prior fragment ih =>
      simp only [interleavedRoot, interleavedCost, List.length_append]
      omega

/-- The expanded text emitted by a stream, expanding each fragment in the
definition environment that existed when that fragment was emitted. -/
def interleavedExpansion {b : Nat} : {n : Nat} →
    InterleavedProgram b n → Word b
  | _, .nil => []
  | _, .define prior _ => interleavedExpansion prior
  | _, .emit prior fragment =>
      interleavedExpansion prior ++
        expandFragment (interleavedGrammar prior).words fragment

theorem interleaved_compile_correct {b n : Nat}
    (program : InterleavedProgram b n) :
    expandFragment (interleavedGrammar program).words
      (interleavedRoot program) = interleavedExpansion program := by
  induction program with
  | nil => rfl
  | @define n prior rhs ih =>
      simp only [interleavedGrammar, interleavedRoot, interleavedExpansion]
      rw [expandFragment_weaken]
      exact ih
  | @emit n prior fragment ih =>
      simp only [interleavedGrammar, interleavedRoot, interleavedExpansion]
      rw [expandFragment_append, ih]

/-- Even when definitions are interleaved with output records, total expanded
output is bounded by `2^(2*m)` when all fragment atoms and directives fit in
the written budget `m`. -/
theorem interleaved_expansion_length_le_two_pow_two_mul {b n : Nat}
    (program : InterleavedProgram b n) (m : Nat)
    (hcost : interleavedCost program ≤ m) :
    (interleavedExpansion program).length ≤ 2^(2*m) := by
  rw [← interleaved_compile_correct program]
  apply expandedRoot_length_le_two_pow_two_mul
  · exact Nat.le_trans (interleavedGrammar_mass_le_cost program) hcost
  · exact Nat.le_trans (interleavedRoot_length_le_cost program) hcost

def serializeInterleavedProgram {b : Nat}
    (literalTag referenceTag endTag start zero one emitTag : Fin b)
    (identifiers : Nat → Word b) (definitionHeader assignment : Word b) :
    {n : Nat} → InterleavedProgram b n → Word b
  | 0, .nil => []
  | n + 1, .define prior rhs =>
      serializeInterleavedProgram literalTag referenceTag endTag start zero one
        emitTag identifiers definitionHeader assignment prior ++
      serializeDefinition literalTag referenceTag identifiers definitionHeader
        assignment endTag n rhs
  | _, .emit prior fragment =>
      serializeInterleavedProgram literalTag referenceTag endTag start zero one
        emitTag identifiers definitionHeader assignment prior ++
      (emitTag :: serializeFragment literalTag referenceTag identifiers fragment) ++
      [endTag]

theorem serializeInterleavedProgram_length_ge_cost {b : Nat}
    (literalTag referenceTag endTag start zero one emitTag : Fin b)
    (identifiers : Nat → Word b) (hnonempty : ∀ i, identifiers i ≠ [])
    (definitionHeader assignment : Word b) (hheader : 1 ≤ definitionHeader.length)
    {n : Nat} (program : InterleavedProgram b n) :
    interleavedCost program ≤
      (serializeInterleavedProgram literalTag referenceTag endTag start zero one
        emitTag identifiers definitionHeader assignment program).length := by
  induction program with
  | nil => simp [interleavedCost, serializeInterleavedProgram]
  | @define n prior rhs ih =>
      simp only [interleavedCost, serializeInterleavedProgram,
        List.length_append]
      have hrecord := serializeDefinition_length_ge literalTag referenceTag
        identifiers hnonempty definitionHeader assignment endTag n rhs hheader
      omega
  | @emit n prior fragment ih =>
      simp only [interleavedCost, serializeInterleavedProgram,
        List.length_append, List.length_cons, List.length_nil]
      have hfragment := serializeFragment_length_ge literalTag referenceTag
        identifiers hnonempty fragment
      omega

theorem interleaved_expansion_length_le_serialized_budget {b n : Nat}
    (literalTag referenceTag endTag start zero one emitTag : Fin b)
    (identifiers : Nat → Word b) (hnonempty : ∀ i, identifiers i ≠ [])
    (definitionHeader assignment : Word b) (hheader : 1 ≤ definitionHeader.length)
    (program : InterleavedProgram b n) (m : Nat)
    (hwritten :
      (serializeInterleavedProgram literalTag referenceTag endTag start zero one
        emitTag identifiers definitionHeader assignment program).length ≤ m) :
    (interleavedExpansion program).length ≤ 2^(2*m) := by
  apply interleaved_expansion_length_le_two_pow_two_mul program m
  exact Nat.le_trans
    (serializeInterleavedProgram_length_ge_cost literalTag referenceTag endTag
      start zero one emitTag identifiers hnonempty definitionHeader assignment
      hheader program)
    hwritten

#print axioms interleaved_compile_correct
#print axioms interleaved_expansion_length_le_two_pow_two_mul
#print axioms serializeInterleavedProgram_length_ge_cost
#print axioms interleaved_expansion_length_le_serialized_budget

end MAISO11.ChosenSystem

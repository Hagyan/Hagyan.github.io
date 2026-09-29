import CompactChecker
set_option autoImplicit false
set_option warningAsError true
namespace MAISO11.Quotation

def ClosedTerm.treeNodes : ClosedTerm → Nat
  | .zero => 1
  | .bit0 t | .bit1 t => 1+t.treeNodes
  | .add s t | .mul s t => 1+s.treeNodes+t.treeNodes

def doubledTree : Nat → ClosedTerm
  | 0 => .zero
  | n+1 => .add (doubledTree n) (doubledTree n)

def doublingProgram : (n : Nat) → PackingProgram 0 (n+1)
  | 0 => .snoc .nil (.num 0)
  | n+1 => .snoc (doublingProgram n)
      (.add (.saved (Fin.last n)) (.saved (Fin.last n)))

theorem doubledTree_nodes (n : Nat) :
    (doubledTree n).treeNodes+1 = 2^(n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [doubledTree,ClosedTerm.treeNodes,Nat.pow_succ]
    have hp : 2^(n+1) = 2^n*2 := Nat.pow_succ 2 n
    omega

theorem doublingProgram_weight (n : Nat) : (doublingProgram n).weight = 1+3*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [doublingProgram,PackingProgram.weight,PackExpr.weight,ih]
    omega

theorem doublingProgram_expansion (n : Nat) :
    (doublingProgram n).expansion Fin.elim0 (Fin.last n) = doubledTree n := by
  induction n with
  | zero => simp only [doublingProgram,PackingProgram.expansion,Fin.lastCases_last,
      PackExpr.expand,numeralTerm,bits,numeralTermBits,doubledTree]
  | succ n ih =>
    simp [doublingProgram,PackingProgram.expansion,PackExpr.expand,doubledTree,ih]

theorem doublingProgram_characters (n : Nat) :
    (doublingProgram n).wire.length ≤ (2*n+22)*(4*n+2) := by
  have h := (doublingProgram n).wire_length
  rw [doublingProgram_weight] at h
  have h₁ : 6*0+2*(n+1)+20 = 2*n+22 := by omega
  have h₂ : 1+3*n+(n+1) = 4*n+2 := by omega
  simpa only [h₁,h₂] using h

theorem doublingProgram_parsed (n : Nat) :
    MAISO11.Wire.readDefinitionPrelude (n+1) (doublingProgram n).wire =
      some ((doublingProgram n).terms Fin.elim0) := by
  have h := MAISO11.Wire.PackingProgram.wire_parses Program.nil (doublingProgram n) []
  simp only [List.append_nil,Program.terms,List.nil_append] at h
  unfold MAISO11.Wire.readDefinitionPrelude
  rw [h]
  simp [PackingProgram.terms_length,Program.expansion]

/-- Quadratic written-size bound and exponential expanded tree size, for files
accepted by the actual definition reader. This is not a shortest-proof bound. -/
theorem parsed_expansion_barrier (n : Nat) :
    ∃ env : List ClosedTerm,
      MAISO11.Wire.readDefinitionPrelude (n+1) (doublingProgram n).wire = some env ∧
      (doublingProgram n).wire.length ≤ (2*n+22)*(4*n+2) ∧
      ∃ t, env[n]? = some t ∧ t.treeNodes+1 = 2^(n+1) := by
  refine ⟨(doublingProgram n).terms Fin.elim0,doublingProgram_parsed n,
    doublingProgram_characters n,doubledTree n,?_,doubledTree_nodes n⟩
  have h := PackingProgram.terms_saved Fin.elim0 (doublingProgram n) (Fin.last n)
  simpa only [Fin.val_last,doublingProgram_expansion] using h
end MAISO11.Quotation

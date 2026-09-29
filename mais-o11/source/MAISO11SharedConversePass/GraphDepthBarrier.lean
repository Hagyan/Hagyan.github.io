import GraphSubterms
set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Shared
open MAISO11.Quotation

/-- Longest constructor path through a closed term. -/
def termDepth : ClosedTerm → Nat
  | .zero => 1
  | .bit0 t | .bit1 t => termDepth t + 1
  | .add s t | .mul s t => max (termDepth s) (termDepth t) + 1

/-- Every node in a backward-reference constructor DAG of size `n` has
constructor depth at most `n`. -/
theorem Graph.depth_le_size {n : Nat} (g : Graph n) (i : Fin n) :
    termDepth (g.expand i) ≤ n := by
  induction g with
  | nil => exact Fin.elim0 i
  | @snoc n g a ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have ha : termDepth (a.expand g.expand) ≤ n + 1 := by
        cases a with
        | zero => simp [Node.expand,termDepth]
        | bit0 j => simpa [Node.expand,termDepth] using Nat.add_le_add_right (ih j) 1
        | bit1 j => simpa [Node.expand,termDepth] using Nat.add_le_add_right (ih j) 1
        | add j k =>
          simp only [Node.expand,termDepth]
          have hj := ih j
          have hk := ih k
          omega
        | mul j k =>
          simp only [Node.expand,termDepth]
          have hj := ih j
          have hk := ih k
          omega
      simpa only [Graph.expand,Fin.lastCases_last] using ha
    · have hj := ih j
      have hj' : termDepth (g.expand j) ≤ n + 1 := Nat.le_trans hj (Nat.le_succ n)
      simpa only [Graph.expand,Fin.lastCases_castSucc] using hj'

/-- A unary spine of length `m` has depth `m+1`, even though its printed
string may have a tiny context-grammar description. -/
def unarySpine : Nat → ClosedTerm
  | 0 => .zero
  | m+1 => .bit0 (unarySpine m)

theorem unarySpine_depth (m : Nat) : termDepth (unarySpine m) = m+1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [unarySpine,termDepth,ih,Nat.succ_eq_add_one]

/-- No ordinary constructor DAG with fewer than `m+1` nodes can represent
the unary spine of length `m`, irrespective of sharing. -/
theorem unarySpine_graph_lower_bound {n m : Nat}
    (g : Graph n) (i : Fin n) (h : g.expand i = unarySpine m) :
    m+1 ≤ n := by
  have hd := g.depth_le_size i
  rw [h,unarySpine_depth] at hd
  exact hd

#print axioms Graph.depth_le_size
#print axioms unarySpine_graph_lower_bound
end MAISO11.Shared

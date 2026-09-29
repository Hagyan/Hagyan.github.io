import DagEquality
set_option autoImplicit false
set_option warningAsError true
open MAISO11.Shared

/-- Only the finite graph and equality table are evaluated here. -/
def runCase (n : Nat) : IO Unit := do
  let table := (duplicateRoot n).table
  let equal := table[(Fin.last (n+1)).castSucc][Fin.last (n+2)]
  let unequal := table[(⟨0,by omega⟩ : Fin (n+3))][Fin.last (n+2)]
  if equal && !unequal then
    IO.println s!"PASS n={n}: {n+3} graph nodes, {comparisonCalls (n+3)} scheduled comparisons; expanded root has {2^(n+2)-1} tree nodes"
  else throw (IO.userError "shared comparison failed")

#eval runCase 0
#eval runCase 4
#eval runCase 20
#eval runCase 60
#print axioms MAISO11.Shared.Graph.table_iff
#print axioms MAISO11.Shared.comparisonCalls_exact
#print axioms MAISO11.Shared.tableWrites_cubic
#print axioms MAISO11.Shared.doublingGraph_matches_definitions
#print axioms MAISO11.Shared.duplicateRoot_expanded_nodes

import CompressionBarrier
set_option autoImplicit false
set_option warningAsError true
open MAISO11.Quotation MAISO11.Wire

#eval ([0,1,4,8,12] : List Nat).map fun n =>
  (n, (doublingProgram n).wire.length,
    (readDefinitionPrelude (n+1) (doublingProgram n).wire).bind
      (fun env => env[n]?.map ClosedTerm.treeNodes))

#print axioms MAISO11.Quotation.doubledTree_nodes
#print axioms MAISO11.Quotation.parsed_expansion_barrier

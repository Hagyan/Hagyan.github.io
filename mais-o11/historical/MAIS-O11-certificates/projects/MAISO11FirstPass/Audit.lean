import FirstPass

set_option warningAsError true

/- These declarations show the hypotheses that still need concrete instances. -/
#print MAISO11.FiniteDiagonal
#print MAISO11.LobConditions
#print MAISO11.SeparationHypotheses

/- This displays the precise conditional conclusion, not just a theorem name. -/
#check MAISO11.SeparationHypotheses.conditional_main

/- No project-specific axioms or unfinished-proof axioms should appear here. -/
#print axioms MAISO11.finite_diagonal_lower_bound
#print axioms MAISO11.lob_rule
#print axioms MAISO11.SeparationHypotheses.direct_lower_bound
#print axioms MAISO11.SeparationHypotheses.witness_large_enough
#print axioms MAISO11.SeparationHypotheses.conditional_main

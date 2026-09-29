import CompactEquality
set_option autoImplicit false
set_option warningAsError true
open MAISO11.Shared MAISO11.Wire MAISO11.Quotation

private def expect (name : String) (ok : Bool) : IO Unit :=
  if ok then IO.println ("PASS: " ++ name)
  else throw (IO.userError ("FAIL: " ++ name))

private def bigGraph := duplicateRoot 60
private def bigEnv := bigGraph.expand
private def equalsRoot : CFormula 63 0 :=
  .eq (.ref (Fin.last 61).castSucc) (.ref (Fin.last 62))
private def unequalRoot : CFormula 63 0 :=
  .eq (.ref ⟨0,by decide⟩) (.ref (Fin.last 62))
private def oracle := graphReferenceEqual bigGraph bigEnv

-- The compared roots denote a term with more than 4.6 quintillion nodes.
-- These evaluations use only a 63-node graph and its equality table.
#eval expect "MP, shared equal roots"
  (mpEqual oracle equalsRoot (.imp equalsRoot equalsRoot) equalsRoot)
#eval expect "MP, reject an unequal root"
  (!(mpEqual oracle equalsRoot (.imp unequalRoot equalsRoot) equalsRoot))

example : formulaEqual oracle equalsRoot equalsRoot = true := by
  exact (formulaEqual_iff bigEnv oracle
    (graphReferenceEqual_correct bigGraph bigEnv rfl) _ _).mpr rfl

#print axioms MAISO11.Wire.formulaEqual_iff
#print axioms MAISO11.Wire.mpEqual_iff
#print axioms MAISO11.Wire.Records.checkWithTermEqual_iff
#print axioms MAISO11.Wire.Records.checkWithTermEqual_derivable
#print axioms MAISO11.Wire.graphReferenceEqual_correct

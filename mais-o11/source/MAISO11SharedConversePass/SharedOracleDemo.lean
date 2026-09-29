import SharedOracle
import SharedPreludeDemo
import SharedConverse
import SharedConverseDemo
import GraphFileChecker
set_option autoImplicit false
set_option warningAsError true
open MAISO11.Shared MAISO11.Wire MAISO11.Quotation MAISO11.Arithmetic

private def d61 : CompiledDefs 61 := compileDefs (doublingDefs 60)
private def root61 : Fin 61 := ⟨60,by decide⟩
private def previous61 : Fin 61 := ⟨59,by decide⟩

private def rootVsItsDefinition : Bool :=
  compiledTermEqual d61.graph d61.refs 0 (.ref root61)
    (.add (.ref previous61) (.ref previous61))

private def quantifiedRootVsItsDefinition : Bool :=
  compiledTermEqual d61.graph d61.refs 1
    (.add (.var 0) (.ref root61))
    (.add (.var 0) (.add (.ref previous61) (.ref previous61)))

private def bigAtom : CFormula 61 0 := .eq (.ref root61) .zero
private def otherAtom : CFormula 61 0 := .eq (.ref previous61) .zero
private def bigContrapAxiom : CFormula 61 0 :=
  .imp (.imp bigAtom (.neg otherAtom)) (.imp otherAtom (.neg bigAtom))
private def bigConjAxiom : CFormula 61 0 :=
  .imp bigAtom (.imp otherAtom (CFormula.conj bigAtom otherAtom))
private def bigReflInstAxiom : CFormula 61 0 :=
  .imp (.all (.eq (.var 0) (.var 0)))
    (.eq (.ref root61) (.add (.ref previous61) (.ref previous61)))

private def bigContrapAccepted : Bool :=
  compiledAxiomCheck d61.graph d61.refs (doublingDefs 60).expand bigContrapAxiom

private def oneBigAxiomRecord : Records 61 1 :=
  Records.snoc Records.nil (.axiom bigContrapAxiom)

private def bigAxiomRecordAccepted : Bool :=
  checkRecordsCompiledTerms d61.graph d61.refs oneBigAxiomRecord

private def oneBigConjRecord : Records 61 1 :=
  Records.snoc Records.nil (.axiom bigConjAxiom)

private def bigConjRecordAccepted : Bool :=
  checkRecordsCompiledTerms d61.graph d61.refs oneBigConjRecord

private def oneBigReflInstRecord : Records 61 1 :=
  Records.snoc Records.nil (.axiom bigReflInstAxiom)

private def bigReflInstRecordAccepted : Bool :=
  checkRecordsCompiledTerms d61.graph d61.refs oneBigReflInstRecord

private def expect (name : String) (ok : Bool) : IO Unit :=
  if ok then IO.println ("PASS: " ++ name)
  else throw (IO.userError ("FAIL: " ++ name))

-- The final root has over 2^61 expanded syntax nodes. The executable
-- comparison compiles only the 61 written definitions and consults a graph table.
#eval expect "compiled root equals its written addition definition"
  rootVsItsDefinition
#eval expect "compiled comparison works beneath a quantifier binder"
  quantifiedRootVsItsDefinition
#eval expect "graph shortcut accepts a propositional axiom with huge abbreviations"
  bigContrapAccepted
#eval expect "compiled record checker accepts the huge-abbreviation axiom"
  bigAxiomRecordAccepted
#eval expect "compiled record checker accepts the huge-abbreviation conjunction axiom"
  bigConjRecordAccepted
#eval expect "graph shortcut accepts reflexivity instantiated with equivalent abbreviations"
  bigReflInstRecordAccepted
#eval expect "compiled graph retains one node per non-reference constructor"
  (d61.size == 61)
#eval expect "compact graph checker accepts the complete 61-definition file"
  (checkWholeSharedGraph 61 1
    ((doublingProgram 60).wire ++ reflexivityRecords.wire))

theorem doublingDefs_prev (n : Nat) :
    (doublingDefs (n+1)).expand (Fin.castSucc (Fin.last n)) = doubledTree n := by
  simp only [doublingDefs,CDefs.expand,Fin.lastCases_castSucc]
  exact doublingDefs_expand n

theorem rootVsItsDefinition_correct : rootVsItsDefinition = true := by
  apply (compiledTermEqual_correct d61.graph d61.refs 0
    (.ref root61) (.add (.ref previous61) (.ref previous61))).mpr
  have hroot : (d61.graph.expand (d61.refs root61)) =
      (doublingDefs 60).expand root61 := compileDefs_refines _ _
  have hprev : (d61.graph.expand (d61.refs previous61)) =
      (doublingDefs 60).expand previous61 := compileDefs_refines _ _
  simp only [CTerm.expand]
  rw [hroot,hprev]
  have hr0 : root61 = Fin.last 60 := by apply Fin.ext; rfl
  have hp0 : previous61 = Fin.castSucc (Fin.last 59) := by apply Fin.ext; rfl
  have hr : (doublingDefs 60).expand root61 = doubledTree 60 := by
    rw [hr0]
    exact doublingDefs_expand 60
  have hp : (doublingDefs 60).expand previous61 = doubledTree 59 := by
    rw [hp0]
    exact doublingDefs_prev 59
  rw [hr,hp]
  rfl

theorem quantifiedRootVsItsDefinition_correct :
    quantifiedRootVsItsDefinition = true := by
  apply (compiledTermEqual_correct d61.graph d61.refs 1
    (.add (.var 0) (.ref root61))
    (.add (.var 0) (.add (.ref previous61) (.ref previous61)))).mpr
  have hterm0 := (compiledTermEqual_correct d61.graph d61.refs 0
    (.ref root61) (.add (.ref previous61) (.ref previous61))).mp
      rootVsItsDefinition_correct
  have hclosed :
      CTerm.close (d61.graph.expand ∘ d61.refs) (.ref root61) =
        CTerm.close (d61.graph.expand ∘ d61.refs)
          (.add (.ref previous61) (.ref previous61)) := by
    apply ofClosed_injective 0
    calc
      Term.ofClosed (CTerm.close (d61.graph.expand ∘ d61.refs) (.ref root61)) =
          CTerm.expand (d61.graph.expand ∘ d61.refs) (.ref root61) :=
        CTerm.close_expand _ _
      _ = CTerm.expand (d61.graph.expand ∘ d61.refs)
          (.add (.ref previous61) (.ref previous61)) := hterm0
      _ = Term.ofClosed (CTerm.close (d61.graph.expand ∘ d61.refs)
          (.add (.ref previous61) (.ref previous61))) :=
        (CTerm.close_expand _ _).symm
  have hLift :
      (Term.ofClosed (d61.graph.expand (d61.refs root61)) : Term 1) =
        (Term.ofClosed (d61.graph.expand (d61.refs previous61))).add
          (Term.ofClosed (d61.graph.expand (d61.refs previous61))) := by
    have h := congrArg (fun a : ClosedTerm => (Term.ofClosed a : Term 1)) hclosed
    simpa [CTerm.close,Term.ofClosed] using h
  simp only [CTerm.expand]
  exact congrArg (Term.add (.var 0)) hLift

theorem bigContrapAccepted_correct : bigContrapAccepted = true := by
  have hcmp : compiledFormulaEqual d61.graph d61.refs
      (.imp otherAtom (.neg bigAtom)) (.imp otherAtom (.neg bigAtom)) = true :=
    (compiledFormulaEqual_correct d61.graph d61.refs _ _).mpr rfl
  have hs : compiledContrapShortcut d61.graph d61.refs bigContrapAxiom = true := by
    simpa [compiledContrapShortcut,bigContrapAxiom,bigAtom,otherAtom] using hcmp
  have hshort : compiledAxiomShortcut d61.graph d61.refs bigContrapAxiom = true := by
    simp [compiledAxiomShortcut,hs]
  simp [bigContrapAccepted,compiledAxiomCheck,hshort]

theorem bigAxiomRecordAccepted_correct : bigAxiomRecordAccepted = true := by
  have hcmp : compiledFormulaEqual d61.graph d61.refs
      (.imp otherAtom (.neg bigAtom)) (.imp otherAtom (.neg bigAtom)) = true :=
    (compiledFormulaEqual_correct d61.graph d61.refs _ _).mpr rfl
  have hs : compiledContrapShortcut d61.graph d61.refs bigContrapAxiom = true := by
    simpa [compiledContrapShortcut,bigContrapAxiom,bigAtom,otherAtom] using hcmp
  have hshort : compiledAxiomShortcut d61.graph d61.refs bigContrapAxiom = true := by
    simp [compiledAxiomShortcut,hs]
  simp [bigAxiomRecordAccepted,oneBigAxiomRecord,checkRecordsCompiledTerms,
    checkRecordsCompiled,checkRecordCompiled,compiledAxiomCheck,hshort]

theorem bigConjRecordAccepted_correct : bigConjRecordAccepted = true := by
  have hcmp : compiledFormulaEqual d61.graph d61.refs
      (CFormula.conj bigAtom otherAtom) (CFormula.conj bigAtom otherAtom) = true :=
    (compiledFormulaEqual_correct d61.graph d61.refs _ _).mpr rfl
  have hs : compiledConjShortcut d61.graph d61.refs bigConjAxiom = true := by
    simpa [compiledConjShortcut,bigConjAxiom,bigAtom,otherAtom] using hcmp
  have hshort : compiledAxiomShortcut d61.graph d61.refs bigConjAxiom = true := by
    simp [compiledAxiomShortcut,hs]
  simp [bigConjRecordAccepted,oneBigConjRecord,checkRecordsCompiledTerms,
    checkRecordsCompiled,checkRecordCompiled,compiledAxiomCheck,hshort]

theorem bigReflInstRecordAccepted_correct : bigReflInstRecordAccepted = true := by
  have hs : compiledReflInstShortcut d61.graph d61.refs bigReflInstAxiom = true := by
    simpa [compiledReflInstShortcut,bigReflInstAxiom,rootVsItsDefinition]
      using rootVsItsDefinition_correct
  have hshort : compiledAxiomShortcut d61.graph d61.refs bigReflInstAxiom = true := by
    simp [compiledAxiomShortcut,hs]
  simp [bigReflInstRecordAccepted,oneBigReflInstRecord,checkRecordsCompiledTerms,
    checkRecordsCompiled,checkRecordCompiled,compiledAxiomCheck,hshort]

/- The hidden instantiation witness is `E 0`. It occurs inside the expansion
of `u_0 := (E 0)+0` and is absent from the two obvious compact candidates:
zero and the entire `u_0` root. -/
private def hiddenDict : Fin 1 → ClosedTerm :=
  fun _ => .add (.bit1 .zero) .zero

private def hiddenBody : Formula 1 :=
  .eq (.add (.var 0) .zero) (.add (.var 0) .zero)

private def hiddenConclusion : CFormula 1 0 :=
  .eq (.ref 0) (.ref 0)

theorem hiddenWitness_is_instance :
    hiddenBody.instantiate (.bit1 .zero) = hiddenConclusion.expand hiddenDict := by
  decide

private def hiddenAxiom : CFormula 1 0 :=
  .imp (.all (.eq (.add (.var 0) .zero) (.add (.var 0) .zero)))
    hiddenConclusion

theorem hiddenCandidate_is_axiom : IsAxiom (hiddenAxiom.expand hiddenDict) := by
  change IsAxiom (.imp (.all hiddenBody) (hiddenConclusion.expand hiddenDict))
  rw [← hiddenWitness_is_instance]
  exact IsAxiom.inst hiddenBody (.bit1 .zero)

theorem hiddenWitness_not_in_obvious_candidates :
    ∀ u ∈ ([Term.zero, Term.ofClosed (hiddenDict 0)] : List (Term 0)),
      hiddenBody.instantiate u ≠ hiddenConclusion.expand hiddenDict := by
  intro u hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with h | h
  · subst u; decide
  · subst u; decide

#print axioms sharedClosedEqual_correct
#print axioms MAISO11.Shared.sharedOpenEqual_correct
#print axioms compiledTermEqual_correct
#print axioms compiledFormulaEqual_correct
#print axioms checkRecordsCompiledTerms_iff
#print axioms MAISO11.Shared.checkWholeSharedGraph_eq_old_accept
#print axioms MAISO11.Shared.checkWholeSharedGraph_sound
#print axioms rootVsItsDefinition_correct
#print axioms quantifiedRootVsItsDefinition_correct
#print axioms bigContrapAccepted_correct
#print axioms MAISO11.Shared.compiledAxiomCheck_eq_reference
#print axioms MAISO11.Shared.compiledAxiomShortcut_sound
#print axioms bigAxiomRecordAccepted_correct
#print axioms bigConjRecordAccepted_correct
#print axioms MAISO11.Shared.compiledReflInstShortcut_sound
#print axioms bigReflInstRecordAccepted_correct
#print axioms hiddenWitness_is_instance
#print axioms hiddenCandidate_is_axiom
#print axioms hiddenWitness_not_in_obvious_candidates

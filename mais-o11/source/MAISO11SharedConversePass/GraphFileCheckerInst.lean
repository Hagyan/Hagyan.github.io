import GraphFileChecker
import InstantiationGraph
set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Shared
open MAISO11.Wire MAISO11.Quotation

/-- The instantiation branch now checks every valid witness compactly before
the remaining restricted logical axiom families use their old fallback. -/
def checkRecordWithInst {r k n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (rec : Record r k) (fs : Records r k) : Bool :=
  match rec with
  | .axiom f =>
      compiledAxiomCheckInst g refs (fun i => g.expand (refs i)) f
  | .mp a b f => mpEqual (compiledTermEqual g refs) (fs.get a) (fs.get b) f

theorem checkRecordWithInst_iff {r k n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (rec : Record r k) (fs : Records r k) :
    checkRecordWithInst g refs rec fs = true ↔
      rec.valid (fun i => g.expand (refs i)) fs := by
  cases rec with
  | «axiom» f =>
    simp [checkRecordWithInst,Record.valid,
      compiledAxiomCheckInst_eq_reference,axiomCheck_iff]
  | mp a b f =>
    simpa [checkRecordWithInst,Record.valid] using
      mpEqual_iff (fun i => g.expand (refs i))
        (compiledTermEqual g refs)
        (fun m s t => compiledTermEqual_correct g refs m s t)
        (fs.get a) (fs.get b) f

def checkRecordsWithInst {r k n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) : Records r k → Bool
  | .nil => true
  | .snoc fs rec =>
      checkRecordsWithInst g refs fs && checkRecordWithInst g refs rec fs

theorem checkRecordsWithInst_iff {r k n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (fs : Records r k) :
    checkRecordsWithInst g refs fs = true ↔
      fs.valid (fun i => g.expand (refs i)) := by
  induction fs with
  | nil => simp [checkRecordsWithInst,Records.valid]
  | @snoc k fs rec ih =>
    simp [checkRecordsWithInst,Records.valid,ih,checkRecordWithInst_iff]

def checkWholeGraphWithInst (r count : Nat) (cs : List Char) : Bool :=
  match decodeWholeShared r count cs with
  | none => false
  | some ⟨p,⟨k,fs⟩⟩ =>
      if 0 < k then
        checkRecordsWithInst (compileDefs p).graph (compileDefs p).refs fs
      else false

theorem checkWholeGraphWithInst_eq_old_accept (r count : Nat)
    (cs : List Char) :
    checkWholeGraphWithInst r count cs = (checkWhole r count cs).isSome := by
  cases hdec : decodeWholeShared r count cs with
  | none =>
    simp [checkWholeGraphWithInst,checkWholeSharedReference,hdec,
      ← checkWholeSharedReference_eq_old]
  | some data =>
    obtain ⟨p,⟨k,fs⟩⟩ := data
    have hrefs : (fun i => (compileDefs p).graph.expand
        ((compileDefs p).refs i)) = p.expand := by
      funext i
      exact compileDefs_refines p i
    have hcheck : checkRecordsWithInst (compileDefs p).graph
        (compileDefs p).refs fs = fs.check p.expand := by
      apply Bool.eq_iff_iff.mpr
      rw [checkRecordsWithInst_iff,hrefs]
      exact (fs.check_iff p.expand).symm
    by_cases hk : 0 < k
    · simp [checkWholeGraphWithInst,checkWholeSharedReference,hdec,hk,
        checkDecoded_isSome,hcheck,← checkWholeSharedReference_eq_old]
    · have hk0 : k = 0 := by omega
      subst k
      simp [checkWholeGraphWithInst,checkWholeSharedReference,hdec,
        checkDecoded_isSome,← checkWholeSharedReference_eq_old]

#print axioms checkRecordsWithInst_iff
#print axioms checkWholeGraphWithInst_eq_old_accept
end MAISO11.Shared

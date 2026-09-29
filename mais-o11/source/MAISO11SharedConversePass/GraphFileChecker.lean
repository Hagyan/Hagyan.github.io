import SharedOracle
import SharedConverse
set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Shared
open MAISO11.Wire MAISO11.Arithmetic MAISO11.Quotation

theorem CDefs.terms_env_eq_expand {r : Nat} (p : CDefs r) :
    envDictionary p.terms p.terms_length = p.expand := by
  funext i
  have hget := (List.getElem?_eq_some_iff.mp (p.terms_get i))
  rcases hget with ⟨_,hget⟩
  simpa [envDictionary,p.terms_length] using hget

theorem checkDecoded_isSome {r k : Nat} (p : CDefs r) (fs : Records r k) :
    (checkDecoded p.terms fs).isSome =
      (decide (0 < k) && fs.check p.expand) := by
  have henv := CDefs.terms_env_eq_expand p
  by_cases hk : 0 < k <;> cases hc : fs.check p.expand <;>
    simp [checkDecoded,p.terms_length,henv,hk,hc]

/-- Boolean acceptance path using compact definition parsing and the compiled
graph comparator for MP formulas at every quantifier depth and graph shortcuts
for two propositional axiom schemes and reflexivity instantiation. It does not
construct the final expanded conclusion for those successful shortcut cases.
Other instantiations and nonmatching candidates use the reference expanding
implementation. -/
def checkWholeSharedGraph (r count : Nat) (cs : List Char) : Bool :=
  match decodeWholeShared r count cs with
  | none => false
  | some ⟨p,⟨k,fs⟩⟩ =>
      if 0 < k then
        checkRecordsCompiledTerms (compileDefs p).graph (compileDefs p).refs fs
      else false

theorem checkWholeSharedGraph_eq_reference_accept (r count : Nat)
    (cs : List Char) :
    checkWholeSharedGraph r count cs =
      (checkWholeSharedReference r count cs).isSome := by
  cases hdec : decodeWholeShared r count cs with
  | none => simp [checkWholeSharedGraph,checkWholeSharedReference,hdec]
  | some data =>
    obtain ⟨p,⟨k,fs⟩⟩ := data
    have hrefs : (fun i => (compileDefs p).graph.expand
        ((compileDefs p).refs i)) = p.expand := by
      funext i
      exact compileDefs_refines p i
    have hcheck :
        checkRecordsCompiledTerms (compileDefs p).graph (compileDefs p).refs fs = true ↔
          fs.check p.expand = true := by
      have h1 := checkRecordsCompiledTerms_iff
        (compileDefs p).graph (compileDefs p).refs fs
      rw [hrefs] at h1
      exact h1.trans (fs.check_iff p.expand).symm
    have hcheckEq :
        checkRecordsCompiledTerms (compileDefs p).graph (compileDefs p).refs fs =
          fs.check p.expand := by
      cases hnew : checkRecordsCompiledTerms (compileDefs p).graph (compileDefs p).refs fs <;>
        cases hold : fs.check p.expand <;> simp_all [hcheck]
    by_cases hk : 0 < k
    ·
      simp [checkWholeSharedGraph,checkWholeSharedReference,hdec,hk,
        checkDecoded_isSome,hcheckEq]
    ·
      have hk0 : k = 0 := by omega
      subst k
      simp [checkWholeSharedGraph,checkWholeSharedReference,hdec,
        checkDecoded_isSome]

theorem checkWholeSharedGraph_eq_old_accept (r count : Nat)
    (cs : List Char) :
    checkWholeSharedGraph r count cs = (checkWhole r count cs).isSome := by
  rw [checkWholeSharedGraph_eq_reference_accept,
    checkWholeSharedReference_eq_old]

theorem checkWholeSharedGraph_sound {r count : Nat} {cs : List Char}
    (h : checkWholeSharedGraph r count cs = true) :
    ∃ f, checkWhole r count cs = some f := by
  rw [checkWholeSharedGraph_eq_old_accept] at h
  cases hc : checkWhole r count cs with
  | none => simp [hc] at h
  | some f => exact ⟨f,rfl⟩

end MAISO11.Shared

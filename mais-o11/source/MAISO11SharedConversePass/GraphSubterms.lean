import GraphCompiler
set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Shared
open MAISO11.Quotation MAISO11.Wire

/-- Syntactic subterms, including the entire term. -/
inductive IsSubterm (s : ClosedTerm) : ClosedTerm → Prop where
  | self : IsSubterm s s
  | bit0 {t} : IsSubterm s t → IsSubterm s (.bit0 t)
  | bit1 {t} : IsSubterm s t → IsSubterm s (.bit1 t)
  | addLeft {t u} : IsSubterm s t → IsSubterm s (.add t u)
  | addRight {t u} : IsSubterm s u → IsSubterm s (.add t u)
  | mulLeft {t u} : IsSubterm s t → IsSubterm s (.mul t u)
  | mulRight {t u} : IsSubterm s u → IsSubterm s (.mul t u)

/-- Every syntactic subterm of an expanded graph root is represented by a
graph node. This includes subterms buried inside an abbreviation definition.
-/
theorem Graph.subterm_has_node {n : Nat} (g : Graph n)
    (i : Fin n) (s : ClosedTerm) (h : IsSubterm s (g.expand i)) :
    ∃ j : Fin n, g.expand j = s := by
  induction g with
  | nil => exact Fin.elim0 i
  | @snoc n g a ih =>
    revert h
    refine Fin.lastCases ?_ (fun k => ?_) i
    · intro h
      have hroot : IsSubterm s (a.expand g.expand) := by
        simpa only [Graph.expand,Fin.lastCases_last] using h
      cases a with
      | zero =>
        cases hroot with
        | self => exact ⟨Fin.last n,by simp [Graph.expand]⟩
      | bit0 k =>
        cases hroot with
        | self => exact ⟨Fin.last n,by simp [Graph.expand]⟩
        | bit0 hs =>
          obtain ⟨j,hj⟩ := ih k hs
          exact ⟨j.castSucc,by simpa only [Graph.expand,Fin.lastCases_castSucc] using hj⟩
      | bit1 k =>
        cases hroot with
        | self => exact ⟨Fin.last n,by simp [Graph.expand]⟩
        | bit1 hs =>
          obtain ⟨j,hj⟩ := ih k hs
          exact ⟨j.castSucc,by simpa only [Graph.expand,Fin.lastCases_castSucc] using hj⟩
      | add k l =>
        cases hroot with
        | self => exact ⟨Fin.last n,by simp [Graph.expand]⟩
        | addLeft hs =>
          obtain ⟨j,hj⟩ := ih k hs
          exact ⟨j.castSucc,by simpa only [Graph.expand,Fin.lastCases_castSucc] using hj⟩
        | addRight hs =>
          obtain ⟨j,hj⟩ := ih l hs
          exact ⟨j.castSucc,by simpa only [Graph.expand,Fin.lastCases_castSucc] using hj⟩
      | mul k l =>
        cases hroot with
        | self => exact ⟨Fin.last n,by simp [Graph.expand]⟩
        | mulLeft hs =>
          obtain ⟨j,hj⟩ := ih k hs
          exact ⟨j.castSucc,by simpa only [Graph.expand,Fin.lastCases_castSucc] using hj⟩
        | mulRight hs =>
          obtain ⟨j,hj⟩ := ih l hs
          exact ⟨j.castSucc,by simpa only [Graph.expand,Fin.lastCases_castSucc] using hj⟩
    · intro h
      have hold : IsSubterm s (g.expand k) := by
        simpa only [Graph.expand,Fin.lastCases_castSucc] using h
      obtain ⟨j,hj⟩ := ih k hold
      exact ⟨j.castSucc,by simpa only [Graph.expand,Fin.lastCases_castSucc] using hj⟩

/-- An accepted abbreviation's expanded root has no syntactic subterm that
escapes the compiled graph. The graph has at most the written prelude length
many nodes, by `compileDefs_size_le_wire`. -/
theorem compiledDefs_subterm_has_node {r : Nat} (p : CDefs r)
    (i : Fin r) (s : ClosedTerm) (h : IsSubterm s (p.expand i)) :
    ∃ j : Fin (compileDefs p).size,
      (compileDefs p).graph.expand j = s := by
  have hs : IsSubterm s ((compileDefs p).graph.expand ((compileDefs p).refs i)) := by
    rw [compileDefs_refines]
    exact h
  exact (compileDefs p).graph.subterm_has_node _ _ hs

#print axioms Graph.subterm_has_node
#print axioms compiledDefs_subterm_has_node
end MAISO11.Shared

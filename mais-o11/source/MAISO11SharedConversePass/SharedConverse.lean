import SharedPrelude
import Std
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option warningAsError true
namespace MAISO11.Wire
open MAISO11.Quotation MAISO11.Arithmetic

theorem close_sound {cs tail : List Char} (h : close cs = some tail) :
    cs = ')' :: tail := by
  cases cs with
  | nil => simp [close] at h
  | cons c rest =>
    by_cases hc : c = ')'
    · subst c
      simp only [close,Option.some.injEq] at h
      subst rest
      rfl
    · simp [close,hc] at h

theorem oldTerm_sound {r : Nat} (env : List ClosedTerm)
    (δ : Fin r → ClosedTerm) (hlen : env.length = r)
    (he : ∀ i : Fin r, env[i.val]? = some (δ i))
    (fuel : Nat) (cs : List Char) (v : ClosedTerm) (tail : List Char)
    (h : readEnvTermFuel env fuel cs = some (v,tail)) :
    ∃ t : CTerm r 0, cs = t.wire ++ tail ∧ v = t.close δ := by
  induction fuel generalizing cs v tail with
  | zero => simp [readEnvTermFuel] at h
  | succ fuel ih =>
    unfold readEnvTermFuel at h
    split at h
    · cases h
      exact ⟨.zero,rfl,rfl⟩
    · rename_i body
      cases hr : readCanonicalIdentifier ('u'::body) with
      | none => simp [hr] at h
      | some result =>
        obtain ⟨i,rest⟩ := result
        cases hv : env[i]? with
        | none => simp [hr,hv] at h
        | some val =>
          have hi : i < r := by
            by_cases hh : i < r
            · exact hh
            have hn : env.length ≤ i := by omega
            simp [List.getElem?_eq_none hn] at hv
          let j : Fin r := ⟨i,hi⟩
          have hvδ : val = δ j := by
            have hh := he j
            change env[i]? = some (δ j) at hh
            rw [hv] at hh
            exact Option.some.inj hh
          have hs : 'u' :: body = identifier i ++ rest :=
            readCanonicalIdentifier_sound hr
          simp [hr,hv] at h
          rcases h with ⟨rfl,rfl⟩
          refine ⟨.ref j, ?_, ?_⟩
          · exact hs
          · exact hvδ
    · rename_i body
      cases hu : readEnvTermFuel env fuel body with
      | none => simp [hu] at h
      | some result =>
        obtain ⟨value,rest⟩ := result
        cases hc : close rest with
        | none => simp [hu,hc] at h
        | some remainder =>
          obtain ⟨t,ht,heq⟩ := ih body value rest hu
          have hr := close_sound hc
          simp [hu,hc] at h
          rcases h with ⟨rfl,rfl⟩
          refine ⟨.bit0 t, ?_, ?_⟩
          · simp [CTerm.wire,ht,hr,List.append_assoc]
          · simp [CTerm.close,heq]
    · rename_i body
      cases hu : readEnvTermFuel env fuel body with
      | none => simp [hu] at h
      | some result =>
        obtain ⟨value,rest⟩ := result
        cases hc : close rest with
        | none => simp [hu,hc] at h
        | some remainder =>
          obtain ⟨t,ht,heq⟩ := ih body value rest hu
          have hr := close_sound hc
          simp [hu,hc] at h
          rcases h with ⟨rfl,rfl⟩
          refine ⟨.bit1 t, ?_, ?_⟩
          · simp [CTerm.wire,ht,hr,List.append_assoc]
          · simp [CTerm.close,heq]
    · rename_i body
      cases hs : readEnvTermFuel env fuel body with
      | none => simp [hs] at h
      | some result =>
        obtain ⟨s,restS⟩ := result
        cases ht : readEnvTermFuel env fuel restS with
        | none => simp [hs,ht] at h
        | some result =>
          obtain ⟨t,restT⟩ := result
          cases hc : close restT with
          | none => simp [hs,ht,hc] at h
          | some remainder =>
            obtain ⟨u,hu,huv⟩ := ih body s restS hs
            obtain ⟨w,hw,hwv⟩ := ih restS t restT ht
            have hr := close_sound hc
            simp [hs,ht,hc] at h
            rcases h with ⟨rfl,rfl⟩
            refine ⟨.add u w, ?_, ?_⟩
            · simp [CTerm.wire,hu,hw,hr,List.append_assoc]
            · simp [CTerm.close,huv,hwv]
    · rename_i body
      cases hs : readEnvTermFuel env fuel body with
      | none => simp [hs] at h
      | some result =>
        obtain ⟨s,restS⟩ := result
        cases ht : readEnvTermFuel env fuel restS with
        | none => simp [hs,ht] at h
        | some result =>
          obtain ⟨t,restT⟩ := result
          cases hc : close restT with
          | none => simp [hs,ht,hc] at h
          | some remainder =>
            obtain ⟨u,hu,huv⟩ := ih body s restS hs
            obtain ⟨w,hw,hwv⟩ := ih restS t restT ht
            have hr := close_sound hc
            simp [hs,ht,hc] at h
            rcases h with ⟨rfl,rfl⟩
            refine ⟨.mul u w, ?_, ?_⟩
            · simp [CTerm.wire,hu,hw,hr,List.append_assoc]
            · simp [CTerm.close,huv,hwv]
    · contradiction

/-- Every accepted old definition line is also accepted by the compact
reader, with precisely the same expanded environment. -/
theorem oldDefinition_complete {r : Nat} (p : CDefs r)
    {cs : List Char} {env : List ClosedTerm} {tail : List Char}
    (h : readDefinition p.terms cs = some (env,tail)) :
    ∃ t : CTerm r 0,
      parseSharedDefinition r cs = some (t,tail) ∧
      env = (p.snoc t).terms := by
  unfold readDefinition at h
  split at h
  · rename_i body
    cases hi : readCanonicalIdentifier body with
    | none => simp [hi] at h
    | some result =>
      obtain ⟨i,rest⟩ := result
      by_cases hir : i = r
      · subst i
        simp [hi,p.terms_length] at h
        split at h
        · rename_i termBytes
          cases ht : readEnvTerm p.terms termBytes with
          | none => simp [ht] at h
          | some result =>
            obtain ⟨v,restT⟩ := result
            cases hn : newline restT with
            | none => simp [ht,hn] at h
            | some remainder =>
              have hs := oldTerm_sound p.terms p.expand p.terms_length
                p.terms_get termBytes.length termBytes v restT ht
              obtain ⟨t,hbytes,hval⟩ := hs
              have hnl := newline_sound hn
              have hid := readCanonicalIdentifier_sound hi
              simp [ht,hn] at h
              rcases h with ⟨rfl,rfl⟩
              refine ⟨t,?_,?_⟩
              · rw [hid,hbytes,hnl]
                simpa [sharedDefinition,List.append_assoc] using
                  parseSharedDefinition_wire t remainder
              · simp [CDefs.terms,hval]
        · simp at h
      · simp [hi,p.terms_length,hir] at h
  · simp at h

theorem oldCount_complete (k : Nat) {r : Nat} (p : CDefs r)
    {cs : List Char} {env : List ClosedTerm} {tail : List Char}
    (h : readDefinitionsCount k p.terms cs = some (env,tail)) :
    ∃ (m : Nat) (q : CDefs m),
      parseSharedCount k r p cs = some ⟨m,q,tail⟩ ∧ env = q.terms := by
  induction k generalizing r p cs env tail with
  | zero =>
    simp [readDefinitionsCount] at h
    rcases h with ⟨rfl,rfl⟩
    exact ⟨r,p,rfl,rfl⟩
  | succ k ih =>
    cases hd : readDefinition p.terms cs with
    | none => simp [readDefinitionsCount,hd] at h
    | some result =>
      obtain ⟨next,rest⟩ := result
      obtain ⟨t,hcompact,heq⟩ := oldDefinition_complete p hd
      have hnext : readDefinitionsCount k (p.snoc t).terms rest =
          some (env,tail) := by
        simpa [readDefinitionsCount,hd,heq] using h
      obtain ⟨m,q,hparsed,hterms⟩ := ih (p.snoc t) hnext
      refine ⟨m,q,?_,hterms⟩
      simpa [parseSharedCount,hcompact] using hparsed

/-- The reverse refinement holds on all input bytes accepted by the old
reader, including arbitrarily nested arithmetic definitions. -/
theorem oldPrelude_complete {r : Nat} {cs : List Char}
    {env : List ClosedTerm} (h : readDefinitionPrelude r cs = some env) :
    ∃ p : CDefs r, parseSharedPrelude r cs = some p ∧ env = p.terms := by
  unfold readDefinitionPrelude at h
  cases hc : readDefinitionsCount r [] cs with
  | none => simp [hc] at h
  | some result =>
    obtain ⟨initial,rest⟩ := result
    have hrest : rest = [] := by
      by_cases he : rest.isEmpty = true
      · exact List.isEmpty_iff.mp he
      · simp [hc,he] at h
        exact h.1.1
    have hlen : initial.length = r := by
      by_cases hl : initial.length = r
      · exact hl
      · simp [hc,hl] at h
    have henv : env = initial := by
      simpa [hc,hrest,hlen] using h.symm
    obtain ⟨m,q,hparsed,hterms⟩ := oldCount_complete r CDefs.nil hc
    have hm : m = r := by
      rw [← q.terms_length,← hterms]
      exact hlen
    subst m
    refine ⟨q,?_,?_⟩
    · simp [parseSharedPrelude,hparsed,hrest]
    · rw [henv,hterms]

/-- The compact parser and the original PA-bin definition reader recognize
the identical language and assign identical expanded meanings. This is an
extensional statement; evaluating `p.terms` can still be exponentially costly. -/
theorem sharedPrelude_iff_old {r : Nat} (cs : List Char) :
    (parseSharedPrelude r cs).map CDefs.terms =
      readDefinitionPrelude r cs := by
  cases hn : parseSharedPrelude r cs with
  | none =>
    cases ho : readDefinitionPrelude r cs with
    | none => rfl
    | some env =>
      obtain ⟨p,hp,_⟩ := oldPrelude_complete ho
      rw [hn] at hp
      contradiction
  | some p =>
    rw [parseSharedPrelude_refines_old hn]
    simp [hn]

theorem parseSharedCount_index (k : Nat) {r : Nat} (p : CDefs r)
    {cs : List Char} {m : Nat} {q : CDefs m} {tail : List Char}
    (h : parseSharedCount k r p cs = some ⟨m,q,tail⟩) :
    m = r+k := by
  induction k generalizing r p cs m q tail with
  | zero =>
    simp [parseSharedCount] at h
    rcases h with ⟨rfl,rfl,rfl⟩
    rfl
  | succ k ih =>
    cases hd : parseSharedDefinition r cs with
    | none => simp [parseSharedCount,hd] at h
    | some result =>
      obtain ⟨t,rest⟩ := result
      have hn : parseSharedCount k (r+1) (p.snoc t) rest =
          some ⟨m,q,tail⟩ := by simpa [parseSharedCount,hd] using h
      have hm := ih (p.snoc t) hn
      omega

/-- Decode the same complete written file, retaining compact definitions. -/
def decodeWholeShared (r count : Nat) (cs : List Char) :
    Option (CDefs r × ((k : Nat) × Records r k)) := do
  let ⟨m,p,rest⟩ ← parseSharedCount r 0 .nil cs
  if hm : m = r then
    let ⟨k,fs⟩ ← parseFile r count rest
    pure ⟨hm ▸ p,k,fs⟩
  else none

theorem decodeWholeShared_wire {r k : Nat} (p : CDefs r)
    (fs : Records r k) :
    decodeWholeShared r k (p.wire ++ fs.wire) = some ⟨p,k,fs⟩ := by
  simp [decodeWholeShared,parseSharedCount_wire,parseFile_wire]

/-- Full-file decoding agrees byte for byte with the existing PA-bin decoder.
The map exposes the old expanded environment only for stating the theorem. -/
theorem decodeWholeShared_iff_old (r count : Nat) (cs : List Char) :
    (decodeWholeShared r count cs).map
      (fun ⟨p,k,fs⟩ => ⟨p.terms, k, fs⟩) = decodeWhole r count cs := by
  cases hc : parseSharedCount r 0 .nil cs with
  | none =>
    have ho : readDefinitionsCount r [] cs = none := by
      cases ho : readDefinitionsCount r [] cs with
      | none => rfl
      | some result =>
        obtain ⟨env,rest⟩ := result
        obtain ⟨m,q,hp,_⟩ := oldCount_complete r CDefs.nil ho
        rw [hc] at hp
        contradiction
    simp [decodeWholeShared,decodeWhole,hc,ho]
  | some result =>
    obtain ⟨m,p,rest⟩ := result
    have hm : m = r := by simpa using
      (parseSharedCount_index r CDefs.nil hc)
    subst m
    have ho := parseSharedCount_refines_old r CDefs.nil hc
    change readDefinitionsCount r [] cs = some (p.terms,rest) at ho
    have hlen := p.terms_length
    simp [decodeWholeShared,decodeWhole,hc,ho,hlen]
    cases hf : parseFile r count rest with
    | none => simp [hf]
    | some result =>
      obtain ⟨k,fs⟩ := result
      simp [hf]

/-- Reference whole-file checker through the compact definition parser. Its
arithmetic axiom branch still expands, so this theorem has no runtime bound. -/
def checkWholeSharedReference (r count : Nat) (cs : List Char) :
    Option (Formula 0) := do
  let ⟨p,_k,fs⟩ ← decodeWholeShared r count cs
  checkDecoded p.terms fs

theorem checkWholeSharedReference_eq_old (r count : Nat) (cs : List Char) :
    checkWholeSharedReference r count cs = checkWhole r count cs := by
  have hd := decodeWholeShared_iff_old r count cs
  cases hs : decodeWholeShared r count cs with
  | none =>
    simp [hs] at hd
    simp [checkWholeSharedReference,checkWhole,hs,←hd]
  | some result =>
    obtain ⟨p,k,fs⟩ := result
    simp [hs] at hd
    simp [checkWholeSharedReference,checkWhole,hs,←hd]

theorem checkWholeSharedReference_sound {r count : Nat} {cs : List Char}
    {f : Formula 0}
    (h : checkWholeSharedReference r count cs = some f) :
    Nonempty (Derivation f) := by
  rw [checkWholeSharedReference_eq_old] at h
  exact checkWhole_sound h

end MAISO11.Wire

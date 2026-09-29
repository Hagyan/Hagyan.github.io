import FragmentPrefix

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.FragmentRange

open MAISO11.Quotation MAISO11.FragmentBalance MAISO11.FragmentPrefix

/-- Half-open interval query, with start `p` and requested length `q`.
Out-of-range endpoints are clipped by the semantics of `drop` and `take`. -/
def atomRange {b n : Nat} (op cl : Fin b)
    (previous : Fin n → Nat → Nat → Summary) : Atom b n → Nat → Nat → Summary
  | .char c, p, q =>
      if p = 0 ∧ q ≠ 0 then Summary.atom (charWeight op cl c) else Summary.empty
  | .use i, p, q => previous i p q

/-- Cache complete atoms, skip atoms wholly preceding the interval, and
descend only into partially selected atoms. No expanded word is computed. -/
def fragmentRange {b n : Nat} (op cl : Fin b) (table : Vector Entry n)
    (previous : Fin n → Nat → Nat → Summary) : Fragment b n → Nat → Nat → Summary
  | [], _, _ => Summary.empty
  | a :: rest, p, q =>
      if q = 0 then Summary.empty else
      let e := atomEntry op cl table a
      if e.length ≤ p then fragmentRange op cl table previous rest (p-e.length) q
      else
        let first := if p = 0 ∧ e.length ≤ q then e.summary
          else atomRange op cl previous a p q
        first.join (fragmentRange op cl table previous rest 0 (q-(e.length-p)))

theorem atomRange_correct {b n : Nat} (op cl : Fin b)
    (previous : Fin n → Nat → Nat → Summary) (words : Fin n → Word b)
    (hp : ∀ i p q, previous i p q = wordSummary op cl (((words i).drop p).take q))
    (a : Atom b n) (p q : Nat) :
    atomRange op cl previous a p q =
      wordSummary op cl (((a.expand words).drop p).take q) := by
  cases a with
  | use i => exact hp i p q
  | char c =>
    cases p with
    | succ p => simp [atomRange, Atom.expand, wordSummary, summarize]
    | zero =>
      cases q with
      | zero => rfl
      | succ q =>
        simp only [atomRange, Nat.succ_ne_zero, not_false_eq_true, and_self,
          ↓reduceIte, Atom.expand, List.drop_zero, List.take_succ_cons, List.take_nil]
        simpa [wordSummary, summarize] using
          (Summary.join_empty (Summary.atom (charWeight op cl c))
            (by simp [Summary.atom]; omega)).symm

theorem fragmentRange_correct {b n : Nat} (op cl : Fin b)
    (table : Vector Entry n) (words : Fin n → Word b)
    (ht : TableCorrect op cl table words)
    (previous : Fin n → Nat → Nat → Summary)
    (hp : ∀ i p q, previous i p q = wordSummary op cl (((words i).drop p).take q))
    (f : Fragment b n) (p q : Nat) :
    fragmentRange op cl table previous f p q =
      wordSummary op cl (((expandFragment words f).drop p).take q) := by
  induction f generalizing p q with
  | nil => simp [fragmentRange, expandFragment, wordSummary, summarize]
  | cons a rest ih =>
    by_cases hq : q = 0
    · subst q
      simp [fragmentRange, wordSummary, summarize]
    · have he := atomEntry_correct op cl table words ht a
      simp only [fragmentRange, hq, ↓reduceIte, he, Entry.word]
      split
      · rename_i hskip
        rw [ih]
        simp only [expandFragment, List.drop_append_eq_append_drop,
          List.drop_eq_nil_of_le hskip, List.nil_append]
      · rename_i hskip
        have hstart : p ≤ (a.expand words).length := by omega
        have hfirst :
            (if p = 0 ∧ (a.expand words).length ≤ q
             then wordSummary op cl (a.expand words)
             else atomRange op cl previous a p q) =
            wordSummary op cl (((a.expand words).drop p).take q) := by
          split
          · rename_i hfull
            rcases hfull with ⟨rfl, hfull⟩
            simp only [List.drop_zero, List.take_of_length_le hfull]
          · exact atomRange_correct op cl previous words hp a p q
        rw [hfirst, ih]
        simp only [expandFragment, List.drop_append_of_le_length hstart,
          List.take_append_eq_append_take, List.length_drop, List.drop_zero,
          wordSummary_append]

def rangeWithTable {b n : Nat} (op cl : Fin b) :
    Grammar b n → Vector Entry n → Fin n → Nat → Nat → Summary
  | .nil, _, i, _, _ => Fin.elim0 i
  | .snoc g f, table, i, p, q =>
      let old := table.pop
      MAISO11.Shared.splitLast
        (fun _ => fragmentRange op cl old
          (fun j s t => rangeWithTable op cl g old j s t) f p q)
        (fun j => rangeWithTable op cl g old j p q) i

theorem rangeWithTable_correct {b n : Nat} (op cl : Fin b)
    (g : Grammar b n) (table : Vector Entry n)
    (ht : TableCorrect op cl table g.words) (i : Fin n) (p q : Nat) :
    rangeWithTable op cl g table i p q =
      wordSummary op cl (((g.words i).drop p).take q) := by
  induction g generalizing p q with
  | nil => exact Fin.elim0 i
  | @snoc n g f ih =>
    have hp := TableCorrect.pop op cl table g f ht
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [rangeWithTable, MAISO11.Shared.splitLast_last,
        Grammar.words, Fin.lastCases_last]
      exact fragmentRange_correct op cl table.pop g.words hp
        (fun j s t => rangeWithTable op cl g table.pop j s t)
        (fun j s t => ih table.pop hp j s t) f p q
    · simp only [rangeWithTable, MAISO11.Shared.splitLast_castSucc,
        Grammar.words, Fin.lastCases_castSucc]
      exact ih table.pop hp j p q

def rangeSummary {b n : Nat} (op cl : Fin b)
    (g : Grammar b n) (i : Fin n) (p q : Nat) : Summary :=
  rangeWithTable op cl g (summaryTable op cl g) i p q

theorem rangeSummary_correct {b n : Nat} (op cl : Fin b)
    (g : Grammar b n) (i : Fin n) (p q : Nat) :
    rangeSummary op cl g i p q = wordSummary op cl (((g.words i).drop p).take q) :=
  rangeWithTable_correct op cl g _ (summaryTable_correct op cl g) i p q

def rangeDemo : String := Id.run do
  let op : Fin 2 := 0
  let cl : Fin 2 := 1
  let g := doubledWord [op, cl] 60
  let table := summaryTable op cl g
  let root := Fin.last 60
  if rangeWithTable op cl g table root 1 2 = ⟨0,-1⟩ ∧
      rangeWithTable op cl g table root (2^61-1) 100 = ⟨-1,-1⟩ ∧
      rangeWithTable op cl g table root (2^61+5) 10 = ⟨0,0⟩ ∧
      rangeWithTable op cl g table root 1 0 = ⟨0,0⟩
    then return "PASS: clipped interval queries over 2^61 characters without expansion"
    else return "FAIL: compressed interval query"

#print axioms rangeSummary_correct
#eval rangeDemo

end MAISO11.FragmentRange

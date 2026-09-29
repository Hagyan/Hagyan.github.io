import FragmentBalance
import Init.Data.Vector.Lemmas

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.FragmentPrefix

open MAISO11.Quotation MAISO11.FragmentBalance

/-- An explicitly stored summary for one expanded string. -/
structure Entry where
  length : Nat
  summary : Summary
  deriving DecidableEq, Repr

def Entry.empty : Entry := ⟨0, Summary.empty⟩

def Entry.append (x y : Entry) : Entry :=
  ⟨x.length + y.length, x.summary.join y.summary⟩

def Entry.word {b : Nat} (op cl : Fin b) (w : Word b) : Entry :=
  ⟨w.length, wordSummary op cl w⟩

theorem Entry.word_append {b : Nat} (op cl : Fin b) (x y : Word b) :
    Entry.word op cl (x ++ y) = (Entry.word op cl x).append (Entry.word op cl y) := by
  simp [Entry.word, Entry.append, List.length_append, wordSummary_append]

def atomEntry {b n : Nat} (op cl : Fin b) (table : Vector Entry n) :
    Atom b n → Entry
  | .char c => ⟨1, Summary.atom (charWeight op cl c)⟩
  | .use i => table[i]

def fragmentEntry {b n : Nat} (op cl : Fin b) (table : Vector Entry n) :
    Fragment b n → Entry
  | [] => Entry.empty
  | a :: rest => (atomEntry op cl table a).append (fragmentEntry op cl table rest)

def TableCorrect {b n : Nat} (op cl : Fin b) (table : Vector Entry n)
    (words : Fin n → Word b) : Prop :=
  ∀ i, table[i] = Entry.word op cl (words i)

theorem atomEntry_correct {b n : Nat} (op cl : Fin b)
    (table : Vector Entry n) (words : Fin n → Word b)
    (h : TableCorrect op cl table words) (a : Atom b n) :
    atomEntry op cl table a = Entry.word op cl (a.expand words) := by
  cases a with
  | char c =>
    simp only [atomEntry, Atom.expand, Entry.word, List.length_singleton]
    congr 1
    simpa [wordSummary, summarize] using
      (Summary.join_empty (Summary.atom (charWeight op cl c))
        (by simp [Summary.atom]; omega)).symm
  | use i => exact h i

theorem fragmentEntry_correct {b n : Nat} (op cl : Fin b)
    (table : Vector Entry n) (words : Fin n → Word b)
    (h : TableCorrect op cl table words) (f : Fragment b n) :
    fragmentEntry op cl table f = Entry.word op cl (expandFragment words f) := by
  induction f with
  | nil => rfl
  | cons a rest ih =>
    simp only [fragmentEntry, expandFragment, Entry.word_append,
      atomEntry_correct op cl table words h a, ih]

/-- Each recursive table is computed once and retained as a materialized vector.
There is no recursive environment lookup that recomputes prior summaries. -/
def summaryTable {b n : Nat} (op cl : Fin b) : Grammar b n → Vector Entry n
  | .nil => #v[]
  | .snoc g f =>
      let old := summaryTable op cl g
      old.push (fragmentEntry op cl old f)

theorem summaryTable_correct {b n : Nat} (op cl : Fin b) (g : Grammar b n) :
    TableCorrect op cl (summaryTable op cl g) g.words := by
  induction g with
  | nil => intro i; exact Fin.elim0 i
  | @snoc n g f ih =>
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [summaryTable, Grammar.words, Fin.lastCases_last,
        Fin.getElem_fin, Fin.val_last, Vector.getElem_push_eq]
      exact fragmentEntry_correct op cl _ _ ih f
    · simp only [summaryTable, Grammar.words, Fin.lastCases_castSucc,
        Fin.getElem_fin, Fin.coe_castSucc, Vector.getElem_push_lt j.isLt]
      exact ih j

theorem summaryTable_length {b n : Nat} (op cl : Fin b)
    (g : Grammar b n) (i : Fin n) :
    (summaryTable op cl g)[i].length = (g.words i).length := by
  rw [summaryTable_correct op cl g i]
  rfl

theorem summaryTable_summary {b n : Nat} (op cl : Fin b)
    (g : Grammar b n) (i : Fin n) :
    (summaryTable op cl g)[i].summary = wordSummary op cl (g.words i) := by
  rw [summaryTable_correct op cl g i]
  rfl

/-- An instrumented query. `visits` counts visited grammar definitions and
written right-hand-side atoms; it is not a compiled-runtime or bit-cost model. -/
structure Query where
  summary : Summary
  visits : Nat
  deriving DecidableEq, Repr

def Query.tick (q : Query) : Query := ⟨q.summary, q.visits + 1⟩

def atomPrefix {b n : Nat} (op cl : Fin b)
    (previous : Fin n → Nat → Query) : Atom b n → Nat → Query
  | .char c, q =>
      ⟨if q = 0 then Summary.empty else Summary.atom (charWeight op cl c), 0⟩
  | .use i, q => previous i q

/-- Whole fragments are answered from the table. Only a fragment containing
the requested boundary invokes `previous`. Oversized requests are clamped,
as with `List.take`. -/
def fragmentPrefix {b n : Nat} (op cl : Fin b) (table : Vector Entry n)
    (previous : Fin n → Nat → Query) : Fragment b n → Nat → Query
  | [], _ => ⟨Summary.empty, 0⟩
  | a :: rest, q =>
      let e := atomEntry op cl table a
      if q < e.length then
        (atomPrefix op cl previous a q).tick
      else
        let tail := fragmentPrefix op cl table previous rest (q - e.length)
        ⟨e.summary.join tail.summary, tail.visits + 1⟩

theorem atomPrefix_correct {b n : Nat} (op cl : Fin b)
    (previous : Fin n → Nat → Query) (words : Fin n → Word b)
    (h : ∀ i q, (previous i q).summary = wordSummary op cl ((words i).take q))
    (a : Atom b n) (q : Nat) :
    (atomPrefix op cl previous a q).summary =
      wordSummary op cl ((a.expand words).take q) := by
  cases a with
  | use i => exact h i q
  | char c =>
    cases q with
    | zero => rfl
    | succ q =>
      simp only [atomPrefix, Nat.succ_ne_zero, ↓reduceIte,
        Atom.expand, List.take_succ_cons, List.take_nil]
      simpa [wordSummary, summarize] using
        (Summary.join_empty (Summary.atom (charWeight op cl c))
          (by simp [Summary.atom]; omega)).symm

theorem fragmentPrefix_correct {b n : Nat} (op cl : Fin b)
    (table : Vector Entry n) (words : Fin n → Word b)
    (ht : TableCorrect op cl table words)
    (previous : Fin n → Nat → Query)
    (hp : ∀ i q, (previous i q).summary = wordSummary op cl ((words i).take q))
    (f : Fragment b n) (q : Nat) :
    (fragmentPrefix op cl table previous f q).summary =
      wordSummary op cl ((expandFragment words f).take q) := by
  induction f generalizing q with
  | nil => simp [fragmentPrefix, expandFragment, wordSummary, summarize]
  | cons a rest ih =>
    have he := atomEntry_correct op cl table words ht a
    simp only [fragmentPrefix, he, Entry.word]
    split
    · rename_i hq
      simp only [Query.tick, expandFragment,
        List.take_append_of_le_length (Nat.le_of_lt hq)]
      exact atomPrefix_correct op cl previous words hp a q
    · rename_i hq
      have hl : (a.expand words).length ≤ q := by omega
      rw [ih]
      simp only [expandFragment, List.take_append_eq_append_take,
        List.take_of_length_le hl, wordSummary_append]

theorem fragmentPrefix_visits {b n : Nat} (op cl : Fin b)
    (table : Vector Entry n) (previous : Fin n → Nat → Query) (bound : Nat)
    (hp : ∀ i q, (previous i q).visits ≤ bound)
    (f : Fragment b n) (q : Nat) :
    (fragmentPrefix op cl table previous f q).visits ≤ f.length + bound := by
  induction f generalizing q with
  | nil => simp [fragmentPrefix]
  | cons a rest ih =>
    simp only [fragmentPrefix]
    split
    · simp only [Query.tick]
      have ha : (atomPrefix op cl previous a q).visits ≤ bound := by
        cases a with
        | char c => simp [atomPrefix]
        | use i => exact hp i q
      simp only [List.length_cons]
      omega
    · have hh := ih (q - (atomEntry op cl table a).length)
      simp only [List.length_cons]
      omega

theorem TableCorrect.pop {b n : Nat} (op cl : Fin b)
    (table : Vector Entry (n+1)) (g : Grammar b n) (f : Fragment b n)
    (ht : TableCorrect op cl table (Grammar.snoc g f).words) :
    TableCorrect op cl table.pop g.words := by
  intro i
  have hi := ht i.castSucc
  change table.pop[i.val] = Entry.word op cl (g.words i)
  rw [Vector.getElem_pop (xs := table) (i := i.val) i.isLt]
  simpa only [Grammar.words, Fin.lastCases_castSucc] using hi

/-- Prefix navigation with a precomputed table. The delayed `splitLast`
branches avoid evaluating the branch not selected by the root index.
Each descent into an abbreviation goes to an earlier grammar definition. -/
def queryWithTable {b n : Nat} (op cl : Fin b) :
    Grammar b n → Vector Entry n → Fin n → Nat → Query
  | .nil, _, i, _ => Fin.elim0 i
  | .snoc g f, table, i, q =>
      let old := table.pop
      (MAISO11.Shared.splitLast
        (fun _ => fragmentPrefix op cl old
          (fun j r => queryWithTable op cl g old j r) f q)
        (fun j => queryWithTable op cl g old j q) i).tick

theorem queryWithTable_correct {b n : Nat} (op cl : Fin b)
    (g : Grammar b n) (table : Vector Entry n)
    (ht : TableCorrect op cl table g.words) (i : Fin n) (q : Nat) :
    (queryWithTable op cl g table i q).summary =
      wordSummary op cl ((g.words i).take q) := by
  induction g generalizing q with
  | nil => exact Fin.elim0 i
  | @snoc n g f ih =>
    have hp := TableCorrect.pop op cl table g f ht
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [queryWithTable, MAISO11.Shared.splitLast_last, Query.tick,
        Grammar.words, Fin.lastCases_last]
      exact fragmentPrefix_correct op cl table.pop g.words hp
        (fun j r => queryWithTable op cl g table.pop j r)
        (fun j r => ih table.pop hp j r) f q
    · simp only [queryWithTable, MAISO11.Shared.splitLast_castSucc, Query.tick,
        Grammar.words, Fin.lastCases_castSucc]
      exact ih table.pop hp j q

/-- The actual instrumented query visits at most the grammar mass. This
counts definitions and RHS atoms, not vector copying, arithmetic bit costs,
table construction, or compiled machine instructions. -/
theorem queryWithTable_visits {b n : Nat} (op cl : Fin b)
    (g : Grammar b n) (table : Vector Entry n) (i : Fin n) (q : Nat) :
    (queryWithTable op cl g table i q).visits ≤ g.mass := by
  induction g generalizing q with
  | nil => exact Fin.elim0 i
  | @snoc n g f ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [queryWithTable, MAISO11.Shared.splitLast_last, Query.tick]
      have hh := fragmentPrefix_visits op cl table.pop
        (fun j r => queryWithTable op cl g table.pop j r) g.mass
        (fun j r => ih table.pop j r) f q
      simp only [Grammar.mass]
      omega
    · simp only [queryWithTable, MAISO11.Shared.splitLast_castSucc, Query.tick]
      have hh := ih table.pop j q
      simp only [Grammar.mass]
      omega

def query {b n : Nat} (op cl : Fin b)
    (g : Grammar b n) (i : Fin n) (q : Nat) : Query :=
  queryWithTable op cl g (summaryTable op cl g) i q

def prefixSummary {b n : Nat} (op cl : Fin b)
    (g : Grammar b n) (i : Fin n) (q : Nat) : Summary :=
  (query op cl g i q).summary

/-- Exact agreement on every grammar, root, and requested prefix length,
including zero and requests beyond the expanded word's end. -/
theorem prefixSummary_correct {b n : Nat} (op cl : Fin b)
    (g : Grammar b n) (i : Fin n) (q : Nat) :
    prefixSummary op cl g i q = wordSummary op cl ((g.words i).take q) :=
  queryWithTable_correct op cl g _ (summaryTable_correct op cl g) i q

theorem query_visits {b n : Nat} (op cl : Fin b)
    (g : Grammar b n) (i : Fin n) (q : Nat) :
    (query op cl g i q).visits ≤ g.mass :=
  queryWithTable_visits op cl g _ i q

/-- A smoke-test family with exponentially many characters, represented in
the actual arbitrary-string grammar. -/
def doubledWord {b : Nat} (w : Word b) : (n : Nat) → Grammar b (n+1)
  | 0 => .snoc .nil (w.map Atom.char)
  | n+1 => .snoc (doubledWord w n) [.use (Fin.last n), .use (Fin.last n)]

def prefixDemo : String := Id.run do
  let op : Fin 2 := 0
  let cl : Fin 2 := 1
  let g := doubledWord [op, cl] 60
  let table := summaryTable op cl g
  let root := Fin.last 60
  let before := queryWithTable op cl g table root 0
  let middle := queryWithTable op cl g table root (2^60+1)
  let beyond := queryWithTable op cl g table root (2^61+11)
  if table[root].length = 2^61 ∧
      before.summary = ⟨0,0⟩ ∧ middle.summary = ⟨1,0⟩ ∧
      beyond.summary = ⟨0,0⟩ ∧
      before.visits ≤ g.mass ∧ middle.visits ≤ g.mass ∧ beyond.visits ≤ g.mass
    then return "PASS: prefix queries over 2^61 expanded characters, without expansion"
    else return "FAIL: compressed prefix query"

def emptyFragmentDemo : String := Id.run do
  let op : Fin 2 := 0
  let cl : Fin 2 := 1
  let empty : Grammar 2 1 := .snoc .nil []
  let g := Grammar.snoc empty
    [.use 0, .char op, .use 0, .char cl, .use 0]
  if prefixSummary op cl g (Fin.last 1) 0 = ⟨0,0⟩ ∧
      prefixSummary op cl g (Fin.last 1) 1 = ⟨1,0⟩ ∧
      prefixSummary op cl g (Fin.last 1) 3 = ⟨0,0⟩
    then return "PASS: empty referenced fragments and clipped prefix lengths"
    else return "FAIL: empty fragment prefix query"

#print axioms summaryTable_correct
#print axioms prefixSummary_correct
#print axioms query_visits
#eval prefixDemo
#eval emptyFragmentDemo

end MAISO11.FragmentPrefix

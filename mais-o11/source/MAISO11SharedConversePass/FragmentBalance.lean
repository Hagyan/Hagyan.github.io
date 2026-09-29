import DagEquality
import StringQuotation
set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.FragmentBalance

/-- Net change in parenthesis depth and lowest depth reached, including
the empty prefix. -/
structure Summary where
  net : Int
  floor : Int
  deriving DecidableEq, Repr

def Summary.join (a b : Summary) : Summary :=
  ⟨a.net + b.net, min a.floor (a.net + b.floor)⟩

def Summary.empty : Summary := ⟨0,0⟩

def Summary.atom (d : Int) : Summary := ⟨d,min 0 d⟩

theorem Summary.join_assoc (a b c : Summary) :
    (a.join b).join c = a.join (b.join c) := by
  cases a with
  | mk an af =>
    cases b with
    | mk bn bf =>
      cases c with
      | mk cn cf =>
        simp only [join,Summary.mk.injEq]
        constructor
        · omega
        · omega

theorem Summary.empty_join (a : Summary) (h : a.floor ≤ 0) :
    Summary.empty.join a = a := by
  cases a with
  | mk an af =>
    change af ≤ 0 at h
    change (⟨0 + an,min 0 (0 + af)⟩ : Summary) = ⟨an,af⟩
    simp
    congr 1
    omega

theorem Summary.join_empty (a : Summary) (h : a.floor ≤ a.net) :
    a.join Summary.empty = a := by
  cases a with
  | mk an af =>
    change af ≤ an at h
    change (⟨an + 0,min af (an + 0)⟩ : Summary) = ⟨an,af⟩
    simp
    congr 1
    omega

/-- Semantic summary of a character stream, where `+1` means `(`,
`-1` means `)`, and `0` means any other character. -/
def summarize : List Int → Summary
  | [] => Summary.empty
  | d :: ds => (Summary.atom d).join (summarize ds)

theorem summarize_floor_nonpos (xs : List Int) : (summarize xs).floor ≤ 0 := by
  induction xs with
  | nil => simp [summarize,Summary.empty]
  | cons d ds ih =>
    simp only [summarize,Summary.join,Summary.atom]
    omega

theorem summarize_append (xs ys : List Int) :
    summarize (xs ++ ys) = (summarize xs).join (summarize ys) := by
  induction xs with
  | nil =>
    simp only [List.nil_append,summarize]
    exact (Summary.empty_join _ (summarize_floor_nonpos ys)).symm
  | cons d ds ih =>
    simp only [List.cons_append,summarize,ih,Summary.join_assoc]

/-- The earliest depth in a stream determines if any prefix underflows. -/
def safeFrom (start : Int) : List Int → Prop
  | [] => 0 ≤ start
  | d :: ds => 0 ≤ start ∧ safeFrom (start + d) ds

theorem safeFrom_iff (start : Int) (xs : List Int) :
    safeFrom start xs ↔ 0 ≤ start + (summarize xs).floor := by
  induction xs generalizing start with
  | nil => simp [safeFrom,summarize,Summary.empty]
  | cons d ds ih =>
    simp only [safeFrom,summarize,Summary.join,Summary.atom]
    rw [ih]
    have hf := summarize_floor_nonpos ds
    by_cases hd : d ≤ 0
    · have hm : min 0 d = d := by omega
      rw [hm]
      omega
    · have hm : min 0 d = 0 := by omega
      rw [hm]
      omega

/-- The summary is enough to decide whether expanded parentheses are
balanced, without expanding a repeated string. -/
def balanced (s : Summary) : Prop := s.net = 0 ∧ 0 ≤ s.floor

theorem balanced_iff (xs : List Int) :
    balanced (summarize xs) ↔
      (summarize xs).net = 0 ∧ safeFrom 0 xs := by
  simp only [balanced,safeFrom_iff]
  omega

/-- A string straight-line program. A node can denote an unmatched
parenthesis fragment: nodes are strings, not necessarily well-formed terms. -/
inductive Fragment (n : Nat) where
  | atom : Int → Fragment n
  | concat : Fin n → Fin n → Fragment n

inductive FragmentGraph : Nat → Type where
  | nil : FragmentGraph 0
  | snoc {n : Nat} : FragmentGraph n → Fragment n → FragmentGraph (n+1)

def Fragment.expand {n : Nat} (env : Fin n → List Int) :
    Fragment n → List Int
  | .atom d => [d]
  | .concat i j => env i ++ env j

def Fragment.compute {n : Nat} (env : Fin n → Summary) :
    Fragment n → Summary
  | .atom d => Summary.atom d
  | .concat i j => (env i).join (env j)

def FragmentGraph.expand {n : Nat} : FragmentGraph n → Fin n → List Int
  | .nil => Fin.elim0
  | .snoc g a => Fin.lastCases (a.expand g.expand) g.expand

def FragmentGraph.compute {n : Nat} : FragmentGraph n → Fin n → Summary
  | .nil => Fin.elim0
  | .snoc g a => Fin.lastCases (a.compute g.compute) g.compute

/-- Bottom-up summaries exactly match the exponentially expanded string. -/
theorem FragmentGraph.compute_correct {n : Nat}
    (g : FragmentGraph n) (i : Fin n) :
    g.compute i = summarize (g.expand i) := by
  induction g with
  | nil => exact Fin.elim0 i
  | @snoc n g a ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [FragmentGraph.compute,FragmentGraph.expand,
        Fin.lastCases_last]
      cases a with
      | atom d =>
        simpa only [Fragment.compute,Fragment.expand,summarize] using
          (Summary.join_empty (Summary.atom d) (by simp [Summary.atom]; omega)).symm
      | concat j k =>
        simp only [Fragment.compute,Fragment.expand,summarize_append,ih]
    · simpa only [FragmentGraph.compute,FragmentGraph.expand,
        Fin.lastCases_castSucc] using ih j

theorem FragmentGraph.balanced_iff {n : Nat}
    (g : FragmentGraph n) (i : Fin n) :
    balanced (g.compute i) ↔
      (summarize (g.expand i)).net = 0 ∧ safeFrom 0 (g.expand i) := by
  rw [g.compute_correct i]
  exact MAISO11.FragmentBalance.balanced_iff _

/-- The same summary computed over the project's actual arbitrary-string
abbreviation grammar. It classifies two designated alphabet characters as
opening and closing delimiters; all other characters have weight zero. -/
def charWeight {b : Nat} (op cl : Fin b) (c : Fin b) : Int :=
  if c = op then 1 else if c = cl then -1 else 0

def wordSummary {b : Nat} (op cl : Fin b)
    (w : MAISO11.Quotation.Word b) : Summary :=
  summarize (w.map (charWeight op cl))

def atomSummary {b n : Nat} (op cl : Fin b)
    (env : Fin n → Summary) : MAISO11.Quotation.Atom b n → Summary
  | .char c => Summary.atom (charWeight op cl c)
  | .use i => env i

def fragmentSummary {b n : Nat} (op cl : Fin b)
    (env : Fin n → Summary) : MAISO11.Quotation.Fragment b n → Summary
  | [] => Summary.empty
  | a :: rest =>
      (atomSummary op cl env a).join (fragmentSummary op cl env rest)

theorem atomSummary_correct {b n : Nat} (op cl : Fin b)
    (ρ : Fin n → MAISO11.Quotation.Word b)
    (a : MAISO11.Quotation.Atom b n) :
    atomSummary op cl (fun i => wordSummary op cl (ρ i)) a =
      wordSummary op cl (a.expand ρ) := by
  cases a with
  | char c =>
    simpa [atomSummary,MAISO11.Quotation.Atom.expand,wordSummary,summarize]
      using (Summary.join_empty (Summary.atom (charWeight op cl c))
        (by simp [Summary.atom]; omega)).symm
  | use i => rfl

theorem wordSummary_append {b : Nat} (op cl : Fin b)
    (x y : MAISO11.Quotation.Word b) :
    wordSummary op cl (x ++ y) =
      (wordSummary op cl x).join (wordSummary op cl y) := by
  simp only [wordSummary,List.map_append,summarize_append]

theorem fragmentSummary_correct {b n : Nat} (op cl : Fin b)
    (ρ : Fin n → MAISO11.Quotation.Word b)
    (f : MAISO11.Quotation.Fragment b n) :
    fragmentSummary op cl (fun i => wordSummary op cl (ρ i)) f =
      wordSummary op cl (MAISO11.Quotation.expandFragment ρ f) := by
  induction f with
  | nil => rfl
  | cons a rest ih =>
    simp only [fragmentSummary,MAISO11.Quotation.expandFragment,
      wordSummary_append,atomSummary_correct,ih]

def grammarSummary {b n : Nat} (op cl : Fin b) :
    MAISO11.Quotation.Grammar b n → Fin n → Summary
  | .nil => Fin.elim0
  | .snoc g f =>
      Fin.lastCases (fragmentSummary op cl (grammarSummary op cl g) f)
        (grammarSummary op cl g)

/-- A bottom-up computation on the actual `StringQuotation.Grammar` agrees
with the net/minimum balance of its fully expanded definitions. -/
theorem grammarSummary_correct {b n : Nat} (op cl : Fin b)
    (g : MAISO11.Quotation.Grammar b n) (i : Fin n) :
    grammarSummary op cl g i = wordSummary op cl (g.words i) := by
  induction g with
  | nil => exact Fin.elim0 i
  | @snoc n g f ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [grammarSummary,MAISO11.Quotation.Grammar.words,
        Fin.lastCases_last]
      have he : (fun j => grammarSummary op cl g j) =
          (fun j => wordSummary op cl (g.words j)) := funext ih
      change fragmentSummary op cl (fun j => grammarSummary op cl g j) f =
        wordSummary op cl (MAISO11.Quotation.expandFragment g.words f)
      rw [he,fragmentSummary_correct]
    · simpa only [grammarSummary,MAISO11.Quotation.Grammar.words,
        Fin.lastCases_castSucc] using ih j

theorem grammarBalanced_iff {b n : Nat} (op cl : Fin b)
    (g : MAISO11.Quotation.Grammar b n) (i : Fin n) :
    balanced (grammarSummary op cl g i) ↔
      (wordSummary op cl (g.words i)).net = 0 ∧
      safeFrom 0 ((g.words i).map (charWeight op cl)) := by
  rw [grammarSummary_correct]
  exact MAISO11.FragmentBalance.balanced_iff _

/-- Executable bottom-up table: every definition contributes exactly one
stored summary. Earlier entries are reused by vector indexing. -/
def cachedGrammarSummary {b n : Nat} (op cl : Fin b) :
    MAISO11.Quotation.Grammar b n → Vector Summary n
  | .nil => Vector.ofFn Fin.elim0
  | .snoc g f =>
      let old := cachedGrammarSummary op cl g
      old.push (fragmentSummary op cl (fun i => old[i]) f)

theorem cachedGrammarSummary_correct {b n : Nat} (op cl : Fin b)
    (g : MAISO11.Quotation.Grammar b n) (i : Fin n) :
    (cachedGrammarSummary op cl g)[i] = wordSummary op cl (g.words i) := by
  induction g with
  | nil => exact Fin.elim0 i
  | @snoc n g f ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [cachedGrammarSummary,Fin.getElem_fin,Fin.val_last,
        Vector.getElem_push_eq,MAISO11.Quotation.Grammar.words,
        Fin.lastCases_last]
      have he : (fun j => (cachedGrammarSummary op cl g)[j]) =
          (fun j => wordSummary op cl (g.words j)) := funext ih
      change fragmentSummary op cl
        (fun j => (cachedGrammarSummary op cl g)[j]) f =
          wordSummary op cl (MAISO11.Quotation.expandFragment g.words f)
      rw [he,fragmentSummary_correct]
    · simp only [cachedGrammarSummary,MAISO11.Quotation.Grammar.words,
        Fin.lastCases_castSucc]
      simpa using ih j

theorem cachedGrammarBalanced_iff {b n : Nat} (op cl : Fin b)
    (g : MAISO11.Quotation.Grammar b n) (i : Fin n) :
    balanced ((cachedGrammarSummary op cl g)[i]) ↔
      (wordSummary op cl (g.words i)).net = 0 ∧
      safeFrom 0 ((g.words i).map (charWeight op cl)) := by
  rw [cachedGrammarSummary_correct]
  exact MAISO11.FragmentBalance.balanced_iff _

#print axioms Summary.join_assoc
#print axioms summarize_append
#print axioms safeFrom_iff
#print axioms FragmentGraph.compute_correct
#print axioms FragmentGraph.balanced_iff
#print axioms grammarSummary_correct
#print axioms grammarBalanced_iff
#print axioms cachedGrammarSummary_correct
#print axioms cachedGrammarBalanced_iff
end MAISO11.FragmentBalance

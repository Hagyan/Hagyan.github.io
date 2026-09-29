import FragmentBalance
import GraphDepthBarrier
set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.FragmentFamily
open MAISO11.Quotation
open MAISO11.Shared

def opening : Fin 3 := ⟨0,by decide⟩
def closing : Fin 3 := ⟨1,by decide⟩
def neutral : Fin 3 := ⟨2,by decide⟩

/-- The two live fragments are the opening and closing halves of a term.
Neither half is required to be a well-formed term. -/
structure Pair where
  count : Nat
  grammar : Grammar 3 count
  opener : Fin count
  closer : Fin count

def base : Pair :=
  ⟨2,.snoc (.snoc .nil [.char opening]) [.char closing],
    Fin.castSucc (Fin.last 0),Fin.last 1⟩

def double (p : Pair) : Pair :=
  let left := Grammar.snoc p.grammar [.use p.opener,.use p.opener]
  let both := Grammar.snoc left
    [.use p.closer.castSucc,.use p.closer.castSucc]
  ⟨p.count+2,both,(Fin.last p.count).castSucc,Fin.last (p.count+1)⟩

theorem double_prefix (p : Pair) :
    (double p).grammar.words (double p).opener =
      p.grammar.words p.opener ++ p.grammar.words p.opener := by
  simp [double,Grammar.words,expandFragment,Atom.expand]

theorem double_suffix (p : Pair) :
    (double p).grammar.words (double p).closer =
      p.grammar.words p.closer ++ p.grammar.words p.closer := by
  simp [double,Grammar.words,expandFragment,Atom.expand]

theorem double_mass (p : Pair) :
    (double p).grammar.mass = p.grammar.mass + 6 := by
  simp [double,Grammar.mass]

def family : Nat → Pair
  | 0 => base
  | n+1 => double (family n)

theorem family_prefix (n : Nat) :
    (family n).grammar.words (family n).opener =
      List.replicate (2^n) opening := by
  induction n with
  | zero =>
    change (Grammar.snoc (Grammar.snoc (Grammar.nil : Grammar 3 0)
      [.char opening]) [.char closing]).words (Fin.castSucc (Fin.last 0)) =
        [opening]
    simp only [Grammar.words,Fin.lastCases_castSucc,Fin.lastCases_last,
      expandFragment,Atom.expand,List.nil_append,List.append_nil]
  | succ n ih =>
    rw [family,double_prefix,ih]
    rw [List.replicate_append_replicate]
    simp [Nat.pow_succ]
    omega

theorem family_suffix (n : Nat) :
    (family n).grammar.words (family n).closer =
      List.replicate (2^n) closing := by
  induction n with
  | zero =>
    change (Grammar.snoc (Grammar.snoc (Grammar.nil : Grammar 3 0)
      [.char opening]) [.char closing]).words (Fin.last 1) =
        [closing]
    simp only [Grammar.words,Fin.lastCases_castSucc,Fin.lastCases_last,
      expandFragment,Atom.expand,List.nil_append,List.append_nil]
  | succ n ih =>
    rw [family,double_suffix,ih]
    rw [List.replicate_append_replicate]
    simp [Nat.pow_succ]
    omega

theorem family_mass (n : Nat) :
    (family n).grammar.mass = 4 + 6*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [family,double_mass,ih]
    omega

/-- This valid final word can be produced from two incomplete fragments.
The neutral symbol plays the role of the zero term. -/
def finalWord (n : Nat) : Word 3 :=
  expandFragment (family n).grammar.words
    [.use (family n).opener,.char neutral,.use (family n).closer]

theorem finalWord_eq (n : Nat) :
    finalWord n = List.replicate (2^n) opening ++
      [neutral] ++ List.replicate (2^n) closing := by
  simp [finalWord,expandFragment,Atom.expand,family_prefix,family_suffix]

theorem finalWord_length (n : Nat) :
    (finalWord n).length = 2 * 2^n + 1 := by
  rw [finalWord_eq]
  simp
  omega

/-- A fixed wire rendering of a unary spine: one opening token per node,
then the zero token, then one closing token per node. -/
def renderSpine : Nat → Word 3
  | 0 => [neutral]
  | m+1 => opening :: (renderSpine m ++ [closing])

theorem renderSpine_eq (m : Nat) :
    renderSpine m = List.replicate m opening ++
      [neutral] ++ List.replicate m closing := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [renderSpine,ih,List.replicate_succ,List.cons_append]
    simp [List.append_assoc]
    rw [← List.replicate_succ',List.replicate_succ]

theorem finalWord_renderSpine (n : Nat) :
    finalWord n = renderSpine (2^n) := by
  rw [finalWord_eq,renderSpine_eq]

/-- The raw grammar has linear atom mass and prints a unary spine of
exponential depth. Every ordinary constructor DAG denoting that term has
exponentially many nodes. The stipulated unary-token rendering is explicit
above; no full PA-bin file parser is assumed. -/
theorem fragment_dag_gap {m : Nat} (n : Nat)
    (g : Graph m) (i : Fin m)
    (h : g.expand i = unarySpine (2^n)) :
    (family n).grammar.mass = 4 + 6*n ∧
    finalWord n = renderSpine (2^n) ∧
    2^n+1 ≤ m := by
  exact ⟨family_mass n,finalWord_renderSpine n,
    unarySpine_graph_lower_bound g i h⟩

#print axioms family_prefix
#print axioms family_suffix
#print axioms finalWord_eq
#print axioms family_mass
#print axioms finalWord_length
#print axioms finalWord_renderSpine
#print axioms fragment_dag_gap
end MAISO11.FragmentFamily

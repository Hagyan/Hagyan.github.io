import CompressionBarrier
set_option autoImplicit false
set_option warningAsError true
namespace MAISO11.Shared
open Quotation

/-- A node refers only to earlier nodes. Constructor identity is syntactic,
not equality of the natural numbers denoted by the terms. -/
inductive Node (n : Nat) where
  | zero
  | bit0 : Fin n → Node n
  | bit1 : Fin n → Node n
  | add : Fin n → Fin n → Node n
  | mul : Fin n → Fin n → Node n
  deriving Repr

def Node.map {n m : Nat} (ρ : Fin n → Fin m) : Node n → Node m
  | .zero => .zero
  | .bit0 i => .bit0 (ρ i)
  | .bit1 i => .bit1 (ρ i)
  | .add i j => .add (ρ i) (ρ j)
  | .mul i j => .mul (ρ i) (ρ j)

def Node.expand {n : Nat} (env : Fin n → ClosedTerm) : Node n → ClosedTerm
  | .zero => .zero
  | .bit0 i => .bit0 (env i)
  | .bit1 i => .bit1 (env i)
  | .add i j => .add (env i) (env j)
  | .mul i j => .mul (env i) (env j)

theorem Node.expand_map {n m : Nat} (ρ : Fin n → Fin m)
    (env : Fin m → ClosedTerm) (a : Node n) :
    (a.map ρ).expand env = a.expand (fun i => env (ρ i)) := by
  cases a <;> rfl

def Node.same {n : Nat} (eq : Fin n → Fin n → Bool) : Node n → Node n → Bool
  | .zero,.zero => true
  | .bit0 i,.bit0 j | .bit1 i,.bit1 j => eq i j
  | .add i j,.add k l | .mul i j,.mul k l => eq i k && eq j l
  | _,_ => false

theorem Node.same_iff {n : Nat} (env : Fin n → ClosedTerm)
    (eq : Fin n → Fin n → Bool)
    (h : ∀ i j, eq i j = true ↔ env i = env j) (a b : Node n) :
    a.same eq b = true ↔ a.expand env = b.expand env := by
  cases a <;> cases b <;> simp [same,expand,h]

inductive Graph : Nat → Type where
  | nil : Graph 0
  | snoc {n : Nat} : Graph n → Node n → Graph (n+1)
  deriving Repr

def Graph.expand {n : Nat} : Graph n → Fin n → ClosedTerm
  | .nil => Fin.elim0
  | .snoc g a => Fin.lastCases (a.expand g.expand) g.expand

/-- Direct constant-branch index case analysis, with the last branch delayed.
Fin.lastCases is a logical eliminator implemented using reverse induction;
it is deliberately avoided in this executable lookup path. -/
def splitLast {α : Type} {n : Nat} (last : Unit → α)
    (earlier : Fin n → α) (i : Fin (n+1)) : α :=
  if h : i.val < n then earlier ⟨i.val,h⟩ else last ()

@[simp] theorem splitLast_last {α : Type} {n : Nat} (last : Unit → α)
    (earlier : Fin n → α) : splitLast last earlier (Fin.last n) = last () := by
  simp [splitLast]

@[simp] theorem splitLast_castSucc {α : Type} {n : Nat} (last : Unit → α)
    (earlier : Fin n → α) (i : Fin n) : splitLast last earlier i.castSucc = earlier i := by
  simp [splitLast,i.isLt]

def Graph.node {n : Nat} : Graph n → Fin n → Node n
  | .nil => Fin.elim0
  | .snoc g a => splitLast (fun _ => a.map Fin.castSucc)
      (fun i => (g.node i).map Fin.castSucc)

theorem Graph.node_expand {n : Nat} (g : Graph n) (i : Fin n) :
    (g.node i).expand g.expand = g.expand i := by
  induction g with
  | nil => exact Fin.elim0 i
  | @snoc n g a ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [node,expand,splitLast_last,Fin.lastCases_last,Node.expand_map,Fin.lastCases_castSucc]
    · simpa only [node,expand,splitLast_castSucc,Fin.lastCases_castSucc,Node.expand_map] using ih j

theorem vector_ofFn_get {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f)[i] = f i := by
  simp only [Fin.getElem_fin,Vector.getElem_ofFn]

/-- A materialized table, not a recursive equality function that recomputes
child comparisons. Old rows are copied; new comparisons consult the old table. -/
def Graph.table {n : Nat} : Graph n → Vector (Vector Bool n) n
  | .nil => Vector.ofFn Fin.elim0
  | .snoc g a =>
    let old := g.table
    Vector.ofFn fun i => Vector.ofFn fun j =>
      splitLast
        (fun _ => splitLast (fun _ => true)
          (fun b => a.same (fun x y => old[x][y]) (g.node b)) j)
        (fun b => splitLast
          (fun _ => (g.node b).same (fun x y => old[x][y]) a)
          (fun c => old[b][c]) j) i

theorem Graph.table_iff {n : Nat} (g : Graph n) (i j : Fin n) :
    g.table[i][j] = true ↔ g.expand i = g.expand j := by
  induction g with
  | nil => exact Fin.elim0 i
  | @snoc n g a ih =>
    refine Fin.lastCases ?_ (fun x => ?_) i
    · refine Fin.lastCases ?_ (fun y => ?_) j
      · simp only [table,vector_ofFn_get,splitLast_last,splitLast_castSucc,Fin.lastCases_last,expand]
      · simpa only [table,vector_ofFn_get,splitLast_last,splitLast_castSucc,Fin.lastCases_last,
          Fin.lastCases_castSucc,expand,Graph.node_expand] using
          Node.same_iff g.expand (fun x y => g.table[x][y]) ih a (g.node y)
    · refine Fin.lastCases ?_ (fun y => ?_) j
      · simpa only [table,vector_ofFn_get,splitLast_last,splitLast_castSucc,Fin.lastCases_last,
          Fin.lastCases_castSucc,expand,Graph.node_expand] using
          Node.same_iff g.expand (fun x y => g.table[x][y]) ih (g.node x) a
      · simpa only [table,vector_ofFn_get,splitLast_last,splitLast_castSucc,Fin.lastCases_castSucc,expand] using ih x y

/-- Number of calls to Node.same made in the table construction: two per
old node at each extension. This counts logical comparisons, not CPU time. -/
def comparisonCalls : Nat → Nat
  | 0 => 0
  | n+1 => comparisonCalls n + 2*n

theorem comparisonCalls_exact (n : Nat) : comparisonCalls n+n = n*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [comparisonCalls,Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
    omega

/-- Every newly constructed matrix writes (n+1)^2 entries, including copies.
The sum of these entry counts is bounded cubically. -/
def tableWrites : Nat → Nat
  | 0 => 0
  | n+1 => tableWrites n+(n+1)*(n+1)

theorem tableWrites_cubic (n : Nat) : tableWrites n ≤ n*n*n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    simp only [tableWrites,Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
    have hp : 0 ≤ n*n := Nat.zero_le _
    omega

def doublingGraph : (n : Nat) → Graph (n+1)
  | 0 => .snoc .nil .zero
  | n+1 => .snoc (doublingGraph n) (.add (Fin.last n) (Fin.last n))

theorem doublingGraph_expansion (n : Nat) :
    (doublingGraph n).expand (Fin.last n) = doubledTree n := by
  induction n with
  | zero => simp only [doublingGraph,Graph.expand,Fin.lastCases_last,Node.expand,doubledTree]
  | succ n ih => simp only [doublingGraph,Graph.expand,Fin.lastCases_last,Node.expand,doubledTree,ih]

/-- This graph shares the exact expansion already certified for our serialized
definition family; it does not materialize that expanded tree. -/
theorem doublingGraph_matches_definitions (n : Nat) :
    (doublingGraph n).expand (Fin.last n) =
      (doublingProgram n).expansion Fin.elim0 (Fin.last n) := by
  rw [doublingGraph_expansion,doublingProgram_expansion]

/-- Add a second copy of the latest root, referencing the same earlier node. -/
def duplicateRoot (n : Nat) : Graph (n+3) :=
  .snoc (doublingGraph (n+1))
    (.add (Fin.last n).castSucc (Fin.last n).castSucc)

theorem duplicateRoot_equal (n : Nat) :
    (duplicateRoot n).table[(Fin.last (n+1)).castSucc][Fin.last (n+2)] = true := by
  apply ((duplicateRoot n).table_iff _ _).mpr
  simp only [duplicateRoot,Graph.expand,Fin.lastCases_castSucc,Fin.lastCases_last]
  simp only [doublingGraph,Graph.expand,Fin.lastCases_castSucc,Fin.lastCases_last,Node.expand]

/-- Comparison against zero rejects the structurally larger addition tree,
even though every term in this example denotes the number zero. -/
theorem doublingGraph_not_zero (n : Nat) :
    (doublingGraph (n+1)).table[(⟨0,by omega⟩ : Fin (n+2))][Fin.last (n+1)] = false := by
  have hroot := doublingGraph_expansion (n+1)
  have hzero : ∀ m, (doublingGraph m).expand ⟨0,by omega⟩ = .zero := by
    intro m
    induction m with
    | zero =>
      change (Graph.snoc Graph.nil Node.zero).expand (Fin.last 0) = _
      simp only [Graph.expand,Fin.lastCases_last,Node.expand]
    | succ m ih =>
      have hi : (⟨0,by omega⟩ : Fin (m+2)) = (⟨0,by omega⟩ : Fin (m+1)).castSucc := rfl
      rw [hi]
      simpa only [doublingGraph,Graph.expand,Fin.lastCases_castSucc] using ih
  have hn : ¬ (doublingGraph (n+1)).table[(⟨0,by omega⟩ : Fin (n+2))][Fin.last (n+1)] = true := by
    intro h
    have he := ((doublingGraph (n+1)).table_iff _ _).mp h
    rw [hzero,hroot] at he
    cases he
  exact Bool.eq_false_iff.mpr hn

theorem duplicateRoot_expanded_nodes (n : Nat) :
    ((duplicateRoot n).expand (Fin.last (n+2))).treeNodes+1 = 2^(n+2) := by
  have he := ((duplicateRoot n).table_iff (Fin.last (n+1)).castSucc (Fin.last (n+2))).mp
    (duplicateRoot_equal n)
  rw [← he]
  simp only [duplicateRoot,Graph.expand,Fin.lastCases_castSucc,doublingGraph_expansion]
  exact doubledTree_nodes (n+1)
end MAISO11.Shared

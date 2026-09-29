import GraphCompiler

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Shared
open MAISO11.Arithmetic MAISO11.Quotation MAISO11.Wire

end MAISO11.Shared

namespace MAISO11.Wire
open MAISO11.Arithmetic MAISO11.Quotation

/-- Interpret a compact term in an arbitrary open-term environment. Compact
abbreviation references are normally closed, but a compiler may temporarily
map them to roots in a graph that also contains bound-variable nodes. -/
def CTerm.evalOpen {r m : Nat} (env : Fin r → Term m) :
    CTerm r m → Term m
  | .var i => .var i
  | .ref i => env i
  | .zero => .zero
  | .bit0 t => .bit0 (t.evalOpen env)
  | .bit1 t => .bit1 (t.evalOpen env)
  | .add s t => .add (s.evalOpen env) (t.evalOpen env)
  | .mul s t => .mul (s.evalOpen env) (t.evalOpen env)

theorem CTerm.evalOpen_ofClosed {r m : Nat} (δ : Fin r → ClosedTerm)
    (t : CTerm r m) :
    t.evalOpen (fun i => Term.ofClosed (δ i)) = t.expand δ := by
  induction t <;> simp [evalOpen,CTerm.expand, *]

end MAISO11.Wire

namespace MAISO11.Shared
open MAISO11.Arithmetic MAISO11.Quotation MAISO11.Wire

/-- A node in a DAG for terms with `m` free variables. Variable leaves carry
their de Bruijn index; all other children refer to earlier graph nodes. -/
inductive OpenNode (m n : Nat) where
  | var : Fin m → OpenNode m n
  | zero
  | bit0 : Fin n → OpenNode m n
  | bit1 : Fin n → OpenNode m n
  | add : Fin n → Fin n → OpenNode m n
  | mul : Fin n → Fin n → OpenNode m n
  deriving Repr

def OpenNode.map {m n k : Nat} (ρ : Fin n → Fin k) :
    OpenNode m n → OpenNode m k
  | .var i => .var i
  | .zero => .zero
  | .bit0 i => .bit0 (ρ i)
  | .bit1 i => .bit1 (ρ i)
  | .add i j => .add (ρ i) (ρ j)
  | .mul i j => .mul (ρ i) (ρ j)

def OpenNode.expand {m n : Nat} (env : Fin n → Term m) :
    OpenNode m n → Term m
  | .var i => .var i
  | .zero => .zero
  | .bit0 i => .bit0 (env i)
  | .bit1 i => .bit1 (env i)
  | .add i j => .add (env i) (env j)
  | .mul i j => .mul (env i) (env j)

theorem OpenNode.expand_map {m n k : Nat} (ρ : Fin n → Fin k)
    (env : Fin k → Term m) (a : OpenNode m n) :
    (a.map ρ).expand env = a.expand (fun i => env (ρ i)) := by
  cases a <;> rfl

def OpenNode.same {m n : Nat} (eq : Fin n → Fin n → Bool) :
    OpenNode m n → OpenNode m n → Bool
  | .var i,.var j => decide (i = j)
  | .zero,.zero => true
  | .bit0 i,.bit0 j | .bit1 i,.bit1 j => eq i j
  | .add i j,.add k l | .mul i j,.mul k l => eq i k && eq j l
  | _,_ => false

theorem OpenNode.same_iff {m n : Nat} (env : Fin n → Term m)
    (eq : Fin n → Fin n → Bool)
    (h : ∀ i j, eq i j = true ↔ env i = env j)
    (a b : OpenNode m n) :
    a.same eq b = true ↔ a.expand env = b.expand env := by
  cases a <;> cases b <;> simp [same,expand,h]

inductive OpenGraph (m : Nat) : Nat → Type where
  | nil : OpenGraph m 0
  | snoc {n : Nat} : OpenGraph m n → OpenNode m n → OpenGraph m (n+1)
  deriving Repr

def OpenGraph.expand {m n : Nat} : OpenGraph m n → Fin n → Term m
  | .nil => Fin.elim0
  | .snoc g a => Fin.lastCases (a.expand g.expand) g.expand

def OpenGraph.node {m n : Nat} : OpenGraph m n → Fin n → OpenNode m n
  | .nil => Fin.elim0
  | .snoc g a => splitLast (fun _ => a.map Fin.castSucc)
      (fun i => (g.node i).map Fin.castSucc)

theorem OpenGraph.node_expand {m n : Nat} (g : OpenGraph m n) (i : Fin n) :
    (g.node i).expand g.expand = g.expand i := by
  induction g with
  | nil => exact Fin.elim0 i
  | @snoc n g a ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [node,expand,splitLast_last,Fin.lastCases_last,
        Fin.lastCases_castSucc,OpenNode.expand_map]
    · simpa only [node,expand,splitLast_castSucc,Fin.lastCases_castSucc,
        OpenNode.expand_map] using ih j

def OpenGraph.table {m n : Nat} : OpenGraph m n → Vector (Vector Bool n) n
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

theorem OpenGraph.table_iff {m n : Nat} (g : OpenGraph m n)
    (i j : Fin n) :
    g.table[i][j] = true ↔ g.expand i = g.expand j := by
  induction g with
  | nil => exact Fin.elim0 i
  | @snoc n g a ih =>
    refine Fin.lastCases ?_ (fun x => ?_) i
    · refine Fin.lastCases ?_ (fun y => ?_) j
      · simp only [table,vector_ofFn_get,splitLast_last,splitLast_castSucc,
          Fin.lastCases_last,expand]
      · simpa only [table,vector_ofFn_get,splitLast_last,splitLast_castSucc,
          Fin.lastCases_last,Fin.lastCases_castSucc,expand,OpenGraph.node_expand] using
          OpenNode.same_iff g.expand (fun x y => g.table[x][y]) ih a (g.node y)
    · refine Fin.lastCases ?_ (fun y => ?_) j
      · simpa only [table,vector_ofFn_get,splitLast_last,splitLast_castSucc,
          Fin.lastCases_last,Fin.lastCases_castSucc,expand,OpenGraph.node_expand] using
          OpenNode.same_iff g.expand (fun x y => g.table[x][y]) ih (g.node x) a
      · simpa only [table,vector_ofFn_get,splitLast_last,splitLast_castSucc,
          Fin.lastCases_castSucc,expand] using ih x y

def embedClosedNode {m n : Nat} (a : Node n) : OpenNode m n :=
  match a with
  | .zero => .zero
  | .bit0 i => .bit0 i
  | .bit1 i => .bit1 i
  | .add i j => .add i j
  | .mul i j => .mul i j

def embedClosedGraph {m n : Nat} : Graph n → OpenGraph m n
  | .nil => .nil
  | .snoc g a => .snoc (embedClosedGraph g) (embedClosedNode a)

theorem embedClosedGraph_expand {m n : Nat} (g : Graph n) (i : Fin n) :
    (embedClosedGraph (m:=m) g).expand i = Term.ofClosed (g.expand i) := by
  induction g with
  | nil => exact Fin.elim0 i
  | @snoc n g a ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [embedClosedGraph,OpenGraph.expand,Graph.expand,
        Fin.lastCases_last]
      cases a <;> simp [embedClosedNode,OpenNode.expand,Node.expand,
        Term.ofClosed,ih]
    · simp only [embedClosedGraph,OpenGraph.expand,Graph.expand,
        Fin.lastCases_castSucc]
      rw [ih j]

structure OpenTermResult (m n : Nat) where
  size : Nat
  graph : OpenGraph m size
  lift : Fin n → Fin size
  root : Fin size

def compileOpenTerm {r m n : Nat} (g : OpenGraph m n)
    (refs : Fin r → Fin n) : CTerm r m → OpenTermResult m n
  | .var i => ⟨n+1,.snoc g (.var i),Fin.castSucc,Fin.last n⟩
  | .ref i => ⟨n,g,id,refs i⟩
  | .zero => ⟨n+1,.snoc g .zero,Fin.castSucc,Fin.last n⟩
  | .bit0 t =>
      let a := compileOpenTerm g refs t
      ⟨a.size+1,.snoc a.graph (.bit0 a.root),
        fun i => (a.lift i).castSucc,Fin.last a.size⟩
  | .bit1 t =>
      let a := compileOpenTerm g refs t
      ⟨a.size+1,.snoc a.graph (.bit1 a.root),
        fun i => (a.lift i).castSucc,Fin.last a.size⟩
  | .add s t =>
      let a := compileOpenTerm g refs s
      let b := compileOpenTerm a.graph (fun i => a.lift (refs i)) t
      ⟨b.size+1,.snoc b.graph (.add (b.lift a.root) b.root),
        fun i => (b.lift (a.lift i)).castSucc,Fin.last b.size⟩
  | .mul s t =>
      let a := compileOpenTerm g refs s
      let b := compileOpenTerm a.graph (fun i => a.lift (refs i)) t
      ⟨b.size+1,.snoc b.graph (.mul (b.lift a.root) b.root),
        fun i => (b.lift (a.lift i)).castSucc,Fin.last b.size⟩

def openTermNodes {r m : Nat} : CTerm r m → Nat
  | .var _ => 1
  | .ref _ => 0
  | .zero => 1
  | .bit0 t | .bit1 t => openTermNodes t + 1
  | .add s t | .mul s t => openTermNodes s + openTermNodes t + 1

theorem openTermNodes_le_weight {r m : Nat} (t : CTerm r m) :
    openTermNodes t ≤ t.weight := by
  induction t with
  | var i => simp [openTermNodes,CTerm.weight]
  | ref i => simp [openTermNodes,CTerm.weight]
  | zero => simp [openTermNodes,CTerm.weight]
  | bit0 t ih => simp [openTermNodes,CTerm.weight] at *; omega
  | bit1 t ih => simp [openTermNodes,CTerm.weight] at *; omega
  | add s t hs ht => simp [openTermNodes,CTerm.weight] at *; omega
  | mul s t hs ht => simp [openTermNodes,CTerm.weight] at *; omega

theorem compileOpenTerm_size {r m n : Nat} (g : OpenGraph m n)
    (refs : Fin r → Fin n) (t : CTerm r m) :
    (compileOpenTerm g refs t).size = n + openTermNodes t := by
  induction t generalizing n with
  | var i => rfl
  | ref i => rfl
  | zero => rfl
  | bit0 t ih => simp [compileOpenTerm,openTermNodes,ih,Nat.add_assoc]
  | bit1 t ih => simp [compileOpenTerm,openTermNodes,ih,Nat.add_assoc]
  | add s t hs ht => simp [compileOpenTerm,openTermNodes,hs,ht,Nat.add_assoc]
  | mul s t hs ht => simp [compileOpenTerm,openTermNodes,hs,ht,Nat.add_assoc]

theorem compileOpenTerm_correct {r m n : Nat} (g : OpenGraph m n)
    (refs : Fin r → Fin n) (t : CTerm r m) :
    (∀ i, (compileOpenTerm g refs t).graph.expand
        ((compileOpenTerm g refs t).lift i) = g.expand i) ∧
    (compileOpenTerm g refs t).graph.expand (compileOpenTerm g refs t).root =
      t.evalOpen (fun i => g.expand (refs i)) := by
  induction t generalizing n with
  | var i =>
    constructor
    · intro j
      simp [compileOpenTerm,OpenGraph.expand,OpenNode.expand]
    · simp [compileOpenTerm,OpenGraph.expand,OpenNode.expand,CTerm.evalOpen]
  | ref i => exact ⟨fun _ => rfl,rfl⟩
  | zero =>
    constructor
    · intro i
      simp [compileOpenTerm,OpenGraph.expand,OpenNode.expand]
    · simp [compileOpenTerm,OpenGraph.expand,OpenNode.expand,CTerm.evalOpen]
  | bit0 t ih =>
    obtain ⟨hp,hr⟩ := ih g refs
    constructor
    · intro i
      simpa only [compileOpenTerm,OpenGraph.expand,Fin.lastCases_castSucc] using hp i
    · simp only [compileOpenTerm,OpenGraph.expand,Fin.lastCases_last,
        OpenNode.expand,CTerm.evalOpen,hr]
  | bit1 t ih =>
    obtain ⟨hp,hr⟩ := ih g refs
    constructor
    · intro i
      simpa only [compileOpenTerm,OpenGraph.expand,Fin.lastCases_castSucc] using hp i
    · simp only [compileOpenTerm,OpenGraph.expand,Fin.lastCases_last,
        OpenNode.expand,CTerm.evalOpen,hr]
  | add s t hs ht =>
    obtain ⟨hsp,hsr⟩ := hs g refs
    obtain ⟨htp,htr⟩ := ht (compileOpenTerm g refs s).graph
      (fun i => (compileOpenTerm g refs s).lift (refs i))
    have he : (fun i => (compileOpenTerm g refs s).graph.expand
        ((compileOpenTerm g refs s).lift (refs i))) =
        (fun i => g.expand (refs i)) := funext (fun i => hsp (refs i))
    constructor
    · intro i
      simp only [compileOpenTerm,OpenGraph.expand,Fin.lastCases_castSucc]
      exact (htp _).trans (hsp i)
    · simp only [compileOpenTerm,OpenGraph.expand,Fin.lastCases_last,
        OpenNode.expand,CTerm.evalOpen]
      rw [htp,hsr,htr,he]
  | mul s t hs ht =>
    obtain ⟨hsp,hsr⟩ := hs g refs
    obtain ⟨htp,htr⟩ := ht (compileOpenTerm g refs s).graph
      (fun i => (compileOpenTerm g refs s).lift (refs i))
    have he : (fun i => (compileOpenTerm g refs s).graph.expand
        ((compileOpenTerm g refs s).lift (refs i))) =
        (fun i => g.expand (refs i)) := funext (fun i => hsp (refs i))
    constructor
    · intro i
      simp only [compileOpenTerm,OpenGraph.expand,Fin.lastCases_castSucc]
      exact (htp _).trans (hsp i)
    · simp only [compileOpenTerm,OpenGraph.expand,Fin.lastCases_last,
        OpenNode.expand,CTerm.evalOpen]
      rw [htp,hsr,htr,he]

/-- Compare arbitrary compact terms, including terms beneath quantifiers, by
compiling both to one variable-labelled DAG and consulting its exact equality
table. -/
def sharedOpenEqual {r n m : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (s t : CTerm r m) : Bool :=
  let base := embedClosedGraph (m:=m) g
  let a := compileOpenTerm base refs s
  let b := compileOpenTerm a.graph (fun i => a.lift (refs i)) t
  b.graph.table[(b.lift a.root)][b.root]

theorem sharedOpenEqual_correct {r n m : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (s t : CTerm r m) :
    sharedOpenEqual g refs s t = true ↔
      s.expand (fun i => g.expand (refs i)) =
        t.expand (fun i => g.expand (refs i)) := by
  unfold sharedOpenEqual
  let base := embedClosedGraph (m:=m) g
  let a := compileOpenTerm base refs s
  let b := compileOpenTerm a.graph (fun i => a.lift (refs i)) t
  have hA := compileOpenTerm_correct base refs s
  have hB := compileOpenTerm_correct a.graph (fun i => a.lift (refs i)) t
  have hBprev := hB.1 a.root
  have hrefs : (fun i => a.graph.expand (a.lift (refs i))) =
      (fun i => Term.ofClosed (g.expand (refs i))) := by
    funext i
    calc
      a.graph.expand (a.lift (refs i)) = base.expand (refs i) := hA.1 _
      _ = Term.ofClosed (g.expand (refs i)) := embedClosedGraph_expand g (refs i)
  have hbase : (fun i => base.expand (refs i)) =
      (fun i => Term.ofClosed (g.expand (refs i))) := funext (fun i =>
        embedClosedGraph_expand g (refs i))
  rw [OpenGraph.table_iff]
  rw [hBprev,hA.2,hB.2,hbase,hrefs]
  rw [CTerm.evalOpen_ofClosed (fun i => g.expand (refs i)) s,
    CTerm.evalOpen_ofClosed (fun i => g.expand (refs i)) t]

end MAISO11.Shared

import SharedPrelude
import DagEquality
set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Shared
open MAISO11.Quotation MAISO11.Wire

/-- The new graph keeps all old roots, via `lift`, and supplies a new root.
All fields are compact graph data; none is an expanded arithmetic term. -/
structure TermResult (n : Nat) where
  size : Nat
  graph : Graph size
  lift : Fin n → Fin size
  root : Fin size

/-- Compile a closed compact term into an extension of an existing graph.
A reference reuses its root and allocates no node. Other constructors allocate
exactly one node after compiling their immediate subterms. -/
def compileTerm {r n : Nat} (g : Graph n) (refs : Fin r → Fin n) :
    CTerm r 0 → TermResult n
  | .var i => Fin.elim0 i
  | .ref i => ⟨n,g,id,refs i⟩
  | .zero => ⟨n+1,.snoc g .zero,Fin.castSucc,Fin.last n⟩
  | .bit0 t =>
      let a := compileTerm g refs t
      ⟨a.size+1,.snoc a.graph (.bit0 a.root),
        fun i => (a.lift i).castSucc,Fin.last a.size⟩
  | .bit1 t =>
      let a := compileTerm g refs t
      ⟨a.size+1,.snoc a.graph (.bit1 a.root),
        fun i => (a.lift i).castSucc,Fin.last a.size⟩
  | .add s t =>
      let a := compileTerm g refs s
      let b := compileTerm a.graph (fun i => a.lift (refs i)) t
      ⟨b.size+1,.snoc b.graph (.add (b.lift a.root) b.root),
        fun i => (b.lift (a.lift i)).castSucc,Fin.last b.size⟩
  | .mul s t =>
      let a := compileTerm g refs s
      let b := compileTerm a.graph (fun i => a.lift (refs i)) t
      ⟨b.size+1,.snoc b.graph (.mul (b.lift a.root) b.root),
        fun i => (b.lift (a.lift i)).castSucc,Fin.last b.size⟩

/-- The compiler preserves every earlier root and gives the new root exactly
the source term's expanded *syntax*, not just the same numerical value. -/
theorem compileTerm_correct {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (t : CTerm r 0) :
    (∀ i, (compileTerm g refs t).graph.expand
        ((compileTerm g refs t).lift i) = g.expand i) ∧
    (compileTerm g refs t).graph.expand (compileTerm g refs t).root =
      t.close (fun i => g.expand (refs i)) := by
  induction t generalizing n with
  | var i => exact Fin.elim0 i
  | ref i => exact ⟨fun _ => rfl,rfl⟩
  | zero =>
    constructor
    · intro i
      simp [compileTerm,Graph.expand]
    · simp [compileTerm,Graph.expand,Node.expand,CTerm.close]
  | bit0 t ih =>
    obtain ⟨hp,hr⟩ := ih g refs
    constructor
    · intro i
      simpa only [compileTerm,Graph.expand,Fin.lastCases_castSucc] using hp i
    · simp only [compileTerm,Graph.expand,Fin.lastCases_last,Node.expand,
        CTerm.close,hr]
  | bit1 t ih =>
    obtain ⟨hp,hr⟩ := ih g refs
    constructor
    · intro i
      simpa only [compileTerm,Graph.expand,Fin.lastCases_castSucc] using hp i
    · simp only [compileTerm,Graph.expand,Fin.lastCases_last,Node.expand,
        CTerm.close,hr]
  | add s t hs ht =>
    obtain ⟨hsp,hsr⟩ := hs g refs
    obtain ⟨htp,htr⟩ := ht (compileTerm g refs s).graph
      (fun i => (compileTerm g refs s).lift (refs i))
    have he : (fun i => (compileTerm g refs s).graph.expand
        ((compileTerm g refs s).lift (refs i))) =
        (fun i => g.expand (refs i)) := funext (fun i => hsp (refs i))
    constructor
    · intro i
      simp only [compileTerm,Graph.expand,Fin.lastCases_castSucc]
      exact (htp _).trans (hsp i)
    · simp only [compileTerm,Graph.expand,Fin.lastCases_last,Node.expand,
        CTerm.close]
      rw [htp,hsr,htr,he]
  | mul s t hs ht =>
    obtain ⟨hsp,hsr⟩ := hs g refs
    obtain ⟨htp,htr⟩ := ht (compileTerm g refs s).graph
      (fun i => (compileTerm g refs s).lift (refs i))
    have he : (fun i => (compileTerm g refs s).graph.expand
        ((compileTerm g refs s).lift (refs i))) =
        (fun i => g.expand (refs i)) := funext (fun i => hsp (refs i))
    constructor
    · intro i
      simp only [compileTerm,Graph.expand,Fin.lastCases_castSucc]
      exact (htp _).trans (hsp i)
    · simp only [compileTerm,Graph.expand,Fin.lastCases_last,Node.expand,
        CTerm.close]
      rw [htp,hsr,htr,he]

theorem compileTerm_preserves {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (t : CTerm r 0) (i : Fin n) :
    (compileTerm g refs t).graph.expand ((compileTerm g refs t).lift i) =
      g.expand i := (compileTerm_correct g refs t).1 i

theorem compileTerm_root {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (t : CTerm r 0) :
    (compileTerm g refs t).graph.expand (compileTerm g refs t).root =
      t.close (fun i => g.expand (refs i)) := (compileTerm_correct g refs t).2

/-- Earlier nodes keep the same numerical index; compilation appends nodes. -/
theorem compileTerm_lift_val {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (t : CTerm r 0) (i : Fin n) :
    ((compileTerm g refs t).lift i).val = i.val := by
  induction t generalizing n with
  | var j => exact Fin.elim0 j
  | ref j => rfl
  | zero => rfl
  | bit0 t ih => simpa only [compileTerm,Fin.coe_castSucc] using ih g refs i
  | bit1 t ih => simpa only [compileTerm,Fin.coe_castSucc] using ih g refs i
  | add s t hs ht =>
    simp only [compileTerm,Fin.coe_castSucc]
    rw [ht,hs]
  | mul s t hs ht =>
    simp only [compileTerm,Fin.coe_castSucc]
    rw [ht,hs]

/-- A source abbreviation reference is literally its existing graph root. -/
theorem compileTerm_ref {r n : Nat} (g : Graph n) (refs : Fin r → Fin n)
    (i : Fin r) : compileTerm g refs (.ref i) = ⟨n,g,id,refs i⟩ := rfl

/-- Number of graph nodes allocated: abbreviation references allocate zero. -/
def termNodes {r : Nat} : CTerm r 0 → Nat
  | .var i => Fin.elim0 i
  | .ref _ => 0
  | .zero => 1
  | .bit0 t | .bit1 t => termNodes t + 1
  | .add s t | .mul s t => termNodes s + termNodes t + 1

theorem termNodes_le_weight {r : Nat} (t : CTerm r 0) :
    termNodes t ≤ t.weight := by
  induction t with
  | var i => exact Fin.elim0 i
  | ref i => simp [termNodes,CTerm.weight]
  | zero => simp [termNodes,CTerm.weight]
  | bit0 t ih => simp [termNodes,CTerm.weight] at *; omega
  | bit1 t ih => simp [termNodes,CTerm.weight] at *; omega
  | add s t hs ht => simp [termNodes,CTerm.weight] at *; omega
  | mul s t hs ht => simp [termNodes,CTerm.weight] at *; omega

theorem compileTerm_size {r n : Nat} (g : Graph n)
    (refs : Fin r → Fin n) (t : CTerm r 0) :
    (compileTerm g refs t).size = n + termNodes t := by
  induction t generalizing n with
  | var i => exact Fin.elim0 i
  | ref i => simp [compileTerm,termNodes]
  | zero => rfl
  | bit0 t ih => simp [compileTerm,termNodes,ih,Nat.add_assoc]
  | bit1 t ih => simp [compileTerm,termNodes,ih,Nat.add_assoc]
  | add s t hs ht => simp [compileTerm,termNodes,hs,ht,Nat.add_assoc]
  | mul s t hs ht => simp [compileTerm,termNodes,hs,ht,Nat.add_assoc]

/-- A compact graph together with one root index for each source definition. -/
structure CompiledDefs (r : Nat) where
  size : Nat
  graph : Graph size
  refs : Fin r → Fin size

def compileDefs : {r : Nat} → CDefs r → CompiledDefs r
  | _, .nil => ⟨0,.nil,Fin.elim0⟩
  | _, .snoc p t =>
      let a := compileDefs p
      let b := compileTerm a.graph a.refs t
      ⟨b.size,b.graph,splitLast (fun _ => b.root)
        (fun i => b.lift (a.refs i))⟩

theorem compileDefs_refines {r : Nat} (p : CDefs r) (i : Fin r) :
    (compileDefs p).graph.expand ((compileDefs p).refs i) = p.expand i := by
  induction p with
  | nil => exact Fin.elim0 i
  | @snoc r p t ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [compileDefs,splitLast_last,CDefs.expand,Fin.lastCases_last]
      rw [compileTerm_root]
      exact congrArg (CTerm.close · t) (funext ih)
    · simp only [compileDefs,splitLast_castSucc,CDefs.expand,Fin.lastCases_castSucc]
      rw [compileTerm_preserves]
      exact ih j

def definitionNodes : {r : Nat} → CDefs r → Nat
  | _, .nil => 0
  | _, .snoc p t => definitionNodes p + termNodes t

theorem compileDefs_size {r : Nat} (p : CDefs r) :
    (compileDefs p).size = definitionNodes p := by
  induction p with
  | nil => rfl
  | snoc p t ih => simp [compileDefs,compileTerm_size,definitionNodes,ih]

theorem definitionNodes_le_mass {r : Nat} (p : CDefs r) :
    definitionNodes p ≤ p.mass := by
  induction p with
  | nil => exact Nat.le_refl 0
  | snoc p t ih =>
    have ht := termNodes_le_weight t
    simp only [definitionNodes,CDefs.mass]
    omega

theorem compileDefs_size_le_wire {r : Nat} (p : CDefs r) :
    (compileDefs p).size ≤ p.wire.length := by
  rw [compileDefs_size]
  exact Nat.le_trans (definitionNodes_le_mass p) p.mass_le_wire

/-- From accepted serialized bytes to a graph whose number of nodes is at
most the input character count. This is not a CPU/bit-complexity claim. -/
theorem compiledPrelude_size_le_input {r : Nat} {cs : List Char}
    {p : CDefs r} (h : parseSharedPrelude r cs = some p) :
    (compileDefs p).size ≤ cs.length := by
  rw [compileDefs_size]
  exact Nat.le_trans (definitionNodes_le_mass p) (parseSharedPrelude_mass_le_input h)

/-- The existing graph equality table now compares roots compiled from any
accepted definition grammar, with exact agreement with expanded syntax. -/
theorem compiledDefs_table_iff {r : Nat} (p : CDefs r) (i j : Fin r) :
    (compileDefs p).graph.table[(compileDefs p).refs i][(compileDefs p).refs j] = true ↔
      p.expand i = p.expand j := by
  rw [Graph.table_iff,compileDefs_refines,compileDefs_refines]

end MAISO11.Shared

import CompactWire
set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Wire
open Arithmetic Quotation

inductive IsAxiom : Arithmetic.Formula 0 → Prop where
  | universalRefl : IsAxiom (.all (.eq (.var 0) (.var 0)))
  | inst (f : Arithmetic.Formula 1) (t : Arithmetic.Term 0) :
      IsAxiom (.imp (.all f) (f.instantiate t))
  | contrap (a b : Arithmetic.Formula 0) :
      IsAxiom (.imp (.imp a (.neg b)) (.imp b (.neg a)))
  | conjIntro (a b : Arithmetic.Formula 0) :
      IsAxiom (.imp a (.imp b (a.conj b)))

theorem IsAxiom.derivable {f : Arithmetic.Formula 0} (h : IsAxiom f) :
    Nonempty (Derivation f) := by
  cases h with
  | universalRefl => exact ⟨.universalRefl⟩
  | inst f t => exact ⟨.inst f t⟩
  | contrap a b => exact ⟨.contrap a b⟩
  | conjIntro a b => exact ⟨.conjIntro a b⟩

/-- All logical checks are on syntactic expansions, never on truth values. -/
inductive Proof {r : Nat} (δ : Fin r → ClosedTerm) : CFormula r 0 → Type where
  | ax {f : CFormula r 0} : IsAxiom (f.expand δ) → Proof δ f
  | mp {a b c : CFormula r 0} : Proof δ a → Proof δ b →
      b.expand δ = .imp (a.expand δ) (c.expand δ) → Proof δ c

theorem Proof.derivable {r : Nat} {δ : Fin r → ClosedTerm} {f : CFormula r 0}
    (d : Proof δ f) : Nonempty (Derivation (f.expand δ)) := by
  induction d with
  | ax h => exact h.derivable
  | mp d e h hd he =>
    obtain ⟨da⟩ := hd
    obtain ⟨de⟩ := he
    rw [h] at de
    exact ⟨.mp da de⟩

def Proof.nodes {r : Nat} {δ : Fin r → ClosedTerm} {f : CFormula r 0} : Proof δ f → Nat
  | .ax _ => 1
  | .mp d e _ => d.nodes+e.nodes+1

def Fits {r n : Nat} (f : CFormula r n) (D W : Nat) : Prop :=
  f.depth ≤ D ∧ f.weight ≤ W

def Proof.bounded {r : Nat} {δ : Fin r → ClosedTerm} {f : CFormula r 0}
    (D W : Nat) : Proof δ f → Prop
  | .ax _ => Fits f D W
  | .mp d e _ => Fits f D W ∧ d.bounded D W ∧ e.bounded D W

theorem Proof.fits {r : Nat} {δ : Fin r → ClosedTerm} {f : CFormula r 0}
    {D W : Nat} (d : Proof δ f) (h : d.bounded D W) : Fits f D W := by
  cases d with
  | ax _ => exact h
  | mp _ _ _ => exact h.1

def Small {r : Nat} (δ : Fin r → ClosedTerm) (f : CFormula r 0) (N D W : Nat) : Prop :=
  ∃ d : Proof δ f, d.nodes ≤ N ∧ d.bounded D W

theorem Small.fits {r : Nat} {δ : Fin r → ClosedTerm} {f : CFormula r 0}
    {N D W : Nat} (h : Small δ f N D W) : Fits f D W := by
  obtain ⟨d,_,hd⟩ := h
  exact d.fits hd

theorem Small.mono {r : Nat} {δ : Fin r → ClosedTerm} {f : CFormula r 0}
    {N M D W : Nat} (h : Small δ f N D W) (hm : N ≤ M) : Small δ f M D W := by
  obtain ⟨d,hn,hd⟩ := h
  exact ⟨d,Nat.le_trans hn hm,hd⟩

theorem Small.ax {r : Nat} {δ : Fin r → ClosedTerm} {f : CFormula r 0}
    {D W : Nat} (h : IsAxiom (f.expand δ)) (hf : Fits f D W) : Small δ f 1 D W :=
  ⟨.ax h, Nat.le_refl _, hf⟩

theorem Small.mp {r : Nat} {δ : Fin r → ClosedTerm} {a b c : CFormula r 0}
    {Na Nb D W : Nat} (ha : Small δ a Na D W) (hb : Small δ b Nb D W)
    (he : b.expand δ = .imp (a.expand δ) (c.expand δ)) (hc : Fits c D W) :
    Small δ c (Na+Nb+1) D W := by
  obtain ⟨da,hna,hda⟩ := ha
  obtain ⟨db,hnb,hdb⟩ := hb
  exact ⟨.mp da db he, by simp only [Proof.nodes]; omega, hc,hda,hdb⟩

theorem Small.refl {r : Nat} (δ : Fin r → ClosedTerm) (s t : CTerm r 0)
    (h : s.expand δ = t.expand δ) (D W : Nat)
    (hd : 1 ≤ D) (hw : 6+s.weight+t.weight ≤ W) : Small δ (.eq s t) 3 D W := by
  let u : CFormula r 0 := .all (.eq (.var 0) (.var 0))
  have hu : Small δ u 1 D W := Small.ax .universalRefl (by
    simp [u,Fits,CFormula.depth,CFormula.weight,CTerm.weight]; omega)
  have hi : Small δ (.imp u (.eq s t)) 1 D W := Small.ax (by
    have hh := IsAxiom.inst (Arithmetic.Formula.eq (.var 0) (.var 0)) (t.expand δ)
    simpa [u,CFormula.expand,Arithmetic.Formula.instantiate,Arithmetic.Formula.subst,
      Arithmetic.Term.subst,instanceSubst,h] using hh) (by
    simp [u,Fits,CFormula.depth,CFormula.weight,CTerm.weight]; omega)
  exact Small.mp hu hi rfl (by simp [Fits,CFormula.depth,CFormula.weight]; omega)

theorem Small.conjunction {r : Nat} {δ : Fin r → ClosedTerm} {a b : CFormula r 0}
    {Na Nb D W : Nat} (ha : Small δ a Na D W) (hb : Small δ b Nb D W)
    (hw : 5+2*a.weight+2*b.weight ≤ W) : Small δ (a.conj b) (Na+Nb+3) D W := by
  have hda := ha.fits.1
  have hdb := hb.fits.1
  have hx : Small δ (.imp a (.imp b (a.conj b))) 1 D W := Small.ax
    (.conjIntro _ _) (by
      simp [Fits,CFormula.depth,CFormula.weight,CFormula.conj,Nat.max_le]; omega)
  have hm := Small.mp ha hx rfl (show Fits (.imp b (a.conj b)) D W by
    simp [Fits,CFormula.depth,CFormula.weight,CFormula.conj,Nat.max_le]; omega)
  have hh := Small.mp hb hm rfl (show Fits (a.conj b) D W by
    simp [Fits,CFormula.depth,CFormula.weight,CFormula.conj,Nat.max_le]; omega)
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem Small.existsIntro {r : Nat} {δ : Fin r → ClosedTerm}
    (f : CFormula r 1) (t : CTerm r 0) (g : CFormula r 0)
    (he : (f.expand δ).instantiate (t.expand δ) = g.expand δ)
    {N D W : Nat} (hg : Small δ g N D W)
    (hd : f.depth+1 ≤ D) (hw : 9+2*f.weight+2*g.weight ≤ W) :
    Small δ f.ex (N+4) D W := by
  let a : CFormula r 0 := .all (.neg f)
  have hgd := hg.fits.1
  have hi : Small δ (.imp a (.neg g)) 1 D W := Small.ax (by
    have hh := IsAxiom.inst (.neg (f.expand δ)) (t.expand δ)
    change IsAxiom (.imp (.all (.neg (f.expand δ)))
      (.neg ((f.expand δ).instantiate (t.expand δ)))) at hh
    rw [he] at hh
    simpa [a,CFormula.expand,Arithmetic.Formula.instantiate,Arithmetic.Formula.subst,
      Arithmetic.Formula.instantiate] using hh) (by
    simp [a,Fits,CFormula.depth,CFormula.weight,Nat.max_le]; omega)
  have hc : Small δ (.imp (.imp a (.neg g)) (.imp g (.neg a))) 1 D W :=
    Small.ax (.contrap _ _) (by
      simp [a,Fits,CFormula.depth,CFormula.weight,Nat.max_le]; omega)
  have hm := Small.mp hi hc rfl (show Fits (.imp g (.neg a)) D W by
    simp [a,Fits,CFormula.depth,CFormula.weight,Nat.max_le]; omega)
  have hx := Small.mp hg hm
    (show (CFormula.imp g (.neg a)).expand δ = Arithmetic.Formula.imp (g.expand δ) (f.ex.expand δ) from rfl)
    (show Fits f.ex D W by
      simp [CFormula.ex,Fits,CFormula.depth,CFormula.weight]; omega)
  simpa [Nat.add_assoc] using hx

theorem Proof.bounded_mono {r : Nat} {δ : Fin r → ClosedTerm} {f : CFormula r 0}
    {D W E V : Nat} (d : Proof δ f) (h : d.bounded D W)
    (hD : D ≤ E) (hW : W ≤ V) : d.bounded E V := by
  induction d with
  | ax _ => exact ⟨Nat.le_trans h.1 hD,Nat.le_trans h.2 hW⟩
  | mp da db _ ha hb =>
    exact ⟨⟨Nat.le_trans h.1.1 hD,Nat.le_trans h.1.2 hW⟩,ha h.2.1,hb h.2.2⟩

theorem Small.enlarge {r : Nat} {δ : Fin r → ClosedTerm} {f : CFormula r 0}
    {N D W E V : Nat} (h : Small δ f N D W) (hD : D ≤ E) (hW : W ≤ V) :
    Small δ f N E V := by
  obtain ⟨d,hn,hd⟩ := h
  exact ⟨d,hn,d.bounded_mono hd hD hW⟩

theorem compact_head {r : Nat} (δ : Fin r → ClosedTerm) (z l s v tail : CTerm r 0)
    (hz : z.expand δ = ((l.pair (s.pair v)).pair tail).expand δ)
    (hw : z.weight ≤ 1 ∧ l.weight ≤ 1 ∧ s.weight ≤ 1 ∧ v.weight ≤ 1 ∧ tail.weight ≤ 1) :
    Small δ (lookup 0 z l s v) 7 1 1000 := by
  let f : CFormula r 1 := .eq z.up ((l.up.pair (s.up.pair v.up)).pair (.var 0))
  let g : CFormula r 0 := .eq z ((l.pair (s.pair v)).pair tail)
  have hg : Small δ g 3 1 1000 := Small.refl δ _ _ hz 1 1000 (by omega) (by
    simp only [CTerm.weight_pair]; omega)
  have he : (f.expand δ).instantiate (tail.expand δ) = g.expand δ := by
    simp [f,g,CFormula.expand,Arithmetic.Formula.instantiate,Arithmetic.Formula.subst,
      Arithmetic.Term.subst_pair,Arithmetic.Term.subst_up_instance,Arithmetic.Term.subst,instanceSubst,
      CTerm.expand]
  exact Small.existsIntro f tail g he hg (by simp [f,CFormula.depth]) (by
    simp [f,g,CFormula.weight,CTerm.up,CTerm.weight]; omega)

theorem compact_step {r : Nat} (δ : Fin r → ClosedTerm) (i : Nat)
    (z head tail l s v : CTerm r 0)
    (hz : z.expand δ = (head.pair tail).expand δ)
    (hw : z.weight ≤ 1 ∧ head.weight ≤ 34 ∧ tail.weight ≤ 1 ∧
      l.weight ≤ 1 ∧ s.weight ≤ 1 ∧ v.weight ≤ 1)
    (h : Small δ (lookup i tail l s v) (14*i+7) (2*i+1) (1000*(i+1))) :
    Small δ (lookup (i+1) z l s v) (14*(i+1)+7) (2*(i+1)+1) (1000*(i+2)) := by
  let D := 2*(i+1)+1
  let W := 1000*(i+2)
  let body : CFormula r 2 :=
    (CFormula.eq z.up.up ((CTerm.var (Fin.succ 0)).pair (.var 0))).conj
      (lookup i (.var 0) l.up.up s.up.up v.up.up)
  let middle : CFormula r 1 :=
    (CFormula.eq z.up (head.up.pair (.var 0))).conj
      (lookup i (.var 0) l.up s.up v.up)
  let g : CFormula r 0 := (CFormula.eq z (head.pair tail)).conj (lookup i tail l s v)
  have hr : Small δ (.eq z (head.pair tail)) 3 D W :=
    Small.refl δ _ _ hz D W (by simp [D]) (by
      simp [W,CTerm.weight_pair]; omega)
  have hh : Small δ (lookup i tail l s v) (14*i+7) D W :=
    h.enlarge (by simp only [D]; omega) (by simp only [W]; omega)
  have hg : Small δ g (14*i+13) D W := by
    have hc := Small.conjunction hr hh (by
      simp [W,CFormula.weight,lookup_weight]; omega)
    exact hc.mono (by omega)
  have he : (middle.expand δ).instantiate (tail.expand δ) = g.expand δ := by
    simp [middle,g,CFormula.conj,CFormula.expand,lookup_expand,
      Arithmetic.Formula.instantiate,Arithmetic.Formula.subst,
      Arithmetic.lookup_subst,Arithmetic.Term.subst_pair,
      Arithmetic.Term.subst_up_instance,Arithmetic.Term.subst,instanceSubst,CTerm.expand]
  have hm : Small δ middle.ex (14*i+17) D W :=
    Small.existsIntro middle tail g he hg (by
      simp [middle,D,CFormula.depth,CFormula.conj,lookup_depth]; omega) (by
      simp [middle,g,W,CFormula.weight,CFormula.conj,lookup_weight,CTerm.up,CTerm.weight]; omega)
  have ho : (body.ex.expand δ).instantiate (head.expand δ) = middle.ex.expand δ := by
    simp [body,middle,CFormula.ex,CFormula.conj,CFormula.expand,lookup_expand,
      Arithmetic.Formula.instantiate,Arithmetic.Formula.subst,
      Arithmetic.lookup_subst,Arithmetic.Term.subst_pair,
      Arithmetic.Term.subst_up_lift,Arithmetic.Term.subst_up_instance,Arithmetic.Term.subst,
      liftSubst,instanceSubst,Arithmetic.Term.up,Arithmetic.Term.subst_comp,CTerm.expand]
  have hx := Small.existsIntro body.ex head middle.ex ho hm (by
    simp [body,D,CFormula.ex,CFormula.depth,CFormula.conj,lookup_depth]; omega) (by
    simp [body,middle,W,CFormula.weight,CFormula.ex,CFormula.conj,lookup_weight,CTerm.up,CTerm.weight]; omega)
  simpa [lookup,body,D,W,Nat.mul_add,Nat.add_assoc] using hx

structure Cell (r : Nat) where
  len : CTerm r 0
  scale : CTerm r 0
  payload : CTerm r 0

def Cell.code {r : Nat} (c : Cell r) : CTerm r 0 := c.len.pair (c.scale.pair c.payload)
def Cell.small {r : Nat} (c : Cell r) : Prop :=
  c.len.weight ≤ 1 ∧ c.scale.weight ≤ 1 ∧ c.payload.weight ≤ 1

/-- A chain of abbreviations with certified *syntactic* expansion equations. -/
inductive Chain {r : Nat} (δ : Fin r → ClosedTerm) : List (Cell r) → CTerm r 0 → Prop where
  | nil : Chain δ [] .zero
  | cons {cs : List (Cell r)} {tail z : CTerm r 0} (c : Cell r)
      (hc : c.small) (hz : z.weight ≤ 1)
      (he : z.expand δ = (c.code.pair tail).expand δ)
      (ht : Chain δ cs tail) : Chain δ (c::cs) z

theorem Chain.root_small {r : Nat} {δ : Fin r → ClosedTerm}
    {cs : List (Cell r)} {z : CTerm r 0} (h : Chain δ cs z) : z.weight ≤ 1 := by
  cases h with
  | nil => exact Nat.le_refl _
  | cons _ _ hz _ _ => exact hz

theorem Chain.cell_small {r : Nat} {δ : Fin r → ClosedTerm}
    {cs : List (Cell r)} {z : CTerm r 0} (h : Chain δ cs z) (i : Fin cs.length) :
    (cs.get i).small := by
  induction h with
  | nil => exact Fin.elim0 i
  | cons c hc _ _ _ ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hc
    · exact ih j

theorem Chain.lookup_small {r : Nat} {δ : Fin r → ClosedTerm}
    {cs : List (Cell r)} {z : CTerm r 0} (h : Chain δ cs z) (i : Fin cs.length) :
    Small δ (lookup i.val z (cs.get i).len (cs.get i).scale (cs.get i).payload)
      (14*i.val+7) (2*i.val+1) (1000*(i.val+1)) := by
  induction h with
  | nil => exact Fin.elim0 i
  | @cons cs tail z c hc hz he ht ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact compact_head δ z c.len c.scale c.payload tail he
        ⟨hz,hc.1,hc.2.1,hc.2.2,ht.root_small⟩
    · have hj := ih j
      have hs := ht.cell_small j
      have hh : c.code.weight ≤ 34 := by simp [Cell.code]; rcases hc with ⟨h1,h2,h3⟩; omega
      simpa using compact_step δ j.val z c.code tail _ _ _ he
        ⟨hz,hh,ht.root_small,hs.1,hs.2.1,hs.2.2⟩ hj

def lastRef {r : Nat} : (m : Nat) → (Fin m → Fin r) → CTerm r 0
  | 0, _ => .zero
  | m+1, σ => .ref (σ (Fin.last m))

theorem lastRef_weight {r m : Nat} (σ : Fin m → Fin r) : (lastRef m σ).weight = 1 := by
  cases m <;> rfl

theorem lastRef_expand {r m : Nat} (δ : Fin r → ClosedTerm) (σ : Fin m → Fin r)
    (τ : Fin m → ClosedTerm) (h : ∀ j, δ (σ j) = τ j) :
    (lastRef m σ).expand δ = (Arithmetic.Term.ofClosed (lastTerm m τ) : Arithmetic.Term 0) := by
  cases m with
  | zero => rfl
  | succ m => simp [lastRef,CTerm.expand,lastTerm,h]

def sourceCell {n r : Nat} (src : Fin n → Slot → Fin r) (i : Fin n) : Cell r :=
  ⟨.ref (src i .len), .ref (src i .scale), .ref (src i .payload)⟩

theorem sourceCell_small {n r : Nat} (src : Fin n → Slot → Fin r) (i : Fin n) :
    (sourceCell src i).small := by simp [sourceCell,Cell.small,CTerm.weight]

theorem sourceCell_expand {n r : Nat} (ρ : Fin n → TermTriple)
    (δ : Fin r → ClosedTerm) (src : Fin n → Slot → Fin r)
    (h : ∀ i s, δ (src i s) = (ρ i).get s) (i : Fin n) :
    (sourceCell src i).code.expand δ = (Summary.ofTriple (ρ i)).code := by
  simp [sourceCell,Cell.code,CTerm.expand,h,Summary.ofTriple,Summary.code,TermTriple.get]

theorem packed_chain {n r : Nat} (ρ : Fin n → TermTriple) (δ : Fin r → ClosedTerm)
    (src : Fin n → Slot → Fin r) (hs : ∀ i s, δ (src i s) = (ρ i).get s)
    (is : List (Fin n)) (saved : Fin is.length → Fin r)
    (hp : ∀ j, δ (saved j) = (packRefs is).expansion ρ j) :
    Chain δ (is.map (sourceCell src)) (lastRef is.length saved) := by
  induction is with
  | nil => exact .nil
  | cons i is ih =>
    let prev : Fin is.length → Fin r := fun j => saved j.castSucc
    have hprev : ∀ j, δ (prev j) = (packRefs is).expansion ρ j := by
      intro j
      simpa [prev,packRefs,PackingProgram.expansion] using hp j.castSucc
    have ht := ih prev hprev
    apply Chain.cons (sourceCell src i) (sourceCell_small src i)
      (by simp only [lastRef_weight]; omega) ?_ ht
    simp only [List.length_cons,lastRef,CTerm.expand]
    rw [hp]
    simp only [packRefs,PackingProgram.expansion,Fin.lastCases_last,pairExpr_expansion,
      valueExpr_expansion,lastExpr_expansion,CTerm.expand_pair]
    rw [sourceCell_expand ρ δ src hs i]
    exact congrArg ((Summary.ofTriple (ρ i)).code.pair) (lastRef_expand δ prev _ hprev).symm

def savedIndex {n : Nat} (j : Fin (List.finRange n).length) : Fin (3*n+n) :=
  ⟨3*n+j.val,by have hj := j.isLt; simp only [List.length_finRange] at hj; omega⟩

theorem dictionary_saved {n : Nat} (p : Program n) (j : Fin (List.finRange n).length) :
    dictionary p (savedIndex j) = (tracePacking n).expansion p.expansion j := by
  have hn : ¬ 3*n+j.val < 3*n := by omega
  simp [dictionary,savedIndex,hn]
  congr 1
  apply Fin.ext
  simp; omega

theorem lastRef_savedIndex (n : Nat) :
    lastRef (List.finRange n).length (savedIndex (n:=n)) = rootRef n := by
  have hz : ∀ (m : Nat) (σ : Fin m → Fin (3*n+n)), m=0 → lastRef m σ = .zero := by
    intro m σ hm; subst m; rfl
  have hp : ∀ (m : Nat) (σ : Fin m → Fin (3*n+n)) (hm : 0<m),
      lastRef m σ = .ref (σ ⟨m-1,by omega⟩) := by
    intro m σ hm
    cases m with
    | zero => omega
    | succ m => rfl
  cases n with
  | zero => exact hz _ _ List.length_finRange
  | succ n =>
    rw [hp _ _ (by simp only [List.length_finRange]; omega)]
    simp only [rootRef]
    congr 1
    apply Fin.ext
    simp [savedIndex,List.length_finRange]

theorem compiler_chain {n : Nat} (p : Program n) :
    Chain (dictionary p) (List.ofFn (sourceCell (sourceIndex (n:=n)))) (rootRef n) := by
  have h := packed_chain p.expansion (dictionary p) sourceIndex (dictionary_source p)
    (List.finRange n) savedIndex (dictionary_saved p)
  simpa [Quotation.map_finRange,lastRef_savedIndex] using h

theorem entry_small {n : Nat} (p : Program n) (i : Fin n) :
    Small (dictionary p) (entry i) (14*i.val+7) (2*i.val+1) (1000*(i.val+1)) := by
  have h := (compiler_chain p).lookup_small ⟨i.val,by simp⟩
  simpa [entry,sourceCell,List.get_eq_getElem] using h

theorem allConj_small {r : Nat} (δ : Fin r → ClosedTerm) (fs : List (CFormula r 0))
    (N D W A : Nat) (hd : 1 ≤ D)
    (h : ∀ f ∈ fs, Small δ f N D W) (ha : ∀ f ∈ fs, f.weight ≤ A)
    (hw : 2*(fs.length*(A+3))+11 ≤ W) :
    Small δ (allConj fs) (fs.length*(N+3)+3) D W := by
  induction fs with
  | nil =>
    simpa [allConj] using Small.refl δ .zero .zero rfl D W hd (by simp [CTerm.weight] at *; omega)
  | cons f fs ih =>
    have hf := h f (by simp)
    have hfa := ha f (by simp)
    have hta : ∀ g ∈ fs, g.weight ≤ A := fun g hg => ha g (by simp [hg])
    have ht := ih (fun g hg => h g (by simp [hg])) hta (by
      simp only [List.length_cons,Nat.succ_mul] at hw; omega)
    have htaw := allConj_weight fs A hta
    have hc := Small.conjunction hf ht (by
      simp only [List.length_cons,Nat.succ_mul] at hw; omega)
    apply hc.mono
    simp only [List.length_cons,Nat.succ_mul]
    omega

def traceN (n : Nat) : Nat := n*(14*n+10)+3
def traceD (n : Nat) : Nat := 2*n+1
def traceW (n : Nat) : Nat := 1000*(n+1)*(n+1)

theorem trace_small {n : Nat} (p : Program n) :
    Small (dictionary p) (trace n) (traceN n) (traceD n) (traceW n) := by
  have hn : 1 ≤ n+1 := by omega
  have hnw : 1000*(n+1) ≤ traceW n := by
    have hh := Nat.mul_le_mul_left (1000*(n+1)) hn
    simpa [traceW] using hh
  have h : ∀ f ∈ List.ofFn (entry (n:=n)), Small (dictionary p) f (14*n+7) (traceD n) (traceW n) := by
    intro f hf
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
    have hi := i.isLt
    exact ((entry_small p i).mono (by omega)).enlarge (by simp only [traceD]; omega)
      (Nat.le_trans (by omega) hnw)
  have ha : ∀ f ∈ List.ofFn (entry (n:=n)), f.weight ≤ 23*n+116 := by
    intro f hf
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
    have hi := i.isLt
    simp [entry,lookup_weight,rootRef_weight,CTerm.weight]; omega
  have hw : 2*(n*(23*n+116+3))+11 ≤ traceW n := by
    simp only [traceW,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul]
    simp only [Nat.mul_assoc,Nat.mul_left_comm n 23]
    have hnn : n*n ≥ 0 := Nat.zero_le _
    omega
  simpa [trace,traceN] using allConj_small (dictionary p) _ (14*n+7)
    (traceD n) (traceW n) (23*n+116) (by simp [traceD]) h ha (by simpa using hw)

def Records.get {r k : Nat} : Records r k → Fin k → CFormula r 0
  | .nil => Fin.elim0
  | .snoc fs f => Fin.lastCases f.formula fs.get

@[simp] theorem Records.get_last {r k : Nat} (fs : Records r k) (f : Record r k) :
    (fs.snoc f).get (Fin.last k) = f.formula := by simp [get]

@[simp] theorem Records.get_castSucc {r k : Nat} (fs : Records r k) (f : Record r k) (i : Fin k) :
    (fs.snoc f).get i.castSucc = fs.get i := by simp [get]

def Record.valid {r k : Nat} (δ : Fin r → ClosedTerm) (fs : Records r k) : Record r k → Prop
  | .axiom f => IsAxiom (f.expand δ)
  | .mp a b f => (fs.get b).expand δ = Arithmetic.Formula.imp ((fs.get a).expand δ) (f.expand δ)

def Records.valid {r k : Nat} (δ : Fin r → ClosedTerm) : Records r k → Prop
  | .nil => True
  | .snoc fs f => fs.valid δ ∧ f.valid δ fs

structure Records.Extends {r k l : Nat} (fs : Records r k) (gs : Records r l) : Prop where
  bound : k ≤ l
  get_eq : ∀ i : Fin k, gs.get (i.castLE bound) = fs.get i

theorem Records.extends_snoc {r k : Nat} (fs : Records r k) (f : Record r k) :
    fs.Extends (fs.snoc f) := by
  refine ⟨by omega,?_⟩
  intro i
  exact fs.get_castSucc f i

theorem Records.Extends.trans {r k l m : Nat} {fs : Records r k} {gs : Records r l} {hs : Records r m}
    (hfg : fs.Extends gs) (hgh : gs.Extends hs) : fs.Extends hs := by
  refine ⟨Nat.le_trans hfg.bound hgh.bound,?_⟩
  intro i
  rw [← Fin.castLE_castLE,hgh.get_eq,hfg.get_eq]

structure Emission {r k : Nat} (δ : Fin r → ClosedTerm) (fs : Records r k)
    (f : CFormula r 0) (cost D W : Nat) where
  count : Nat
  file : Records r count
  size_eq : count = k+cost
  extension : fs.Extends file
  last : Fin count
  last_is_last : last.val+1 = count
  last_eq : file.get last = f
  valid : file.valid δ
  bounded : file.bounded D W

/-- A proof-tree-to-file compiler. Every emitted MP index refers backwards,
and the expanded formulas satisfy the checked inference relation. -/
noncomputable def Proof.emit {r : Nat} {δ : Fin r → ClosedTerm} {f : CFormula r 0}
    (d : Proof δ f) {k : Nat} (fs : Records r k) (D W : Nat)
    (hv : fs.valid δ) (hb : fs.bounded D W) (hd : d.bounded D W) :
    Emission δ fs f d.nodes D W := by
  induction d generalizing k with
  | @ax f ha =>
    exact ⟨k+1,fs.snoc (.axiom f),rfl,fs.extends_snoc _,Fin.last k,rfl,
      by simp [Record.formula],
      ⟨hv,ha⟩,hb,hd⟩
  | @mp a b c da db he iha ihb =>
    let x := iha fs hv hb hd.2.1
    let y := ihb x.file x.valid x.bounded hd.2.2
    let ia : Fin y.count := x.last.castLE y.extension.bound
    have ha : y.file.get ia = a := by
      rw [show ia = x.last.castLE y.extension.bound from rfl,y.extension.get_eq,x.last_eq]
    let out : Record r y.count := .mp ia y.last c
    have ho : out.valid δ y.file := by
      simp only [out,Record.valid,ha,y.last_eq]
      exact he
    refine ⟨y.count+1,y.file.snoc out,?_,x.extension.trans (y.extension.trans (y.file.extends_snoc out)),
      Fin.last y.count,rfl,by simp [out,Record.formula],⟨y.valid,ho⟩,y.bounded,hd.1⟩
    have hx := x.size_eq
    have hy := y.size_eq
    simp only [Proof.nodes]
    omega

theorem Small.file {r : Nat} {δ : Fin r → ClosedTerm} {f : CFormula r 0}
    {N D W : Nat} (h : Small δ f N D W) :
    ∃ (k : Nat) (fs : Records r k) (last : Fin k), k ≤ N ∧ last.val+1=k ∧
      fs.get last = f ∧ fs.valid δ ∧ fs.bounded D W ∧
      fs.wire.length ≤ N*((2*r+2*D+7)*W+4*N+14) := by
  obtain ⟨d,hn,hd⟩ := h
  let out := d.emit .nil D W trivial trivial hd
  have hk : out.count ≤ N := by have ho := out.size_eq; omega
  refine ⟨out.count,out.file,out.last,hk,out.last_is_last,out.last_eq,out.valid,out.bounded,?_⟩
  exact Nat.le_trans (out.file.wire_bound D W N hk out.bounded) (Nat.mul_le_mul_right _ hk)

def traceCharacters (n : Nat) : Nat :=
  traceN n * ((12*n+9)*traceW n+4*traceN n+14)

/-- Complete compact trace proof, with every formula and MP reference charged.
The separately generated definition/quotation prelude is not included. -/
theorem trace_file {n : Nat} (p : Program n) :
    ∃ (k : Nat) (fs : Records (3*n+n) k) (last : Fin k), k ≤ traceN n ∧ last.val+1=k ∧
      fs.get last = trace n ∧ fs.valid (dictionary p) ∧
      fs.bounded (traceD n) (traceW n) ∧ fs.wire.length ≤ traceCharacters n := by
  have h := (trace_small p).file
  have hh : 2*(3*n+n)+2*traceD n+7 = 12*n+9 := by simp only [traceD]; omega
  simpa only [hh,traceCharacters] using h

theorem Records.valid_derivable {r k : Nat} (δ : Fin r → ClosedTerm) (fs : Records r k)
    (h : fs.valid δ) (i : Fin k) : Nonempty (Derivation ((fs.get i).expand δ)) := by
  induction fs with
  | nil => exact Fin.elim0 i
  | @snoc k fs f ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Records.get_last]
      cases f with
      | «axiom» a => exact h.2.derivable
      | mp a b c =>
        obtain ⟨da⟩ := ih h.1 a
        obtain ⟨db⟩ := ih h.1 b
        have he := h.2
        change (fs.get b).expand δ = .imp ((fs.get a).expand δ) (c.expand δ) at he
        rw [he] at db
        exact ⟨.mp da db⟩
    · simpa using ih h.1 j

/-- Only definition records precede the proof here. Earlier optional local
equality certificates are not needed to expand these closed definitions. -/
def definitionPrelude {n : Nat} (p : Program n) : List Char :=
  p.wire ++ (tracePacking n).wire

theorem definitionPrelude_characters {b n : Nat} (g : Grammar b n) :
    (definitionPrelude (compile g)).length ≤
      (6*g.mass+20)*(4*(b+4)*g.mass^2+3*g.mass)+(8*n+20)*(112*n) := by
  have hq := compile_characters g
  have hp := tracePacking_characters n
  simp only [definitionPrelude,List.length_append]
  omega

def fullCharacters (b M n : Nat) : Nat :=
  (6*M+20)*(4*(b+4)*M^2+3*M)+(8*n+20)*(112*n)+traceCharacters n

theorem compiled_trace_file {b n : Nat} (g : Grammar b n) :
    ∃ (k : Nat) (fs : Records (3*n+n) k) (last : Fin k),
      k ≤ traceN n ∧ last.val+1=k ∧ fs.get last = trace n ∧
      fs.valid (dictionary (compile g)) ∧
      (definitionPrelude (compile g) ++ fs.wire).length ≤ fullCharacters b g.mass n := by
  obtain ⟨k,fs,last,hk,hl,hf,hv,_,hc⟩ := trace_file (compile g)
  refine ⟨k,fs,last,hk,hl,hf,hv,?_⟩
  have hp := definitionPrelude_characters g
  simp only [List.length_append,fullCharacters]
  omega

theorem traceCharacters_mono {n m : Nat} (h : n ≤ m) : traceCharacters n ≤ traceCharacters m := by
  have hN : traceN n ≤ traceN m := by
    exact Nat.add_le_add_right (Nat.mul_le_mul h (by omega)) 3
  have hW : traceW n ≤ traceW m := by
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 1000 (by omega)) (by omega)
  have ht := Nat.mul_le_mul (show 12*n+9 ≤ 12*m+9 by omega) hW
  apply Nat.mul_le_mul hN
  omega

/-- A polynomial bound in the written grammar mass, for each fixed base b. -/
theorem compiled_trace_file_mass {b n : Nat} (g : Grammar b n) :
    ∃ (k : Nat) (fs : Records (3*n+n) k) (last : Fin k),
      k ≤ traceN n ∧ last.val+1=k ∧ fs.get last = trace n ∧
      fs.valid (dictionary (compile g)) ∧
      (definitionPrelude (compile g) ++ fs.wire).length ≤ fullCharacters b g.mass g.mass := by
  obtain ⟨k,fs,last,hk,hl,hf,hv,hc⟩ := compiled_trace_file g
  refine ⟨k,fs,last,hk,hl,hf,hv,Nat.le_trans hc ?_⟩
  have hn := g.count_le_mass
  have ht := traceCharacters_mono hn
  have hp := Nat.mul_le_mul (show 8*n+20 ≤ 8*g.mass+20 by omega)
    (show 112*n ≤ 112*g.mass by omega)
  simp only [fullCharacters]
  omega

/-- The final expanded sentence is literally the earlier arithmetic trace
formula, and follows by the restricted Enderton derivation rules. -/
theorem trace_file_conclusion {n k : Nat} (p : Program n) (fs : Records (3*n+n) k)
    (i : Fin k) (hv : fs.valid (dictionary p)) (hf : fs.get i = trace n) :
    (fs.get i).expand (dictionary p) =
      traceFormula p (Arithmetic.Term.ofClosed (packedRoot p)) ∧
    Nonempty (Derivation (traceFormula p (Arithmetic.Term.ofClosed (packedRoot p)) : Arithmetic.Formula 0)) := by
  have he : (fs.get i).expand (dictionary p) =
      traceFormula p (Arithmetic.Term.ofClosed (packedRoot p)) := by rw [hf,trace_expand]
  exact ⟨he,by rw [← he]; exact fs.valid_derivable (dictionary p) hv i⟩

end MAISO11.Wire

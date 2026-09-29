import PAFormula

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Arithmetic
open Quotation

theorem unpair_some_iff (z a b : Nat) :
    arithUnpair z = some (a, b) ↔ z = arithPair a b := by
  constructor
  · intro h
    have hp := List.find?_some
      (p := fun ab : Nat × Nat => decide (arithPair ab.1 ab.2 = z)) h
    exact (of_decide_eq_true hp).symm
  · intro h
    subst z
    exact arithUnpair_pair a b

theorem decodeValue_some_iff (z : Nat) (v : Value) :
    decodeValue z = some v ↔ z = encodeValue v := by
  constructor
  · intro h
    unfold decodeValue at h
    cases he : arithUnpair z with
    | none => simp [he] at h
    | some ab =>
      rcases ab with ⟨a,b⟩
      cases hf : arithUnpair b with
      | none => simp [he, hf] at h
      | some cd =>
        rcases cd with ⟨c,d⟩
        have hv : (⟨a,c,d⟩ : Value) = v := by simpa [he, hf] using h
        subst v
        rw [(unpair_some_iff z a b).mp he, (unpair_some_iff b c d).mp hf]
        rfl
  · intro h
    subst z
    exact decode_encodeValue v

theorem readValue_zero_iff (z : Nat) (v : Value) :
    readValue z 0 = some v ↔ ∃ tail, z = arithPair (encodeValue v) tail := by
  constructor
  · intro h
    unfold readValue at h
    cases he : arithUnpair z with
    | none => simp [he] at h
    | some ab =>
      rcases ab with ⟨a,b⟩
      have hd : decodeValue a = some v := by simpa [he] using h
      exact ⟨b, by rw [(unpair_some_iff z a b).mp he, (decodeValue_some_iff a v).mp hd]⟩
  · rintro ⟨tail, rfl⟩
    simp [readValue, decode_encodeValue]

theorem readValue_succ_iff (z i : Nat) (v : Value) :
    readValue z (i+1) = some v ↔
      ∃ head tail, z = arithPair head tail ∧ readValue tail i = some v := by
  constructor
  · intro h
    unfold readValue at h
    cases he : arithUnpair z with
    | none => simp [he] at h
    | some ab =>
      exact ⟨ab.1,ab.2,(unpair_some_iff z ab.1 ab.2).mp he, by simpa [he] using h⟩
  · rintro ⟨head,tail,rfl,h⟩
    simpa [readValue] using h

/-- The index is a metalevel natural. This is a finite PA formula for each
fixed index, NOT yet a single uniform sequence-access formula with index input. -/
def lookup : (i : Nat) → {n : Nat} → Term n → Term n → Term n → Term n → Formula n
  | 0, _, z,l,s,v =>
      (Formula.eq z.up ((l.up.pair (s.up.pair v.up)).pair (.var 0))).ex
  | i+1, _, z,l,s,v =>
      ((Formula.eq z.up.up ((Term.var (Fin.succ 0)).pair (.var 0))).conj
        (lookup i (.var 0) l.up.up s.up.up v.up.up)).ex.ex

theorem lookup_realize (i : Nat) {n : Nat} (z l s v : Term n) (ρ : Fin n → Nat) :
    (lookup i z l s v).realize ρ ↔
      readValue (z.eval ρ) i = some ⟨l.eval ρ, s.eval ρ, v.eval ρ⟩ := by
  induction i generalizing n with
  | zero =>
    rw [readValue_zero_iff]
    simp [lookup, Formula.realize_ex, Formula.realize, Term.eval_pair,
      Term.eval_up, Term.eval, extend, encodeValue]
  | succ i ih =>
    rw [readValue_succ_iff]
    simp [lookup, Formula.realize_ex, Formula.realize_conj, Formula.realize,
      ih, Term.eval_pair, Term.eval_up, Term.eval, extend]

/-- A symbolic lookup at the head of a packed trace. Only logical/equality
axioms are used; the numeric code and decoder are never evaluated. -/
def headLookupProof {n : Nat} (l s v tail : Term n) :
    Derivation (lookup 0 ((l.pair (s.pair v)).pair tail) l s v) := by
  apply Derivation.existsIntro _ tail
  change Derivation ((Formula.eq
    (((l.pair (s.pair v)).pair tail).up)
    ((l.up.pair (s.up.pair v.up)).pair (.var 0))).instantiate tail)
  simp only [Formula.instantiate, Formula.subst, Term.subst_pair,
    Term.subst_up_instance, Term.subst, instanceSubst, Fin.cases_zero]
  exact .refl _

theorem lookup_subst (i : Nat) {n m : Nat} (z l s v : Term n) (σ : Fin n → Term m) :
    (lookup i z l s v).subst σ =
      lookup i (z.subst σ) (l.subst σ) (s.subst σ) (v.subst σ) := by
  induction i generalizing n m with
  | zero =>
    simp [lookup, Formula.ex, Formula.subst, Term.subst_pair,
      Term.subst_up_lift, Term.subst, liftSubst]
  | succ i ih =>
    simp [lookup, Formula.ex, Formula.conj, Formula.subst, ih,
      Term.subst_pair, Term.subst_up_lift, Term.subst, liftSubst]

/-- Prepending an arbitrary symbolic head extends a lookup proof by two
existential introductions and one conjunction introduction. -/
def stepLookupProof (i : Nat) {n : Nat} (head tail l s v : Term n)
    (d : Derivation (lookup i tail l s v)) :
    Derivation (lookup (i+1) (head.pair tail) l s v) := by
  let body : Formula (n+2) :=
    (Formula.eq (head.pair tail).up.up ((Term.var (Fin.succ 0)).pair (.var 0))).conj
      (lookup i (.var 0) l.up.up s.up.up v.up.up)
  let middle : Formula (n+1) :=
    (Formula.eq (head.pair tail).up (head.up.pair (.var 0))).conj
      (lookup i (.var 0) l.up s.up v.up)
  have hm : Derivation middle.ex := by
    apply Derivation.existsIntro _ tail
    simpa [middle, Formula.instantiate, Formula.conj, Formula.subst,
      Term.subst_pair, Term.subst_up_instance, Term.subst, instanceSubst,
      lookup_subst] using (Derivation.conjunction (.refl (head.pair tail)) d)
  apply Derivation.existsIntro body.ex head
  simpa [body, middle, Formula.instantiate, Formula.ex, Formula.conj, Formula.subst,
    lookup_subst, Term.subst_pair, Term.subst_up_lift, Term.subst_up_instance,
    Term.subst, liftSubst, instanceSubst, Term.up, Term.subst_comp] using hm

theorem headLookup_within {n : Nat} (l s v tail : Term n) :
    Within (lookup 0 ((l.pair (s.pair v)).pair tail) l s v) 7 := by
  apply Within.existsIntro _ tail 3
  simp only [Formula.instantiate, Formula.subst, Term.subst_pair,
    Term.subst_up_instance, Term.subst, instanceSubst, Fin.cases_zero]
  exact Within.refl _

theorem stepLookup_within (i : Nat) {n : Nat} (head tail l s v : Term n)
    (k : Nat) (h : Within (lookup i tail l s v) k) :
    Within (lookup (i+1) (head.pair tail) l s v) (k+14) := by
  let body : Formula (n+2) :=
    (Formula.eq (head.pair tail).up.up ((Term.var (Fin.succ 0)).pair (.var 0))).conj
      (lookup i (.var 0) l.up.up s.up.up v.up.up)
  let middle : Formula (n+1) :=
    (Formula.eq (head.pair tail).up (head.up.pair (.var 0))).conj
      (lookup i (.var 0) l.up s.up v.up)
  have hm : Within middle.ex (k+10) := by
    have hx : Within (middle.instantiate tail) (k+6) := by
      simpa [middle, Formula.instantiate, Formula.conj, Formula.subst,
        Term.subst_pair, Term.subst_up_instance, Term.subst, instanceSubst,
        lookup_subst, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Within.conjunction _ _ 3 k (Within.refl (head.pair tail)) h)
    simpa [Nat.add_assoc] using Within.existsIntro middle tail (k+6) hx
  have ho : Within (body.ex.instantiate head) (k+10) := by
    simpa [body, middle, Formula.instantiate, Formula.ex, Formula.conj, Formula.subst,
      lookup_subst, Term.subst_pair, Term.subst_up_lift, Term.subst_up_instance,
      Term.subst, liftSubst, instanceSubst, Term.up, Term.subst_comp] using hm
  simpa [body, lookup, Nat.add_assoc] using Within.existsIntro body.ex head (k+10) ho

structure Summary (n : Nat) where
  len : Term n
  scale : Term n
  payload : Term n

def Summary.code {n : Nat} (v : Summary n) : Term n :=
  v.len.pair (v.scale.pair v.payload)

def Summary.eval {n : Nat} (v : Summary n) (ρ : Fin n → Nat) : Value :=
  ⟨v.len.eval ρ, v.scale.eval ρ, v.payload.eval ρ⟩

def Summary.ofTriple {n : Nat} (v : TermTriple) : Summary n :=
  ⟨Term.ofClosed v.len, Term.ofClosed v.scale, Term.ofClosed v.payload⟩

def packedTerms {n : Nat} : List (Summary n) → Term n
  | [] => .zero
  | v :: vs => v.code.pair (packedTerms vs)

theorem packedTerms_eval {n : Nat} (vs : List (Summary n)) (ρ : Fin n → Nat) :
    (packedTerms vs).eval ρ = encodeValues (vs.map (fun v => v.eval ρ)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp [packedTerms, Term.eval_pair, ih, encodeValues, Summary.code,
      Summary.eval, encodeValue]

/-- An explicit object-calculus proof for every selected entry. -/
def lookupProof {n : Nat} : (vs : List (Summary n)) → (i : Fin vs.length) →
    Derivation (lookup i.val (packedTerms vs)
      (vs.get i).len (vs.get i).scale (vs.get i).payload)
  | [], i => Fin.elim0 i
  | v :: vs, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact headLookupProof v.len v.scale v.payload (packedTerms vs)
    · exact stepLookupProof j.val v.code (packedTerms vs) _ _ _ (lookupProof vs j)

/-- A bound on actual object-calculus proof-tree nodes. This is NOT yet
a bound on the written characters of serialized compressed PA files. -/
theorem lookup_within {n : Nat} (vs : List (Summary n)) (i : Fin vs.length) :
    Within (lookup i.val (packedTerms vs)
      (vs.get i).len (vs.get i).scale (vs.get i).payload) (14*i.val+7) := by
  induction vs with
  | nil => exact Fin.elim0 i
  | cons v vs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact headLookup_within v.len v.scale v.payload (packedTerms vs)
    · simpa [packedTerms, Summary.code, Nat.mul_add, Nat.add_assoc] using
        stepLookup_within j.val v.code (packedTerms vs) _ _ _ (14*j.val+7) (ih j)

def programSummaries {n : Nat} (p : Program n) : List (Summary 0) :=
  List.ofFn (fun i => Summary.ofTriple (p.expansion i))

def programTraceTerm {n : Nat} (p : Program n) : Term 0 := packedTerms (programSummaries p)

theorem map_ofFn {α β : Type} {n : Nat} (g : α → β) (f : Fin n → α) :
    (List.ofFn f).map g = List.ofFn (fun i => g (f i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.ofFn_succ, ih]

theorem programTraceTerm_eval {n : Nat} (p : Program n) :
    (programTraceTerm p).eval Fin.elim0 = p.traceCode := by
  rw [programTraceTerm, packedTerms_eval]
  unfold programSummaries Program.traceCode
  congr 1
  simp only [map_ofFn]
  congr 1
  funext i
  have hp := congrFun (Program.expansion_eval p) i
  simpa [Summary.ofTriple, Summary.eval, Term.eval_ofClosed, TermTriple.eval] using hp

theorem program_lookup_within {n : Nat} (p : Program n) (i : Fin n) :
    Within (lookup i.val (programTraceTerm p)
      (Term.ofClosed (p.expansion i).len)
      (Term.ofClosed (p.expansion i).scale)
      (Term.ofClosed (p.expansion i).payload)) (14*i.val+7) := by
  have hl : (programSummaries p).length = n := by simp [programSummaries]
  let j : Fin (programSummaries p).length := ⟨i.val, by rw [hl]; exact i.isLt⟩
  have h := lookup_within (programSummaries p) j
  simpa [programTraceTerm, programSummaries, Summary.ofTriple, j] using h

theorem compiledTraceTerm_eval {b n : Nat} (g : Grammar b n) :
    (programTraceTerm (compile g)).eval Fin.elim0 = packedWitness (compile g) := by
  rw [programTraceTerm_eval, packedWitness_eq_traceCode]

def lastTerm : (m : Nat) → (Fin m → ClosedTerm) → ClosedTerm
  | 0, _ => .zero
  | m+1, σ => σ (Fin.last m)

theorem pairExpr_expansion {n m k : Nat} (ρ : Fin n → TermTriple)
    (σ : Fin m → ClosedTerm) (a b : PackExpr n m) :
    (Term.ofClosed ((pairExpr a b).expand ρ σ) : Term k) =
      (Term.ofClosed (a.expand ρ σ)).pair (Term.ofClosed (b.expand ρ σ)) := by
  simp [pairExpr, PackExpr.expand, Term.ofClosed, Term.pair,
    numeralTerm, bits, numeralTermBits]

theorem valueExpr_expansion {n m k : Nat} (ρ : Fin n → TermTriple)
    (σ : Fin m → ClosedTerm) (i : Fin n) :
    (Term.ofClosed ((valueExpr i).expand ρ σ) : Term k) =
      (Summary.ofTriple (ρ i)).code := by
  simp [valueExpr, pairExpr_expansion, PackExpr.expand, TermTriple.get,
    Summary.ofTriple, Summary.code]

theorem lastExpr_expansion {n m : Nat} (ρ : Fin n → TermTriple)
    (σ : Fin m → ClosedTerm) :
    (lastExpr n m).expand ρ σ = lastTerm m σ := by
  cases m with
  | zero => simp [lastExpr, lastTerm, PackExpr.expand, numeralTerm, bits, numeralTermBits]
  | succ m => rfl

/-- Syntactic identity with the expansion of the previous compact packing
compiler, stronger than merely agreement of numeric denotations. -/
theorem packRefs_expansion {n k : Nat} (ρ : Fin n → TermTriple) (is : List (Fin n)) :
    (Term.ofClosed (lastTerm is.length ((packRefs is).expansion ρ)) : Term k) =
      packedTerms (is.map (fun i => Summary.ofTriple (ρ i))) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [packRefs, List.length_cons, lastTerm, PackingProgram.expansion,
      Fin.lastCases_last, pairExpr_expansion, valueExpr_expansion,
      lastExpr_expansion, List.map_cons, packedTerms]
    exact congrArg ((Summary.ofTriple (ρ i)).code.pair) ih

def packedRoot {n : Nat} (p : Program n) : ClosedTerm :=
  lastTerm (List.finRange n).length ((tracePacking n).expansion p.expansion)

theorem packedRoot_exact {n : Nat} (p : Program n) :
    (Term.ofClosed (packedRoot p) : Term 0) = programTraceTerm p := by
  unfold packedRoot tracePacking
  rw [packRefs_expansion, Quotation.map_finRange]
  rfl

/-- The old compact trace definitions expand to exactly the term used in
these object-level lookup proofs. There is no unproved PA equality bridge. -/
theorem packedRoot_lookup_within {n : Nat} (p : Program n) (i : Fin n) :
    Within (lookup i.val (Term.ofClosed (packedRoot p))
      (Term.ofClosed (p.expansion i).len)
      (Term.ofClosed (p.expansion i).scale)
      (Term.ofClosed (p.expansion i).payload) : Formula 0) (14*i.val+7) := by
  rw [packedRoot_exact]
  exact program_lookup_within p i

def allConj {m : Nat} : List (Formula m) → Formula m
  | [] => .eq .zero .zero
  | f :: fs => f.conj (allConj fs)

theorem allConj_realize {m : Nat} (fs : List (Formula m)) (ρ : Fin m → Nat) :
    (allConj fs).realize ρ ↔ ∀ f ∈ fs, f.realize ρ := by
  induction fs with
  | nil => simp [allConj, Formula.realize]
  | cons f fs ih => simp [allConj, Formula.realize_conj, ih]

theorem Within.mono {m : Nat} {f : Formula m} {k l : Nat}
    (h : Within f k) (hkl : k ≤ l) : Within f l := by
  obtain ⟨d,hd⟩ := h
  exact ⟨d, Nat.le_trans hd hkl⟩

theorem allConj_within {m : Nat} (fs : List (Formula m)) (k : Nat)
    (h : ∀ f ∈ fs, Within f k) :
    Within (allConj fs) (fs.length*(k+3)+3) := by
  induction fs with
  | nil => simpa [allConj] using (Within.refl (Term.zero : Term m))
  | cons f fs ih =>
    have hf := h f (by simp)
    have ht := ih (fun g hg => h g (by simp [hg]))
    simpa [allConj, List.length_cons, Nat.add_mul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using Within.conjunction f (allConj fs) k _ hf ht

def programEntry {n m : Nat} (p : Program n) (z : Term m) (i : Fin n) : Formula m :=
  lookup i.val z (Term.ofClosed (p.expansion i).len)
    (Term.ofClosed (p.expansion i).scale) (Term.ofClosed (p.expansion i).payload)

/-- A program-specialized formula. The program itself is NOT yet an
arithmetic input to one uniform PA checker formula. -/
def traceFormula {n m : Nat} (p : Program n) (z : Term m) : Formula m :=
  allConj (List.ofFn (programEntry p z))

theorem programEntry_realize {n m : Nat} (p : Program n) (z : Term m)
    (i : Fin n) (ρ : Fin m → Nat) :
    (programEntry p z i).realize ρ ↔ readValue (z.eval ρ) i.val = some (p.eval i) := by
  simp only [programEntry, lookup_realize, Term.eval_ofClosed]
  change (readValue (z.eval ρ) i.val = some ((p.expansion i).eval)) ↔ _
  rw [congrFun (Program.expansion_eval p) i]

/-- Exact agreement on arbitrary, including malformed, trace codes. -/
theorem traceFormula_realize {n m : Nat} (p : Program n) (z : Term m)
    (ρ : Fin m → Nat) :
    (traceFormula p z).realize ρ ↔ checkTrace p (z.eval ρ) = true := by
  have he : (traceFormula p z).realize ρ ↔
      ∀ i : Fin n, readValue (z.eval ρ) i.val = some (p.eval i) := by
    simp [traceFormula, allConj_realize, List.mem_ofFn, programEntry_realize]
  rw [he]
  exact ⟨checkTrace_of_lookup p (z.eval ρ), checkTrace_sound p (z.eval ρ)⟩

/-- A genuine finite object-calculus derivation exists with a quadratic
node bound. Neither serialized character length nor uniform Bew is claimed. -/
theorem traceFormula_within {n : Nat} (p : Program n) :
    Within (traceFormula p (Term.ofClosed (packedRoot p)) : Formula 0)
      (n*(14*n+10)+3) := by
  have h : ∀ f ∈ List.ofFn (programEntry p (Term.ofClosed (packedRoot p)) : Fin n → Formula 0),
      Within f (14*n+7) := by
    intro f hf
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
    apply (packedRoot_lookup_within p i).mono
    have hi := i.isLt
    omega
  simpa [traceFormula, Nat.add_assoc] using allConj_within _ (14*n+7) h

theorem lookup_zero_rejected (i : Nat) {m : Nat} (l s v : Term m) (ρ : Fin m → Nat) :
    ¬ (lookup i .zero l s v).realize ρ := by
  rw [lookup_realize]
  simp [Term.eval, Quotation.readValue_zero]

end MAISO11.Arithmetic

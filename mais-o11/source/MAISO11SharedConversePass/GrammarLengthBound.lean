import FragmentBalance
set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Quotation

/-- Expanding a fragment of k atoms uses at most k times the longest available
word length, with terminal characters contributing one. -/
theorem expandFragment_length_le {b n : Nat} (env : Fin n → Word b)
    (B : Nat) (hB : 1 ≤ B) (he : ∀ i, (env i).length ≤ B)
    (f : Fragment b n) :
    (expandFragment env f).length ≤ f.length * B := by
  induction f with
  | nil => simp [expandFragment]
  | cons a f ih =>
    have ha : (a.expand env).length ≤ B := by
      cases a with
      | char c => exact hB
      | use i => exact he i
    simp only [expandFragment,List.length_append,List.length_cons,
      Nat.add_mul,Nat.one_mul]
    omega

/-- The mass charges every right-hand-side atom and every definition.
Every expanded word has exponentially bounded length, including grammars
whose fragments cross syntax or parenthesis boundaries. No fixed alphabet
size assumption is needed for this token-count bound. -/
theorem Grammar.words_length_lt_pow_mass {b n : Nat} (g : Grammar b n)
    (i : Fin n) : (g.words i).length < 2 ^ g.mass := by
  induction g with
  | nil => exact Fin.elim0 i
  | @snoc n g f ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Grammar.words,Fin.lastCases_last,Grammar.mass]
      have he := expandFragment_length_le g.words (2^g.mass)
        Nat.one_le_two_pow (fun j => Nat.le_of_lt (ih j)) f
      have hm := Nat.mul_le_mul_right (2^g.mass)
        (Nat.le_of_lt (Nat.lt_two_pow_self (n := f.length)))
      have hb : (expandFragment g.words f).length ≤ 2^(g.mass+f.length) := by
        rw [Nat.pow_add,Nat.mul_comm]
        exact Nat.le_trans he hm
      have hp := Nat.two_pow_pos (g.mass+f.length)
      rw [Nat.pow_succ]
      omega
    · simp only [Grammar.words,Fin.lastCases_castSucc,Grammar.mass]
      exact Nat.lt_of_lt_of_le (ih j)
        (Nat.pow_le_pow_right (by decide) (by omega))

/-- A particular serialization may supply a bound on mass by its physical
character length. Names and record overhead can only make that length larger. -/
theorem Grammar.words_length_lt_pow_budget {b n : Nat} (g : Grammar b n)
    (i : Fin n) (L : Nat) (hL : g.mass ≤ L) :
    (g.words i).length < 2^L :=
  Nat.lt_of_lt_of_le (g.words_length_lt_pow_mass i)
    (Nat.pow_le_pow_right (by decide) hL)

end MAISO11.Quotation

namespace MAISO11.FragmentBalance
open MAISO11.Quotation

theorem charWeight_bounds {b : Nat} (op cl c : Fin b) :
    -1 ≤ charWeight op cl c ∧ charWeight op cl c ≤ 1 := by
  unfold charWeight
  split
  · decide
  · split <;> decide

/-- A stream of unit delimiter changes cannot have net change or minimum
prefix magnitude larger than its number of characters. -/
theorem summarize_bounds (xs : List Int)
    (h : ∀ d ∈ xs, -1 ≤ d ∧ d ≤ 1) :
    -(xs.length : Int) ≤ (summarize xs).net ∧
      (summarize xs).net ≤ (xs.length : Int) ∧
      -(xs.length : Int) ≤ (summarize xs).floor ∧
      (summarize xs).floor ≤ 0 := by
  induction xs with
  | nil => simp [summarize,Summary.empty]
  | cons d ds ih =>
    have hd := h d (by simp)
    have ht := ih (fun e he => h e (by simp [he]))
    simp only [summarize,Summary.join,Summary.atom,List.length_cons]
    omega

theorem wordSummary_bounds {b : Nat} (op cl : Fin b) (w : Word b) :
    -(w.length : Int) ≤ (wordSummary op cl w).net ∧
      (wordSummary op cl w).net ≤ (w.length : Int) ∧
      -(w.length : Int) ≤ (wordSummary op cl w).floor ∧
      (wordSummary op cl w).floor ≤ 0 := by
  have h : ∀ d ∈ w.map (charWeight op cl), -1 ≤ d ∧ d ≤ 1 := by
    intro d hd
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hd
    exact charWeight_bounds op cl c
  simpa only [wordSummary,List.length_map] using
    summarize_bounds (w.map (charWeight op cl)) h

theorem natAbs_le_of_bounds (z : Int) (N : Nat)
    (hl : -(N : Int) ≤ z) (hu : z ≤ (N : Int)) : z.natAbs ≤ N := by
  cases z with
  | ofNat z => exact Int.ofNat_le.mp hu
  | negSucc z => change z+1 ≤ N; omega

theorem wordSummary_abs_le_length {b : Nat} (op cl : Fin b) (w : Word b) :
    (wordSummary op cl w).net.natAbs ≤ w.length ∧
      (wordSummary op cl w).floor.natAbs ≤ w.length := by
  obtain ⟨hnl,hnu,hfl,hfu⟩ := wordSummary_bounds op cl w
  exact ⟨natAbs_le_of_bounds _ _ hnl hnu,
    natAbs_le_of_bounds _ _ hfl (by omega)⟩

/-- Both integers of every grammar summary have magnitude below 2^mass. -/
theorem grammarSummary_abs_lt_pow_mass {b n : Nat} (op cl : Fin b)
    (g : Grammar b n) (i : Fin n) :
    (grammarSummary op cl g i).net.natAbs < 2^g.mass ∧
      (grammarSummary op cl g i).floor.natAbs < 2^g.mass := by
  rw [grammarSummary_correct]
  have hw := g.words_length_lt_pow_mass i
  obtain ⟨hn,hf⟩ := wordSummary_abs_le_length op cl (g.words i)
  exact ⟨Nat.lt_of_le_of_lt hn hw,Nat.lt_of_le_of_lt hf hw⟩

/-- Bit length of a nonnegative magnitude, with zero encoded by no magnitude
bits. A separate sign bit is counted by `signedBits`. -/
def magnitudeBits (N : Nat) : Nat := if N = 0 then 0 else N.log2 + 1

def signedBits (z : Int) : Nat := magnitudeBits z.natAbs + 1

theorem magnitudeBits_le_of_lt_pow (N m : Nat) (h : N < 2^m) :
    magnitudeBits N ≤ m := by
  by_cases hz : N = 0
  · simp [magnitudeBits,hz]
  · have hl := (Nat.log2_lt hz).mpr h
    simp only [magnitudeBits,hz,if_false]
    omega

/-- Each balance component uses at most mass+1 signed-magnitude bits.
This is a representation bound, not a running-time theorem. -/
theorem grammarSummary_signedBits_le {b n : Nat} (op cl : Fin b)
    (g : Grammar b n) (i : Fin n) :
    signedBits (grammarSummary op cl g i).net ≤ g.mass+1 ∧
      signedBits (grammarSummary op cl g i).floor ≤ g.mass+1 := by
  obtain ⟨hn,hf⟩ := grammarSummary_abs_lt_pow_mass op cl g i
  have hnb := magnitudeBits_le_of_lt_pow _ _ hn
  have hfb := magnitudeBits_le_of_lt_pow _ _ hf
  simp only [signedBits]
  omega

theorem grammarSummary_total_signedBits_le {b n : Nat} (op cl : Fin b)
    (g : Grammar b n) (i : Fin n) :
    signedBits (grammarSummary op cl g i).net +
      signedBits (grammarSummary op cl g i).floor ≤ 2*(g.mass+1) := by
  obtain ⟨hn,hf⟩ := grammarSummary_signedBits_le op cl g i
  omega

theorem cachedGrammarSummary_signedBits_le {b n : Nat} (op cl : Fin b)
    (g : Grammar b n) (i : Fin n) :
    signedBits ((cachedGrammarSummary op cl g)[i]).net ≤ g.mass+1 ∧
      signedBits ((cachedGrammarSummary op cl g)[i]).floor ≤ g.mass+1 := by
  have he : (cachedGrammarSummary op cl g)[i] = grammarSummary op cl g i := by
    rw [cachedGrammarSummary_correct,grammarSummary_correct]
  rw [he]
  exact grammarSummary_signedBits_le op cl g i

private theorem sum_le_length_mul (xs : List Nat) (B : Nat)
    (h : ∀ x ∈ xs, x ≤ B) : xs.sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- The signed numeric payloads of all n materialized summaries together
have a quadratic bit bound. Vector metadata and operation costs are excluded. -/
theorem cachedGrammarSummary_table_bits_le {b n : Nat} (op cl : Fin b)
    (g : Grammar b n) :
    (List.ofFn (fun i : Fin n =>
      signedBits ((cachedGrammarSummary op cl g)[i]).net +
        signedBits ((cachedGrammarSummary op cl g)[i]).floor)).sum ≤
      2*g.mass*(g.mass+1) := by
  have hp : ∀ x ∈ (List.ofFn (fun i : Fin n =>
      signedBits ((cachedGrammarSummary op cl g)[i]).net +
        signedBits ((cachedGrammarSummary op cl g)[i]).floor)),
      x ≤ 2*(g.mass+1) := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨hn,hf⟩ := cachedGrammarSummary_signedBits_le op cl g i
    omega
  have hs := sum_le_length_mul _ (2*(g.mass+1)) hp
  simp only [List.length_ofFn] at hs
  have hm := Nat.mul_le_mul_right (2*(g.mass+1)) g.count_le_mass
  have he : g.mass*(2*(g.mass+1)) = 2*g.mass*(g.mass+1) := by
    simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  rw [he] at hm
  exact Nat.le_trans hs hm

end MAISO11.FragmentBalance

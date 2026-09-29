import FragmentBalance

/-!
Arithmetic decoding bridge for the length-retaining, unmarked base-b code.
STATUS: source pending kernel verification. These are semantic Lean statements,
not derivations in PA and not a theorem about the specified Bew predicate.
The recursion runs over expanded length; it is a specification, not the
compressed polynomial-time algorithm. In particular no small-size claim is
made for numerals naming the expanded raw payload.
-/

set_option autoImplicit false

namespace MAISO11.CodedScan

open MAISO11.Quotation MAISO11.FragmentBalance

/-- Retain exactly n low-order digits, including leading zeroes. -/
def decode {b : Nat} (hb : 0 < b) : Nat → Nat → Word b
  | 0, _ => []
  | n + 1, c => decode hb n (c / b) ++ [⟨c % b, Nat.mod_lt c hb⟩]

/-- Arithmetic scan; no intermediate decoded list occurs in this definition. -/
def scanCode {b : Nat} (hb : 0 < b) (op cl : Fin b) : Nat → Nat → Summary
  | 0, _ => Summary.empty
  | n + 1, c =>
      (scanCode hb op cl n (c / b)).join
        (Summary.atom (charWeight op cl ⟨c % b, Nat.mod_lt c hb⟩))

@[simp] theorem decode_length {b : Nat} (hb : 0 < b) (n c : Nat) :
    (decode hb n c).length = n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp [decode, ih]

theorem wordSummary_singleton {b : Nat} (op cl a : Fin b) :
    wordSummary op cl [a] = Summary.atom (charWeight op cl a) := by
  change (Summary.atom (charWeight op cl a)).join Summary.empty = _
  apply Summary.join_empty
  simp only [Summary.atom]
  omega

theorem scanCode_correct {b : Nat} (hb : 0 < b) (op cl : Fin b)
    (n c : Nat) :
    scanCode hb op cl n c = wordSummary op cl (decode hb n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      simp only [scanCode, decode, wordSummary_append, wordSummary_singleton, ih]

private theorem decode_raw_reverse {b : Nat} (hb : 0 < b) (w : Word b) :
    decode hb w.reverse.length (rawCode b w.reverse) = w.reverse := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp only [List.reverse_cons, List.length_append, List.length_singleton,
        rawCode_append, rawCode, List.length_nil, Nat.pow_zero,
        Nat.mul_one, Nat.add_zero, Nat.pow_one, decode]
      have hd : (rawCode b w.reverse * b + a.val) / b = rawCode b w.reverse := by
        rw [Nat.mul_comm (rawCode b w.reverse) b, Nat.mul_add_div hb]
        simp [Nat.div_eq_of_lt a.isLt]
      have hm : (rawCode b w.reverse * b + a.val) % b = a.val := by
        simp [Nat.mod_eq_of_lt a.isLt]
      rw [hd, ih]
      have he : (⟨(rawCode b w.reverse * b + a.val) % b,
          Nat.mod_lt _ hb⟩ : Fin b) = a := Fin.ext hm
      rw [he]

/-- The separate length field prevents loss of leading zero characters. -/
theorem decode_raw {b : Nat} (hb : 0 < b) (w : Word b) :
    decode hb w.length (rawCode b w) = w := by
  simpa only [List.reverse_reverse] using decode_raw_reverse hb w.reverse

theorem raw_decode {b : Nat} (hb : 0 < b) (n c : Nat)
    (hc : c < b ^ n) : rawCode b (decode hb n c) = c := by
  induction n generalizing c with
  | zero =>
      have : c = 0 := by simp only [Nat.pow_zero] at hc; omega
      simp [decode, rawCode, this]
  | succ n ih =>
      have hq : c / b < b ^ n := by
        apply (Nat.div_lt_iff_lt_mul hb).2
        simpa only [Nat.pow_succ] using hc
      simp only [decode, rawCode_append, rawCode, List.length_singleton,
        List.length_nil, Nat.pow_zero, Nat.mul_one, Nat.add_zero, Nat.pow_one]
      rw [ih (c / b) hq]
      rw [Nat.mul_comm (c / b) b, Nat.add_comm]
      exact Nat.mod_add_div c b

/-- Exact concatenation for valid length/payload pairs. No positivity of the
lengths is required, and base 1 is permitted if it has an inhabitant. -/
theorem decode_concat {b : Nat} (hb : 0 < b) (nx ny cx cy : Nat)
    (hx : cx < b ^ nx) (hy : cy < b ^ ny) :
    decode hb (nx + ny) (cx * b ^ ny + cy) =
      decode hb nx cx ++ decode hb ny cy := by
  have h := decode_raw hb (decode hb nx cx ++ decode hb ny cy)
  simpa only [List.length_append, decode_length, rawCode_append,
    raw_decode hb nx cx hx, raw_decode hb ny cy hy] using h

theorem scanCode_concat {b : Nat} (hb : 0 < b) (op cl : Fin b)
    (nx ny cx cy : Nat) (hx : cx < b ^ nx) (hy : cy < b ^ ny) :
    scanCode hb op cl (nx + ny) (cx * b ^ ny + cy) =
      (scanCode hb op cl nx cx).join (scanCode hb op cl ny cy) := by
  rw [scanCode_correct, decode_concat hb nx ny cx cy hx hy, wordSummary_append,
    ← scanCode_correct, ← scanCode_correct]

/-- Bridge for each actual expanded grammar word, using the existing raw code. -/
theorem scanCode_raw {b : Nat} (hb : 0 < b) (op cl : Fin b) (w : Word b) :
    scanCode hb op cl w.length (rawCode b w) = wordSummary op cl w := by
  rw [scanCode_correct, decode_raw]

theorem cachedGrammarSummary_eq_scanCode {b n : Nat} (hb : 0 < b)
    (op cl : Fin b) (g : Grammar b n) (i : Fin n) :
    (cachedGrammarSummary op cl g)[i] =
      scanCode hb op cl (g.words i).length (rawCode b (g.words i)) := by
  rw [cachedGrammarSummary_correct, scanCode_raw]

end MAISO11.CodedScan

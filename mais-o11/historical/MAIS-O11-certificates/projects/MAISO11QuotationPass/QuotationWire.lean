import StringQuotation

/-! Actual finite-alphabet serialization and a checked polynomial character bound.
Identifiers are u followed by a unary bit-length header, 0, and the binary digits
of index+1. Digits in identifier bodies are most-significant-first. Numeral terms
use unary binary constructors D(x)=2x and E(x)=2x+1.
-/

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.Quotation

/-- Least-significant-first bits. This function computes no expanded string. -/
def bits : Nat → List Bool
  | 0 => []
  | n + 1 => decide ((n + 1) % 2 = 1) :: bits ((n + 1) / 2)
termination_by n => n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

def bitValue : List Bool → Nat
  | [] => 0
  | b :: bs => 2 * bitValue bs + if b then 1 else 0

theorem bits_value (n : Nat) : bitValue (bits n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [bits, bitValue]
    | succ n =>
      rw [bits, bitValue, ih ((n + 1) / 2) (Nat.div_lt_self (by omega) (by omega))]
      have hm := Nat.mod_lt (n + 1) (by decide : 0 < 2)
      have hd := Nat.mod_add_div (n + 1) 2
      by_cases hb : (n + 1) % 2 = 1
      · simp only [hb, decide_true, Bool.true_eq, ↓reduceIte]; omega
      · simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

theorem bits_length_le (n : Nat) : (bits n).length ≤ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [bits]
    | succ n =>
      have hd : (n + 1) / 2 < n + 1 := Nat.div_lt_self (by omega) (by decide : 1 < 2)
      have hh := ih ((n + 1) / 2) hd
      simp only [bits, List.length_cons]
      omega

def bitChar (b : Bool) : Char := if b then '1' else '0'

def identifier (i : Nat) : List Char :=
  ['u'] ++ List.replicate (bits (i + 1)).length '1' ++ ['0'] ++
    ((bits (i + 1)).reverse.map bitChar)

theorem identifier_length (i : Nat) :
    (identifier i).length = 2 * (bits (i + 1)).length + 2 := by
  simp [identifier]; omega

theorem identifier_length_le (i : Nat) : (identifier i).length ≤ 2 * i + 4 := by
  rw [identifier_length]
  have := bits_length_le (i + 1)
  omega

def readUnary : List Char → Option (Nat × List Char)
  | '0' :: cs => some (0, cs)
  | '1' :: cs => do
    let (k, rest) ← readUnary cs
    pure (k + 1, rest)
  | _ => none

def readBits : Nat → List Char → Option (List Bool × List Char)
  | 0, cs => some ([], cs)
  | n + 1, '0' :: cs => do
    let (bs, rest) ← readBits n cs
    pure (false :: bs, rest)
  | n + 1, '1' :: cs => do
    let (bs, rest) ← readBits n cs
    pure (true :: bs, rest)
  | _, _ => none

def readIdentifier : List Char → Option (Nat × List Char)
  | 'u' :: cs => do
    let (k, rest) ← readUnary cs
    let (bs, tail) ← readBits k rest
    let v := bitValue bs.reverse
    if v = 0 then none else pure (v - 1, tail)
  | _ => none

theorem readUnary_encode (n : Nat) (tail : List Char) :
    readUnary (List.replicate n '1' ++ '0' :: tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, readUnary, ih]

theorem readBits_encode (bs : List Bool) (tail : List Char) :
    readBits bs.length (bs.map bitChar ++ tail) = some (bs, tail) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [bitChar, readBits, ih]

/-- A framing theorem: an identifier decodes without consuming the next token. -/
theorem readIdentifier_encode (i : Nat) (tail : List Char) :
    readIdentifier (identifier i ++ tail) = some (i, tail) := by
  simp only [identifier, List.append_assoc, List.cons_append, List.nil_append]
  rw [readIdentifier, readUnary_encode]
  simp only [bind, Option.bind]
  rw [show (bits (i + 1)).length = (bits (i + 1)).reverse.length by simp,
    readBits_encode]
  simp [bits_value]

theorem identifier_injective {i j : Nat} (h : identifier i = identifier j) : i = j := by
  have hh := congrArg readIdentifier h
  have hi := readIdentifier_encode i []
  have hj := readIdentifier_encode j []
  simp only [List.append_nil] at hi hj
  rw [hi, hj] at hh
  exact congrArg Prod.fst (Option.some.inj hh)

theorem register_lt {n : Nat} (i : Fin n) (s : Slot) :
    3 * i.val + s.offset < 3 * n := by
  have := i.isLt
  have := s.offset_le_two
  omega

theorem fresh_register {n : Nat} (i : Fin n) (s t : Slot) :
    identifier (3 * i.val + s.offset) ≠ identifier (3 * n + t.offset) := by
  intro h
  have he := identifier_injective h
  have hl := register_lt i s
  omega

def numeralBits : List Bool → List Char
  | [] => ['0']
  | b :: bs => ['(', if b then 'E' else 'D'] ++ numeralBits bs ++ [')']

def numeral (n : Nat) : List Char := numeralBits (bits n)

theorem numeralBits_length (bs : List Bool) :
    (numeralBits bs).length = 3 * bs.length + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [numeralBits, ih]; omega

theorem numeral_length_le (n : Nat) : (numeral n).length ≤ 3 * n + 1 := by
  unfold numeral
  rw [numeralBits_length]
  have := bits_length_le n
  omega

def Expr.wire {n : Nat} : Expr n → List Char
  | .num k => numeral k
  | .ref i s => identifier (3 * i.val + s.offset)
  | .add x y => ['(', '+'] ++ x.wire ++ y.wire ++ [')']
  | .mul x y => ['(', '*'] ++ x.wire ++ y.wire ++ [')']

theorem Expr.wire_length {n : Nat} (e : Expr n) :
    e.wire.length ≤ (6 * n + 7) * e.weight := by
  induction e with
  | num k =>
    have h := numeral_length_le k
    simp only [wire, weight]
    have hn : 3 ≤ 6 * n + 7 := by omega
    have hh := Nat.mul_le_mul_right (k + 1) hn
    omega
  | ref i s =>
    have h := identifier_length_le (3 * i.val + s.offset)
    have hs := s.offset_le_two
    have hi := i.isLt
    simp only [wire, weight, Nat.mul_one]
    omega
  | add x y hx hy =>
    simp only [wire, List.length_append, List.length_cons, List.length_nil, weight]
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  | mul x y hx hy =>
    simp only [wire, List.length_append, List.length_cons, List.length_nil, weight]
    simp only [Nat.mul_add, Nat.mul_one]
    omega

def definition {n : Nat} (i : Nat) (s : Slot) (e : Expr n) : List Char :=
  "def ".toList ++ identifier (3 * i + s.offset) ++ " := ".toList ++ e.wire ++ ['\n']

def Triple.wire {n : Nat} (t : Triple n) : List Char :=
  definition n .len t.len ++ definition n .scale t.scale ++ definition n .payload t.payload

theorem definition_length {n : Nat} (s : Slot) (e : Expr n) :
    (definition n s e).length ≤ (6 * n + 20) * (e.weight + 1) := by
  have he := e.wire_length
  have hn := identifier_length_le (3 * n + s.offset)
  have hs := s.offset_le_two
  simp only [definition, List.length_append, List.length_cons, List.length_nil]
  change 4 + (identifier (3 * n + s.offset)).length + 4 + e.wire.length + (1 + 0) ≤ _
  have hm := Nat.mul_le_mul_right e.weight (show 6 * n + 7 ≤ 6 * n + 20 by omega)
  simp only [Nat.mul_add, Nat.mul_one]
  omega

theorem Triple.wire_length {n : Nat} (t : Triple n) :
    t.wire.length ≤ (6 * n + 20) * (t.weight + 3) := by
  have hl := definition_length Slot.len t.len
  have hs := definition_length Slot.scale t.scale
  have hp := definition_length Slot.payload t.payload
  simp only [Triple.wire, List.length_append, Triple.weight]
  simp only [Nat.mul_add, Nat.mul_one] at *
  omega

def Program.wire {n : Nat} : Program n → List Char
  | .nil => []
  | .snoc p t => p.wire ++ t.wire

theorem Program.wire_length {n : Nat} (p : Program n) :
    p.wire.length ≤ (6 * n + 20) * (p.weight + 3 * n) := by
  induction p with
  | nil => simp [wire, weight]
  | @snoc n p t ih =>
    have ht := t.wire_length
    have hs := Nat.mul_le_mul_right (p.weight + t.weight + 3 * n + 3)
      (show 6 * n + 20 ≤ 6 * (n + 1) + 20 by omega)
    simp only [wire, List.length_append, weight]
    have h : p.wire.length + t.wire.length ≤
        (6 * n + 20) * (p.weight + t.weight + 3 * n + 3) := by
      simp only [Nat.mul_add] at *
      omega
    calc
      _ ≤ (6 * n + 20) * (p.weight + t.weight + 3 * n + 3) := h
      _ ≤ (6 * (n + 1) + 20) * (p.weight + t.weight + 3 * n + 3) := hs
      _ = _ := by congr 1

/-- A cubic polynomial in written input mass for every fixed alphabet base. -/
theorem compile_characters {b n : Nat} (g : Grammar b n) :
    (compile g).wire.length ≤
      (6 * g.mass + 20) * (4 * (b + 4) * g.mass ^ 2 + 3 * g.mass) := by
  have hw := (compile g).wire_length
  have ht := compile_weight g
  have hn := g.count_le_mass
  have ha : 6 * n + 20 ≤ 6 * g.mass + 20 := by omega
  have hb : (compile g).weight + 3 * n ≤
      4 * (b + 4) * g.mass ^ 2 + 3 * g.mass := by omega
  exact Nat.le_trans hw (Nat.mul_le_mul ha hb)

end MAISO11.Quotation

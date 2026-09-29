import SharedPrelude
set_option autoImplicit false
set_option warningAsError true
open MAISO11.Wire MAISO11.Quotation

def doublingDefs : (n : Nat) → CDefs (n+1)
  | 0 => .snoc .nil .zero
  | n+1 => .snoc (doublingDefs n)
      (.add (.ref (Fin.last n)) (.ref (Fin.last n)))

theorem doublingDefs_wire (n : Nat) :
    (doublingDefs n).wire = (doublingProgram n).wire := by
  induction n with
  | zero =>
    simp [doublingDefs,CDefs.wire,sharedDefinition,doublingProgram,
      PackingProgram.wire,packingDefinition,PackExpr.wire,CTerm.wire,
      numeral,numeralBits,bits]
  | succ n ih =>
    simp [doublingDefs,CDefs.wire,sharedDefinition,
      doublingProgram,PackingProgram.wire,packingDefinition,PackExpr.wire,
      CTerm.wire,ih]

theorem doublingDefs_expand (n : Nat) :
    (doublingDefs n).expand (Fin.last n) = doubledTree n := by
  induction n with
  | zero => simp only [doublingDefs,CDefs.expand,Fin.lastCases_last,CTerm.close,doubledTree]
  | succ n ih =>
    simp only [doublingDefs,CDefs.expand,Fin.lastCases_last,
      CTerm.close,doubledTree,Fin.lastCases_castSucc,ih]

theorem doublingDefs_characters (n : Nat) :
    (doublingDefs n).wire.length ≤ (2*n+22)*(4*n+2) := by
  rw [doublingDefs_wire]
  exact doublingProgram_characters n

theorem parseActualDoublingPrelude (n : Nat) :
    parseSharedPrelude (n+1) (doublingProgram n).wire =
      some (doublingDefs n) := by
  rw [← doublingDefs_wire]
  exact parseSharedPrelude_wire _

private def expect (name : String) (ok : Bool) : IO Unit :=
  if ok then IO.println ("PASS: " ++ name)
  else throw (IO.userError ("FAIL: " ++ name))

#eval expect "actual 61-definition prelude parses without expanding"
  ((parseSharedPrelude 61 (doublingProgram 60).wire).isSome)

-- The expanded root has 2^61 - 1 nodes. The test above never evaluates it.
#print axioms MAISO11.Wire.parseSharedPrelude_refines_old
#print axioms MAISO11.Wire.parseSharedPrelude_sound_wire
#print axioms MAISO11.Wire.parseSharedPrelude_mass_le_input
#print axioms MAISO11.Wire.two_definition_readers_agree_on_wire
#print axioms parseActualDoublingPrelude
#print axioms doublingDefs_expand
#print axioms doublingDefs_characters

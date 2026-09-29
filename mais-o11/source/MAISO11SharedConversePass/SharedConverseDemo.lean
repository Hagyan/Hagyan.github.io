import SharedConverse
import SharedPreludeDemo
set_option autoImplicit false
set_option warningAsError true
open MAISO11.Wire MAISO11.Quotation

def reflexivityRecords : Records 61 1 :=
  .snoc .nil (.axiom (.all (.eq (.var 0) (.var 0))))

theorem decodeActualDoublingFile :
    decodeWholeShared 61 1
      ((doublingProgram 60).wire ++ reflexivityRecords.wire) =
        some ⟨doublingDefs 60,1,reflexivityRecords⟩ := by
  rw [← doublingDefs_wire]
  exact decodeWholeShared_wire _ _

private def expect (name : String) (ok : Bool) : IO Unit :=
  if ok then IO.println ("PASS: " ++ name)
  else throw (IO.userError ("FAIL: " ++ name))

-- This decodes an actual definition prelude and proof record without
-- materializing the final abbreviation's 2^61 - 1 expanded syntax nodes.
#eval expect "61-definition complete proof file decoded compactly"
  ((decodeWholeShared 61 1
    ((doublingProgram 60).wire ++ reflexivityRecords.wire)).isSome)

#print axioms MAISO11.Wire.oldTerm_sound
#print axioms MAISO11.Wire.oldDefinition_complete
#print axioms MAISO11.Wire.oldPrelude_complete
#print axioms MAISO11.Wire.sharedPrelude_iff_old
#print axioms MAISO11.Wire.decodeWholeShared_iff_old
#print axioms MAISO11.Wire.checkWholeSharedReference_eq_old
#print axioms MAISO11.Wire.checkWholeSharedReference_sound
#print axioms decodeActualDoublingFile

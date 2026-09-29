import CompactChecker
set_option autoImplicit false
set_option warningAsError true

/-- Counts are supplied explicitly because the certified grammar has no header. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [registers,records,path] =>
    match registers.toNat?,records.toNat? with
    | some r,some k =>
      let bytes ← IO.FS.readFile path
      match MAISO11.Wire.checkWhole r k bytes.toList with
      | some f =>
        IO.println "ACCEPT: final expanded formula"
        IO.println (reprStr f)
        return 0
      | none =>
        IO.eprintln "REJECT: malformed file or invalid proof in the supported calculus"
        return 1
    | _,_ =>
      IO.eprintln "Register and record counts must be natural numbers."
      return 2
  | _ =>
    IO.eprintln "Usage: lake exe pabincheck <register-count> <record-count> <file>"
    return 2

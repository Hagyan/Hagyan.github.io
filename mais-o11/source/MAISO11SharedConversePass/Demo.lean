import Examples
import TracePacking

open MAISO11.Quotation

def main : IO Unit := do
  let p := compile boundaryExample
  IO.println s!"Boundary-crossing example: mass {boundaryExample.mass}; quotation definitions {p.wire.length} characters; local certificate {p.certifiedWire.length} characters."
  let boundaryWord := boundaryExample.words (Fin.last 2)
  IO.println s!"Expanded final fragment: {String.mk (boundaryWord.map (fun a => Char.ofNat a.val))}"
  IO.println s!"Length: {boundaryWord.length}; marked base-128 code: {markedCode 128 boundaryWord}."
  -- Executing the expanded checker here would materialize expanded arithmetic
  -- terms. The universal acceptance theorem is used instead; do not try this
  -- evaluation for the large examples below.
  IO.FS.writeFile "boundary-quotation.pabin" (String.mk p.certifiedWire)
  let traceDefs := (tracePacking 3).wire
  IO.FS.writeFile "boundary-quotation-with-trace.pabin" (String.mk (p.certifiedWire ++ traceDefs))
  IO.println s!"Additional encoded-trace definitions: {traceDefs.length} characters; complete fragment {p.certifiedWire.length + traceDefs.length} characters."
  for n in [8, 16, 32, 64] do
    let g := doubling (b := 128) ⟨48, by decide⟩ n
    let q := compile g
    -- Only produce syntax. Never evaluate q.eval: its scale has exponentially
    -- many bits. 2^n is the expanded length, not the expanded code itself.
    let traceLen := (tracePacking (n + 1)).wire.length
    IO.println s!"Doubling {n}: input mass {g.mass}; expanded length {2 ^ n}; definitions {q.wire.length} characters; local certificate {q.certifiedWire.length} characters; extra trace definitions {traceLen} characters."
  IO.println "These are quotation and local equality certificates, not proofs of Bew or of MAIS-O11."

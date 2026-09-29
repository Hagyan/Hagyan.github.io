import ChosenSystemExpansion

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.ChosenSystem
open MAISO11.Quotation

/-- Read the unary length header used in a binary identifier. -/
def readUnarySymbols {b : Nat} (zero one : Fin b) : Word b → Option (Nat × Word b)
  | [] => none
  | c :: rest =>
      if c = zero then some (0, rest)
      else if c = one then do
        let (n, tail) ← readUnarySymbols zero one rest
        pure (n + 1, tail)
      else none

theorem readUnarySymbols_encode {b : Nat} (zero one : Fin b)
    (hne : zero ≠ one) (n : Nat) (tail : Word b) :
    readUnarySymbols zero one (List.replicate n one ++ zero :: tail) =
      some (n, tail) := by
  induction n with
  | zero => simp [readUnarySymbols]
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, readUnarySymbols]
      simp [hne.symm, ih]

/-- Read exactly `n` binary digits from the finite alphabet. -/
def readBitsSymbols {b : Nat} (zero one : Fin b) :
    Nat → Word b → Option (List Bool × Word b)
  | 0, rest => some ([], rest)
  | _n + 1, [] => none
  | n + 1, c :: rest =>
      if c = zero then do
        let (bits, tail) ← readBitsSymbols zero one n rest
        pure (false :: bits, tail)
      else if c = one then do
        let (bits, tail) ← readBitsSymbols zero one n rest
        pure (true :: bits, tail)
      else none

theorem readBitsSymbols_encode {b : Nat} (zero one : Fin b)
    (hne : zero ≠ one) (bits : List Bool) (tail : Word b) :
    readBitsSymbols zero one bits.length
      (bits.map (fun bit => if bit then one else zero) ++ tail) =
      some (bits, tail) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      cases bit <;> simp [readBitsSymbols, hne, hne.symm, ih]

/-- Decode a self-delimiting binary identifier directly over the finite
alphabet. The returned tail is preserved, so adjacent tokens remain framed. -/
def readIdentifierSymbols {b : Nat} (start zero one : Fin b) :
    Word b → Option (Nat × Word b)
  | [] => none
  | c :: rest =>
      if c = start then
        match readUnarySymbols zero one rest with
        | none => none
        | some (width, rest) =>
          match readBitsSymbols zero one width rest with
          | none => none
          | some (bits, tail) =>
            let value := Quotation.bitValue bits.reverse
            if value = 0 then none else some (value - 1, tail)
      else none

theorem readIdentifierSymbols_encode {b : Nat} (start zero one : Fin b)
    (hne : zero ≠ one) (i : Nat) (tail : Word b) :
    readIdentifierSymbols start zero one
      (binaryIdentifierCode start zero one i ++ tail) = some (i, tail) := by
  unfold readIdentifierSymbols
  simp only [binaryIdentifierCode, List.cons_append, List.append_assoc,
    List.nil_append, if_pos rfl]
  rw [readUnarySymbols_encode zero one hne (bits (i + 1)).length
    (((bits (i + 1)).reverse.map (fun bit => if bit then one else zero)) ++ tail)]
  simp only [if_true]
  have hbits : readBitsSymbols zero one (bits (i + 1)).length
      ((bits (i + 1)).reverse.map (fun bit => if bit then one else zero) ++ tail) =
        some ((bits (i + 1)).reverse, tail) := by
    simpa using readBitsSymbols_encode zero one hne (bits (i + 1)).reverse tail
  rw [hbits]
  simp [Quotation.bits_value]

/-- Decode one explicit-kind fragment token. Literal payload characters are
consumed only after `literalTag`; a reference begins only after `referenceTag`. -/
def parseTaggedAtom {b n : Nat} (literalTag referenceTag start zero one : Fin b) :
    Word b → Option (Atom b n × Word b)
  | [] => none
  | tag :: rest =>
      if tag = literalTag then
        match rest with
        | [] => none
        | c :: tail => some (.char c, tail)
      else if tag = referenceTag then
        match readIdentifierSymbols start zero one rest with
        | none => none
        | some (index, tail) =>
          if h : index < n then some (.use ⟨index, h⟩, tail) else none
      else none

theorem parseTaggedAtom_serializeAtom {b n : Nat}
    (literalTag referenceTag start zero one : Fin b)
    (hlt : literalTag ≠ referenceTag) (hne : zero ≠ one)
    (a : Atom b n) (tail : Word b) :
    parseTaggedAtom literalTag referenceTag start zero one
      (serializeAtom literalTag referenceTag
        (fun i => binaryIdentifierCode start zero one i) a ++ tail) =
      some (a, tail) := by
  cases a with
  | char c => simp [parseTaggedAtom, serializeAtom, hlt]
  | use i =>
      simp [parseTaggedAtom, serializeAtom, hlt.symm,
        readIdentifierSymbols_encode start zero one hne i.val tail, i.isLt]

/-- Parse a tagged fragment up to its reserved end marker. The marker is only
recognized at token boundaries; literal payloads are consumed after the
literal tag, so they may themselves equal the marker. -/
def parseTaggedFragmentUntilFuel {b n : Nat}
    (literalTag referenceTag endTag start zero one : Fin b) :
    Nat → Word b → Option (Fragment b n × Word b)
  | 0, [] => none
  | 0, tag :: rest => if tag = endTag then some ([], rest) else none
  | _fuel + 1, [] => none
  | fuel + 1, tag :: rest =>
      if tag = endTag then some ([], rest) else
        match parseTaggedAtom literalTag referenceTag start zero one (tag :: rest) with
        | none => none
        | some (a, rest) =>
          match parseTaggedFragmentUntilFuel literalTag referenceTag endTag
              start zero one fuel rest with
          | none => none
          | some (fragment, tail) => some (a :: fragment, tail)

theorem parseTaggedFragmentUntilFuel_serialize {b n : Nat}
    (literalTag referenceTag endTag start zero one : Fin b)
    (hlr : literalTag ≠ referenceTag)
    (hle : literalTag ≠ endTag) (hre : referenceTag ≠ endTag)
    (hne : zero ≠ one) (fragment : Fragment b n) (tail : Word b)
    (fuel : Nat) (hfuel : fragment.length ≤ fuel) :
    parseTaggedFragmentUntilFuel literalTag referenceTag endTag start zero one
      fuel
      (serializeFragment literalTag referenceTag
        (fun i => binaryIdentifierCode start zero one i) fragment ++
        endTag :: tail) = some (fragment, tail) := by
  induction fragment generalizing fuel with
  | nil =>
      cases fuel <;> simp [serializeFragment, parseTaggedFragmentUntilFuel]
  | cons a rest ih =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          have hrest : rest.length ≤ fuel := by simp at hfuel; omega
          cases a with
          | char c =>
              let suffix := serializeFragment literalTag referenceTag
                (fun i => binaryIdentifierCode start zero one i) rest ++
                endTag :: tail
              have hAtom : parseTaggedAtom (n := n)
                  literalTag referenceTag start zero one
                  (literalTag :: c :: suffix) =
                    some ((.char c : Atom b n), suffix) := by
                simpa [serializeAtom] using
                  (parseTaggedAtom_serializeAtom literalTag referenceTag start zero one
                    hlr hne (.char c : Atom b n) suffix)
              have hTail : parseTaggedFragmentUntilFuel literalTag referenceTag endTag
                  start zero one fuel suffix = some (rest, tail) := by
                simpa [suffix] using ih fuel hrest
              simp only [serializeFragment, serializeAtom]
              change parseTaggedFragmentUntilFuel literalTag referenceTag endTag
                start zero one (fuel + 1) (literalTag :: c :: suffix) = _
              simp [parseTaggedFragmentUntilFuel, hle, hAtom, hTail]
          | use i =>
              let suffix := serializeFragment literalTag referenceTag
                (fun j => binaryIdentifierCode start zero one j) rest ++
                endTag :: tail
              have hAtom : parseTaggedAtom (n := n)
                  literalTag referenceTag start zero one
                  (referenceTag :: (binaryIdentifierCode start zero one i.val ++ suffix)) =
                    some ((.use i : Atom b n), suffix) := by
                simpa [serializeAtom] using
                  (parseTaggedAtom_serializeAtom literalTag referenceTag start zero one
                    hlr hne (.use i : Atom b n) suffix)
              have hTail : parseTaggedFragmentUntilFuel literalTag referenceTag endTag
                  start zero one fuel suffix = some (rest, tail) := by
                simpa [suffix] using ih fuel hrest
              simp only [serializeFragment, serializeAtom]
              simp only [List.cons_append, List.append_assoc]
              change parseTaggedFragmentUntilFuel literalTag referenceTag endTag
                start zero one (fuel + 1)
                (referenceTag :: (binaryIdentifierCode start zero one i.val ++ suffix)) = _
              simp [parseTaggedFragmentUntilFuel, hre, hAtom, hTail]

/-- Consume a fixed header only when it is an exact prefix. -/
def stripPrefix {b : Nat} : Word b → Word b → Option (Word b)
  | [], input => some input
  | _ :: _, [] => none
  | c :: pre, x :: input =>
      if c = x then stripPrefix pre input else none

theorem stripPrefix_append {b : Nat} (pre tail : Word b) :
    stripPrefix pre (pre ++ tail) = some tail := by
  induction pre with
  | nil => rfl
  | cons c pre ih => simp [stripPrefix, ih]

/-- Parse one `DEF id := fragment <end>` record. Its identifier must be the
next fresh index, and references in the body are decoded as backward indices. -/
def parseSerializedDefinition {b n : Nat}
    (literalTag referenceTag endTag start zero one : Fin b)
    (definitionHeader assignment : Word b) (index : Nat) (input : Word b) :
    Option (Fragment b n × Word b) := do
  let afterHeader ← stripPrefix definitionHeader input
  let (found, afterIdentifier) ← readIdentifierSymbols start zero one afterHeader
  if found != index then none else do
    let body ← stripPrefix assignment afterIdentifier
    parseTaggedFragmentUntilFuel literalTag referenceTag endTag start zero one
      body.length body

theorem parseSerializedDefinition_encode {b n : Nat}
    (literalTag referenceTag endTag start zero one : Fin b)
    (hlr : literalTag ≠ referenceTag)
    (hle : literalTag ≠ endTag) (hre : referenceTag ≠ endTag)
    (hne : zero ≠ one) (definitionHeader assignment : Word b)
    (index : Nat) (rhs : Fragment b n) (tail : Word b) :
    parseSerializedDefinition literalTag referenceTag endTag start zero one
      definitionHeader assignment index
      (serializeDefinition literalTag referenceTag
        (fun i => binaryIdentifierCode start zero one i)
        definitionHeader assignment endTag index rhs ++ tail) = some (rhs, tail) := by
  have hids : ∀ i, binaryIdentifierCode start zero one i ≠ [] := by
    intro i
    exact binaryIdentifierCode_nonempty start zero one i
  have hfragment := serializeFragment_length_ge literalTag referenceTag
    (fun i => binaryIdentifierCode start zero one i) hids rhs
  have hbody : rhs.length ≤
      (serializeFragment literalTag referenceTag
        (fun i => binaryIdentifierCode start zero one i) rhs ++ endTag :: tail).length := by
    simp only [List.length_append, List.length_cons]
    omega
  have hparsed := parseTaggedFragmentUntilFuel_serialize
    literalTag referenceTag endTag start zero one hlr hle hre hne rhs tail
    _ hbody
  have hparsed' : parseTaggedFragmentUntilFuel literalTag referenceTag endTag
      start zero one
      (List.length (serializeFragment literalTag referenceTag
        (fun i => binaryIdentifierCode start zero one i) rhs) +
        (List.length tail + 1))
      (serializeFragment literalTag referenceTag
        (fun i => binaryIdentifierCode start zero one i) rhs ++ endTag :: tail) =
        some (rhs, tail) := by
    simpa only [List.length_append, List.length_cons] using hparsed
  simp [parseSerializedDefinition, serializeDefinition, stripPrefix_append,
    readIdentifierSymbols_encode start zero one hne index,
    hparsed', List.append_assoc]

/-- Parse exactly the first `count` definition records. Definition `k` must
carry identifier `k`, and its body can refer only to the `k` earlier entries. -/
def parseSerializedGrammar {b : Nat}
    (literalTag referenceTag endTag start zero one : Fin b)
    (definitionHeader assignment : Word b) :
    (count : Nat) → Word b → Option (Grammar b count × Word b)
  | 0, input => some ⟨.nil, input⟩
  | count + 1, input => do
      let ⟨prior, afterPrior⟩ ← parseSerializedGrammar literalTag referenceTag
        endTag start zero one definitionHeader assignment count input
      let (rhs, tail) ← parseSerializedDefinition (n := count)
        literalTag referenceTag endTag start zero one definitionHeader assignment
        count afterPrior
      pure ⟨.snoc prior rhs, tail⟩

theorem parseSerializedGrammar_encode {b n : Nat}
    (literalTag referenceTag endTag start zero one : Fin b)
    (hlr : literalTag ≠ referenceTag)
    (hle : literalTag ≠ endTag) (hre : referenceTag ≠ endTag)
    (hne : zero ≠ one) (definitionHeader assignment : Word b)
    (g : Grammar b n) (tail : Word b) :
    parseSerializedGrammar literalTag referenceTag endTag start zero one
      definitionHeader assignment n
      (serializeGrammar literalTag referenceTag
        (fun i => binaryIdentifierCode start zero one i)
        definitionHeader assignment endTag n g ++ tail) = some ⟨g, tail⟩ := by
  induction g generalizing tail with
  | nil => simp [parseSerializedGrammar, serializeGrammar]
  | @snoc n g rhs ih =>
      simp only [serializeGrammar, List.append_assoc, parseSerializedGrammar]
      rw [ih (serializeDefinition literalTag referenceTag
        (fun i => binaryIdentifierCode start zero one i)
        definitionHeader assignment endTag n rhs ++ tail)]
      simp [parseSerializedDefinition_encode literalTag referenceTag endTag start zero one
        hlr hle hre hne definitionHeader assignment n rhs tail]

/-- Decode a complete file in the grammar-plus-root model: the declared number
of definition records is followed by one tagged root fragment and the reserved
final marker, with no trailing data. This does not parse AX/MP/GEN records. -/
def parseSerializedProofFile {b : Nat} (count : Nat)
    (literalTag referenceTag endTag start zero one : Fin b)
    (definitionHeader assignment : Word b) (input : Word b) :
    Option (Grammar b count × Fragment b count) := do
  let ⟨g, body⟩ ← parseSerializedGrammar literalTag referenceTag endTag start zero one
    definitionHeader assignment count input
  let (root, tail) ← parseTaggedFragmentUntilFuel literalTag referenceTag endTag
    start zero one body.length body
  if tail = [] then pure ⟨g, root⟩ else none

theorem SerializedProofFile.parse_wire {b n : Nat}
    (file : SerializedProofFile b n) :
    parseSerializedProofFile n file.literalTag file.referenceTag file.definitionEndTag
      file.identifierStart file.identifierZero file.identifierOne
      file.definitionHeader file.assignment file.wire = some (file.grammar, file.root) := by
  have hsymbols : file.identifierZero ≠ file.identifierOne := by
    intro h
    have hc := congrArg file.alphabet h
    rw [file.zero_char, file.one_char] at hc
    exact (by decide : ('0' : Char) ≠ '1') hc
  have hgrammar := parseSerializedGrammar_encode file.literalTag file.referenceTag
    file.definitionEndTag file.identifierStart file.identifierZero file.identifierOne
    file.literal_ne_reference file.literal_ne_end file.reference_ne_end
    hsymbols
    file.definitionHeader file.assignment file.grammar
    (serializeFragment file.literalTag file.referenceTag
      (fun i => binaryIdentifierCode file.identifierStart file.identifierZero
        file.identifierOne i) file.root ++
      [file.definitionEndTag])
  have hids : ∀ i,
      binaryIdentifierCode file.identifierStart file.identifierZero
        file.identifierOne i ≠ [] := by
    intro i
    exact binaryIdentifierCode_nonempty file.identifierStart file.identifierZero
      file.identifierOne i
  have hrootLen := serializeFragment_length_ge file.literalTag file.referenceTag
    (fun i => binaryIdentifierCode file.identifierStart file.identifierZero
      file.identifierOne i) hids file.root
  have hroot := parseTaggedFragmentUntilFuel_serialize file.literalTag
    file.referenceTag file.definitionEndTag file.identifierStart file.identifierZero
    file.identifierOne file.literal_ne_reference file.literal_ne_end
    file.reference_ne_end hsymbols
    file.root []
    (serializeFragment file.literalTag file.referenceTag
      (fun i => binaryIdentifierCode file.identifierStart file.identifierZero
        file.identifierOne i) file.root ++
      [file.definitionEndTag]).length (by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega)
  simp only [List.length_append, List.length_cons, List.length_nil] at hroot
  unfold SerializedProofFile.wire
  unfold parseSerializedProofFile
  dsimp only [SerializedProofFile.identifiers]
  simp only [List.append_assoc]
  rw [hgrammar]
  simp [hroot]

#print axioms readIdentifierSymbols_encode
#print axioms parseTaggedAtom_serializeAtom
#print axioms parseTaggedFragmentUntilFuel_serialize
#print axioms parseSerializedDefinition_encode
#print axioms parseSerializedGrammar_encode
#print axioms SerializedProofFile.parse_wire

end MAISO11.ChosenSystem

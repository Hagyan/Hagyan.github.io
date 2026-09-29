import GrammarLengthBound
import QuotationWire

set_option autoImplicit false
set_option warningAsError true

namespace MAISO11.ChosenSystem

open MAISO11.Quotation

/-- Encode a natural-number identifier in the concrete self-delimiting code
used by `QuotationWire.identifier`, but over the finite character alphabet
used by a serialized proof file. -/
def binaryIdentifierCode {b : Nat} (start zero one : Fin b) (i : Nat) : Word b :=
  [start] ++ List.replicate (bits (i + 1)).length one ++ [zero] ++
    ((bits (i + 1)).reverse.map (fun bit => if bit then one else zero))

theorem binaryIdentifierCode_toChars {b : Nat} (alphabet : Fin b → Char)
    (start zero one : Fin b) (hstart : alphabet start = 'u')
    (hzero : alphabet zero = '0') (hone : alphabet one = '1') (i : Nat) :
    (binaryIdentifierCode start zero one i).map alphabet = identifier i := by
  simp [binaryIdentifierCode, identifier, bitChar, hstart, hzero, hone,
    List.map_map]

theorem binaryIdentifierCode_nonempty {b : Nat} (start zero one : Fin b)
    (i : Nat) : binaryIdentifierCode start zero one i ≠ [] := by
  simp [binaryIdentifierCode]

theorem binaryIdentifierCode_injective {b : Nat} (alphabet : Fin b → Char)
    (start zero one : Fin b) (hstart : alphabet start = 'u')
    (hzero : alphabet zero = '0') (hone : alphabet one = '1')
    {i j : Nat} (h : binaryIdentifierCode start zero one i =
      binaryIdentifierCode start zero one j) : i = j := by
  have hc := congrArg (List.map alphabet) h
  rw [binaryIdentifierCode_toChars alphabet start zero one hstart hzero hone i,
    binaryIdentifierCode_toChars alphabet start zero one hstart hzero hone j] at hc
  exact identifier_injective hc

theorem binaryIdentifierCode_readIdentifier {b : Nat}
    (alphabet : Fin b → Char) (start zero one : Fin b)
    (hstart : alphabet start = 'u') (hzero : alphabet zero = '0')
    (hone : alphabet one = '1') (i : Nat) (tail : List Char) :
    MAISO11.Quotation.readIdentifier
      ((binaryIdentifierCode start zero one i).map alphabet ++ tail) =
      some (i, tail) := by
  rw [binaryIdentifierCode_toChars alphabet start zero one hstart hzero hone]
  exact MAISO11.Quotation.readIdentifier_encode i tail

theorem binaryIdentifierCode_length {b : Nat} (alphabet : Fin b → Char)
    (start zero one : Fin b) (hstart : alphabet start = 'u')
    (hzero : alphabet zero = '0') (hone : alphabet one = '1') (i : Nat) :
    (binaryIdentifierCode start zero one i).length =
      2 * (bits (i + 1)).length + 2 := by
  calc
    (binaryIdentifierCode start zero one i).length =
        ((binaryIdentifierCode start zero one i).map alphabet).length := by simp
    _ = (identifier i).length := by
      rw [binaryIdentifierCode_toChars alphabet start zero one hstart hzero hone]
    _ = 2 * (bits (i + 1)).length + 2 := identifier_length i

/--
If a file's definitions form an acyclic string grammar of mass at most `m`,
and the unexpanded proof-record stream has at most `m` atoms, then expanding
that stream has at most `2^(2*m)` characters. The two hypotheses are the
serializer-accounting obligations: definition bodies and definition headers
must fit in the written budget, as must the root stream.
-/
theorem expandedRoot_length_le_two_pow_two_mul
    {b n : Nat} (g : Grammar b n) (root : Fragment b n) (m : Nat)
    (hmass : g.mass ≤ m) (hroot : root.length ≤ m) :
    (expandFragment g.words root).length ≤ 2^(2*m) := by
  have hwords : ∀ i, (g.words i).length ≤ 2^g.mass := by
    intro i
    exact Nat.le_of_lt (g.words_length_lt_pow_mass i)
  have hfragment := expandFragment_length_le g.words (2^g.mass)
    Nat.one_le_two_pow hwords root
  have hmassPow : 2^g.mass ≤ 2^m :=
    Nat.pow_le_pow_right (by decide) hmass
  have hmPow : m ≤ 2^m :=
    Nat.le_of_lt (Nat.lt_two_pow_self (n := m))
  calc
    (expandFragment g.words root).length ≤ root.length * 2^g.mass := hfragment
    _ ≤ m * 2^g.mass := Nat.mul_le_mul_right _ hroot
    _ ≤ m * 2^m := Nat.mul_le_mul_left _ hmassPow
    _ ≤ 2^m * 2^m := Nat.mul_le_mul_right _ hmPow
    _ = 2^(m + m) := by rw [← Nat.pow_add]
    _ = 2^(2*m) := by congr 1; omega

/-- Fragment tokens carry an explicit kind tag. This prevents a literal string
from being mistaken for a reference merely because it spells an identifier. -/
def serializeAtom {b n : Nat} (literalTag referenceTag : Fin b)
    (identifiers : Nat → Word b) : Atom b n → Word b
  | .char c => [literalTag, c]
  | .use i => referenceTag :: identifiers i.val

/-- Serialize a fragment using tagged literal and reference tokens. -/
def serializeFragment {b n : Nat} (literalTag referenceTag : Fin b)
    (identifiers : Nat → Word b) : Fragment b n → Word b
  | [] => []
  | a :: rest => serializeAtom literalTag referenceTag identifiers a ++
      serializeFragment literalTag referenceTag identifiers rest

theorem serializeAtom_length_ge_two {b n : Nat}
    (literalTag referenceTag : Fin b) (identifiers : Nat → Word b)
    (hnonempty : ∀ i, identifiers i ≠ []) (a : Atom b n) :
    2 ≤ (serializeAtom literalTag referenceTag identifiers a).length := by
  cases a with
  | char c => simp [serializeAtom]
  | use i =>
    simp only [serializeAtom, List.length_cons]
    cases h : identifiers i.val with
    | nil => exact False.elim (hnonempty i.val h)
    | cons c cs => simp [h]

theorem serializeFragment_length_ge {b n : Nat}
    (literalTag referenceTag : Fin b) (identifiers : Nat → Word b)
    (hnonempty : ∀ i, identifiers i ≠ []) (f : Fragment b n) :
    f.length ≤ (serializeFragment literalTag referenceTag identifiers f).length := by
  induction f with
  | nil => simp [serializeFragment]
  | cons a rest ih =>
    have ha := serializeAtom_length_ge_two literalTag referenceTag identifiers
      hnonempty a
    simp only [serializeFragment, List.length_cons, List.length_append]
    omega

/-- The serializer for one `DEF id := fragment;` record. `definitionHeader`
contains the fixed nonempty `DEF ` prefix. The definition terminator is a
reserved one-symbol tag, distinct from either fragment-token tag. -/
def serializeDefinition {b n : Nat} (literalTag referenceTag : Fin b)
    (identifiers : Nat → Word b) (definitionHeader : Word b)
    (assignment : Word b) (terminator : Fin b) (index : Nat)
    (rhs : Fragment b n) : Word b :=
  definitionHeader ++ identifiers index ++ assignment ++
    serializeFragment literalTag referenceTag identifiers rhs ++ [terminator]

/-- Serialize the grammar in declaration order. A `snoc` definition receives
the next natural identifier, so references in its body can name only earlier
definitions, as required by `Grammar`. -/
def serializeGrammar {b : Nat} (literalTag referenceTag : Fin b)
    (identifiers : Nat → Word b)
    (definitionHeader : Word b)
    (assignment : Word b) (terminator : Fin b) :
    (n : Nat) → Grammar b n → Word b
  | 0, .nil => []
  | n + 1, .snoc g rhs =>
      serializeGrammar literalTag referenceTag identifiers definitionHeader
        assignment terminator n g ++
      serializeDefinition literalTag referenceTag identifiers definitionHeader
        assignment terminator n rhs

theorem serializeDefinition_length_ge {b n : Nat}
    (literalTag referenceTag : Fin b) (identifiers : Nat → Word b)
    (hnonempty : ∀ i, identifiers i ≠ [])
    (definitionHeader assignment : Word b) (terminator : Fin b) (index : Nat)
    (rhs : Fragment b n) (hheader : 1 ≤ definitionHeader.length) :
    rhs.length + 1 ≤
      (serializeDefinition literalTag referenceTag identifiers definitionHeader
        assignment terminator index rhs).length := by
  have hbody := serializeFragment_length_ge literalTag referenceTag identifiers
    hnonempty rhs
  simp only [serializeDefinition, List.length_append]
  omega

theorem serializeGrammar_length_ge_mass {b n : Nat}
    (literalTag referenceTag : Fin b) (identifiers : Nat → Word b)
    (hnonempty : ∀ i, identifiers i ≠ [])
    (definitionHeader assignment : Word b) (terminator : Fin b)
    (hheader : 1 ≤ definitionHeader.length) (g : Grammar b n) :
    g.mass ≤ (serializeGrammar literalTag referenceTag identifiers definitionHeader
      assignment terminator n g).length := by
  induction g with
  | nil => simp [serializeGrammar, Grammar.mass]
  | @snoc n g rhs ih =>
    simp only [Grammar.mass, serializeGrammar, List.length_append]
    have hrecord := serializeDefinition_length_ge literalTag referenceTag
      identifiers hnonempty definitionHeader assignment terminator n rhs hheader
    omega

/-- A finite-alphabet grammar-plus-root wire model using the concrete binary
identifier code. The character map is injective and maps the code's three
distinguished symbols to the exact prefix and digit characters expected by
`QuotationWire`. It stores a declaration-ordered definition prelude and one
root fragment; parsing the AX/MP/GEN record syntax is outside this model. -/
structure SerializedProofFile (b n : Nat) where
  grammar : Grammar b n
  root : Fragment b n
  alphabet : Fin b → Char
  alphabet_injective : ∀ x y, alphabet x = alphabet y → x = y
  identifierStart : Fin b
  identifierZero : Fin b
  identifierOne : Fin b
  literalTag : Fin b
  referenceTag : Fin b
  definitionEndTag : Fin b
  literal_ne_reference : literalTag ≠ referenceTag
  literal_ne_end : literalTag ≠ definitionEndTag
  reference_ne_end : referenceTag ≠ definitionEndTag
  start_char : alphabet identifierStart = 'u'
  zero_char : alphabet identifierZero = '0'
  one_char : alphabet identifierOne = '1'
  definitionHeader : Word b
  header_nonempty : 1 ≤ definitionHeader.length
  assignment : Word b
  

def SerializedProofFile.identifiers {b n : Nat}
    (file : SerializedProofFile b n) : Nat → Word b :=
  fun i => binaryIdentifierCode file.identifierStart file.identifierZero
    file.identifierOne i

theorem SerializedProofFile.identifiers_nonempty {b n : Nat}
    (file : SerializedProofFile b n) : ∀ i, file.identifiers i ≠ [] := by
  intro i
  exact binaryIdentifierCode_nonempty file.identifierStart file.identifierZero
    file.identifierOne i

theorem SerializedProofFile.identifiers_injective {b n : Nat}
    (file : SerializedProofFile b n) :
    ∀ i j, file.identifiers i = file.identifiers j → i = j := by
  intro i j h
  exact binaryIdentifierCode_injective file.alphabet file.identifierStart
    file.identifierZero file.identifierOne file.start_char file.zero_char
    file.one_char h

def SerializedProofFile.wire {b n : Nat}
    (file : SerializedProofFile b n) : Word b :=
  serializeGrammar file.literalTag file.referenceTag
    (fun i => binaryIdentifierCode file.identifierStart file.identifierZero
      file.identifierOne i)
    file.definitionHeader file.assignment file.definitionEndTag n file.grammar ++
    serializeFragment file.literalTag file.referenceTag
      (fun i => binaryIdentifierCode file.identifierStart file.identifierZero
        file.identifierOne i) file.root ++
    [file.definitionEndTag]

def SerializedProofFile.charWire {b n : Nat}
    (file : SerializedProofFile b n) : List Char :=
  file.wire.map file.alphabet

def SerializedProofFile.writtenLength {b n : Nat}
    (file : SerializedProofFile b n) : Nat := file.charWire.length

theorem SerializedProofFile.writtenLength_eq_wireLength {b n : Nat}
    (file : SerializedProofFile b n) : file.writtenLength = file.wire.length := by
  simp [SerializedProofFile.writtenLength, SerializedProofFile.charWire]

theorem SerializedProofFile.readIdentifier {b n : Nat}
    (file : SerializedProofFile b n) (i : Nat) (tail : List Char) :
    MAISO11.Quotation.readIdentifier
      ((file.identifiers i).map file.alphabet ++ tail) =
      some (i, tail) := by
  change MAISO11.Quotation.readIdentifier
    ((binaryIdentifierCode file.identifierStart file.identifierZero
      file.identifierOne i).map file.alphabet ++ tail) = some (i, tail)
  exact binaryIdentifierCode_readIdentifier file.alphabet file.identifierStart
    file.identifierZero file.identifierOne file.start_char file.zero_char
    file.one_char i tail

theorem serializedFile_grammarMass_le_writtenLength {b n : Nat}
    (file : SerializedProofFile b n) :
    file.grammar.mass ≤ file.writtenLength := by
  unfold SerializedProofFile.writtenLength SerializedProofFile.charWire
    SerializedProofFile.wire
  simp only [List.length_map, List.length_append]
  have hids : ∀ i, binaryIdentifierCode file.identifierStart
      file.identifierZero file.identifierOne i ≠ [] := by
    intro i
    exact binaryIdentifierCode_nonempty file.identifierStart file.identifierZero
      file.identifierOne i
  have hm := serializeGrammar_length_ge_mass file.literalTag file.referenceTag
    (fun i => binaryIdentifierCode file.identifierStart file.identifierZero
      file.identifierOne i) hids file.definitionHeader file.assignment
    file.definitionEndTag file.header_nonempty file.grammar
  omega

theorem serializedFile_rootLength_le_writtenLength {b n : Nat}
    (file : SerializedProofFile b n) :
    file.root.length ≤ file.writtenLength := by
  unfold SerializedProofFile.writtenLength SerializedProofFile.charWire
    SerializedProofFile.wire
  simp only [List.length_map, List.length_append]
  have hids : ∀ i, binaryIdentifierCode file.identifierStart
      file.identifierZero file.identifierOne i ≠ [] := by
    intro i
    exact binaryIdentifierCode_nonempty file.identifierStart file.identifierZero
      file.identifierOne i
  have hr := serializeFragment_length_ge file.literalTag file.referenceTag
    (fun i => binaryIdentifierCode file.identifierStart file.identifierZero
      file.identifierOne i) hids file.root
  omega

/-- The expansion bound now follows from the actual character count of this
serialized grammar-plus-root representation. -/
theorem serializedFile_expandedRoot_length_le_two_pow_two_mul
    {b n : Nat} (file : SerializedProofFile b n) (m : Nat)
    (hwritten : file.writtenLength ≤ m) :
    (expandFragment file.grammar.words file.root).length ≤ 2^(2*m) := by
  apply expandedRoot_length_le_two_pow_two_mul file.grammar file.root m
  · exact Nat.le_trans (serializedFile_grammarMass_le_writtenLength file)
      hwritten
  · exact Nat.le_trans (serializedFile_rootLength_le_writtenLength file)
      hwritten

#print axioms expandedRoot_length_le_two_pow_two_mul
#print axioms binaryIdentifierCode_injective
#print axioms SerializedProofFile.readIdentifier
#print axioms serializedFile_expandedRoot_length_le_two_pow_two_mul

end MAISO11.ChosenSystem

import CompactChecker
set_option autoImplicit false
set_option warningAsError true
open MAISO11.Arithmetic MAISO11.Wire

-- Non-vacuous instantiation under a second quantifier.
def nestedBody : Formula 1 := .all (.eq (.var 1) (.var 0))
def witness : Term 0 := .add (.bit1 .zero) (.bit0 (.bit1 .zero))
def nestedInstance : Formula 0 := .imp (.all nestedBody) (nestedBody.instantiate witness)
-- A vacuous instance: the supplied term leaves no occurrence in the result.
def vacuousBody : Formula 1 := .all (.eq (.var 0) (.var 0))

example : axiomCheck nestedInstance = true := by decide
example : axiomCheck (.imp (.all vacuousBody) (vacuousBody.instantiate witness)) = true := by decide
example : axiomCheck (.imp (.all nestedBody) (.all (.eq (.zero) (.zero)))) = false := by decide
example : axiomCheck (.eq (.zero) (.zero)) = false := by decide
example : axiomCheck (.eq (.zero) (.bit1 .zero)) = false := by decide

-- A three-record derivation of reflexivity: universal reflexivity,
-- its instantiation, and modus ponens.
def compactRefl : CFormula 0 0 := .all (.eq (.var 0) (.var 0))
def compactZeroEq : CFormula 0 0 := .eq .zero .zero

def reflRecords : Records 0 3 :=
  ((Records.nil.snoc (.axiom compactRefl)).snoc
    (.axiom (.imp compactRefl compactZeroEq))).snoc
      (.mp ⟨0,by decide⟩ ⟨1,by decide⟩ compactZeroEq)

def badMPRecords : Records 0 3 :=
  ((Records.nil.snoc (.axiom compactRefl)).snoc
    (.axiom (.imp compactRefl compactZeroEq))).snoc
      (.mp ⟨0,by decide⟩ ⟨1,by decide⟩ (.eq .zero (.bit1 .zero)))

def unjustifiedRefl : Records 0 1 := Records.nil.snoc (.axiom compactZeroEq)

-- The executable tests below exercise the full parser, including its dependent
-- index casts. Failures raise an IO error instead of silently printing false.
def expect (name : String) (ok : Bool) : IO Unit :=
  if ok then IO.println ("PASS: " ++ name) else throw (IO.userError ("FAIL: " ++ name))

#eval expect "nested instantiation" (axiomCheck nestedInstance)
#eval expect "valid complete proof" (checkWhole 0 3 reflRecords.wire == some (.eq .zero .zero))
#eval expect "incorrect MP conclusion" (checkWhole 0 3 badMPRecords.wire == none)
#eval expect "unjustified reflexivity axiom" (checkWhole 0 1 unjustifiedRefl.wire == none)
#eval expect "wrong record count" (checkWhole 0 2 reflRecords.wire == none)
#eval expect "trailing garbage" (checkWhole 0 3 (reflRecords.wire ++ ['x']) == none)
#eval expect "empty proof" (checkWhole 0 0 [] == none)

def oneLetter : MAISO11.Quotation.Grammar 2 1 := .snoc .nil [.char ⟨0,by decide⟩]
def refRefl : CFormula 4 0 := .all (.eq (.var 0) (.var 0))
def refEq : CFormula 4 0 := .eq (.ref ⟨0,by decide⟩) (.ref ⟨0,by decide⟩)
def refRecords : Records 4 3 :=
  ((Records.nil.snoc (.axiom refRefl)).snoc
    (.axiom (.imp refRefl refEq))).snoc
      (.mp ⟨0,by decide⟩ ⟨1,by decide⟩ refEq)
#eval expect "compiled dictionary and referenced terms"
  (checkWhole 4 3 (definitionPrelude (MAISO11.Quotation.compile oneLetter) ++ refRecords.wire) ==
    some (refEq.expand (dictionary (MAISO11.Quotation.compile oneLetter))))

#print axioms MAISO11.Wire.instance_candidate
#print axioms MAISO11.Wire.axiomCheck_iff
#print axioms MAISO11.Wire.checkWhole_sound
#print axioms MAISO11.Wire.compiled_trace_checked

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


def main : IO Unit := do
  IO.FS.createDirAll "examples"
  IO.FS.writeFile "examples/reflexivity.pabin" (String.mk reflRecords.wire)
  IO.FS.writeFile "examples/invalid-mp.pabin" (String.mk badMPRecords.wire)

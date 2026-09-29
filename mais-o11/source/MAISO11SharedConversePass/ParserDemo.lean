import CompactParser

open MAISO11.Quotation MAISO11.Wire

def oneLetter : Grammar 2 1 := .snoc .nil [.char ⟨0,by decide⟩]

#eval readDefinitionPrelude 0 (definitionPrelude (compile (Grammar.nil : Grammar 2 0)))
#eval (readDefinitionPrelude 4 (definitionPrelude (compile oneLetter))).map
  (fun env => env == List.ofFn (dictionary (compile oneLetter)))
#eval (parseFile 4 1
  ((Records.nil.snoc (.axiom (CFormula.eq CTerm.zero CTerm.zero) : Record 4 0)).wire)).isSome
#eval (parseFile 4 1 "M[u101,u101] (=00)\n".toList).isSome
#eval (parseTerm 0 0 "(D0)junk".toList).isSome
#eval (parseTerm 0 0 "D0junk".toList).isSome

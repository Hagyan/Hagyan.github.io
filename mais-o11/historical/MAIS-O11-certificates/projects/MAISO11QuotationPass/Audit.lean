import Examples
import TracePacking

open MAISO11.Quotation

#print axioms compile_correct
#print axioms compile_markedCode
#print axioms rawCode_lt_scale
#print axioms quoteFragment_weight
#print axioms compile_weight
#print axioms compile_characters
#print axioms readIdentifier_encode
#print axioms identifier_injective
#print axioms fresh_register
#print axioms compiled_expansion_value
#print axioms localFormulas_derivable
#print axioms compiled_localCertificate_checked
#print axioms compile_certificate_characters
#print axioms compile_certificate_with_budget
#print axioms boundaryExample_expansion
#print axioms doubling_length
#print axioms doubling_quoted_length
#print axioms arithPair_injective
#print axioms arithUnpair_pair
#print axioms readValue_encode
#print axioms checkTrace_sound
#print axioms checkTrace_complete
#print axioms checkTrace_rejects_missing
#print axioms compiled_trace_sound
#print axioms packRefs_correct
#print axioms packedWitness_checked
#print axioms packedWitness_lookup
#print axioms PackingProgram.expansion_eval
#print axioms tracePacking_characters
#print axioms compiled_bundle_characters

-- These print the full statements so the scope can be inspected directly.
#check compile_correct
#check compile_certificate_characters
#check compiled_localCertificate_checked
#check compiled_trace_sound
#check packedWitness_lookup
#check compiled_bundle_characters

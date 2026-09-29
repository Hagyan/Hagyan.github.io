# MAIS-O11: raw-string quotation milestone

Lean **4.19.0**, `Std` only. No Mathlib or external Lean packages.

**Scope:** concrete compilers from raw string abbreviations to compact arithmetic
terms and a single coded witness trace, a checked arithmetic-trace verifier,
polynomial character bounds, and local equality certificates. The project
does not prove polynomial internalization for the complete PA-bin checker or
resolve either part of MAIS-O11.

## Verify

In this directory:

```bash
lake build
lake env lean Audit.lean
lake exe quotationdemo
```

The demo generates `boundary-quotation.pabin` and its trace-definition extension.
Optionally check the serialized examples with the independent diagnostics:

```bash
python3 check_local_file.py boundary-quotation.pabin --self-test
python3 check_local_file.py boundary-quotation-with-trace.pabin --self-test
python3 verify_boundary.py
```

The Lean acceptance theorem is universal over the structured grammar. The
Python check is a test of the printed example, and recognizes only the local
equality/instantiation fragment. Neither is a complete PA-bin proof-file checker.

## Files

| File | Content |
|---|---|
| `StringQuotation.lean` | Arbitrary raw fragments; fresh sequential definitions; length, scale, and code compiler; correctness and weight bounds |
| `QuotationWire.lean` | Binary identifiers, identifier decoder and framing theorem, binary numerals, explicit serialization, character bounds |
| `LocalCertificates.lean` | Ordinary closed PA terms; a restricted Enderton proof checker; local proof certificates; complete serialized certificate bound |
| `ArithmeticTrace.lean` | Injective arithmetic pairing, decoder, encoded-vector access, and a sound and complete arithmetic-trace checker |
| `TracePacking.lean` | Compact arithmetic terms for the entire encoded trace, witness acceptance, and a quadratic extra-character bound |
| `Examples.lean` | A fragment crossing formula boundaries and a universally proved exponential-expansion family |
| `Audit.lean` | Axiom reports and exact principal theorem statements |
| `Demo.lean` | Measured outputs, without evaluating enormous expanded codes |
| `check_local_file.py` | Independent, unverified diagnostic for the printed local certificates |
| `verify_boundary.py` | Independent numeric round trip for the printed small example and its coded trace |
| `RESEARCH-NOTE.md` | Mathematical construction, scope, and remaining PA-bin obligations |
| `checked-output.txt` | Clean build and verification transcript |
| `SHA256SUMS` | Hashes for the delivered files |

## Main bound

For alphabet base `b`, a grammar of `n` definitions has mass `M` equal to `n`
plus the number of atoms in all right-hand sides. The full local certificate has
at most

```text
20 + (40*M + 100) * (4*(b + 4)*M^2 + 3*M)
```

characters. This is a checked bound on written syntax, not on a fully expanded
word or canonical numeral. `compile_certificate_with_budget` substitutes a
budget `k` when supplied with a proof that `M <= k`.

For `n` source definitions, packing all the summaries into a single integer adds
at most `(8*n + 20)*(112*n)` characters. The full bound remains cubic in `M`.
`packedWitness_checked` proves that this compactly represented integer passes
the typed arithmetic-trace checker, and `packedWitness_lookup` identifies every
entry with its source fragment's correct summary.

For each expanded fragment `w`, the generated terms denote
`length(w)`, `b^length(w)`, and its raw base-`b` value. Adding the last two yields
the code with a leading marker digit 1.

## What remains

The current Lean theorem starts with a parsed grammar. Connecting the original
file bytes and code to that grammar, arithmetizing the expansion relation inside
PA, and proving the required instances of the fixed `Bew` predicate are still
needed. Full Enderton axiom recognition, compressed substitution, the internal
Löb instance, and proof assembly are also outside this certificate.

The arithmetic trace code and decoder are concrete, but `checkTrace` is still a
Lean program over typed syntax, not a literal PA formula with a generated PA
proof of acceptance. Its bounded-search decoder is not claimed to be fast.
The large examples generate syntax only; do not evaluate their enormous codes
or run that decoder on them.

The local equality proofs assert that the generated abbreviations satisfy their
definitions. They do not assert `Bew` of the original file.

## Reading the example syntax

`D` and `E` are the numeral constructors `2*x` and `2*x+1`. Arithmetic uses
fully parenthesized prefix `(+xy)` and `(*xy)`. The local formula syntax uses
`(=xy)`, `(>AB)`, and `(Av0A)`. `A` tags an axiom record;
`M[antecedent,implication]` tags a modus ponens record. Line references count
only axiom/MP records, beginning at zero. Each reference uses the same
self-delimiting binary integer notation as the abbreviation names.

The identifier `u101` denotes index 0: `1` is the bit-length header, `0` its
separator, and `1` the body encoding `index+1`. All printed characters count.

Audited dependencies are among `propext`, `Quot.sound`, and `Classical.choice`;
the audit lists them per theorem. There are no admitted proofs, custom axioms,
`native_decide` proofs, or unsafe declarations.

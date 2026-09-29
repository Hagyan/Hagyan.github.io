# MAIS-O11: shared parsing of the PA-bin definition prelude

## Result

`SharedPrelude.lean` adds an executable parser for closed arithmetic
abbreviation definitions in the same written `def u_i := term` grammar as the
previous checker. Its output is a typed chain `CDefs r` of compact syntax
trees. Each reference has type `Fin r` at the point where it is introduced,
so it can name only an earlier definition. The parser does not compute the
expanded meaning of an abbreviation.

The strongest new theorem is `parseSharedPrelude_refines_old`: whenever the
new parser accepts an arbitrary input string and returns `p`, the old
expansion-based `readDefinitionPrelude` accepts that **same string** and
returns exactly `p.terms`, its mathematical expansion. The proof passes
through a syntax-soundness theorem for each parsed definition and a
fuel-induction proving that the old closed-term reader expands every
canonically written compact term correctly. This is a one-way refinement:
we have not yet proved that every input accepted by the old reader is
accepted by the new one.

`parseSharedPrelude_sound_wire` proves that any accepted string is precisely
the serialization of its returned compact chain. `CDefs.mass_le_wire` and
`parseSharedPrelude_mass_le_input` prove that the number of retained syntax
nodes, counting definitions, does not exceed the written input length.
These are representation-size bounds, not a measured running-time bound.

## Connection to the actual serialized grammar

`SharedPreludeDemo.lean` defines a compact chain for the existing
`doublingProgram`. Lean proves its bytes equal the program's actual serialized
definitions, its semantic root equals the old expanded `doubledTree`, and
its written size is at most `(2*n+22)*(4*n+2)`. The actual 61-definition
prelude (`n=60`) parses successfully without constructing its expanded
root, which would have `2^61-1` syntax nodes. The `#eval` checks only the
parser's `Option.isSome`; the expansion appears in theorem statements and
proofs, not in that computation.

This generalizes the previous graph example in an important direction:
the earlier project proved efficient equality of an already-built graph,
while the new project can read arbitrary canonical closed-term definition
lines into a shared representation without expanding them.

## Remaining checker boundary

The new parser does not yet feed the full `checkWhole` function. That function
still calls the old `readDefinitionPrelude`, materializes expanded terms,
and runs expanded-formula `axiomCheck`. The previous
`CompactEquality.lean` provides a sound interface from shared term equality
to formula equality and MP checking, but its concrete graph comparator
uses expansion as a fallback for general terms. A complete compressed
checker needs:

1. A general compiler from the parsed `CDefs` and each compact formula term
   into shared graph nodes, with a full equality oracle and a size bound.
2. Compact axiom recognition, including substitution under quantifiers.
3. Integration into the whole-file checker, with equivalence to the fixed
   PA-bin predicate on all accepted files, in both directions.
4. PA proofs certifying checker acceptance and the uniform formalized Löb
   instances with a polynomial bound on written proof characters.

The fourth requirement is separate from an efficient external parser. This
project proves no polynomial bound on `F_PA_bin(k,n)` and no PA-bin Part 1
witness. It does isolate the expansion in definition parsing and remove it
in a new, formally sound executable path.

## Verification

Lean 4.19.0 with Std. From the extracted project directory:

```bash
lake build
lake env lean SharedPreludeDemo.lean
```

The build and 61-definition test passed. The new audited theorems depend
only on Lean's standard `propext` and `Quot.sound`; there is no `sorry`,
custom object-language axiom, or `native_decide` in the new modules.

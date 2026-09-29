# MAIS-O11 Part 1: robust size ledger for the chosen-system branch

**28 September 2026.** This note repairs one fragile point in the earlier
slow-verifier draft. It replaces the unproved *linear* translation bound by a
coarse bound that allows arbitrary nested string-fragment abbreviations of the
kind described in MAIS-A1. This is still a mathematical proof draft, not a
Lean certificate and not a result for fixed `PA_bin` or MAIS-O11(2).

## The change

Fix one explicit Hilbert presentation `B` of PA with binary numerals and the
specified nested, charged string-fragment abbreviations. For a literal
instantiation, freeze `B` to the proof syntax and rules fixed in MAIS-A1 §2.
Keep the encodings distinct: `B` uses its fixed formula numbering for its
proof search, `S` uses the odd/even formula numbering specified below, and
written proof files use their finite-alphabet string codes. Each is
primitive-recursively related to its own syntax. Let `D(x)` be a parameterized diagonal
sentence and define

\[
 H(n)\;:\Longleftrightarrow\;
   \text{there is no B-proof of }D(\bar n)\text{ of written length at most }2^n.
\]

The parameterized diagonal lemma gives one fixed formula `D(x)` and a fixed
`B`-proof of `forall x, D(x) <-> H(x)`. In particular, the expanded formula
length of `D(\bar n)` is `O(log(n+2))`. The larger cutoff is deliberate: it
absorbs the expansion cost of arbitrary abbreviation fragments in the
chosen system's proof files.

If `B` is consistent, then, for every standard `n`,

\[
 B\vdash D(\bar n),\qquad \ell_B(D(\bar n))>2^n.
\]

Indeed, a `B`-proof of length at most `2^n` would, by numeralwise checking,
make `B` prove `not H(n)`, while `D(n)` and the diagonal equivalence make it
prove `H(n)`. Conversely, the true finite search establishing `H(n)` is a
terminating primitive-recursive computation, so PA proves that particular
instance, however large its proof is.

There cannot be one B-proof of `forall n, H(n)`: together with the fixed
diagonal equivalence it would give a fixed proof of `forall n, D(n)`, whose
binary-numeral instances have `O(log n)`-length proofs, contradicting the
`2^n` lower bound for sufficiently large `n`. Thus the verifier's guard is
true instance by instance but not uniformly provable in B.

## The chosen proof system

Expand PA's finite alphabet by nullary sentence symbols `p_n`, with binary
indices and an effective formula coding satisfying `#p_n = 2n+1`. Preserve
the PA proof syntax and allow its full nested string-fragment abbreviation
rule. Add the axiom family

\[
 R_n := (\exists u\,\mathrm{Bew}_S(u,\overline{2n+1}))\to p_n.
\]

The proof checker expands a file, checks the ordinary Hilbert derivation,
then scans the expanded derivation and runs the finite test `H(j)` for every
occurrence of every token `p_j`. This is a primitive-recursive checker: the
tests are finite bounded searches, and MAIS-A1 places no polynomial-time
bound on checking. A syntactic fixed point makes `Bew_S` exactly the
arithmetization of this checker; the axiom displayed above is therefore
literally `Box_S p_n -> p_n`.

Freeze the numeral spelling in `B` as follows. Let `dbl(t)` abbreviate the
fully parenthesized prefix PA term `×(S(S(0)),t)`, and `odd(t)` the term
`+(×(S(S(0)),t),S(0))`. Set
`nu(0)=0`, `nu(2k)=dbl(nu(k))` for `k>0`, and
`nu(2k+1)=odd(nu(k))` for `k>=0`; write `bar n` for `nu(n)`. These are the
binary numeral constructors specified in MAIS-A1, with every abbreviation
expanded by the same fixed term spelling. In particular,
`bar(2n+1)` is syntactically `odd(bar n)`, and each numeral has length
`O(log(n+2))`.

PA proves the uniform guard implication

\[
 \forall n\bigl(\Box_S p_n\to H(n)\bigr),
\]

because any accepted file ending in `p_n` has that occurrence in its expanded
derivation, and the checker explicitly tested `H(n)`. Combining it with the
uniform diagonal equivalence gives a *single fixed B-proof* of
`forall n, (Box_S p_n -> D(n))`.

Every standard guard succeeds by the finite diagonal argument. Thus every
ordinary PA proof remains an S-proof and each `R_n` is accepted as a one-line
S-proof. Interpret every `p_j` by `0=0`: each `R_j` then becomes an implication
with a true consequent, while PA axioms and inference rules remain valid.
This proves consistency relative to `Con(B)`. The three Hilbert--Bernays--Löb
conditions follow for this actual checker: concrete accepted proofs have PA
verification traces; proof concatenation preserves the union of already
checked predicate occurrences; and formalized `Sigma_1` completeness applies
to the arithmetic `Box_S` formula, with arithmetic PA proofs embedding into
S. Löb's theorem therefore gives `S |- p_n` for every standard `n`.

## The fragment-expansion bound

Let `m` be the written length of an S-proof file. There are at most `m`
abbreviation definitions, each with right-hand side length at most `m`, and
each can refer only to earlier definitions. If `E_i` is the greatest fully
expanded length after the first `i` definitions, then

\[
 E_0\le 1,\qquad E_{i+1}\le m+mE_i.
\]

The often-quoted `E_i <= (m+1)^i` is false already at `i=1` when `m>1`.
Set `F_i=E_i+1`. Then `F_{i+1}<=mF_i+1<=(m+1)F_i` and `F_0<=2`, so
`E_i<=2(m+1)^i<=(m+1)^(i+1)` for `m>=1`. Every reference expands to a
fragment of length at most `E_m`, while every literal character contributes
one. Hence expanding any written fragment of length at most `m`, including
the entire proof stream, yields length at most `m E_m <=
2m(m+1)^m <= (m+1)^(m+2)`. We retain the looser whole-proof bound
`(m+1)^(m+3)` to absorb fixed record-parser conventions. Thus its length is
`2^(O(m log(m+2)))`, and in particular at most `2^(c(m+1)^2)` for a fixed
constant `c`. This estimate permits abbreviations to cut across token
boundaries and formula-subtree boundaries; no token-origin claim is used.

### Existing Lean expansion bound and the serializer bridge

The project already has a generic Lean theorem in `GrammarLengthBound.lean`:
for an acyclic string grammar, every expanded definition has length below
`2^mass`, where `mass` charges each right-hand-side atom and each definition.
On 28 September 2026, the user ran `lake build ChosenSystemExpansion` with
Lean 4.19.0 on macOS; Lake reported `Build completed successfully`. The
`expandedRoot_length_le_two_pow_two_mul` and
`serializedFile_expandedRoot_length_le_two_pow_two_mul` reports each listed
only `propext` and `Quot.sound`, with no `sorryAx`. That build kernel-checked
the serializer accounting then in the file. A later local build of the current
concrete-identifier version is recorded below.

The serializer model now maps its finite alphabet to characters and derives
identifiers from the project's `QuotationWire.identifier` encoding. Lean
source lemmas state the exact character mapping, identifier length,
injectivity, and the `readIdentifier` round trip that leaves the following
tail unchanged. References are emitted as these self-delimiting identifiers;
the character-level file count is related to the finite-alphabet wire length,
and grammar-mass/root-length accounting feeds the `2^(2*m)` expansion
theorem. A new serializer module now proves parser/serializer round trips for
the tagged grammar-plus-root model. The actual proof-file protocol and
accepted-file size hypotheses remain open.

The current source fully qualifies the decoder as
`MAISO11.Quotation.readIdentifier` in both the theorem statement and proof.
On 28 September 2026, both `ChosenSystemExpansion` and
`ChosenSystemSerialization` built in this workspace with Lean 4.19.0. The six
round-trip theorems in the new module list only `propext` and `Quot.sound`;
the expansion declarations do too, with no `sorryAx`. The added
`ChosenSystemInterleaving` target also builds: it proves that definitions may
occur between output fragments, that compiling them to a final grammar and
concatenated root preserves the expanded text, and that expansion is at most
`2^(2*m)` from the serialized directive length. Its four checked declarations
list only `propext` and `Quot.sound`. The bundled Linux toolchain needed a
local rebuild of its corrupted `Init.Data.List.MinMax.olean` from matching
Lean source before Lake could run. The user's earlier error log showing
`sorryAx` came from a different or earlier source copy.

The parser module handles tagged fragments, a definition prelude in
declaration order, and one root stream. The interleaving module proves the
same expansion result for abstract definition/output directives in sequence.
Neither parses the actual `AX`/`MP`/`GEN` record syntax or proves that every
accepted S-proof yields the abstract stream with mass and root length bounded
by concrete file length. Those obligations remain open, so the active ledger
retains the independently derived, weaker `(m+1)^(m+3)` expansion estimate.
If the final map is proved, then `E <= m*2^m <= 2^(2*m)`; the `O(E^3)`
translation gives a B-proof bound `2^(O(m))` and a linear-in-`n` direct-proof
lower bound.

Translate an arbitrary accepted S-proof of `p_n` as follows:

1. Expand its abbreviations completely.
2. Replace each actual predicate token `p_j` by the closed arithmetic formula
   `D(\bar j)`, leaving arithmetic numerals and quoted Gödel codes unchanged.
3. Keep translated PA axioms and inference steps. Replace each `R_j` axiom
   line by an instance of the fixed B-theorem
   `forall j, (Box_S p_j -> D(j))`.

The interpretation is closed under substitution and preserves generalization.
In particular, an induction instance containing `p_j` becomes an ordinary PA
induction instance because every `D(\bar j)` is closed. The quotation inside
`Box_S p_j` remains the old code `2j+1`; it is not recursively re-quoted.

If the expanded source has `E` characters, every index `j` occurring in it
has at most `E` binary digits, there are at most `E` source records, and each
translated formula has length `O(E^2)`. Replacing an `R_j` line uses the
fixed uniform theorem plus a numeral-specialization proof for the exact code
`2j+1`. The frozen binary numeral grammar below makes this specialization
syntactically exact. Universal instantiation and modus ponens cost
`O(log(j+2))`; with at most `E` records and `O(E^2)` characters per translated
formula or record, the full uncompressed translation has length `O(E^3)`.
Enlarging a fixed constant if necessary, this yields

\[
 \text{every S-proof of }p_n\text{ of length }m
 \quad\Longrightarrow\quad
 \ell_B(D(\bar n))\le 2^{C(m+1)^2}.
\]

Combining with `ell_B(D(\bar n)) > 2^n` gives

\[
 \ell_S(p_n)>\sqrt{n/C}-1.
\]

This is the key repair: the proof no longer needs the earlier linear compiler
claim or a restriction to whole-expression macros.

## The MAIS-O11(1) inequality

The one-line proof of `Box_S p_n -> p_n` has length at most `a(1+log(n+2))`:
the formula contains the fixed proof predicate, the code numeral `2n+1`, and
the binary name `p_n`. Also `|p_n|+1 <= b(1+log(n+2))`. The reflection lengths
tend to infinity because the `R_n` are pairwise distinct and only finitely
many finite proof files have any fixed length bound.

For the fixed cheap-reflection constant `C_1(S)`,

\[
 \sqrt{n/C}-1 \;>
 2a(1+\log(n+2))+C_1(S)b(1+\log(n+2))
\]

for every sufficiently large `n`. Thus a tail of `P_i := p_{n_i}`, for
example `n_i=2^{N+i}` with `N` chosen sufficiently large, satisfies MAIS-O11
Part 1 with `delta=1`.

## What this repairs, and what remains

This establishes a robust candidate proof of the **chosen-system branch** of
Part 1 under the literal MAIS-A1 efficiency definition, assuming consistency
of PA. Its important feature is the slow primitive-recursive checker; no
polynomial-time checking requirement appears in that definition. The earlier
linear translation estimate is unnecessary. A formal proof still needs one
fixed coding/checker implementation and the corresponding PA derivations of
the guard lemma, fixed point, derivability conditions, and translation bound.
No Lean certificate for those metatheoretic statements is present.

Nothing transfers to the agenda's fixed `PA_bin` checker: its proof predicate
and abbreviation grammar are fixed, and the guard was built into a different
system. Part 1's fixed-`PA_bin` branch and Part 2 remain open. The compiler
obstacle recorded in `PA-BIN-THIRD-AUDIT.md` is still the relevant next target
for those questions.

## Formalization closure check

The odd/even formula-code requirement has a direct primitive-recursive
implementation. Start from an injective prefix code `c_0` for formulas in the
expanded language, including the binary-indexed `p_n` tokens. Set

    #p_n := 2*n+1
    #φ   := 2*c_0(φ)+2       when φ is not exactly one atom p_n.

Decode odd inputs as `p_((k-1)/2)` and even inputs by decoding `c_0(k/2-1)`;
reject the unused even codes whose `c_0` formula is itself a lone `p_n`.
This is primitive recursive, injective, and keeps binary code length
`O(|φ|+1)`. Thus the required code assignment can be explicit without
enumerating formulas by length.

The guard implication has a direct PA proof once the checker is defined with the
guard as an explicit conjunct. Let `RawDerives_e(u,y)` say that `u` parses,
expands, and checks as a Hilbert derivation with conclusion code `y`. Let
`Occur(u,j)` say that `p_j` occurs in at least one fully expanded derivation
formula, including the root formula. Let `M(u)` be the maximum index of such
an atom, with zero as the default, and define

    Guard(u) := forall j <= M(u), Occur(u,j) -> H(j)
    Bew_S(u,y) := RawDerives_e(u,y) AND Guard(u).

These are primitive-recursive relations: the expansion is a finite acyclic
macro expansion, the index scan is over a finite string, and each `H(j)` is
a finite bounded proof search. Because `#p_n = 2n+1` and `RawDerives` checks
the decoded root, PA proves the fixed syntax lemma

    RawDerives_e(u, 2*n+1) -> Occur(u,n).

Combining that lemma with the `Guard` conjunct and existential elimination
gives a fixed PA derivation of

\[
\forall n\bigl(\Box_S p_n\to H(n)\bigr).
\]

The size of this derivation does not depend on the runtime of the finite
search in `H(n)`: the search remains represented by its fixed graph formula.
This closes the *mathematical shape* of the uniform guard lemma. The exact
parser, occurrence predicate, self-reference index, and resulting PA proof
object have not yet been fixed or emitted, so it is not a machine-checked
closure. The fixed-point formula for `Bew_S` must be the arithmetization of
this exact guarded checker. An externally equivalent unguarded algorithm
would define a different box and cannot replace it in `R_n`.

| Formal component | Current status |
|---|---|
| Odd/even formula numbering with `#p_n=2n+1` | Explicit primitive-recursive construction above |
| Atom-occurrence consequence of a proof ending in `p_n` | Fixed syntax lemma; its PA derivation depends on the concrete parser coding |
| Uniform guard theorem `Box_S p_n -> H(n)` | Fixed PA proof follows from the explicit guard conjunct; proof object not emitted |
| Consistency, conservativity, D1–D3, and Löb | Standard translation/metatheory arguments; not instantiated against a finalized checker |
| Fixed-point checker and exact `R_n` syntax | Finite-alphabet grammar and axiom pattern are specified below; generated checker source and fixed-point constants are absent |
| Fragment-expansion formalization | `ChosenSystemExpansion`, `ChosenSystemSerialization`, and `ChosenSystemInterleaving` build with Lean 4.19.0; expansion and parser/serializer theorems list only `propext` and `Quot.sound`, with no `sorryAx` |
| Robust translation and character bound | Corrected coarse recurrence and `O(E^3)` translation are mathematical derivations; interleaved abstract fragments now obey the size bound, but the actual proof-file parser/name-printer map, accepted-file bounds, and checker-specific proof objects remain unverified |
| Lean/kernel certificate | Current expansion, grammar-plus-root serialization, and interleaved-fragment modules build successfully. No Lean certificate covers the actual metatheoretic checker, fixed point, PA derivations, or Löb argument |

## Fixed-point checker contract

This section makes the proposed verifier precise enough to implement and
audit. It remains a specification: the byte-level checker source, its fixed
point constants, and the PA derivation objects have not been emitted.

### Serialized proof files

Start with the finite character alphabet and formula grammar of `B`, and add
the characters needed for binary indices, record tags, separators, and the
letter `p`. The atom `p_n` is serialized as `p` followed by the canonical
binary expansion of `n` and a terminator. A proof file is a string of records
of these forms:

```text
DEF u_i := fragment ;
AX formula-fragment ;
MP earlier-line earlier-line ;
GEN earlier-line variable ;
```

`u_i` is a self-delimiting binary identifier. A `DEF` identifier is fresh;
its fragment may contain references only to earlier definitions. Definitions
may occur anywhere, with scope over the remaining file. References expand to
raw character fragments before the affected record is parsed. This allows a
fragment to cross later token and formula boundaries. Every character,
including tags, identifiers, and separators, contributes to written proof
length. Each non-definition record expands to one formula. `AX` is accepted
exactly when its expanded formula is a `B` axiom instance or has the added
reflection-axiom form below; `MP` and `GEN` must cite earlier records and
match the selected Hilbert rules. The last expanded derivation formula is the
conclusion. `B` axiom schemes, including induction, are allowed to contain
the new atoms `p_n`.

For `S`, use the odd/even formula numbering already specified above:
`#_S(p_n)=2n+1`, and every other formula receives an even code. `#_B` remains
the formula numbering used by the base PA proof checker. The code of a written
proof file is its base-alphabet string code, not either formula code. In
`H_d`, `d` and `Sub(d,j)` use `#_B`; `Box_S` uses `#_S`. This separation keeps
both the written `p_n` name and the binary numeral for its S formula code at
logarithmic length.

### The guarded relation

For candidate parameters `e,d`, define the following relations. `Raw_{e,d}(u,y)`
means that `u` decodes as a file, all its abbreviations expand legally, the
expanded records form a Hilbert derivation by the rules above, the added axiom
test uses the proof formula indexed by `e`, and the expanded root formula has
code `y`. `Occur(u,j)` means that token `p_j` occurs in any expanded
derivation formula, including the root. Let `M(u)` be the maximum such index,
or zero if there are no such tokens. Set

```text
H_d(j) := not exists q,
          Prf_B(q, Sub(d,j)) and WrittenLength_B(q) <= 2^j
Guard_d(u) := forall j <= M(u), Occur(u,j) -> H_d(j)
V_{e,d}(u,y) := Raw_{e,d}(u,y) and Guard_d(u)
Box_{e,d}(y) := exists u, V_{e,d}(u,y)
```

Here `d` is the `#_B` code of a one-free-variable formula and `Sub(d,j)` is
the `#_B` code of its closed instance at the canonical binary numeral for
`j`. The bounded search in `H_d` ranges over the finite alphabet
of `B` and counts the written file characters, including abbreviation
definitions. Macro expansion, parsing, line checking, occurrence scanning,
and the bounded proof search are primitive recursive. Thus `V_{e,d}` is
primitive recursive for each fixed pair. The `AX` recognizer accepts the exact
expanded formula

```text
(exists u, Prf_e(u, binary_numeral(2*n+1))) -> p_n
```

as `R_n`. The occurrence predicate is computed from the fully expanded
derivation, so it makes no claim about which source fragment produced a
token.

### Removing the self-reference circularity

The diagonal sentence and the checker fixed point are separate steps. First,
let `theta(z,x)` say that no `B`-proof of written length at most `2^x`
concludes the instance at `x` of the one-variable formula with code `z`.
The parameterized diagonal lemma gives one formula `D(x)`, with code `d`, and
a fixed `B` proof of `forall x (D(x) <-> theta(d,x))`. Set
`H_d(x) := theta(d,x)`. This diagonal construction refers to `B` and the
code `d`, but not to `S`.

Next, for provisional checker index `e`, compile `V_{e,d}` with this fixed
`H_d` guard. Let `Prf_e(u,y)` be the fixed arithmetic computation formula
for program index `e`. The extra-axiom recognizer matches exactly
`(exists u Prf_e(u,2*n+1)) -> p_n`. The map `e |-> index(V_{e,d})` is
computable, so Kleene's recursion theorem gives an index `e` whose program
computes this checker. Set `Box_S(y) := exists u Prf_e(u,y)`. The fixed-point
identity makes the proof predicate used by the recognizer the predicate of
this very checker. This defines one proof system `S` with added axiom scheme
`Box_S p_n -> p_n`. A kernel-level formalization must emit `d`, `e`, the
generated checker source, and `B` proofs of the diagonal equivalence and of
the represented graph identity for `Prf_e`. Those objects are still missing
here. Mere external equivalence between two checkers is not enough to
substitute one proof predicate for the other in `R_n`.

### Uniform guard lemma and Löb conditions

Let `CodeP(n,y)` be the fixed arithmetic relation `y=odd(n)`, where `odd` is
the term spelling fixed above. The concrete parser must support one fixed `B`
derivation of

```text
Raw(u,y) and CodeP(n,y) -> Occur(u,n).
```

This is the root-occurrence syntax lemma: if the checked derivation ends in
the decoded atom `p_n`, its expanded root contains `p_n`. The odd/even code
assignment and root parser make the implication uniform in `n`. Also,
`Occur(u,n)` implies `n<=M(u)`. The `Guard` conjunct therefore yields one
fixed `B` proof of the arithmetic sentence
`forall n forall y (CodeP(n,y) and Box_S(y) -> H_d(n))`. By definition,
`CodeP(n,odd(n))` is `odd(n)=odd(n)`, an equality-reflexivity axiom
instance. Universal instantiation and modus ponens therefore give one fixed
proof of `forall n (Box_S(odd(n)) -> H_d(n))`; composing with the diagonal
equivalence gives `forall n (Box_S(odd(n)) -> D(n))`. At the instance
`n=bar j`, the code term `odd(bar j)` is syntactically the canonical numeral
`bar(2j+1)`, so it is exactly the code numeral used in `R_j`.

The remaining per-index cost is ordinary Hilbert specialization of this one
fixed universal theorem. Its formula contains a fixed number of occurrences
of `n`; substituting `bar j` produces `O(log(j+2))` characters. One
universal-instantiation axiom instance and modus ponens yield the required
instance, with total written length `O(log(j+2))`. Thus both the code-numeral
bridge and the axiom-instance constructor have explicit logarithmic cost.

For this exact relation, the three derivability-condition proof objects have
the following constructions:

1. **D1, necessitation of a proved sentence.** For each concrete accepted
   file, its finite `V`-computation is true. Numeralwise representability
   gives a `B` proof of that check, hence an `S` proof of its existential
   provability assertion. This is instancewise; it does not assert a uniform
   proof of all guard tests.
2. **D2, distribution.** A primitive-recursive join renames the abbreviations
   in two input files, concatenates their derivations, and appends one MP
   record. Its new conclusion contains no `p_j` not already in the proved
   implication. The guard of the joined file follows from the guards of both
   inputs by taking the union of their occurrence sets. PA must prove this
   closure statement for the exact join function.
3. **D3, provable sentences are provably provable.** `Box_S A` is a
   `Sigma_1` sentence because `V` is primitive recursive. PA's formalized
   `Sigma_1` completeness proves `Box_S A -> Box_B(Box_S A)`; arithmetic `B`
   proofs embed into `S` with an empty guard. This gives
   `Box_S A -> Box_S Box_S A`.

The consistency interpretation maps each `p_j` to `0=0` and fixes arithmetic
symbols. It sends each added axiom to `Box_S p_n -> (0=0)`, a `B` theorem,
and sends PA axioms and rules to PA axioms and rules. Hence every arithmetic
theorem of `S` translates to a `B` theorem; under `Con(B)`, `S` is consistent.
The diagonal argument under `Con(B)` also makes every finite guard `H(n)` true,
so each `R_n` is an accepted one-line proof. Löb's theorem applied to the
actual `Box_S` then gives `S |- p_n` for every standard `n`.

### The character ledger against this serializer

The expansion bound above applies to this grammar because all references are
acyclic, every written definition and record has length at most `m`, and
there are at most `m` of them. After expansion, an input of total size `E`
contains at most `E` records and every binary index has at most `E` digits.
Replacing every `p_j` by the closed formula `D(\bar j)` multiplies a formula
length by at most `O(E)`, since `|D(\bar j)|=O(log(j+2))=O(E)`. A translated
formula therefore has length `O(E^2)`. Use an ordinary uncompressed `B`
derivation, and for each `R_j` use the instance of the one fixed theorem
`forall j (Box_S p_j -> D(j))`; the number of source records is at most `E`.
The exact code numeral is fixed by the recursive grammar above. A
universal-instantiation axiom and its modus-ponens step cost
`O(log(j+2))`; all translated formulas and records cost at most `O(E^2)`
each. With at most `E` source records, the uncompressed translation has
length `O(E^3)`. Therefore `E<=(m+1)^(m+3)` implies the stated
`ell_B(D(\bar n)) <= 2^(C(m+1)^2)` after increasing a fixed constant.

This specification now exposes the work needed to finish the formal proof:
emit the fixed-point checker source and constants; prove the root-occurrence,
guard, D1--D3, consistency, and translation lemmas in the chosen PA calculus;
and verify the character costs against its actual record serializer. The
local source currently supplies none of those proof objects, so the result
remains a conditional paper proof rather than a closed formal verification.

The Lean 4.19.0 binary in this workspace exits with `failed to locate
application` before elaborating any source file. Setting `LAKE_HOME` lets the
bundled Lake launch Lean, but the same Lean startup error follows. This is an
environment failure, not a rejection of the proposed proof. The expanded
language construction therefore remains a conditional mathematical proof
draft. It does not resolve fixed `PA_bin` Part 1 or Part 2.

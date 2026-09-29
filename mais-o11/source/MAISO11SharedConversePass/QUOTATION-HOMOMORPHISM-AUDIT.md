# Exact numeral quotation by fragment homomorphisms

This is a mathematical construction, not a new Lean certificate. It audits
`StringQuotation.lean`, `QuotationWire.lean`, and `recovered/spec/MAIS-A1.tex`.
It does not identify their arithmetic quotation compiler with the fixed Bew.

## Conditional theorem

Let A be a fixed alphabet of size b = 2^r, r >= 1, with a fixed bijection
d : A -> {0,...,b-1}. Let G be an acyclic straight-line string grammar,
whose productions may refer only to earlier productions. Let M count all
right-hand-side terminal/reference occurrences and productions. Its designated
output expands to w. Define

    raw(w) = sum_{i=0}^{|w|-1} d(w_i) b^(|w|-1-i)
    marked(w) = b^|w| + raw(w).

There is an effectively constructed fragment grammar of O_r(M+1) mass
whose output is exactly the canonical binary-constructor numeral for raw(w),
and another with the same bound for marked(w). With fresh identifiers using
a fixed self-delimiting binary index code of O(log(i+2)) characters, their
written sizes are O_r((M+1) log(M+2)). They require no expansion of w.

The numeral convention here is the one implemented by QuotationWire:
N(0) is the character `0`; N(2q) is `(D` N(q) `)` for positive even 2q;
N(2q+1) is `(E` N(q) `)`. Thus the *outermost* constructor records the
least significant bit. D and E denote x -> 2x and x -> 2x+1.
If an actual syntax expands these constructors into fixed one-hole contexts
over PA's primitive alphabet, replace each prefix/suffix by its fixed context.
The same argument works when each context contains its argument exactly once.

## Bit identity and numeral orientation

Write h(a) for the r-bit, most-significant-first binary representation of d(a),
padded with leading zeros. Extend h to words by concatenation. The base-2 value
of h(w) equals raw(w), by induction using

    val_2(xy) = val_2(x) 2^|y| + val_2(y).

The binary representation of marked(w) is exactly `1` h(w). Indeed h(w)
has r|w| bits and value strictly below 2^(r|w|). Adding 2^(r|w|)
therefore introduces its initial 1 without any carry into its payload.
This handles the empty word: marked(empty) = 1, with binary string `1`.

For any canonical most-significant-first bit word q, define P(0) = `(D`,
P(1) = `(E`, and C(0) = C(1) = `)`. Then its exact numeral string is

    P(reverse(q)) ++ `0` ++ C(q).

P and C here denote letterwise homomorphisms. A direct induction on the
least-significant-first word reverse(q) proves this agrees with
`numeralBits` in QuotationWire. The order reversal is essential: mapping
the MSB-first word directly to outer constructors generally gives the wrong
integer. For example 6 has bits 110 and numeral `(D(E(E0)))`.

For marked coding one may use the particularly simple output

    P(reverse(h(w))) ++ `(E0)` ++ C(h(w)).

No leading-zero normalization is needed, even if all source digits are zero.

## Grammar transformations and cost proof

Homomorphism: replace each terminal a in every production by its fixed image
h(a), and each reference X by its transformed reference X_h. Induction in
definition order proves expand(X_h) = h(expand(X)). The mass grows by at
most a constant depending on r. All references remain backward references.

Reversal: reverse the order of atoms in each production; reverse each terminal
image; replace a reference X by the corresponding X_rev. Induction proves
expand(X_rev) = reverse(expand(X)). This preserves acyclicity and is linear
in grammar mass. The need to reverse production atom order cannot be omitted.

Apply these operations to produce prefix and closing-parenthesis grammars.
Their definition sets are disjoint, with fresh renamed identifiers, and an
extra output production concatenates their roots and the central constant.
There are O_r(M+1) definitions and occurrences. Standard binary identifier
encodings charge O(log(M+2)) per occurrence, giving the stated character bound.
If only the coarse bound already proved for QuotationWire.identifier is used,
the result is still polynomial (quadratic), without needing a new logarithmic
identifier-length lemma. The sharper character bound above is a mathematical
bound for that identifier encoding, not currently its checked Lean theorem.

## Raw coding and leading zeros

Simply applying the marked construction after omitting the initial 1 is not
canonical for raw coding: its binary expansion may begin with arbitrarily many
zero bits. However removing these zeros preserves polynomial grammar size.

Binarize the bit grammar, introducing O_r(M+1) productions with right-hand
sides empty, a single bit, or XY. Compute a Boolean nz(X) indicating whether
expand(X) contains a 1. In definition order create a trimmed variant T(X):

* T(empty) and T(0) expand to the empty word; T(1) expands to `1`.
* If X = YZ and nz(Y) is true, set T(X) := T(Y) Z.
* If X = YZ and nz(Y) is false, set T(X) := T(Z).

Retain the original productions as well as the trimmed variants. The original
Z in the second bullet is intentional: zeros after the first 1 must remain.
Induction proves T(X) expands to expand(X) with its leading zeros deleted.
Only O(1) new symbols and productions are introduced per binarized production.
The all-zero and empty cases yield q = empty, whose numeral is exactly `0`.
Now apply reversal and P,C to this trimmed grammar. Nothing in this procedure
tests exponentially many bits or stores their expansion.

Raw coding itself is not injective on arbitrary words: leading zero source
digits are lost. A separate length field, a sentinel, or a restriction on
admissible leading digits is required for a genuine numbering. This issue
does not invalidate the raw-code numeral theorem; it limits its use as a
claim about the specified Goedel numbering.

## What the uploaded specification does and does not fix

MAIS-A1 line 104 chooses a fixed finite alphabet, fully parenthesized prefix
syntax, binary-constructor numerals, arbitrary string abbreviations, and
base-|Sigma_S| codes of proof files. It does not enumerate Sigma_S or assert
its size is a power of two. It does not specify its digit enumeration,
the leading-zero convention, or a sentinel. Line 109 separately says to fix
a standard numbering of formulas and a Delta_1 Bew predicate. The claimed
code-size bound does not itself fix these omitted serialization choices.

Consequently the conditional theorem cannot simply be declared to apply to
the actual default coding. Adding unused alphabet symbols to obtain a power
of two changes the base, hence the numbers appearing in the fixed predicate.
One must either establish that the intended alphabet already has this size,
or construct a quantitatively controlled proof-predicate/coding bridge.
The file-level base convention and the formula-code convention also need to
be matched explicitly; a proof of a fact about codes of written proof files
does not automatically establish the same fact about codes of expanded
conclusion formulas.

For a base b which is not a power of two, this particular fixed-length bit
homomorphism is unavailable. Conversion of exponentially expanded base-b
words to canonical binary numerals is a separate problem. This audit proves
no impossibility or lower bound for that conversion.

## Relationship to the existing certificate and remaining proof obligation

StringQuotation.compile constructs *arithmetic expressions* using + and *
whose denotations are length, scale, and raw payload. Its marked-code result
adds scale and payload. QuotationWire serializes these expressions using
small binary numeral constants. Neither construction asserts that its output
is the canonical numeral syntax of the enormous resulting integer.

The homomorphism construction above supplies exact numeral syntax in its
conditional power-of-two case; it does not provide a short PA derivation that
the arithmetic-expression quotation equals that numeral. It also does not
give a short PA derivation of Bew for a compressed proof. The local arithmetic
identities needed for such a bridge must be represented as actual PA proof
files, checked under the actual arithmetic axioms, with character bounds.
Externally proving their semantics in Lean does not discharge that obligation.

Thus the useful milestone is a precise, implementable way to remove the
syntactic numeral-output obstacle for aligned base coding. The fixed-coding
bridge, PA internalization, and full compressed proof checking remain open.

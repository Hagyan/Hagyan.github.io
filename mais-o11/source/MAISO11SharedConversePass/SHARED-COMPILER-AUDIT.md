# Arbitrary string abbreviations cannot always compile to small term DAGs

Research audit, 25 September 2026. This note concerns the representation used by
the checker, not a lower bound for shortest PA proofs and not a resolution of
MAIS-O11.

**Result.** Under the agenda's unrestricted fixed-string abbreviation rule,
there are accepted proof files of polynomial written length whose expanded
conclusions contain a term requiring exponentially many nodes in any ordinary
term DAG. Thus the verified compiler for `CDefs` cannot be extended to all
string-fragment abbreviations while retaining both exact expanded syntax and a
polynomial bound on its ordinary-DAG output. The obstruction already occurs in
closed terms without variables, quantifiers, substitution, or induction.

## 1. Which abbreviation rule is being audited

The supplied `recovered/spec/MAIS-A1.tex`, lines 100 and 104, permits a fresh
symbol to stand for a fixed string, including earlier abbreviation symbols. Its
PA-bin checker expands these strings and checks the resulting Enderton proof.
It does not require each right-hand side to be a complete term or formula.

By contrast, the verified Lean `CDefs.snoc` constructor takes a right-hand side
of type `CTerm r 0`: it is a complete closed term, and every reference denotes a
closed term. `GraphCompiler.lean` correctly compiles this smaller language.
Those requirements are essential to its linear retained-node bound.

The construction below assumes literal string fragments such as `(E` and `)`
are permitted as definition right-hand sides. It therefore applies to the
unrestricted reading of the supplied agenda. If the intended grammar restricts
definitions to complete expressions, it describes a different abbreviation
discipline and this example is excluded. The agenda does not provide an
executable parser resolving every token-level convention.

## 2. Explicit family of fragment definitions

Use the existing Lean project's fully parenthesized token convention:

- `0` is the zero term;
- `(E` followed by a term and `)` denotes the unary constructor `E(t)=2t+1`;
- `(=` followed by two terms and `)` denotes equality;
- `(>` followed by two formulas and `)` denotes implication.

Let `I_j` denote the actual self-delimiting identifier `identifier j`; the
subscript notation is for this explanation and is not written in the file.
For each nonnegative integer n, write these definitions in order. Quotation
marks and subscripts below are explanatory, not literal file characters.

```text
def I_0 := (E
def I_1 := )
for k = 0,...,n-1:
    def I_(2k+2) := I_(2k) I_(2k)
    def I_(2k+3) := I_(2k+1) I_(2k+1)
def I_(2n+2) := I_(2n) 0 I_(2n+1)
```

There are no separator spaces between the right-hand-side pieces: these are
concatenations of self-delimiting identifiers and literal characters. Each
definition mentions only earlier identifiers. The two base right-hand sides
are deliberately incomplete term fragments.

Induction on k gives

\[
\operatorname{expand}(I_{2k})=\texttt{(E}^{\,2^k},\qquad
\operatorname{expand}(I_{2k+1})=\texttt{)}^{\,2^k}.
\]

Consequently the final abbreviation expands to the well-formed term

\[
T_n=E^{2^n}(0),
\]

with exactly `2^n` unary constructor nodes and one zero leaf. Its height is
`2^n`. Its expanded wire has `3*2^n+1` characters. It is also the canonical
all-ones binary numeral for `2^(2^n)-1` under this constructor convention.

To turn this into a proof file, append a propositional tautology axiom record
whose expanded formula is

\[
(T_n=T_n)\to(T_n=T_n).
\]

Under the project's tag convention, the exact appended string is the
concatenation

```text
"A (>" ++ "(=" ++ I_(2n+2) ++ I_(2n+2) ++ ")"
       ++ "(=" ++ I_(2n+2) ++ I_(2n+2) ++ "))\n"
```

Enderton's propositional-tautology axiom family accepts this expanded formula.
Alternatively, a calculus using only fixed propositional axiom schemas may use
`A → (A → A)` in the last line, changing only constant-size overheads.

**Acceptance scope:** this is an accepted proof under unrestricted fragment
expansion followed by the stated propositional axiom check. It is not an
accepted input of the current Lean closed-term prelude parser: that parser
rejects the very first right-hand side `(E`. We have not supplied a new verified
unrestricted PA-bin parser here, so this acceptance argument is mathematical,
based on the agenda's grammar description, rather than a theorem about a
completed Lean PA-bin implementation.

## 3. Character ledger

For the project's precise identifier encoding,

\[
|I_j|=2\,|\operatorname{bits}(j+1)|+2\le 2j+4.
\]

Every identifier used above has index at most `2n+2`. Set `H=4n+8`. Thus all
identifier occurrences have length at most H. A definition line has fixed
overhead nine characters: `def `, ` := `, and newline.

| Record kind | Number | Upper bound per record |
|---|---:|---:|
| Initial opening/closing definitions | 2 | `H+11` |
| Doubling definitions | `2n` | `3H+9` |
| Final complete-term definition | 1 | `3H+10` |
| Final `A→A` tautology record | 1 | `4H+12` |

Since every row costs at most `4H+12`, this gives the conservative bound

\[
L_n\le B(n):=(2n+4)(16n+44).
\]

This exact B(n) is conditional on the literal syntax and tag convention just
specified; it is not claimed as an exact bound for every unspecified choice in
the agenda. Any fixed alternative axiom tag, fixed parenthesization convention,
or fixed-length spelling of the unary constructor changes the constants only.
For instance, if a unary constructor is written as `a t b` for fixed strings a
and b, double the fragments a and b instead. The obstruction therefore does
not depend on the particular single-letter E token.

Using the actual logarithmic bit length of these identifiers gives the sharper
asymptotic bound `L_n = O(n log(n+2))`. The displayed quadratic B(n) is already
enough to refute every polynomial ordinary-DAG output bound.

## 4. The DAG lower bound

An ordinary term DAG has one constructor label per node; outgoing edges point
to the constructor's immediate subterms. Its meaning is obtained solely by
unfolding shared nodes. In particular, nodes do not contain context parameters,
iteration counts, or a compressed program describing an entire path.

**Lemma.** In the project's `Graph m`, if node i expands to a term of height h,
then `h ≤ i.val < m`.

**Proof.** Induct along the topological node order. A zero node has height zero.
Every unary node has one child of smaller index, so its height is at most its
own index. Every binary node has height one plus the maximum child height;
again each child index is smaller than its own index. This also proves that
adding later nodes preserves the claim for earlier nodes. ∎

**Corollary.** If any node of `Graph m` expands to `T_n`, then

\[
m\ge 2^n+1.
\]

Equivalently, the distinct subterms of `T_n` are
`0,E(0),...,E^(2^n)(0)`; their distinct heights prohibit sharing between them.

For every fixed polynomial p, `2^n+1 > p(B(n))` for all sufficiently large n.
Hence no transformation on all these fragment files can produce an exactly
equivalent ordinary term DAG with at most p(input-length) nodes. This is an
unconditional output-size obstruction, independent of algorithm design and of
unproved complexity-class separations.

The same argument rules out polynomial normalization of unrestricted fragment
abbreviations into the present `CDefs` language while preserving exact syntax:
`GraphCompiler.compileDefs` would turn the normalized prelude into a DAG with
at most its retained syntax mass, contradicting this lower bound.

Replacing the term by a shorter arithmetically equal term does not meet this
specification: formula matching, quotation, and modus ponens concern exact
expanded syntax. In the present E-example even the represented natural number
grows doubly exponentially, but numerical growth is not needed for the proof.

## 5. Kernel-checked part of the audit

The proof of the graph-height lemma and its unary-chain corollary was checked
against the existing `DagEquality.lean` using Lean 4.19.0. The temporary audit
source is `tmp/shared-compiler-audit/FragmentHeightAudit.lean`.

Its central theorem is:

```lean
theorem fragment_family_graph_lower_bound {m : Nat}
    (g : Graph m) (i : Fin m) (n : Nat)
    (h : g.expand i = unaryChain (2^n)) : 2^n + 1 ≤ m
```

The more general checked lemma is:

```lean
theorem graph_height_le_index {n : Nat} (g : Graph n) (i : Fin n) :
    height (g.expand i) ≤ i.val
```

Compilation exited successfully; the lower-bound theorem uses only
`propext` and `Quot.sound`, with no custom axioms, `sorry`, or `admit`. The
unrestricted macro parser, the entire file-acceptance theorem, the full
character ledger, and the eventual exponential-versus-polynomial comparison
are not formalized in that temporary audit. The separately developed project
module `GraphDepthBarrier.lean` also checks the depth obstruction.

## 6. Binders create an additional representation issue

The preceding obstruction is already decisive and does not depend on binding.
Binding nevertheless explains a second gap between `CDefs` and arbitrary raw
strings. A macro `u := x` expanded inside `∀x∀y(u=x)` places x at de Bruijn
index 1; expanded inside `∀y∀x(u=x)` it places x at index 0. The two expanded
formulas are closed, yet the same raw fragment does not have one invariant
closed-term interpretation. Fragments can also contain an opening quantifier
whose scope extends beyond that fragment.

Therefore the current contract `refs : Fin r → ClosedTerm` cannot describe
arbitrary source macros. A suitable checker must preserve named syntax and
track scope, or use contexts with explicit renaming/substitution information.
Simply adding constructors for generalization and PA axioms does not repair
the representation mismatch.

## 7. Routes that remain open

The barrier rules out ordinary-DAG normalization. It does not show that
unrestricted compressed proof checking requires superpolynomial time, or that
short PA proofs of checker computations cannot exist.

A representation that shares contexts handles this particular counterexample:
take `C_0(x)=E(x)`, `C_(k+1)(x)=C_k(C_k(x))`, and `T_n=C_n(0)`. This has O(n)
grammar size because it shares a path with a hole. Such parameterized context
nodes are strictly richer than the nodes of `Shared.Graph`. No theorem here
asserts polynomial conversion of every PA-bin string macro into such a grammar.

Two research directions are accordingly viable targets, with different proof
obligations:

1. Keep the source string straight-line program and perform the required
   parsing, equality, substitution, and side-condition checks directly on its
   compressed representation.
2. Prove an explicit polynomial conversion into a richer context or forest
   grammar, then verify the required operations there.

Either route still needs the particular Enderton axiom checker, generalization
and substitution conditions, a rigorous computational bound, and PA proof
internalization. These are separate from the verified ordinary-DAG result.

## 8. Literature cross-check and caution

The height limitation of DAG compression and its repair by context grammars
are established themes in tree compression; see Ganardi, Jeż, and Lohrey,
[Balancing Straight-Line Programs](https://arxiv.org/abs/1902.03568).

Ganardi, Hucke, Lohrey, and Noeth,
[Tree Compression Using String Grammars](https://arxiv.org/abs/1504.05535),
Theorems 7–9, distinguish preorder-string SLPs, tree grammars, and
balanced-parenthesis SLPs, including exponential succinctness separations.
Their preorder separation cannot simply be cited as an obstruction for the
agenda's fully parenthesized strings; the encodings differ. The unary-chain
construction above avoids that transfer issue and proves the required
ordinary-DAG obstruction directly in fully parenthesized notation.

No novelty claim is made for the general compression phenomenon. Its relevance
here is identifying an exact, previously hidden incompatibility between the
agenda's abbreviation grammar and the proposed PA-bin compiler milestone.

# Current certificate status — 27 September 2026

MAIS-O11 Parts 1 and 2 remain unresolved.

The newest strategic step is in `LOB-INTERNALIZATION-REDIRECT.md`. For Part 2,
the immediate target is polynomial internalization of the particular proof
assembled by the Löb construction, not a global compiler for every accepted
PA-bin proof file. The latter is stronger and includes arbitrary propositional
tautology axiom records. The one-instance summary work is a compressed
arithmetic-certificate example, not an O11 witness or a proof of the Löb
internalization bound.

| Component | Status |
|---|---|
| Restricted whole-file checker and compact universal instantiation | Successful Lean 4.19.0 checks recorded earlier in this session |
| Cached arbitrary-fragment balance summary | Successful Lean 4.19.0 check recorded earlier in this session |
| Expanded-length and numeric-storage bounds (`GrammarLengthBound`) | Successful Lean 4.19.0 check reported in the preceding agent run |
| Explicit fragment family and ordinary-DAG size obstruction | Successful Lean 4.19.0 check recorded earlier in this session |
| Prefix query correctness and instrumented visits (`FragmentPrefix`) | Source complete and independently audited; successful kernel run still pending |
| Interval query correctness (`FragmentRange`) | Source complete and mathematically audited; successful kernel run still pending |
| Matching delimiters, three-query witness check, two-boundary traversal bound | Mathematical argument and independent Python audit; not a Lean or PA certificate |
| Binary addition and local existential summary proofs | Explicit PA-admissible proof objects checked by the new Python calculus; not an exact Enderton or Lean certificate |
| Saved arithmetic proof object for an exponential-word summary table | Fresh JSON replay passed; 407 local Join roots; assembly currently checked externally |
| Concrete summary theorem in Lean | `SummaryFiniteCheck.lean` generated; 204-rule table and 407 Join relations independently specified; kernel run pending |
| Uniform scan and existential expansion-table theorem | Mathematical induction argument for explicit auxiliary coding; PA derivation not emitted |
| Polynomial-bit sequence/table coding | Explicit coding and mathematical size bound; executable round trips passed |
| Arithmetic decoder bridge (`CodedScan`) | Source written; kernel verification pending; semantic Lean theorem, not a PA derivation |
| Exact numeral grammar for power-of-two coding | Mathematical construction only; conditional on coding choices |
| Full PA-bin parser, fixed Bew bridge, polynomial PA acceptance proofs | Not established |

The current workspace has neither `lake` nor `lean` on `PATH`. Consequently,
the newly generated `SummaryFiniteCheck.lean` has not been run by Lean here.
This is not a theorem rejection or a successful verification.

From this directory on a working Lean installation:

```bash
lake build GraphFileCheckerInst FragmentBalance GraphDepthBarrier SpecTransfer GrammarLengthBound FragmentFamily
lake build FragmentPrefix FragmentRange
python3 check_fragment_navigation.py
```

The project pins Lean 4.19.0. The second command is the outstanding formal check.
The third runs an independent executable audit, not a kernel certificate.
The prefix file includes executable examples, but no passing output from those
examples is asserted for the current server run.

See `CONVERSE-NOTE.md` for scope and the audit files for assumptions and gaps.
See `NAVIGATION-MILESTONE.md` for the exact matching theorem and the remaining
PA obligation. The numerical audit output is in `NAVIGATION-AUDIT-OUTPUT.txt`.

The arithmetic step is `PA-ARITHMETIC-MILESTONE.md`: the proof generator now derives
numerical additions and closed existential Join assertions from arithmetic
axioms. This extends beyond the earlier reflexivity-only local certificates.
It does not supply the uniform PA theorem about decoded grammar semantics.

```bash
python3 pa_eq_kernel.py
python3 pa_summary_certificate.py
python3 pa_summary_replay.py --verify summary-arithmetic-demo.json
python3 emit_summary_lean.py summary-arithmetic-demo.json SummaryFiniteCheck.lean
lake env lean SummaryFiniteCheck.lean
```

The first three commands use the experimental PA-admissible calculus, not
Lean. The last two generate and check an independent Lean proof of the fixed
finite example. It does not establish fixed-Bew acceptance. Recorded replay
output is in `PA-AGGREGATE-REPLAY-OUTPUT.txt`.

The latest step is `SYMBOLIC-EXPANSION-MILESTONE.md`, with the detailed
`UNIFORM-SCAN-AUDIT.md`. Expanded codes can remain existential in a fixed
uniform PA theorem for the auxiliary encoding; the named grammar/local-table
codes have polynomial bit length. The single packed-table antecedent still
needs a polynomial PA proof, and the fixed-Bew bridge remains open.

```bash
python3 packed_summary_tables.py summary-arithmetic-demo.json
lake build CodedScan
```

The coding audit passed. The Lean command remains outstanding.

## 27 September research-direction correction

`LOB-INTERNALIZATION-REDIRECT.md` factors the standard proof-length argument
into diagonalization cost and internalization cost for the specific
Löb-assembled derivation. A polynomial bound on the agenda's global expansion
function would be sufficient, but Part 2 does not itself ask for that stronger
O12 result. The targeted construction still has to handle any tautology
axiom records in its reflection-proof input; no polynomial bound is claimed.
The quadratic-trailer Part 1 example remains only a loophole under the three
bare efficiency bullets: it violates the constant-cost composition property
used by the intended proof calculus. No new result for PA-bin has been
established in this direction correction.

## 27 September finite Lean source update

The new `emit_summary_lean.py` exports the replay-checked grammar to
`SummaryFiniteCheck.lean`. The generated source defines computation over the
explicit 204-rule grammar, states the backward-reference and table-equality
checks, and contains explicit witness proof terms for all 407 local Join
equations. It states that the final summary is `(2^101+1,0,0)`, so the sample
compressed word is balanced and has the expected length. The source is
designed for Lean 4.19.0 but remains pending a kernel run because no Lean
executable is available in this workspace.

This is an independent proof of the finite semantic instance. It does not
replay the experimental Python proof objects, provide a PA Hilbert derivation
of the packed-table predicate, or connect the auxiliary representation to the
agenda's fixed PA-bin checker and `Bew`. The next research step is still the
uniform arithmetic proof linking the packed table lookup equations to the
individual Join roots; both MAIS-O11 parts remain unresolved.

---

# Symbolic expansion and polynomial-bit table coding

26 September 2026. MAIS-O11 remains unresolved. This note supplies a
mathematical uniform-induction argument for an explicitly chosen auxiliary
coding, together with coding implementations and pending Lean source. It does
not claim a newly kernel-checked PA derivation or fixed-Bew equivalence.

## 1. The useful theorem

The table of local Join proofs can be used without printing the enormous
expanded word codes. The intended uniform arithmetic statement is

    ValidGrammar(g) AND LocalJoinTable(g,t)
      -> exists e, Expanded(g,e) AND
           forall i < productions(g), NF(e[i],t[i]).

Here e stores expanded words as pairs (length, raw base-b payload); NF compares
their actual digit scan with the supplied summaries. The proof is two nested
inductions, on productions and positions within each RHS. It remains uniform
in the codes g,t, rather than a separate argument for each standard grammar.

`UNIFORM-SCAN-AUDIT.md` gives the proof in detail. The conclusion is a fixed
theorem provable in PA after defining the indicated elementary operations and
finite-sequence coding. This is a mathematical PA-provability argument by
effective formalization, **not a printed Enderton proof or a Lean certificate**.
The distinction applies to every claim of PA provability in this note.

An instance names only g and t. The expansion table e stays existentially
quantified. Applying existential elimination later requires a statement
uniform in e; one cannot extract its value, print its enormous numeral, and
retain the same size claim.

## 2. The scan means decoded characters, not certificate acceptance

Fix b>=2 and distinct digits op,cl<b. A word is (L,c) with c<b^L, retaining
leading zeros through L. Concatenation is

    (L,c) * (K,d) = (L+K, c*b^K+d).

Define T_d on unmatched-close/open pairs (R,O): an opening digit increments O;
a closing digit decrements O when O>0, otherwise increments R; a neutral digit
does nothing. The arithmetic Scan reads the L base-b digits of c from left
to right and iterates T.

Writing J for the uniquely determined result of Join, the elementary identity

    T_d(J(s,t)) = J(s,T_d(t))

has an exhaustive proof by cases on the digit and the relevant unmatched
counts. This yields, by induction on K,

    Scan(L+K,c*b^K+d) = J(Scan(L,c),Scan(K,d))  when d<b^K.

Crucially, NF is defined using this actual arithmetic digit scan. Defining NF
merely as 'there exists an accepted local table' would make the proposed
bridge circular. No axiom about arbitrary semantic truth is used.

The displayed Scan recurrence changes the payload parameter. To specify a
literal primitive recursion, use the digit-fold H(L,c,i) in the audit note,
then prove the recurrence by induction. This fixes a definability detail that
could otherwise be hidden by the phrase 'primitive recursive'.

## 3. Explicit sequence coding with polynomial bit length

The audit called for a concrete finite-sequence encoding. Use

    Pair(a,b) = (a+b)^2+a+1.

This is injective: if s=a+b, then Pair(a,b)-1 lies between s^2 and s^2+s,
and these intervals are disjoint for different s. Thus s is determined, then
a is determined by subtraction, then b=s-a. PA proves this argument using
elementary inequalities. The arithmetic inverse can be defined by bounded
search; the executable implementation uses integer square root.

For a sequence x_0,...,x_(n-1), choose w>=1 with every x_i<2^w and put

    p = sum_(i<n) x_i * 2^(w*i),
    SeqCode = Pair(n,Pair(w,p)).

A valid sequence representation has w>=1 and p<2^(n*w). Entry i<n is

    (p div 2^(w*i)) mod 2^w.

These formulas specify a concrete arithmetical sequence predicate after the
graphs of exponentiation and division are expanded. The representation need
not have minimal w: admitting larger widths simplifies the append lemma.
The generator chooses max(1,max_i bitlength(x_i)) deterministically.

**Size.** If a,b<2^B, Pair(a,b)<2^(2B+3). There are only two pairing layers in
SeqCode, so its bit length is O(n*w+log(n+2)+log(w+2)). Encode a summary triple
by Pair(L,Pair(R,O)); if its coordinates have B bits, it has O(B) bits.
For O(M) table and accumulator entries with O(M)-bit coordinates, the complete
local-table code has O(M^2) bits. This avoids repeatedly nesting Pair once per
entry, which would give a much worse bit-length recurrence.

Grammar RHSs are sequences of tagged atoms. For a literal digit d use 2d;
for a reference index j use 2j+1. Encode the list of RHS codes by the same
scheme. For a fixed alphabet and grammar mass M, an RHS code has at most
O(M log(M+2)) bits, and the outer code has O(M^2 log(M+2)) bits. This loose
bound suffices; no uncharged identifiers are being assumed. Backward-reference
checks remain part of ValidGrammar.

The local-table code contains both the root summary table and every RHS
intermediate accumulator, in production/atom order. Thus the single arithmetic
predicate LocalJoinTable can quantify over a bounded set of locations and
check Join between each adjacent accumulator and the correct literal or
earlier-reference entry. Empty RHSs have the zero summary.

To append an entry when proving sequence existence in PA, first increase the
width if needed, recode the finitely many old entries, and append the new
digit block. Induction on sequence length proves the recoding preserves all
lookups. These are elementary finite-recursion lemmas, so the outer grammar
induction can construct e without assuming an infinite sequence or a choice
principle. Their explicit PA derivations are still to be emitted.

## 4. What this removes, and what it does not

The expansion table can contain numbers with exponentially many bits. That
does not prevent the *uniform theorem* above or a short instance naming only
g,t. PA proves existence by finite induction; the proof does not need to
evaluate the existential witness as a literal numeral.

The two named input codes g,t now also have explicit polynomial bit bounds.
Consequently, if a polynomial-size PA proof of the single antecedent
ValidGrammar(g) AND LocalJoinTable(g,t) is supplied, applying the fixed theorem
preserves polynomial size under polynomial proof assembly. No term depending
on the printed size of e enters this conditional size argument.

**The remaining antecedent obligation is real.** The 407 local arithmetic
proofs from the previous milestone are not yet one PA proof about the packed
table code. We still must prove lookup equations, tags and bounds for that
code, and combine local assertions under the bounded index quantifiers.
Polynomial payload size does not, by itself, prove a polynomial PA proof-size
bound. This note does not import an unverified general efficient-computation
theorem to skip that work.

The auxiliary coding is explicit. It has not silently replaced the problem's
fixed proof predicate. A PA-provable equivalence to the intended decoder and
Bew remains necessary. Also, delimiter summaries handle only one syntactic
service: full term/formula recognition, substitution, and the tautology axiom
family remain separate issues.

## 5. Artifacts and evidence

`CodedScan.lean` specifies numerical decoding and scanning against the existing
`rawCode`. Its source includes decoder length, both inversion directions for
valid codes, concatenation, and

    cachedGrammarSummary ... = scanCode ... length rawPayload.

The concat theorem in that file assumes both payload bounds. Actual grammar
words have these bounds by the existing raw-code theorem. Its scan is a
semantic specification that recurses over expanded length, not the compressed
polynomial-time implementation. The file remains **pending kernel verification**;
it is also not an object-language PA derivation even if Lean verifies it.

`packed_summary_tables.py` implements the sequence coding and checks round trips
against the saved arithmetic-certificate example. The measured code sizes are:

| Code | Bits |
|---|---:|
| Grammar | 120,766 |
| Root summary table | 326,421 |
| Intermediate accumulator table | 652,033 |
| Combined local table | 1,304,065 |

These are auxiliary numeric codes for the grammar and local data, not the
expanded word code. The example's expanded word has 2^101+1 characters, and
its payload is never computed. The coding audit passed; it is not a proof of
the coding lemmas in PA or Lean.

From the project directory:

```bash
python3 packed_summary_tables.py summary-arithmetic-demo.json
lake build CodedScan
```

The first command reproduces the completed executable audit. The second is
an outstanding formal check. Lean still fails at startup in the server
environment, so no successful run of the second command is reported.

---

# Uniform arithmetic scan theorem — independent audit

Status: mathematical proof with explicit PA induction obligations; not an emitted Enderton derivation and not a Lean-checked theorem. No claim about the unspecified intended Bew follows yet.

Fix natural b >= 2 and distinct digits op, cl < b. Write x dotminus y for truncated subtraction. A summary is a natural pair (R,O), counting unmatched closing and opening delimiters. Define

J((r,o),(q,p)) = (r + (q dotminus o), (o dotminus q) + p).

Equivalently, witnesses c,u,v satisfy c+u=o, c+v=q, and u=0 or v=0, with output (r+v,u+p). PA proves existence by the decidable comparison o<=q and uniqueness by the same comparison. There is no unproved choice or minimum oracle in this presentation.

Define T_d(r,o) by (r,o+1) for d=op; by (r+1,0) for d=cl and o=0; by (r,o-1) for d=cl and o>0; otherwise (r,o). Distinctness of op,cl matters.

## The essential elementary identity

For every s,t,d, PA proves

T_d(J(s,t)) = J(s,T_d(t)).

Proof: opening and neutral cases follow by addition. For closing, put s=(r,o), t=(q,p). If p>0 then J's opening count is positive and both sides subtract one from its final p contribution. If p=0 and o>q, both sides have closing count r and opening count o-q-1; use q+1<=o. If p=0 and o<=q, both sides have closing count r+(q-o)+1 and opening count zero. These are exhaustive PA-decidable cases. The ordinary identities of truncated subtraction in these cases follow directly from its defining graph and addition cancellation.

Also J(s,(0,0))=s. This identity and the step identity suffice for concatenation; one need not first prove full associativity.

## A genuinely primitive-recursive definition

The recurrence Scan(L+1,c)=T_(c mod b)(Scan(L,c div b)) is not literally an ordinary primitive recursion because its parameter changes. To avoid hiding a definability step, define H(L,c,0)=(0,0), and

H(L,c,i+1)=T_( (c div b^(L dotminus (i+1))) mod b )(H(L,c,i)).

Set Scan(L,c)=H(L,c,L). Pair coding, exponentiation, division with remainder for b>0, truncated subtraction, and this fold are primitive recursive. PA proves their totality and uniqueness by the corresponding induction arguments; then finitely many definitional function symbols may be introduced conservatively. Their presence does NOT license arbitrary true assertions about these functions.

Prove the desired Scan recurrence in PA by induction i<=L: the first i states in H(L+1,c,.) equal those in H(L,c div b,.), using (c div b) div b^j = c div b^(j+1). The final digit is c mod b. The base Scan(0,c)=(0,0) is direct. All uses of subtraction have explicit i<=L guards.

## Concatenation theorem

PA proves uniformly, for Ly>=0 and cy<b^Ly,

Scan(Lx+Ly,cx*b^Ly+cy) = J(Scan(Lx,cx),Scan(Ly,cy)).

No bound on cx is needed for this identity, although cx<b^Lx is needed to call (Lx,cx) a valid exact-length word code. Induct on Ly, strengthening the induction hypothesis to all cy. At Ly=0, cy<1 implies cy=0 and use the right identity for J. At Ly=k+1, put q=cy div b and d=cy mod b. Prove q<b^k, and

(cx*b^(k+1)+cy) div b = cx*b^k+q,
(cx*b^(k+1)+cy) mod b = d.

These follow from cy=b*q+d and d<b and uniqueness of division with remainder. Apply the Scan recurrence, then the induction hypothesis to q, then the step identity, then the Scan recurrence on cy. This is a finite PA proof schema yielding one fixed universally quantified PA theorem after all definitions are eliminated. It does not assert that PA proves every true primitive-recursive identity.

The pair (L,c) retains leading zeros. Payload c alone is not an injective word code, so dropping L or silently switching to a sentinel convention invalidates the decoder bridge.

## Grammar theorem and the actual remaining bridge

Specify a concrete primitive-recursive encoding of finite lists, tagged atoms, topologically ordered productions, and references. Define a valid grammar by backward references and valid literal digits. Define its evaluation table by processing productions in order and folding concatenation on (L,c). Define its summary table by the same folds using J and literal summaries. Ordinary induction on production index, with an inner induction on RHS length and the concatenation theorem above, proves that every table entry's summary equals Scan of its evaluated (L,c). This statement is uniformly provable in PA: all quantifiers over table indices and fold positions must be present, not merely separate standard-instance assertions. Sequence coding and finite-recursion existence need explicit definitions in a final derivation.

This establishes existence of a fixed PA theorem for the chosen auxiliary encoding. Consequently its finite derivation has a fixed, input-independent symbol cost. It does not provide that cost, an Enderton proof file, or a kernel certificate. Nor does it identify this auxiliary encoding with the source specification's fixed formula numbering or Delta_1 Bew. The uploaded specification describes base-alphabet proof-file codes but leaves digit enumeration, leading-zero/length convention, detailed record decoder and exact arithmetical Bew formula unprinted. A PA-provable equivalence to that decoder must be supplied; extensional agreement on standard inputs alone is inadequate.

There is also a size trap: an expanded payload c can have exponentially many binary digits in the compressed grammar mass. Do not instantiate the uniform theorem with a literal binary numeral for c and declare the result polynomial. Keep evaluated codes existential or represented by compressed arithmetic expressions, and prove the required linkage to the intended coded-string/formula predicates. A polynomial summary table by itself is not a polynomial proof of this linkage. This theorem handles one syntactic service, not tautology recognition, arbitrary axiom verification, or the full PA-bin internalization compiler.

## Stronger existential formulation (avoids literal expanded codes)

Let g encode a finite backward-reference grammar with m productions, and t encode a table of m natural-pair summaries. Let LocalJoinTable(g,t) require: correct table length; each production's literal/ref atom summaries are obtained from the specified digit map or earlier t entries; and the RHS fold ends at t_i. This may quantify finite per-RHS intermediate tables, or include them explicitly in t; choose one convention before serialization. For empty RHS the value is (0,0).

Let Expanded(g,e) require that e is a table of m length/payload pairs, computed from literals (1,d), earlier e entries, and concatenation (L,c)*(K,d)=(L+K,c*b^K+d), starting with (0,0). Let NF((L,c),(R,O)) abbreviate c<b^L and Scan(L,c)=(R,O). Then the fixed PA theorem is

forall g,t, (ValidGrammar(g) and LocalJoinTable(g,t)) ->
  exists e, (Expanded(g,e) and forall i<m, NF(e_i,t_i)).

One proves in PA existence and uniqueness of the expansion table for every valid g. A primitive-recursive evaluator processes each production and folds over its finite RHS using earlier entries, so it is total in PA. Its potentially enormous output value is not a problem for induction or totality. To avoid appealing to a semantic evaluator as an unexplained oracle, use coded bounded sequences, prove the sequence-extension lemma, and induct on the number of processed productions; the inner RHS induction constructs the next (L,c) entry. Backward references ensure that all lookups are already available. The digit bounds and concatenation bound

c<b^L and d<b^K -> c*b^K+d < b^(L+K)

preserve valid exact-length codes at each fold. Applying the concatenation theorem at each inner step and the induction hypothesis for referenced entries proves NF. This gives the displayed theorem after existentially quantifying the constructed e.

The proof uses no numeral naming an expanded payload. Instantiating this fixed theorem with compact g,t therefore avoids that *particular* exponential numeral problem. However, g and t must themselves be coded with polynomial-size input numerals, their LocalJoinTable sentence must have a polynomial PA proof, and the existential result must subsequently be consumed without extracting a gigantic literal witness. These are distinct obligations. In particular, separate local arithmetic derivations do not automatically constitute a proof of one coded LocalJoinTable(g,t) formula: pack their indices and sequence values, prove lookup equations and record tags, then combine them by the chosen bounded-quantifier/finite-table lemma. The theorem leaves e existential; neither witness extraction nor a bound on an explicit e numeral is claimed.

---

# Local arithmetic derivations for compressed summaries

26 September 2026. Neither part of MAIS-O11 is resolved. This milestone
constructs and replays actual derivations in a small PA-admissible calculus.
It does not yet produce the specified Enderton proof-file format, a fixed-Bew
certificate, or a new Lean kernel certificate.

## 1. What changed

The previous local equality certificates derived only reflexive equalities
after expanding definitions. Correct computations of lengths and balances
were established externally. Reflexivity alone could not certify a numerical
calculation such as the addition of two different binary numerals.

The new code explicitly derives binary addition equations from the two
recursive addition axioms, equality rules, and induction. It then derives
closed existential formulas certifying the numerical operation used to
combine fragment summaries. There is no rule accepting an equation because
Python evaluates both sides to the same integer.

The remaining major gap is different: local numerical derivations must be
connected, inside PA and for the intended coding, to decoded string semantics
and eventually the fixed Bew predicate. The externally checked assembly of
local proofs is not yet that internal theorem.

## 2. Eliminate signed arithmetic from the local certificate

Represent a word by (L,R,O): length, unmatched closing parentheses, and
unmatched opening parentheses. Ignoring neutral characters, its reduced
parenthesis word is a block of R closes followed by O opens. If the earlier
signed summary is (d,m), the relation is

    d = O - R,      m = -R.

For input summaries x=(Lx,Rx,Ox), y=(Ly,Ry,Oy), define the arithmetic formula

    Join(x,y,(L,R,O)) := exists c,u,v,
        c+u=Ox AND c+v=Ry AND (u=0 OR v=0)
        AND Lx+Ly=L AND Rx+v=R AND u+Oy=O.

This is a fixed first-order formula over natural-number addition and equality,
with conjunction, disjunction, and existential quantifiers. These connectives
can be expanded in the usual negation/implication/universal language. No
minimum, order, subtraction, or signed-integer primitive occurs in Join.

**Uniqueness and correctness.** The first three conditions force
c=min(Ox,Ry), u=Ox-c, v=Ry-c. If u=0, then c=Ox and Ry=Ox+v. If v=0,
then c=Ry and Ox=Ry+u. These cases determine the unique triple, agreeing when
Ox=Ry. Conversely these values satisfy all three conditions. Concatenation
cancels exactly c opens from the left word against closes from the right.
The remaining counts are therefore R=Rx+v and O=u+Oy, exactly as asserted.
The length equation is ordinary concatenation length. This also reproduces
the signed-summary concatenation law.

## 3. The arithmetic object calculus and its trust boundary

`pa_eq_kernel.py` has native terms 0, S(t), t+u, and variables. Its only
arithmetic axioms are

    t+0=t,          t+S(u)=S(t+u).

The inference rules are reflexivity, symmetry, transitivity, successor and
addition congruence, simultaneous substitution into an assumption-free
derivation, and equational induction. An induction node contains a designated
induction hypothesis plus explicit base and step proofs. The checker verifies
both instances, excludes the induction hypothesis from the base, discharges
that hypothesis, and checks that the induction variable is absent from every
remaining assumption. Assumptions cannot be imported as closed theorems.

These are PA-admissible rules. Equality rules follow from first-order equality;
substitution follows by generalization and instantiation; induction follows
by discharging the step hypothesis, generalizing the induction variable, and
applying the PA induction schema. The eigenvariable restriction is essential
to that argument. The finitely many induction uses occur in a fixed prelude,
not once per unary unit of a numeral.

The prelude explicitly derives zero-left, successor-left, associativity,
commutativity, and the shuffle equation

    (a+b)+(c+d) = (a+c)+(b+d).

Those five named lemmas are proof objects, not additional trusted axioms.
The prelude has 70 proof records and 61 shared term nodes.

`pa_summary_certificate.py` adds only conjunction introduction, left/right
disjunction introduction, and existential introduction. These too are
PA-admissible rules. Their premise formulas and witness substitutions are
checked syntactically, including capture conditions and formula well-formedness.
The final Join assertions are closed sentences. In the equational API,
`is_closed` means no undischarged assumptions; template theorems may still
have free variables, interpreted by universal generalization.

This Python checker is an experimental trusted implementation. Its correctness
has not been proved in Lean. It deliberately refuses optimized Python mode,
which disables the assertions used by its equational validation. A valid
object-calculus derivation is not itself a file accepted by the project's
specified Enderton checker. An exact serializer and its verification remain
to be supplied; the PA-admissibility argument does not hide that missing code.

## 4. Binary addition really is derived

Here binary constructors abbreviate native terms:

    D(t) := t+t,       E(t) := S(t+t).

N(0)=0, N(2h)=D(N(h)) for h>0, and N(2h+1)=E(N(h)). All repeated subterms
are shared. This is an explicit efficient numeral representation in the
native PA language. It must not silently be identified with a different
literal D/E syntax or coding used by the target checker; the corresponding
definitional translation still needs to be implemented where required.

`add_proof(a,b)` derives N(a)+N(b)=N(a+b). Zero cases use the derived
zero-left theorem or the right-zero axiom. For nonzero operands it recursively
proves the addition of the half-values. Shuffle converts

    (N(h)+N(h))+(N(j)+N(j))
      = (N(h)+N(j))+(N(h)+N(j)),

and congruence applies the recursive proof twice. Successor-left and the
right-successor axiom handle odd operands. For two odd operands, a separately
constructed successor proof handles the carry. The successor proof itself
recurses on the half-value of an odd input; it uses no recursive call back to
the addition compiler. Thus the recursion is well founded on bit length.

For B-bit inputs, successor uses O(B) inference records. Addition satisfies
T(B)<=T(B-1)+O(B), hence O(B^2) inference records. A deliberately conservative
bound allowing fresh numeral suffix construction is O(B^3) term nodes. These
are bounds for the explicit shared representation, not an established exact
Enderton character-count theorem.

A local Join proof uses five addition derivations, a reflexive zero equality
for the appropriate disjunct, conjunction introduction, and three existential
introductions with c,u,v as witnesses. Its proof record count is polynomial
in the bit length of its inputs and output. The generator uses numerical
arithmetic to choose witnesses; the verifier checks the printed derivation
rather than trusting those calculations.

## 5. Grammar tables and proof size

For every RHS atom, the compiler combines the current accumulator with the
character summary or an earlier definition's table entry. Empty RHSs have
the empty summary, and empty references require no special arithmetic case.
There are at most M such joins when M is definitions plus RHS atom occurrences.
Expanded lengths are below 2^M, so all summary and cancellation coordinates
have O(M) bits. The local derivations therefore have O(M^3) arithmetic
inference records and, using the conservative bound above, O(M^4) term nodes.
Writing DAG references with binary identifiers adds a logarithmic factor.
These polynomial bounds concern local arithmetic proof data; they do not
bound proofs of full checker acceptance or the Löb transformation.

Every proof rule used after the fixed prelude is PA-admissible by a fixed
logical template, with substitutions of explicitly shared terms/formulas.
This supports a polynomial translation to ordinary PA proofs with charged
acyclic term abbreviations. However, the exact specified PA-bin serializer,
native numeral conversion where needed, and explicit constants are not yet
implemented or kernel-verified. In particular the current JSON file is not
being passed off as that serializer's output.

`pa_summary_replay.py` saves terms, arithmetic derivations, logical derivations,
the grammar, the summary table, and the local proof roots. A fresh process
validates every proof, reconstructs each requested Join formula from the
actual operands/results, checks its root against that formula, and checks the
accumulator and earlier-reference links. It does not trust proof labels.
The table assembly is currently checked externally. No expanded word is built.

## 6. Concrete evidence and adversarial audit

The saved `summary-arithmetic-demo.json` covers a 204-definition grammar with
407 RHS atom occurrences, including empty definitions and empty references.
It generates the word consisting of 2^100 opens, one neutral character, and
2^100 closes. The final summary is (2^101+1,0,0).

Fresh replay checks 407 closed Join roots using 912 arithmetic proof records,
494 term nodes, and 6,105 logical introduction records. The serialized proof
object is 1,028,707 bytes. It does not contain the expanded word. Sharing makes
this regular example much smaller than the worst-case polynomial bounds.

Additional checks cover all 1,024 additions of operands below 32, 100 successor
calculations, and a 256-bit carry calculation (4,937 proof records, 1,858 term
nodes), plus 84 explicit Join cases. These are implementation checks, not
universal correctness proofs.

The independent audit found two actual malformed-certificate defects: unchecked
logical syntax, and an invalid zero index combined with terms created during
verification. Both were repaired. Verification now checks logical syntax and
witness indices, requires valid term endpoints, and forbids growth of the
serialized term table during arithmetic checking. Regression checks reject
these malformed inputs, undischarged hypotheses, invalid induction scopes,
forward proof references, corrupted equations, altered numerical results,
wrong roots, and cyclic grammar references. A trial 'corrupt equality' test
initially changed zero to zero; it was corrected to perform a genuine mutation.
No false arithmetic theorem was obtained in the reviewed attacks.

## 7. The remaining uniform theorem, stated without circular definitions

The required PA statement has the following shape, for the actual chosen
string coding:

    Concat(x,y,z) AND NF(x,Lx,Rx,Ox) AND NF(y,Ly,Ry,Oy)
      AND Join((Lx,Rx,Ox),(Ly,Ry,Oy),(L,R,O))
        -> NF(z,L,R,O).

NF must mean the scan/reduction of the decoded word, or be independently
proved equivalent to that meaning. Defining NF only as 'a table satisfying
Join exists' would omit the connection we need. Character lemmas and a uniform
induction on the grammar must then connect the certified table to Expansion.
These displayed predicates are a specification of the remaining obligation;
they are not yet formulas with a completed PA derivation in this project.

Expanded word codes can require exponentially many binary digits. A promising
way to avoid writing those numerals is to prove expansion-table existence in
PA and quantify its codes symbolically. This needs a genuine totality and
correctness theorem for that coding. Local Join proofs do not supply it.

Even completing the balance bridge would not establish full term/formula
recognition, substitution correctness, arbitrary-tautology axiom handling,
or polynomial internalization for the fixed Bew. Those remain separate
obligations for MAIS-O11.

## 8. Reproduce locally

From the extracted project directory:

```bash
python3 pa_eq_kernel.py
python3 pa_summary_certificate.py
python3 pa_summary_replay.py --verify summary-arithmetic-demo.json
```

To regenerate the same demonstration:

```bash
python3 pa_summary_replay.py --write summary-arithmetic-demo.json
```

No third-party Python package is required. Do not use Python's `-O` option.
The earlier outstanding Lean check remains:

```bash
lake build FragmentPrefix FragmentRange
```

The server's Lean executable still fails before reading source. No new successful
Lean verification is claimed for this milestone.

---

# Compressed matching delimiters: construction, audit, and PA obligation

26 September 2026. MAIS-O11 remains unresolved. The mathematical arguments below
are separate from their Lean status: `FragmentPrefix.lean` and
`FragmentRange.lean` still await a successful kernel run. The Python audit is
executable evidence, not a formal certificate. No novelty claim is made for
compressed-string navigation as an algorithmic result.

## 1. A precise failure in the previous shortcut

Let S(w)=(d(w),m(w)), where d is net opening-minus-closing count and m is the
minimum over all prefix counts, including the empty prefix. Then

    S(xy) = (d(x)+d(y), min(m(x), d(x)+m(y))).

Although d(y) can be recovered by subtracting d(x) from d(xy), m(y) cannot in
general be recovered from these two summaries. Both `()(` and `(()` have
summary (1,0), and both first-character prefixes have summary (1,0). Their
remaining suffixes `)(` and `()` have different summaries: (0,-1) and (0,0).
Thus no function of just S(x) and S(xy) computes S(y) for every x,y. This is
an information-loss obstruction, not an implementation inconvenience.

`FragmentRange` directly traverses the compressed representation to obtain
the missing information. Its intended exact Lean theorem is

    rangeSummary op cl g i p q =
      wordSummary op cl (((g.words i).drop p).take q).

The source contains proofs with no placeholders, but elaboration and kernel
verification are pending. The companion `RANGE-NOTE.md` audits the recurrence.

## 2. Matching theorem and a short witness check

Fix two distinct characters `(` and `)`, with weights +1 and -1; all other
characters have weight zero. Let w have length L, and suppose w[a]='('. Define
the matching close locally as the first position j>a at which the running
height, started at 1 just after position a, returns to zero. No assumption
that the entire word is well formed is necessary for this local definition.

**Theorem.** For 0<=a<j<L, j is the matching close for a if and only if

1. w[a]='(';
2. w[j]=')';
3. S(w[a+1:j])=(0,0), with the right endpoint excluded.

**Proof.** If these three conditions hold, the height remains at least 1
throughout the interior and equals 1 at its end. The final closing character
then makes the height zero for the first time. Conversely, before a first
return to zero, integer heights are at least 1. Each character changes height
by at most one, so the returning character must have weight -1, the preceding
height must be 1, and the interior must have net weight zero and no negative
prefix. Its minimum is exactly zero because the empty prefix is included. QED.

This gives a **three-query witness check**: query the two endpoint characters
and the interior. In particular, a later PA acceptance proof need not contain
or verify the binary search used to discover j. It can check the proposed
position using this equivalence. The theorem concerns a single delimiter pair,
not term/formula sorting, variable binding, or the validity of a proof line.

## 3. Finding the witness without expansion

For 0<=t<=L-a-1 put

    C(t) := minimum-prefix-weight(w[a+1:a+1+t]) <= -1.

C is monotone: extending a word only adds candidate prefixes to its minimum.
C(0) is false. If C(L-a-1) is false there is no matching close. Otherwise
binary search finds the least t with C(t); the answer is j=a+t.

To justify the last assertion, minimality implies every earlier prefix has
weight at least zero. At t the weight crosses below zero, and a one-character
step can decrease it by at most one, so this prefix has weight exactly -1.
Its last character is a close, and the preceding interior has summary (0,0).
The theorem above applies. Conversely, the first matching close gives this
least t. The binary search maintains a false lower endpoint and a true upper
endpoint and halves their distance each time, so it terminates.

## 4. Explicit size and cost scope

Let M be the number of definitions plus all atom occurrences in an acyclic
fragment grammar. Each reference points to an earlier definition. With a
cached length/summary table and random access to definitions, an interval
query skips atoms before its start, uses cached summaries for whole selected
atoms, and descends only into partially selected atoms.

In the expanded derivation, a partially selected occurrence must contain
one of the two boundaries strictly inside it. At each depth there are at most
two such occurrences, lying on the two boundary paths. Along either path,
definition indices strictly decrease. Hence any definition is scanned at most
twice. Each scan examines at most its written RHS length: the query visits at
most 2M definitions-plus-atoms. Empty expansions cannot be partial and are
skipped; repeated references do not invalidate the two-path argument. An
out-of-bounds request is equivalent to its intersection with [0,L), and follows
the same bound. The root can be treated as the initial scan.

The existing expanded-length bound gives L<2^M, so in-range positions, lengths,
net weights, and minima have O(M) bits. Under an ordinary array representation
with O(M)-bit addition, subtraction, comparison and minimum, preprocessing and
one interval query take O(M^2) bit operations. Matching uses O(M) queries, for
O(M^3) bit operations and O(M^2) bits of stored numeric data. These are
mathematical bounds for the specified implementation model, **not certified
Lean runtime bounds**. The persistent-vector implementation in the Lean source
requires separate accounting for copying. Arbitrarily oversized input
coordinates also have their own bit-length cost; matching in-range positions
does not introduce that issue.

The three-query witness check uses O(M) arithmetic/branch steps, each on O(M)
bits, in this model. Recording those steps and their referenced positions
would give O(M^2) bits of numerical trace. We have not yet supplied a complete
serialized trace language, trace checker, or PA proof printer for that trace.

## 5. What would actually bridge this result to PA?

The useful next internal theorem is not a PA proof of the search algorithm's
optimality. It is a fixed PA theorem of the following schematic form:

    ValidGrammar(g) and NavigationCertificate(g,i,a,j,c)
      imply forall y, Expansion(g,i,y) -> MatchingClose(y,a,j).

All predicates here must be explicitly defined arithmetic formulas for the
chosen coding, and the implication must be derived in the actual PA-bin
calculus. This displayed schema is an obligation, **not a theorem already
proved in PA**. One then needs polynomial-size PA proofs of certificate
acceptance for the produced c, and a proved connection between Expansion and
the syntax relations used by the fixed Bew predicate. For a concrete formula
code, that connection also needs the appropriate quotation/equality proofs.
Semantic equality of two external checkers does not supply those proofs.

This separates three targets that had been too easy to conflate:

- computing a correct delimiter position externally;
- verifying its finite numerical witness externally;
- producing a short PA proof about the fixed arithmetized syntax predicate.

Only the first target and the mathematical specification of the second are
established in this note. Further, even polynomial local navigation does not
make a full parser polynomial if it calls navigation once per expanded node.
The exponential-depth example still rules out that traversal strategy.

## 6. Evidence and literature boundary

`check_fragment_navigation.py` is an independent tuple/array model. Its recorded
run compared 99,824 interval answers, 27,108 matching answers, and 47,020
candidate-match checks with explicit-string reference computations. It includes
every word of length at most six over `(`, `)`, and a neutral character, empty
definitions, and 500 deterministic randomized grammars. On a mass-608 grammar
with 2^101+1 expanded characters, four matches were found without expansion,
using 102 or 103 queries each. Finite tests cannot prove the universal claims.

Ganardi, Hucke, Lohrey and Noeth, *Tree Compression Using String Grammars*,
arXiv:1504.05535v2, provide compressed navigation results. Their paper also
warns against extending such local algorithms indiscriminately: general
context-free compressed membership can be PSPACE-complete, and a fixed tree
automaton can have PSPACE-complete evaluation on SLP-compressed preorder
traversals. These results do not show that PA syntax checking is PSPACE-hard;
the input representation and particular language matter.

Source: https://arxiv.org/pdf/1504.05535 (introduction and Section 3).

## 7. Verification status and local commands

The server's stock Lean 4.19 executable cannot discover its application path:
its numeric `/proc/<pid>/exe` lookup is denied before source loading. This
diagnoses the environment failure; it says nothing about whether the new proof
scripts elaborate. The runtime was not modified to bypass the restriction.

On the working local installation, from the project directory:

```bash
lake build FragmentPrefix FragmentRange
python3 check_fragment_navigation.py
```

The first command is the outstanding formal check. The second repeats the
independent executable audit. Neither command, even if successful, certifies
a solution of either part of MAIS-O11 or polynomial PA internalization.

---

# MAIS-O11: compact parsing and shared-graph equality

## The verified result

This checkpoint extends the previous compact-parser equivalence result in two
directions. First, `SharedConverse.lean` proves that the compact definition
reader and the original expanding reader accept exactly the same definition
preludes on every input string. Second, `GraphCompiler.lean` compiles any
accepted compact definition list to a shared DAG whose roots have exactly the
same expanded syntax as the definitions.

The compiler theorem `compileDefs_refines` states that graph expansion at a
compiled definition root is the same arithmetic syntax tree as expansion of
the compact definition. `compileTerm_root` gives the corresponding result for
an arbitrary closed compact term, while `compileTerm_preserves` shows that
previous graph roots retain their meanings when a term is appended.
`compiledDefs_table_iff` connects the graph's equality table to exact equality
of expanded syntax trees. This is syntactic equality, not equality of the
natural numbers denoted by terms.

The graph has one node per non-reference constructor: references reuse an
existing root. The bounds `compileDefs_size_le_wire` and
`compiledPrelude_size_le_input` show that its number of nodes is at most the
written syntax size (and, for a parsed prelude, at most its input character
count). `DagEquality.lean` bounds equality-table writes by the cube of the
number of graph nodes. These are bounds on this graph representation and table
construction; they are not an end-to-end complexity result for full PA-bin
proof checking.

`SharedOracle.lean` uses this graph for closed-term comparison, and
`OpenGraph.lean` provides the variable-labelled extension used at positive
binder depths. The theorems `sharedClosedEqual_correct` and
`sharedOpenEqual_correct` prove exact agreement with expanded syntax. In
`SharedOracleDemo.lean`, the graph for the 61 written doubling definitions has
61 nodes. It compares `u_60` with `u_59 + u_59` using the compiled roots and a
graph equality table. The expanded tree has `2^61 - 1` syntax nodes. Lean's
executable demo reports that the roots compare equal without materializing
that tree.

`OpenGraph.lean` removes the earlier binder-depth fallback. Its `OpenNode`
adds de Bruijn-variable leaves to the same backward-reference DAG structure;
`OpenGraph.table_iff` proves that the resulting table decides exact syntax
equality of expanded open terms. `compileOpenTerm_correct` certifies roots and
preservation of prior roots, and `compileOpenTerm_size` gives the exact node
count: variables and explicit constructors allocate one node, while compact
abbreviation references allocate none. `openTermNodes_le_weight` bounds that
count by the compact written term weight. `sharedOpenEqual_correct` proves
that two compact terms, at any binder depth, compare equal in the graph table
exactly when their expanded open syntax trees are identical.

The demo now also compares `x + u_60` with `x + (u_59 + u_59)` at binder depth
1. This exercises the case that defeated a simple structural comparator: the
large closed abbreviation is compared with its differently written closed
definition beneath an open constructor. The theorem `compiledTermEqual_correct`
connects this variable-labelled comparator to the exact expansion semantics.

`SharedOracle.lean` has graph shortcuts for contraposition,
conjunction-introduction, and instances of `∀x, x=x` whose two compact
conclusion terms expand to identical syntax. `compiledAxiomCheck_eq_reference`
proves that these shortcuts preserve the old four-family axiom relation
exactly. Successful shortcuts bypass expansion. Other universal-instantiation
cases and failed shortcuts still use the expanding reference checker. A demo
record instantiates reflexivity with `u_60` on one side and its explicit
definition `u_59+u_59` on the other; the graph accepts it without constructing
the large expansion.

`GraphFileChecker.lean` joins compact definition parsing to graph-based MP
comparison and those successful axiom shortcuts. The theorem
`checkWholeSharedGraph_eq_old_accept` proves exact agreement with the earlier
expanding checker on every input within the implemented file grammar;
`checkWholeSharedGraph_sound` transfers accepted records to the existing
derivability theorem. The checker returns a Boolean; it does not produce a PA
proof of its own correctness or a proof-length bound.

## What the compact whole-file demo does and does not exercise

`SharedConverseDemo.lean` parses a file containing the 61 definitions and a
reflexivity axiom record without expanding its final abbreviation. The
reflexivity record itself does not mention the large abbreviation. The
separate graph-comparison demo is what compares the 61st abbreviation with
its explicit written definition.

Modus-ponens comparisons now use graph equality at every binder depth. Three
axiom shapes have successful graph shortcuts. The 61-definition whole-file
example still uses a small reflexivity axiom; the separate record demos
exercise all three shortcuts with huge abbreviations. The checker can still
expand exponentially large abbreviations for other universal instantiations
and unsuccessful shortcut candidates.
Thus successful cases are more compact, but the restricted whole-file
checker is not compact on every input.

`InstantiationGraph.lean` now solves universal-instantiation recognition for
the restricted closed-term abbreviation grammar. Its search checks every
internal graph node, every written target subterm, and zero for a vacuous
quantified variable. `GraphSubterms.lean` proves that a term buried inside an
abbreviation occurs at a graph node. The binder-aware substitution theorem
handles arbitrary nested quantifiers, and `compiledInstCandidates_iff`
proves search completeness. `compiledInstCandidate_count_bound` bounds the
number of candidate checks by graph nodes plus written target weight plus one.

`GraphFileCheckerInst.lean` integrates this search into the restricted
whole-file checker. Its `checkWholeGraphWithInst_eq_old_accept` theorem proves
agreement with the original expanding checker for every file in that grammar.
A certified example accepts the witness `E 0` hidden inside `u_0 := (E 0)+0`.
Remaining axiom families retain the old expanding fallback; neither this
theorem nor the candidate-count bound is a polynomial PA internalization.

The full agenda permits arbitrary *string fragments* in definitions, not just
complete closed terms. `GraphDepthBarrier.lean` proves a unary spine of length
`m` needs at least `m+1` ordinary constructor-graph nodes. The separate
`SHARED-COMPILER-AUDIT.md` gives polynomial-length fragment-macro files with
an expanded unary spine of length `2^m`. Thus the ordinary term-DAG compiler
cannot polynomially normalize the full fragment grammar. This is a limitation
of that representation, not an overhead lower bound for PA.

`FragmentBalance.lean` certifies the next representation: a pair of integers
tracks net and minimum-prefix parenthesis balance under concatenation.
`FragmentGraph.compute_correct` establishes the generic string-DAG case.
More importantly, `grammarSummary_correct` computes these summaries over the
project's actual arbitrary-fragment `StringQuotation.Grammar` and proves exact
agreement with expanded strings; `grammarBalanced_iff` checks parentheses
without expansion. This covers one syntactic property of the raw fragment
grammar, not complete first-order parsing or the PA proof checker. A bound
on the bit complexity of this implementation remains mathematical rather
than formally verified. `SpecTransfer.lean` proves an abstract
conditional link between superlinear overhead growth and arbitrarily strong
Part 1 witnesses; `SPEC-SECOND-AUDIT.md` supplies the finite-alphabet and
Löb assumptions mathematically, not as a PA-bin Lean implementation.

## Materialized summaries and the next prefix certificate

The functional environment `grammarSummary` is a semantic specification;
references can recompute earlier results when it is evaluated directly.
`cachedGrammarSummary` now constructs a materialized vector, storing one
summary per definition. `cachedGrammarSummary_correct` proves the same exact
expanded-string specification and was checked successfully with Lean 4.19.0.

`GrammarLengthBound.lean` proves that each expanded definition has length
less than `2^g.mass`. Each signed balance component needs at most `g.mass+1`
bits; all cached numeric balance payloads together need at most
`2*g.mass*(g.mass+1)` bits. This excludes vector metadata and is a storage
bound, not a compiled-machine runtime theorem. The mass-to-file-length step
is an explicit assumption that every atom and definition costs a character.

`FragmentFamily.lean` now supplies the raw-fragment construction behind the
DAG obstruction: its grammar has mass `4+6*m`, and its expanded final word
is the stipulated unary rendering of depth `2^m`. Combined with
`GraphDepthBarrier.lean`, every ordinary graph for that unary term has at
least `2^m+1` nodes. These theorems were checked successfully. This is an
abstract alphabet and rendering, not a full PA-bin parser or axiom certificate.

`FragmentPrefix.lean` contains the next implementation: a cached table of
expanded lengths and balance summaries, then a query for the summary of
`(g.words i).take q`. The source includes `prefixSummary_correct` and a bound
of `g.mass` on visited definitions and written atoms. Each scan follows only
one partially consumed reference. It handles empty references and oversized
requests. The instrumented bound excludes table preparation, vector copying,
and integer bit costs. External cost analysis must include the bit length of
the supplied `q` as well as grammar mass.

**Verification status:** a fresh kernel run of `FragmentPrefix.lean` is pending.
The restored toolchain currently exits before elaboration with
`failed to locate application` (Lake reports that it cannot detect its
installation configuration). An independent source audit found no semantic
counterexample. This is not a successful Lean transcript for that new module.
The earlier successful checks of the cached summary, length bounds, and
fragment-family modules remain separately recorded.

The new `PA-BIN-THIRD-AUDIT.md` gives a short file with exponentially large
intermediate tautology lines and a fixed small conclusion. It defeats a
compiler that expands every intermediate formula, but its redundant lines
give no lower bound on shortest proofs or on F. Compact intermediate-code
certificates remain necessary for the proposed general internalization route.

`QUOTATION-HOMOMORPHISM-AUDIT.md` supplies a conditional mathematical way
to write exact canonical numeral syntax compactly: when the coding alphabet
has size `2^r`, fixed-width digit replacement, reversal, and leading-zero
trimming preserve linear grammar mass (for fixed r). This has not been
formalized in Lean, and the agenda does not fix a power-of-two alphabet or
the required formula-numbering convention. It therefore supplies a possible
component, not a theorem about the fixed Bew predicate. It also corrects a
potentially misleading output-size argument: a huge *expanded* numeral does
not by itself force a huge proof *file* when fragment abbreviations are allowed.

## Scope against the uploaded agenda

The agenda names PA in Enderton's Hilbert calculus, generalization records,
abbreviations for previously defined strings, and written-character proof
length. The current serialized checker supports only a restricted fragment:
four logical axiom families, axiom and modus-ponens records, closed-term
abbreviation definitions, and definitions placed before proof records. It
does not implement all logical and arithmetic PA axiom schemes, induction,
generalization records, open proof lines, arbitrary string abbreviations, or
the agenda's complete arithmetized proof predicate.

The separate [specification audit](SPEC-AUDIT.md) gives the detailed
comparison. One strategic issue it identifies is that literal Enderton axiom
recognition includes arbitrary propositional tautologies. This obstructs a
naive polynomial-time checker: exact polynomial-time recognition of all
tautologies would imply `P = coNP`. That observation does not rule out short
PA proofs or a polynomial-size compiler producing internal proofs conditional
on valid input; those are distinct claims and require a separate construction.

## Verification and limits

The earlier modules have recorded Lean 4.19.0 checks. The prefix and range
modules added subsequently remain pending verification. From this directory:

```bash
lake build
lake build GraphFileCheckerInst FragmentBalance GraphDepthBarrier SpecTransfer
lake build GrammarLengthBound FragmentFamily
# New modules: local verification requested; current server run blocked.
lake build FragmentPrefix FragmentRange
lake env lean SharedConverseDemo.lean
lake env lean SharedOracleDemo.lean
```

The earlier demos printed `PASS` for compact parsing, graph size, closed and
binder-depth graph equality, three huge-abbreviation axiom records, and
restricted whole-file acceptance. The `#print axioms` audit of the new
principal theorems, including the quantified example and the axiom record
examples, reports `[propext, Quot.sound]`; the
parser/compiler/checker modules introduce no custom axioms, `sorry`, `admit`,
or `native_decide`. The previously checked main theorems use standard logical dependencies
`[propext, Quot.sound]` (with `Classical.choice` for one abstract balance
predicate lemma).

The Lean graph checkpoint itself establishes neither a Part 1 proof-length
witness nor a negative result. It also does not establish MAIS-O11 Part 2's
PA-bin overhead bound. The full audit-compatible fragment grammar and
PA-internal correctness/length construction remain. The
agenda's arbitrary-tautology axiom family must remain explicit; the two
shortcut shapes do not implement or recognize arbitrary tautologies, and
replacing the family with a fixed Frege basis would change the specified
system.

## 26 September update: compressed interval navigation

The new `FragmentRange.lean` supplies source proofs for direct interval summaries;
like `FragmentPrefix.lean`, it is still awaiting a successful kernel run.
`NAVIGATION-MILESTONE.md` gives a mathematical matching-delimiter construction,
a three-query witness check, a two-boundary traversal bound, and the exact
remaining PA proof obligation. `check_fragment_navigation.py` independently
audits these claims on small explicit words and a word of length 2^101+1.
The tests passed; they are not a Lean or PA certificate.

The old shortcut of subtracting prefix minima is impossible: the summaries
lose information. Direct interval traversal repairs that local obstacle.
Polynomial PA internalization and both parts of MAIS-O11 remain unresolved.

## 26 September arithmetic update

`PA-ARITHMETIC-MILESTONE.md` records explicit binary-addition and existential
Join derivations in a PA-admissible object calculus, extending beyond the
earlier reflexivity-only local certificates. The saved JSON demonstration
contains 407 local proofs for a summary table of a word of length 2^101+1.
Fresh replay passed. The exact Enderton serializer, uniform PA decoded-string
correctness theorem, fixed-Bew connection, and Lean verification remain open.

## 26 September symbolic-expansion update

`SYMBOLIC-EXPANSION-MILESTONE.md` and `UNIFORM-SCAN-AUDIT.md` give the
mathematical uniform PA scan/grammar induction argument for an explicit
auxiliary coding. Keeping expanded words existential avoids printing their
huge payload numerals. A fixed-width finite-sequence coding gives polynomial
bit length for the named grammar and local-table codes; its executable
round-trip audit passed. `CodedScan.lean` supplies pending source for the
arithmetic decoder bridge. No new successful Lean or emitted PA verification
is claimed. Polynomial PA proofs of the packed-table antecedent and the exact
Bew bridge remain unresolved. The fixed PA-bin branch of MAIS-O11 Part 1 and
Part 2 also remain unresolved.

## 27 September chosen-system Part 1 audit

A separate, more recent construction uses a slow guarded verifier and a
countable family of nullary predicate sentences. Under the literal MAIS-O11(1)
permission to choose any efficient system, it appears to give a conditional
affirmative witness: short one-line reflection axioms, a large lower bound on
direct proofs by interpretation into a finite-diagonal PA family, and a
fixed-factor subsequence. Two independent audits found no decisive structural
contradiction. The original note used cutoff `n` and a linear translation
claim; the new `CHOSEN-SYSTEM-PART1-ROBUST-LEDGER.md` repairs that quantitative
dependency. It allows arbitrary string-fragment abbreviations, bounds full
expansion by `2^(O(m^2))`, and sets the diagonal cutoff to `2^n`, obtaining a
`sqrt(n)` direct-proof lower bound. The exact fixed-point checker,
derivability-condition proofs, and written-character ledger are still not
end-to-end formalized or Lean-certified.

It does not answer the fixed PA-bin version of Part 1 or Part 2. The separate
connective-tag Lean project certifies syntax invariants and conditional numeric
implications only; it does not certify the nullary-predicate construction.
See `CHOSEN-SYSTEM-PART1-AUDIT.md` in the refreshed project archive for the
construction, audit boundary, and active PA-bin target.

## 27 September robust chosen-system ledger

`CHOSEN-SYSTEM-PART1-ROBUST-LEDGER.md` repairs the original candidate's
linear-translation dependency. For an arbitrary `m`-character abbreviation
file, full expansion is bounded by `(m+1)^(m+3)`, hence by `2^(O(m^2))`.
The diagonal predicate now forbids `B` proofs of `D(n)` up to length `2^n`,
so translating any short `S` proof of `p_n` gives `ell_S(p_n) >
sqrt(n/C)-1`. This still dominates the `O(log n)` one-line reflection
proof and the `C_1(|p_n|+1)` toll, yielding `delta=1` on a tail under the
chosen-system branch. The fixed-point checker, derivability conditions, and
character-level translation remain to be formalized and checked in Lean.

This does not resolve the fixed `PA_bin` branch of Part 1 or Part 2. The new
ledger is a conditional mathematical construction, not a Lean certificate.

## 27 September compressed-tautology route for Part 2

The arbitrary Enderton tautology axiom family remains the main obstacle to a
short internalization proof for exact PA-bin. The new
`COMPRESSED-TAUTOLOGY-CIRCUIT-ROUTE.md` records a narrower target: compile the
propositional skeleton of a string-fragment compressed formula to a succinct
Boolean evaluation description and compressed gate-constraint formula, prove
correctness in PA with polynomial written cost, and use the gate constraints
in one promised-valid tautology axiom. This avoids expanding large formulas
and does not require a polynomial-time tautology checker.

The literature provides polynomial-time Boolean expression evaluation for
SLP-compressed tree traversals, despite an exponential gap between string and
tree-grammar compression. That supports the algorithmic direction, but does
not supply the uniform circuit description or the PA-bin proof. The fixed `Bew` bridge,
full propositional-skeleton parser, and polynomial proof-length bound remain
unproved; neither part of MAIS-O11 is resolved.

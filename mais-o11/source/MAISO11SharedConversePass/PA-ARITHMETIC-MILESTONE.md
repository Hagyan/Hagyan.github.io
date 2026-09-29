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

No new successful Lean verification is claimed for this milestone. The current
workspace has neither `lake` nor `lean` on `PATH`.

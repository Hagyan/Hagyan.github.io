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

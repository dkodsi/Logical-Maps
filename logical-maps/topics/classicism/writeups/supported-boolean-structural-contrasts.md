# Supported Boolean models: complete predecessor and current distinctness

Direct source: OpenAI Codex, prompted by Daniel Kodsi, *Observer separation with propositional completeness and divergent possibilities*, 25 October 2026, §§1–3 and 5a, unpaginated. The proofs below independently check and reorganize two constructions from that source for integration. The metatheory is ZFC and the framework fixed C. These are ordinary mathematical checks, not human or Lean certificates.

## 1. A finite-support lemma used by both models

Let $A=\operatorname{RO}(2^{\mathbb N})$, the complete atomless regular-open Boolean algebra of Cantor space, and let $G=\operatorname{Aut}(A)$. Every nonzero interval is isomorphic to $A$. Indeed, any nonempty open subspace is the disjoint union of finitely or countably many basic clopen copies of Cantor space. Its regular-open algebra is the corresponding product of copies of $A$; a finite clopen partition, or the dense union of cylinders $0^n1$, represents each such finite or countable product as $A$ again.

For a finite set $P\subseteq A$, let $H_P$ be its pointwise stabilizer and $c_1,\ldots,c_m$ the nonzero cells of the finite Boolean algebra it generates. The elements fixed by $H_P$ are precisely the unions of these cells: if an element splits a cell, an interval isomorphism swaps its two nonzero pieces and moves it while fixing $P$.

More strongly, **every $H_P$-invariant subset $S\subseteq A$ has a supremum attained by finitely many members**, with the empty-family convention. For any cell met by a member $b$, either $b$ covers the cell or a symmetry supported inside that cell swaps the two complementary parts cut by $b$. Then $b$ and its image cover the cell. At most two members per cell suffice, and their join covers exactly all cells met by $S$. Complementation gives finite attainment of infima as well.

Consequently, for any finitely supported predicate, every ultrafilter on $A$ commutes with both quantifiers: its range is invariant under the stabilizer of a support, and the relevant meet/join is already attained by a finite subfamily. This fact is about admitted ranges; it does not claim that arbitrary ultrafilters preserve arbitrary external infinite meets.

## 2. A complete predecessor with necessary BF and BC_t, but not necessary Actuality

Start with individuals a singleton, propositions $A$, and at every function type all actual functions with finite $A$-support under conjugation. Equality is crisp literal identity. Application and lambda terms preserve finite support; Boolean operations and the actual $A$-meet/join quantifiers are equivariant. The haecceities have the support of their named object and show that defined identity is precisely crisp identity.

Every ultrafilter gives the classical Boolean, identity and quantifier truth clauses, by §1. These evaluations jointly separate $A$. Hence H-equivalence gives equality of Boolean values, and abstraction gives equal functions, validating C's restricted rule. Native Box is the crisp test $a=1$, so this component satisfies C5 and full BF. It satisfies BC_t at every ultrafilter because $A$ is externally complete. It fails Actuality at every ultrafilter: a true lower bound of all truths would be an atom, and $A$ is atomless.

Adjoin an unrestricted predecessor. For each flattened relational type $\rho=\bar\sigma t$, its domain consists of pairs $(R,a)$, where $R$ is any subset of the root argument-tuple domains and $a$ is a component entity of type $\rho$. Individuals remain a singleton. Application sections the current row and applies the component operation to the component arguments; these sections are admitted recursively. Component projections are onto at every type by using empty current rows. Root truth is the first coordinate of its proposition algebra $2\times A$.

Quantifiers use current truth for the first row and component quantification for the second. Surjectivity of projections makes the component quantifier clause exact. Defined root identity is literal equality of pairs in its first coordinate and component identity in its second: arbitrary current singleton rows and component haecceities prove both bounds. The root and component ultrafilter evaluations are H interpretations and jointly separate $2\times A$, so the combined hierarchy validates C's restricted rule, with all lambda operations admitted.

The root proposition algebra is externally complete, and component BC_t has value 1, giving **necessary BC_t** at the root. Current BF follows directly: if all $Fx$ are literally Top, their quantified proposition is Top, also in the component by surjectivity. Component BF has value 1 by C5, so **necessary full BF** holds. An arbitrary externally chosen current selector graph is admitted with empty component row, giving full current Relational Choice.

The root-only proposition $(1,0)$ witnesses Actuality. The proposition value of Actuality has component 0, so necessary Actuality fails. Also every nonzero $(0,a)$ has an atomless interval below it, so current Atomicity_t fails. No all-type completeness flag is inferred from BC_t.

For completeness, this root also has full logical observer separation. Each ultrafilter $U$ supplies the admitted operation $E_U(\epsilon,a)=(\mathbf1_{a\in U},a)$: its current row is arbitrary and its component operation identity. The finite-attainment lemma and onto projections give all whole-operation quantifier identities. Identity separates first bits; ultrafilters separate component values; a distinct component relation differs at a tuple, which lifts to a root tuple. This observer assertion is retained as proof content pending the native node.

## 3. A supported cofinite interior with full current ND but failing BF_t

Now put $B=2\times A\times\mathcal P(\mathbb N)$ and let $G$ act only on the middle factor. Use the equivariant S4 interior

\[
j'(\epsilon,a,S)=\left(
\mathbf1_{(\epsilon,a,S)=\top},\quad
\begin{cases}1_A,&a=1_A\text{ and }S\text{ cofinite},\\0_A,&\text{otherwise},\end{cases}\quad
\begin{cases}S,&a=1_A\text{ and }S\text{ cofinite},\\\varnothing,&\text{otherwise}.\end{cases}
\right). \tag{1}
\]

Its opens are Bottom, Top and $(0,1_A,S)$ for cofinite $S$. Individuals are a singleton. Set $\delta_t(p,q)=j'(p\leftrightarrow q)$ and recursively admit all nonexpansive functions having finite $A$-support; use open-meet function equality, equivalently $j'$ of the flattened pointwise equivalence meet.

The [cofinite-interior soundness proof](boolean-cofinite-interior.html), §§1–2, applies with this extra support restriction. Here are its added obligations. The interior is equivariant, so equality and haecceities preserve finite support. Evaluation and currying preserve nonexpansivity and finite support together. Actual $B$-meet/join quantifiers are equivariant, and the usual open-lower-bound argument makes them nonexpansive. The middle projection of an admitted range is invariant under a finite-support stabilizer; §1 makes its meet and join finitely attained. Thus all middle-ultrafilter evaluations, as well as the first coordinate and principal tail coordinates, give classical quantifier truth clauses. They jointly separate $B$. Defined equality is the displayed $\delta$ by its admitted haecceities, and the same H-evaluation argument proves C. No crisp identity or full external function domain is substituted for the admitted hierarchy.

Evaluate at one fixed middle ultrafilter $U$. Every typed equality value is an output of $j'$, hence is Bottom, Top, or $(0,1_A,S)$ with $S$ cofinite. If it is false at $U$, it must therefore be **raw Bottom**, whose negation and native Box are Top. This proves full current ND, at every original type.

The local proposition equality identifies exactly equal $A$-coordinates and tail sets differing finitely, ignoring the first bit. Its quotient Boolean algebra is

\[
A\times(\mathcal P(\mathbb N)/\mathrm{Fin}). \tag{2}
\]

Both factors are atomless, proving the native Atomlessness principle. Partition $\mathbb N$ into infinite blocks $A_i$. The empty-supported predicate

\[
X(\epsilon,a,S)=
\begin{cases}(0,1_A,\mathbb N),&[S]_{\rm Fin}\in\{[A_i]_{\rm Fin}:i\in\mathbb N\},\\
\bot,&\text{otherwise}
\end{cases} \tag{3}
\]

is nonexpansive: differing outputs require tails differing infinitely, so their input equality is raw Bottom. Its actual extension consists of all $A$-coordinates paired with the block classes. Any upper bound must have $A$-coordinate 1; in its tail coordinate deleting one selected point from each block gives a strictly smaller upper bound. Thus no join exists. The admitted $Y(p)=X(\neg p)$ gives the native GLB failure. This proves current failure of BC_t at the same evaluation as ND and Atomlessness.

Necessary ND_t nevertheless fails. At any principal tail coordinate $n$, take $p=\top$ and $q=(1,1_A,\mathbb N\setminus\{n\})$. Their equality is $(0,1_A,\mathbb N\setminus\{n\})$, false at $n$, while the Box of its negation is Bottom. The same pair refutes ND_t at the first coordinate. At every middle ultrafilter ND_t is true by the preceding argument. Its proposition value is therefore exactly $(0,1_A,\varnothing)$, with $j'$-value Bottom. Hence necessary ND_t fails at $U$.

The native proved theorem [ND_t + BF_t implies necessary ND_t](nd-t-and-bf-t-imply-necessary-nd-t.html) now gives failure of current BF_t. Thus this single evaluation satisfies full ND and Atomlessness while refuting BC_t, BF_t and necessary ND_t. The all-type ND assertion is an external schema about one evaluation, not an infinitary object-language conjunction.

Both models retain exact current-versus-necessary distinctions. The first is an unrestricted predecessor of a C5 component, not itself asserted C5. The second is current-ND but explicitly not C5. No signature, arithmetic, Maximalism or unreviewed combination-model verdict is included in this batch.

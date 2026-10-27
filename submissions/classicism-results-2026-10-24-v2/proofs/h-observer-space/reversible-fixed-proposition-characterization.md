# Reversible separation and the propositions fixed by every reversible observer

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new arguments: `misc`, this note, §§1–5, unpaginated.

Over C5, reversible logical separation has an exact characterization without mentioning the current truth of an observer's outputs: the only propositions fixed by every reversible logical observer are Bottom and Top. The characterization is one finitary sentence. It does not require Actuality, atoms, Boolean Completeness, Zorn, Choice, or a finite proposition domain.

The proof constructs the least invariant proposition above any given proposition by taking the admitted existential join of its reversible images. Thus a failure of reversible separation supplies an admitted, nonzero, currently false proposition fixed by every reversible observer. The invariant is a proposition object, rather than an external set of orbits.

## 1. The finite qualification and invariant propositions

Work over C5 in the fixed relational language. Put 0=Bottom, 1=Top, I=λp.p, and p≤q iff p∧q=p. Composition is the admitted term (E∘F)(p)=E(Fp).

Let B(E) be the conjunction of the whole Boolean and type-t quantifier preservation identities in $`\mathrm{Good}_{\{t\}}`$. Use precisely those identity clauses in this definition. The translated equality truth clauses in the original Good definition follow from Boolean preservation over C, so B and $`\mathrm{Good}_{\{t\}}`$ have the same qualified members here. This choice makes the endpoint-valued nature of the guard below explicit.

Define the admitted predicate A:(tt)t by

```math
{A(E):=B(E)\land\exists F^{tt}
\,[B(F)\land E\circ F=I\land F\circ E=I]}
\tag{1}
```

Every equation is identity of the complete displayed operations. The inverse F is an admitted operation and has the same qualification. Thus A is exactly the current class of reversible $`\mathrm{Good}_{\{t\}}`$ observers, expressed by a single finite formula.

Two established C5 facts will be used. First, each $`\mathrm{Good}_{\{t\}}`$ observer is Good at any requested finite list of quantifier types, including tt. The same statement applies to its qualified inverse. Second, Functionality lifts propositional separation for this class to full relational separation. These are the [type-reduction theorem](../modal-selectors-and-quantifier-reduction.md), §4, and its [finite-formula application](injective-separation-decomposition.md), §6. No object-language quantification over types is introduced.

For a proposition p put

```math
\mathrm{Inv(p):=\forall E^{tt}\,[A(E)\to Ep=p]}
\tag{2}
```

The restriction concerns propositions fixed by every member of A. It does not say the observers themselves commute with each other, and it is different from [central observer separation](central-logical-observers.md).

The proposed finite condition is

```math
\mathrm{TrivialFix:=
\forall p^t\,[\mathrm{Inv}(p)\to(p=0\lor p=1)]}
\tag{3}
```

### Why the membership guard is an endpoint

Under C5 every identity proposition at every admitted type is 0 or 1. Boolean combinations of endpoint-valued propositions are again endpoint-valued. Quantification preserves this property under C5's Barcan principles: if every instance is Top, BF makes the universal Top; otherwise a Bottom instance makes that universal Bottom by the quantifier order law. The existential case follows dually, or from a Top witness and the all-Bottom case.

Consequently the finite formula A(E), whose atomic clauses are whole-operation identities, always satisfies

```math
{A(E)=0\ \lor\ A(E)=1}
\tag{4}
```

The existential inverse quantifier is covered by this argument. Any Boolean observer fixes A(E). This conclusion does not treat an arbitrary currently true predicate membership as an endpoint, and it does not apply the Logical Equivalence rule to an optional assumption.

Identity belongs to A. Composition of two A-members belongs to A, with the reverse composite of their admitted inverses as inverse. An inverse of an A-member also belongs to A. All these are whole-operation calculations using the supplied identities; no external inverse is selected.

## 2. An admitted orbit join

Define the admitted operation O:tt by

```math
{O(p):=\exists E^{tt}\,[A(E)\land Ep]}
\tag{5}
```

Over C5, the quantifier is the Boolean join of this admitted family. Equation (4) means that its joinands are Ep for eligible E and Bottom otherwise. Thus (5) is an actual admitted join of the reversible images, with endpoint guards. It is not an assumed join of an arbitrary external family.

Identity supplies one joinand, so

```math
{p\le O(p)}
\tag{6}
```

**Lemma 1.** Every O(p) is invariant.

Fix an admitted A-member G. It preserves the existential quantifier at tt by the type-reduction theorem, and fixes each guard A(E) by (4). Hence

```math
{G(O(p))=\exists E^{tt}\,[A(E)\land G(Ep)]}
\tag{7}
```

For each E, the displayed joinand is below O(p). If A(E) is false, its guard is Bottom. If A(E) is true, G∘E is an A-member, and G(Ep) is one of the qualified images in (5). The admitted join's upper-bound property therefore gives G(O(p))≤O(p).

Choose an admitted qualified inverse F of G. The same argument gives F(O(p))≤O(p). Applying the monotone G and using G∘F=I gives O(p)≤G(O(p)). Antisymmetry proves

```math
{G(O(p))=O(p)}
\tag{8}
```

This proves Inv(O(p)). The proof uses join bounds and one inverse; it does not necessitate the optional qualification of G or silently reindex an external set.

**Lemma 2.** O(p) is the least invariant proposition above p. Explicitly, for every invariant q,

```math
{O(p)\le q\quad\longleftrightarrow\quad p\le q}
\tag{9}
```

The forward implication uses (6). Conversely, if p≤q and q is invariant, each eligible E satisfies Ep≤Eq=q. Ineligible joinands in (5) are Bottom, so q bounds their admitted join. This proves (9).

In particular O is monotone and idempotent, O0=0, O1=1, and

```math
\mathrm{Inv(p)\quad\longleftrightarrow\quad O(p)=p}
\tag{10}
```

The map O is an auxiliary closure operation. It is not asserted to preserve negation or to be a Good observer.

## 3. The exact characterization

**Theorem.** Over C5,

```math
\boxed{
\mathrm{Rev}
\quad\longleftrightarrow\quad
\mathrm{TrivialFix}
}
\tag{11}
```

Equivalently, over H the full theory Rev is exactly C5 plus the single sentence TrivialFix. Here C5 retains its established type-schema meaning; (11) does not replace that background by a finite sentence.

**From separation to trivial fixed propositions.** Suppose p is invariant. If p is true, all A-members accept p, and all accept Top. Propositional reversible separation identifies p with Top. If p is false, all A-members reject p and Bottom, so separation identifies p with Bottom. This proves (3).

**From trivial fixed propositions to separation.** Let r≠0. By (6), O(r)≠0. Lemma 1 and (3) therefore give O(r)=1. Its current truth and the ordinary existential truth condition in (5) supply an admitted E with A(E) and Er true:

```math
{r\ne0\quad\Longrightarrow\quad
\exists E^{tt}\,[A(E)\land Er]}
\tag{12}
```

Now let p≠q and take r=p△q, the Boolean symmetric difference. Then r≠0. The witness from (12) preserves the Boolean operations, so E(p△q)=Ep△Eq. Truth of this symmetric difference means that Ep and Eq have different current truth values. Thus the A-members separate every unequal pair of propositions. Equality-to-agreement is ordinary substitution.

This is propositional reversible separation with the one qualification list {t}. The same admitted E and inverse have every requested finite qualification by the C5 type reduction. C5 Functionality then lifts separation to each relational output type. Hence full Rev follows. The converse direction of the full-H formulation uses the established Rev⇒C5 theorem before applying (11).

No simultaneous choice of E for all r occurs in (12). The proof supplies a witness only for the current r, through the truth condition of an admitted existential proposition.

One may also state the theorem as the identity law

```math
\boxed{\forall p\,[O(p)=(p\ne0)]}
\tag{13}
```

Under C5, p≠0 is itself an endpoint. If p=0 both sides are Bottom. If p≠0, TrivialFix makes O(p)=Top, which equals p≠0. Conversely (13) and (10) make every invariant p an endpoint. Thus (13), (3), and Rev are equivalent over C5.

## 4. Exact obstruction and the invariant algebra

Failure of Rev has a canonical invariant witness. By the type/list compression, a failure of full Rev over C5 is already a failure of separation by A at t. Choose p≠q with identical current A-profiles and let r=p△q. Every eligible Er is then false. Consequently O(r) is currently false, while r≤O(r) makes O(r) nonzero. Lemma 1 gives

```math
{\neg\mathrm{Rev}\quad\Longrightarrow\quad
\exists u^t\,[u\ne0\land\neg u\land\mathrm{Inv}(u)]}
\tag{14}
```

Conversely, any u with the properties on the right is missed by every reversible observer and cannot be separated from Bottom. Therefore (14) is an equivalence, with ¬Rev understood through the single finite propositional formula just specified. A nonendpoint invariant always yields such a false nonzero invariant: use it if false and its complement if true. This explains the truth-free condition (3).

The invariant propositions form a Boolean subalgebra. They contain 0 and 1 and are closed under the Boolean operations because every A-member preserves those operations. They are also closed under meets and joins of admitted families of invariant propositions: for an admitted family F:σt, the same G preserves its σ-quantifier and fixes each Fx; Functionality collects those output identities before substitution under the quantifier. This asserts closure for admitted families at each fixed type, not Boolean Completeness for arbitrary current predicates or external sets.

Define the dual admitted operation

```math
{C(p):=\neg O(\neg p)
       =\forall E^{tt}\,[A(E)\to Ep]}
\tag{15}
```

It is the greatest invariant proposition below p, by the complemented version of (9). Thus

```math
{C(p)\le p\le O(p),\qquad
\mathrm{Inv}(p)\ \longleftrightarrow\ C(p)=p
\ \longleftrightarrow\ O(p)=p}
\tag{16}
```

For invariant q the orbit closure has the useful restricted meet law

```math
{O(p\land q)=O(p)\land q}
\tag{17}
```

Indeed each eligible E maps p∧q to Ep∧q, and the fixed-guard quantifier identity distributes q through (5). In general no unrestricted binary meet law for O is claimed. Under Rev, (13) makes O precisely the endpoint-valued nonzero test, while (15) makes C precisely the endpoint-valued Top test. These auxiliary maps need not be logical observers.

## 5. Place in the map and remaining questions

Equation (11) supplies an exact algebraic converse for Rev, beyond its previously known consequences C5, necessary OS and No Pure Contingency. It says that the admitted action of reversible logical observers leaves no nontrivial proposition fixed. This is stronger information than the absence of a particular pure contingent sentence: the invariant witness in (14) may require parameters, and its construction uses the admitted class of reversible observers.

The [component-shift model](component-shift-symmetry-reversible-gap.md), which satisfies C5, necessary SplitMono and No Pure Contingency but fails Rev, must therefore have a nonzero false invariant of the form (5). The present theorem gives its internal existence without claiming an additional explicit coordinate description of that model's witness.

The theorem does not identify TrivialFix with the existing first-order endpoint-parameter noncontingency schema. Whether that narrower schema supplies a converse remains a separate comparison. It also does not resolve InjSep⇒SplitMono or OS+J⇒Rev∨K. No inference from the absence of an arrow is used.

The invariance in (2) should not be confused with centrality of an observer. Invariant propositions are fixed by all reversible observers; a central observer commutes with all ordinary qualified observers. The two restrictions concern different objects and different quantifier classes.

## 6. Sources

The admitted orbit join, its least-invariant property, the finite characterization (11), obstruction (14), and invariant-algebra calculations are original ordinary arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–5, unpaginated.

The observer definitions and Rev⇒C5 theorem are in [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md), §§1, 4 and 6. The finite-list compression is the original [modal-selector/type-reduction proof](../modal-selectors-and-quantifier-reduction.md), §4, applied as in [Injective separation decomposition](injective-separation-decomposition.md), §6. All retain their own source statements.

The C framework, algebraic order and quantifiers are Bacon and Dorr, *Classicism*, draft of 16 May 2023, §§1.3, 1.5 and 2.2, as summarized in the [background](../../source/topics/classicism/background.md). The background BF and Functionality consequences are recorded in [C5 implies necessary Barcan](../../source/topics/classicism/results/necessary-distinctness-necessary-r-implies-necessary-barcan-r.yaml) and [Barcan implies Functionality](../../source/topics/classicism/results/barcan-r-implies-functionality-r.yaml). These sources provide the framework, not attribution for the new theorem.

No database record, named human review, or formal-verification status is added by this note.

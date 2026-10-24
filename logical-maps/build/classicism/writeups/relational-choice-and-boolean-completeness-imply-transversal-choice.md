# Relational Choice and Boolean Completeness imply Transversal Choice

Integration and comparison by Codex (OpenAI), prompted by Daniel Kodsi,
23 October 2026. The conjecture is Zachary Goodsell's, communicated on
27 September 2026. The direct proof and refinements reproduced below are
independent Codex research, prompted by Daniel Kodsi, from 22 October 2026.
Published background and the older components of the composition retain
 their own attribution.

## 1. The settled statement and the two proofs

In the fixed framework C, with the map's relational type system,

\[
\mathrm{Relational\ Choice}+\mathrm{Boolean\ Completeness}
\;\Longrightarrow\;\mathrm{Transversal\ Choice}.
\]

All three schemata are unboxed. Here **RC means Relational Choice**, not
Rigid Comprehension. The stable conjecture ID and its original certificate
date are retained.

There are two useful proofs. The short database composition is

\[
\begin{aligned}
\mathrm{RC}+\mathrm{BC}&\Rightarrow\mathrm{Actuality},\\
\mathrm{BC}+\mathrm{Actuality}&\Rightarrow\mathrm{Weak\ Rigid\ Comprehension},\\
\mathrm{RC}+\mathrm{Weak\ Rigid\ Comprehension}&\Rightarrow\mathrm{TC}.
\end{aligned}
\]

The first implication is the independent Codex research prompted by Daniel
Kodsi, recorded in
[RC+BC implies Actuality](relational-choice-and-boolean-completeness-imply-actuality.md)
and its [full proof](relational-choice-and-boolean-completeness-imply-actuality.md).
The second is Cian Dorr's Proposition 1, p. 2, in the draft of 30 July 2026,
[recorded here](completeness-and-actuality-imply-weak-rigid-comprehension.md).
The third is the proof recorded on 25 September 2026 by Claude Fable 5.1
(Anthropic), prompted by Zachary Goodsell following Christopher Sun's
observation,
[RC+Weak Rigid Comprehension implies TC](relational-choice-and-weak-rigid-comprehension-imply-transversal-choice.md).
BC and RC remain available for the second and third steps respectively;
there is no claim that Actuality alone gives Weak Rigid Comprehension.

The **direct proof** does not pass through either Actuality or Weak Rigid
Comprehension. It builds a partially ordered collection of partial
transversals, proves closure under the required algebraic joins, and obtains
a fixed point of a guarded progressive construction. Its contribution is
therefore retained in full below, together with its refinements. No proof of
this new implication is attributed to Bacon or to a paper supplying only
its definitions.

## 2. Exact local strengths retained from the direct proof

Fix an admitted type $\sigma$, including $e$, and put $\rho=\sigma t$.
Write $\mathrm{RC}_{\alpha,\beta}$ for relational selection with input type
$\alpha$ and output type $\beta$, and $\mathrm{BC}_\tau$ for Boolean
Completeness at the relational type $\tau$.

A **represented** family means an admitted predicate in the language of C.
Let $\mathrm{ChainBC}_\tau$ require joins of represented families totally
ordered by the algebraic Boolean order; let $\mathrm{WOChainBC}_\tau$
require them only for represented families which that order internally
well-orders. These are descriptions of local formulas, not new principle
records or external set-theoretic completeness assumptions. The empty
family has the already available bottom as its join.

| Premises over C | Conclusion | Evidence retained below |
| --- | --- | --- |
| $\mathrm{RC}_{\rho,\sigma}+\mathrm{WOChainBC}_\rho$ | $\mathrm{TC}_\sigma$ | Direct argument plus guarded point-output refinement |
| $\mathrm{RC}_{\rho,\rho}+\mathrm{WOChainBC}_\rho$ | $\mathrm{TC}_\sigma$ | Original functional-graph argument |
| $\mathrm{RC}_{\tau,\tau}+\mathrm{WOChainBC}_\tau$ | $\mathrm{BC}_\tau$ | Cut and fixed-point argument |
| $\mathrm{RC}_{\tau,\tau}+\mathrm{CBC}_{\kappa,\tau}+\mathrm{CCC}_{\kappa,\tau}$ | $\mathrm{BC}_\tau$ | Countable disjoint-increment argument |
| $\mathrm{RC}_{\rho,\sigma}+\mathrm{CBC}_{\kappa,\rho}+\mathrm{CCC}_{\kappa,\rho}$ | $\mathrm{TC}_\sigma$ | The same disjoint-increment argument applied directly to the guarded operation |

In particular, the first two conclusions hold with ChainBC or BC in place
of WOChainBC. The point-output choice premise is the useful later
refinement of the original choice instance; the two displayed original
proofs remain independently readable.

Here $\mathrm{CBC}_{\kappa,\tau}$ means that every represented
$\kappa$-countable family of $\tau$-entities has a Boolean join, and
$\mathrm{CCC}_{\kappa,\tau}$ means that every represented disjoint family
of nonbottom $\tau$-entities is $\kappa$-countable. Countability is the map's
Frege-countability notion: there is a represented relation to
$\mathbb N_\kappa$ such that two family members share a numerical label
exactly when they are identical. Labels have the appropriate Frege number
type $\nu_\kappa$; the construction does not assume a single-valued
labeling, a selected enumeration, externally standard numbers, or Infinity.

For clarity, the last row follows without upgrading the point-output
choice premise to $\mathrm{RC}_{\rho,\rho}$. Under failure of
$\mathrm{TC}_\sigma$, the guarded operation $g$ of Part B is strict on
all partial transversals. Form the represented union $A$ of its internal
$g$-chains as in Part A. No completeness is needed to form $A$ or prove it
internally well-ordered. For $F\in A$, put

\[
d_F=g(F)\wedge_\rho\neg_\rho F.
\]

Strictness makes $d_F$ nonbottom. If $F<G$ in $A$, its defining predecessor
condition gives $g(F)\le G$, so $d_F\wedge_\rho d_G=0$. Thus the
represented image of the increments is disjoint and the increment map is
injective. CCC supplies numerical labels for that image; composition with
the represented increment graph labels $A$. CBC therefore gives the one
join of $A$ needed by the final step of the fixed-point proof. Evaluation's
adjunction, already proved in Part A, ensures that this join is a partial
transversal. The fixed point contradicts strictness. This is the point-output
refinement recorded in
[the structural handoff, §1](../../../../submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/structural-lane-handoff.md).
Part C retains the full, separate BC-upgrade proof at arbitrary $\tau$.

The composition offers a different locality advantage. The Actuality
result needs only $\mathrm{RC}_{t,t}+\mathrm{BC}_{tt}$. Christopher Sun's
[Actuality implies Transversal](actuality-implies-transversal.md)
and
[Transversal plus RC implies TC](transversal-and-relational-choice-imply-transversal-choice.md)
then give

\[
\mathrm{RC}_{t,t}+\mathrm{BC}_{tt}+\mathrm{RC}_{\sigma t,\sigma}
\Rightarrow\mathrm{TC}_\sigma.
\]

Consequently all-type RC with BC at $tt$ alone suffices for all-type TC.
This is complementary to the direct proof's completeness premise at
$\sigma t$; it does not erase that proof or its chain/CBC+CCC refinements.

## 3. Shared limits and useful consequences

The direct construction works for an equivalence relation that is an
equivalence relation only actually. It uses no ND, BF, Plenitude, or
identity of actually coextensive property entities. Its crucial
partial-transversal predicate has **$\forall x\,y\,\Box$** scope.
A separate final purification, reproduced in Part A, gives a witness with
**$\Box\forall x\,y$** partiality. That normalization is not substituted
into the chain-join argument.

The internal fixed-point proof uses admitted predicates and represented
graphs, not an external ordinal iteration. The guarded operation of Part B
is a term built for this particular purpose; it is not a representation
of arbitrary functional graphs and gives no Plenitude conclusion.

With BC, the recorded TC⇒RC, TC⇒Zorn, Zorn⇒Well-Ordering and
Well-Ordering⇒TC arrows make RC, TC, Zorn and Well-Ordering equivalent.
Necessitating the discharged implication gives the boxed conditional
$\Box\mathrm{RC}+\Box\mathrm{BC}\Rightarrow\Box\mathrm{TC}$.
Neither step permits necessitation of an optional unboxed premise.
The RC-alone⇒TC question remains separate.

## 4. Provenance and exact verification boundary

The frozen submission's
[catalog entry rigidity.16](../../../../submissions/classicism-results-2026-10-24-v2/CATALOG.md#rigidity.16)
identifies the direct theorem. Its three source notes are reproduced below
with their mathematical text preserved:

- [Original direct proof, §§1–9](../../../../submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/relational-choice-boolean-completeness-transversal-proof.md).
- [Guarded operation, §§1–6](../../../../submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/rc-guarded-progressive-operation.md).
- [Countable-completeness and CCC proof, §§1–4](../../../../submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/relational-choice-countable-completeness-ccc.md).

Their statements about no record edit, no formalization, or an unchanged
map describe the drafts when written. They are retained as historical
source text, not as current database-status assertions. The current exact
status is: the three component implication records in §1 have separate
verified Lean certificates; the generated statement for **this stable
conjecture ID remains `lean: stated`**. No machine certificate for every
local strengthening in §2 is asserted here. No human checker is claimed.

The canonical record's short proof is the composition; the following
independent argument remains part of its mathematical documentation.

---

## Part A. Preserved original direct proof

Original title: Relational Choice and Boolean Completeness imply Transversal Choice

22 October 2026. Original scratch proof by the OpenAI Codex research agents in the extension and quotient lanes, with a separate algebraic audit by the coordinating agent. No human check or Lean formalization is claimed. No map record has been edited. This addresses the existing conjecture `relational-choice-and-boolean-completeness-imply-transversal-choice`, attributed in the map to Zachary Goodsell, 27 September 2026. The proof below is new evidence, not a proof attributed to Goodsell or to a published source.

### Exact claim and conventions

For any type σ, including e, the following instances suffice over C:

* Boolean Completeness at the relational type ρ:=σt.
* Relational Choice with both input and output type ρ.

They imply Transversal Choice at σ. Consequently the full schemata satisfy

    C ⊢ Relational Choice + Boolean Completeness → Transversal Choice.

All hypotheses and the conclusion are unboxed. No Necessity of Distinctness, Actuality, BF, Plenitude, Functionality, or extensional identification of coextensive properties is used. We use the LUB form of Boolean Completeness, equivalent in C to its recorded GLB form. Every set-like collection below is an admitted predicate, and every union or image is given by existential quantification. All order-theoretic reasoning takes place at the evaluation point.

At relational type τ, ≤ is the algebraic Boolean order. For propositions p,q, p≤q is equivalent to □(p→q). At a property type σt, F≤G is equivalent to □∀x(Fx→Gx). The latter is used only when it follows from the algebraic order; no converse-Barcan interchange is made.

### 1. Evaluation preserves represented algebraic joins

Fix x^σ. Evaluation e_x(F):=Fx is an order map B_{σt}→B_t and has the C-definable right adjoint

    r_x(p):=λz^σ.(z=x→p).

Indeed,

    F≤r_x(p) iff Fx≤p.                                  (1)

The formulas ∀z(Fz→(z=x→p)) and Fx→p are logically equivalent by equality substitution and universal instantiation. Logical Equivalence and the definition of algebraic order give (1). This is a theorem of C, valid without ND or BF.

Suppose Q is an algebraic LUB of a represented family C^{ρt}. Then Qx is a LUB in B_t of the represented evaluation image

    V_x(p):=∃F(CF∧p=Fx).

It is an upper bound because F≤Q implies Fx≤Qx. If p bounds every Fx with CF, (1) makes r_x(p) an upper bound of C; hence Q≤r_x(p), and Qx≤p by (1). Thus evaluation preserves this join. This argument does not separately assume Boolean Completeness at t.

### 2. A chain-complete poset of partial transversals

Fix R^{σσt} which is an equivalence relation actually. It need not be necessarily an equivalence relation. Define the predicate P on property entities F^ρ by

    P(F) := ∀x^σ y^σ. □(Fx∧Fy∧Rxy→x=y).                (2)

The boxes in (2) are **inside** the universal quantifiers. This exact scope is essential: we do not assert □∀xy(...), and BF is not needed. Since □ implies truth, a P-instance has at most one actual member in each actual R-cell. The bottom property 0_ρ satisfies P.

Order the P-instances by the inherited Boolean order. It is an antisymmetric partial order on actual entities. We prove that every represented chain of P-instances has a LUB which is again a P-instance.

Let C^{ρt} satisfy ∀F(CF→P(F)) and be totally ordered by ≤. Boolean Completeness at ρ gives its ambient LUB Q. Fix arbitrary actual x,y and write

    k := (Rxy→x=y).

For every F,G in C,

    Fx∧Gy ≤ k.                                         (3)

If F≤G, this follows from Fx≤Gx and P(G); if G≤F, it follows from Gy≤Fy and P(F). Fix F. Equation (3) says that every Gy lies below Fx→k. By §1, Qy is their LUB, so Fx∧Qy≤k. Now let F vary: every Fx lies below Qy→k, so §1 gives Qx∧Qy≤k. Equivalently,

    □(Qx∧Qy∧Rxy→x=y).

Since x,y were arbitrary, P(Q). This uses the Boolean implication adjunction twice, not an unlicensed interchange of a box with quantification. Q is also the LUB within P. The empty chain has LUB 0_ρ. Therefore P is a represented chain-complete antisymmetric poset with least element.

### 3. Every nonfull partial transversal has a strict extension in P

Say

    Full(F):=∀x∃y(Rxy∧Fy).

Suppose P(F) and ¬Full(F). Choose x whose actual R-cell contains no F-instance. Put

    q := ∀z(Fz∧(Rxz∨Rzx)→z=x),
    G := λy.(Fy∨(y=x∧q)).                              (4)

Actually q is true: actual symmetry of R makes either R-direction describe x's cell, and that cell has no F-instance. Actual reflexivity gives ¬Fx. Hence Gx is true and Fx false, so G≠F. The defining formula gives F≤G by a theorem of C; thus F<G.

Also P(G). For arbitrary actual u,v, expand Gu∧Gv into four cases under the box. If both conjuncts come from F, the required implication follows from P(F) at u,v. If both come from the new summand, u=x=v. If exactly one comes from the new summand, q rules out a distinct old F-member related in either direction to x. These are logical implications using equality substitution and instantiation of q; they do not require R to be an equivalence relation at other worlds. Consequently □(Gu∧Gv∧Ruv→u=v), and universal generalization gives P(G).

The two R-directions in q are deliberate. They avoid using necessary symmetry of R, which is not a premise.

### 4. Relational Choice supplies a progressive functional graph

On entities F,G of type ρ define a serial relation U by the following exhaustive cases:

* If P(F) and ¬Full(F), require P(G) and F<G.
* Otherwise require G=F.

Section 3 proves seriality in the first case; reflexivity supplies the second. Relational Choice at (ρ,ρ) gives an actual functional graph f⊆U. On P this graph is total, single-valued, stays in P, and is progressive: F≤f(F). Here and below f(F) is explanatory notation for the unique graph value, **not** an assumption that the graph is represented by an operation. Every use can be expanded with an existential variable and the graph relation.

Moreover,

    P(F)∧¬Full(F) → F<f(F).                            (5)

It remains to obtain a fixed point of this progressive graph on P. The following lemma is available in C itself.

### 5. Internal Bourbaki–Witt lemma, without Plenitude

**Lemma.** Let P^{ρt} carry a represented antisymmetric partial order, have a least element 0, and have a LUB in P for every represented chain, including the empty chain. Let f be a represented total single-valued graph from P to P with x≤f(x) for every x∈P. Then f has a fixed point.

The proof uses only predicate comprehension and ordinary quantification admitted in C. In particular it does not assume an external set of ordinals, standard finiteness, an operation representing f, or extensionality of property entities.

Call a predicate C^{ρt} an **f-chain** when:

1. C⊆P and the inherited order well-orders C: every admitted nonempty subproperty of C has a least member.
2. For each x∈C, x is the LUB in P of the graph image

       { f(y): y∈C and y<x }.                          (6)

Condition 2 is a formula about being a LUB; it does not presume this image has a LUB before the condition is asserted. The singleton {0} is an f-chain. If x<y lie in an f-chain, then f(x)≤y by (6).

**Comparison.** Any two f-chains C,D are comparable by initial segment. Define I to consist of those common members x for which the C- and D-predecessor properties below x are coextensive. I is an initial segment of both C and D: if x∈I and y<x lies in either chain, then y lies in both, and the predecessor properties below y are equal in extension as subsets of their common predecessor property below x.

If both C\I and D\I were nonempty, let c,d be their respective least members. Their predecessor properties are each coextensive with I. The graph images in (6) are therefore coextensive. Since an antisymmetric poset has at most one LUB for a given actual family, c=d. This equality and equality of their predecessor extensions place c in I, contradiction. Hence C≡I or D≡I (actual coextension), proving comparison by initial segment. Notice that equality of predicate codes was never inferred from coextension; only uniqueness of their order-theoretic LUB was used.

**Union.** Define the admitted property

    A(x):=∃C^{ρt}(C is an f-chain ∧ Cx).

Comparison makes A a chain. It is internally well-ordered: given any nonempty represented X⊆A, choose x∈X and an f-chain C containing x. Let m be the least member of X∩C. For any z∈X, choose an f-chain D containing z. If D is an initial segment of C, then z∈C and m≤z. If C is an initial segment of D, then either z∈C, giving the same conclusion, or z lies strictly above every member of C, including m. Thus m is least in X.

For x∈A choose an f-chain C containing x. Comparison shows that A and C have the same predecessor extension below x. Condition (6) for C therefore gives it for A, again using only actual coextension of the represented images. Hence A is itself an f-chain, and it contains every f-chain by definition.

**The supremum is a fixed point.** Let u be the LUB of A in P. If u∉A, then A has no largest member. For every x∈A choose y∈A with x<y; (6) gives f(x)≤y≤u. Conversely x≤f(x) for each x, so any upper bound of f[A] bounds A. Therefore u is the LUB of f[A]. Adjoining u at the end of A gives another f-chain: its new predecessor property is A, and the defining LUB condition is the one just proved. This contradicts the definition of A, which would then contain u. Thus u∈A.

If u<f(u), adjoining f(u) at the end of A again gives an f-chain. Its new LUB condition holds because f(u) is the greatest member of f[A]: for x<u in A, (6) gives f(x)≤u≤f(u), and f(u) itself is in that image. Again the definition of A would put f(u) into A, contradicting u being an upper bound. Progressivity leaves f(u)=u. This proves the lemma.

**Independent route through a recorded proof.** The quotient lane also checked the lemma against the existing write-up `topics/classicism/writeups/transversal-choice-r-implies-zorn-r.md`. Under the assumption that f has no fixed point, the functional graph taking a chain C to f(sup_P C) is a strict-upper-bound selector and is invariant under actual coextension of C, because the supremum is unique as an entity. Restricting Lewin's conforming-property argument there to P supplies the same contradiction. All four places marked (E) in that write-up are licensed by this LUB uniqueness; no Transversal Choice is used to construct the selector. The self-contained proof above avoids depending on that adaptation for the conclusion.

### 6. Completion of the conjectured implication

Apply the lemma to the poset P of §2 and the functional graph f of §4. Obtain F∈P with f(F)=F. By (5), Full(F). Thus every actual R-cell has an F-instance. Since P(F) implies actual at-most-one membership in each R-cell, F is an actual transversal of R.

R was any actual equivalence relation at any type σ. Therefore RC+BC implies TC in C, with the sharpened instance scope stated at the start.

### 7. Audit summary and limitations

The proof closes the actual-coextension gap by passing to unique **algebraic supremum entities**, not by equating coextensive property codes. The principal technical devices are evaluation's right adjoint, pointwise boxes in the definition of partial transversals, and a fixed-point theorem for functional graphs.

* No optional assumption is necessitated. Every boxed formula is either part of P(F), follows from the algebraic order, or follows from a theorem of C using its rules.
* No box is moved across a universal quantifier. The distinction between ∀xy□ and □∀xy is preserved throughout.
* The selected graph need not be represented by an operation. Relational Choice, rather than Functional Choice or Plenitude, suffices.
* The f-chain construction quantifies only over admitted predicates and uses admitted unions, images, predecessor properties, and intersections. It invokes no externally arbitrary subset or ordinal sequence.
* R is assumed to be an equivalence relation only actually. The symmetric guard in (4) handles other-world failures of symmetry.
* This is a new ordinary mathematical proof, checked by other agents but not yet by a human or a proof assistant. The existing conjecture record and its formalization status have deliberately been preserved.

### 8. Sharpening to Boolean chain completeness

Define ChainBC_τ, within the existing language of C, to say that every represented family of τ-entities totally ordered by the algebraic Boolean order has an algebraic LUB. This is weaker on its face than BC_τ.

The proof in §§1–6 only needs ChainBC_ρ: the family C in §2 is a chain, and no other Boolean join is assumed to exist. Therefore the exact stronger claim is

    C ⊢ RC_{σt,σt} + ChainBC_{σt} → TC_σ.              (7)

At the full-schema level, RC+ChainBC is in fact equivalent to RC+BC. One route is (7), followed by the recorded TC⇒Zorn. Given any represented S⊆B_τ, its property of upper bounds is nonempty (it contains 1), and every represented chain of upper bounds has an infimum by ChainBC and Boolean complementation. That infimum is still an upper bound of S. Apply Zorn to this property in the reverse Boolean order, using the standard invalid-code padding if the recorded whole-type formulation is required. Obtain a minimal upper bound u. For every other upper bound v, u∧v is another upper bound below u, so minimality gives u=u∧v, that is u≤v. Hence u is the required LUB.

The quotient lane supplies an even more local argument, requiring only RC_{τ,τ}+ChainBC_τ. For a fixed represented S let

    P(b):=∀u(UpperBound_S(u)→b≤u).

This cut contains 0 and is closed under represented chain joins. If b∈P is not an upper bound of S, choose x∈S with x≰b; then b∨x∈P and b<b∨x. RC selects a progressive functional graph on P, strict unless its input is an upper bound. The fixed-point lemma yields b both below every upper bound and itself an upper bound, hence a LUB of S. Thus

    C ⊢ RC_{τ,τ} + ChainBC_τ → BC_τ.                  (8)

This local upgrade uses no Boolean complements: the same argument works for an internally represented bounded join-semilattice with represented binary joins and joins of represented chains. It explains structurally why Relational Choice removes the apparent gap between Boolean chain completeness and Boolean completeness in the conjecture's premise set.

#### Technical further weakening

The self-contained fixed-point proof in §5 calls the completeness premise only for the union A of all f-chains, which it has already proved internally well-ordered, and for the empty chain/least element. The LUB assertions in the definition of an f-chain are hypotheses on that chain and are inherited by the union; their existence is not independently assumed for every possible predecessor family. Consequently all the preceding results remain valid if ChainBC_τ is weakened to the existence of LUBs only for represented families which the Boolean order itself internally well-orders. This is an internal well-order condition, not a schema ranging over externally standard ordinals. The chain-complete formulation remains the simpler main statement.

### 9. Immediate corollaries and scope of new evidence

The recorded implications TC⇒RC and TC⇒Zorn/Well-Ordering now show that, in the presence of BC, Relational Choice, Transversal Choice, Zorn, and Well-Ordering are equivalent. This is a new consequence of the proof, not something already present in the unchanged derived map. Necessitating the discharged C-implication also gives □RC+□BC⇒□TC, with no unboxed premise being necessitated.

At the graph level, the ordinary Boolean homomorphism extension proof in `retraction-extension-lane.md`, §1, now needs only RC+BC: the new theorem supplies Zorn, and the maximal partial homomorphism is already a total single-valued relation. An **operation** representing that graph still requires Plenitude. No graph-to-operation upgrade is being silently inferred from RC+BC.

The recorded `full-two-object-chain` supplies a concrete check on this distinction. It satisfies □Relational Choice and □Rigid Comprehension, hence □BC, but its root proposition {identity at W0} is distinct from bottom and becomes bottom after the arrow W0→W1. Thus ND_t fails at the root, and Plenitude fails by the recorded implication Plenitude⇒ND. RC+BC therefore does not supply the operation representation that the graph-level extension theorem lacks. This is existing model evidence, not a new countermodel construction.

#### Final witness normalization: necessary partiality

There is a simple optional strengthening of the final witness. For arbitrary R and T define

    Pur_R(T)(x):=T(x)∧∀y(T(y)∧Rxy→x=y).

C proves, as a logical theorem about this displayed term,

    □∀xy(Pur_R(T)(x)∧Pur_R(T)(y)∧Rxy→x=y).

Indeed, at any point the first conjunct at x supplies the universal condition, while the first conjunct at y supplies T(y). If T is an actual partial transversal, its defining at-most-one condition also shows Pur_R(T) and T are actually coextensive. Therefore the actual transversal obtained in §6 can be replaced by a witness F which is necessarily partial under a full outer □∀, while still meeting every actual R-cell exactly once. No BF or additional choice/completeness instance is used.

This is a FINAL witness normalization only. It does not strengthen P in §2: the algebraic chain-join argument there still establishes only pointwise boxed independence, and its quantifier-scope warnings remain essential. The same normalization shows directly that the all-type Transversal Choice schema is equivalent to its version requiring necessarily partial witnesses.

### Consolidated handoff and subsequent refinements

The live exact-scope index for this research lane is `structural-lane-handoff.md` in the same directory. In particular, the independent audit sharpened the choice premise to RC_(σt,σ) by constructing an explicit guarded progressive operation; its proof is in `rc-guarded-progressive-operation.md`. The index also records the separately audited countable-completeness/CCC bridge and countable Boolean-type finiteness results. None of these scratch additions changes the repository's records or generated state.


---

## Part B. Preserved guarded point-output refinement

Original title: RC supplies a guarded progressive operation on partial selectors

OpenAI Codex research argument, 22 October 2026. Independently audited in outline by the coordinating agent. This sharpens the exact choice instance in the new RC+BC⇒TC proof. It is not a representation theorem for arbitrary functional graphs, and it uses no Plenitude.

### Exact statement

For any admitted σ, including e, put ρ=σt. Over C, for every R^{σσt} which is an equivalence relation actually, Relational Choice at **(ρ,σ)** supplies an admitted operation g:ρ→ρ (depending on R) such that

    F≤gF,
    P(F)→P(gF),
    P(F)∧¬Full(F)→F<gF,

where

    P(F):=∀u v □(Fu∧Fv∧Ruv→u=v),
    Full(F):=∀u∃v(Ruv∧Fv).

All hypotheses are actual and unboxed. Therefore BC at σt together with RC at (σt,σ) implies TC at σ by the already audited chain-completeness/fixed-point argument. RC at (σt,σt) remains an alternative sufficient premise because individual outputs can first be replaced by haecceity codes.

### 1. The actual selected point

Let

    Miss(F,x):=¬∃z(Rxz∧Fz),
    U(F,x):=(¬Full(F)→Miss(F,x)).

This is serial. If ¬Full(F), classical quantifier duality supplies x with Miss(F,x); otherwise any individual of the inhabited σ-domain works. Apply RC at (ρ,σ) to get an actually functional S⊆U.

No necessary functionality or necessary containment of S is asserted. It may have multiple outputs, no outputs, or unsuitable outputs elsewhere.

### 2. A formula that protects itself at every world

Define

    Unique_S(F,y):=∀z(S(F,z)→z=y),
    Safe_R(F,y):=∀z(Fz∧(Ryz∨Rzy)→z=y),
    N(F,y):=S(F,y)∧Unique_S(F,y)∧Safe_R(F,y),
    g:=λF^ρ y^σ [Fy∨N(F,y)].

This has the admitted type ρρ. The guard is evaluated wherever the output predicate is evaluated. If S loses functionality, all its conflicting outputs fail Unique_S, so no such pair is added. If an old F-member would conflict with y under either R-direction, Safe_R blocks y.

The H theorem Fy→(Fy∨N(F,y)) gives F≤gF algebraically.

### 3. Preservation of P

Fix actual u,v. There is an H-theorem implication

    (Fu∧Fv∧Ruv→u=v)
          → ((gF)u∧(gF)v∧Ruv→u=v),

with g expanded as above. Check the four disjunctive cases:

* both points come from F: use the antecedent;
* both come from N: Unique_S(F,u), together with S(F,v), gives v=u;
* u comes from N and v from F: Safe_R(F,u), Ruv and Fv give v=u;
* u comes from F and v from N: Safe_R(F,v), Ruv and Fu give u=v.

Necessitate only this H theorem and combine it with P(F)'s existing boxed pair-safety assertion. Then generalize over actual u,v. This proves P(F)→P(gF), without □∀uv, BF, ND, or necessary Equiv(R).

### 4. Strict progress at every nonfull input

Suppose P(F) and ¬Full(F). Let x be S's unique actual value at F. Its containment in U gives Miss(F,x). Therefore Fx is false, by actual reflexivity of R.

Unique_S(F,x) holds by actual functionality. Safe_R(F,x) holds because actual symmetry makes either R-direction place an F-member in x's missed cell, which has none. Thus N(F,x), so (gF)x while ¬Fx. Consequently F≠gF. Together with F≤gF this gives F<gF.

Actual truth of either guard is never necessitated. The uniform implication in §3 is the only new boxed reasoning.

### 5. Why this does not imply Plenitude or Actuality

The output gF is a property whose extension adds the selected point actually. It is **not** asserted to be the rigid haecceity of that point, or to be identical to a separately chosen output entity of a graph. Away from the evaluation point, the guards can delete its new summand. Thus g need not represent the original selected graph as an operation.

Nor is g required to identify actually coextensive inputs or even send them to actually coextensive outputs. Different intensions of the same actual partial selector can receive different S-values. This is still the obstacle to a straightforward RC-alone transfinite construction using ordinary actual unions as limit stages.

### 6. Resulting location of the RC-alone obstruction

A failed TC instance plus this RC instance would supply a represented algebraically progressive operation g on P which is strict everywhere on P. The union of all g-chains from the fixed-point construction is an internally well-ordered chain of P-members with no ambient algebraic supremum. The difficulty is therefore genuinely at coherent limit formation. It cannot be attributed merely to the absence of a selected operation.

This also permits the BC proof's abstract fixed-point lemma to be stated for operations if desired, though the stronger already checked functional-graph version remains correct.

---

## Part C. Preserved countable-completeness and CCC refinement

Original title: Relational Choice, countable completeness, and the countable chain condition

22 October 2026. New ordinary mathematical argument by OpenAI Codex, independently checked by the quotient-lane agent. No human check, Lean formalization, or database edit is claimed. This is a further consequence of the graph Bourbaki–Witt argument in `relational-choice-boolean-completeness-transversal-proof.md`, §5; it is not attributed to a published source.

### Exact statement

Fix a relational type τ and a counting type κ. All statements below are actual, unboxed, in the original language and fixed framework C.

* RC_(τ,τ): Relational Choice for relations whose input and output types are both τ.
* CBC_(κ,τ): every represented κ-countable family of τ-entities has an algebraic Boolean supremum.
* CCC_(κ,τ): every represented family of pairwise disjoint, nonbottom τ-entities is κ-countable.

Here κ-countable has the existing Frege-countability definition: a represented label relation L(x,n) with n in N_κ such that, for members x,y of the family, they share an N_κ-label if and only if x=y. A point can have more than one label; no single-valued choice of labels is assumed.

**Theorem.** Over C,

    RC_(τ,τ) + CBC_(κ,τ) + CCC_(κ,τ)  ⇒  BC_τ.

Consequently, with τ=σt, these premises imply Transversal Choice at σ by the separately proved BC_(σt)+RC_(σt,σt) theorem. This is type-local. No all-type CCC assumption is needed, and no necessity of distinctness, Actuality, BF, operation representing a chosen graph, or well-order on N_κ is used.

### 1. The cut and the strict progressive graph

Fix a represented family X of τ-entities. For a Boolean element b put

    P(b) := ∀u (UpperBound_X(u) → b≤u).

Bottom belongs to P. Any existing Boolean supremum of a represented family contained in P belongs to P: each upper bound u of X bounds the whole family, so its supremum is below u.

Suppose, for contradiction, that X has no supremum. Then no b in P is an upper bound of X, since such a b would be below every upper bound and hence be the supremum. For each b in P there is x in X with x≰b. The element c=b∨x belongs to P and satisfies b<c. Relational Choice gives an actual total single-valued graph f, taking each b in P to a strictly larger member of P; outside P use the input itself to make the relation on the whole type serial. The notation f(b) below denotes its unique graph value, not a represented operation.

### 2. The union of all f-chains needs no completeness premise

Call C⊆P an f-chain if the inherited Boolean order internally well-orders C and every a in C is the supremum within P of the represented image

    { f(b) : b∈C and b<a }.

This is a formula asserting the relevant supremum properties, not an assumption that every arbitrary family has a supremum. The singleton consisting of bottom is an f-chain. If a<b in an f-chain, then f(a)≤b.

The comparison argument in the cited §5 uses only these asserted supremum properties and their uniqueness as entities: any two f-chains agree on their common predecessor segment, and two least divergent elements would be suprema of coextensive predecessor images, hence equal. Thus the chains are comparable by initial segments. Their represented union

    A(a) := ∃C (C is an f-chain and Ca)

is internally well-ordered and is itself an f-chain. To see the least-element assertion, intersect a nonempty represented subproperty of A with one f-chain containing one of its members; its least member is least in the whole subproperty by initial-segment comparison. For a∈A, comparison makes its predecessor extension the same as in any f-chain containing a, so the defining supremum condition transfers. None of this invokes chain completeness, countable completeness, choice on predicate codes, external ordinals, or equality of coextensive predicate entities.

### 3. Disjoint increments make A countable

For a in A define the Boolean increment

    d_a := f(a)∧¬a.

It is nonbottom because a<f(a). Its graph is represented by existentially binding the unique f-value. If a<b in A, the f-chain property gives f(a)≤b, while d_b≤¬b. Consequently d_a∧d_b=0. Since A is a chain, distinct members have disjoint increments; since increments are nonzero, a↦d_a is injective.

The represented image D of these increments is therefore a pairwise disjoint nonbottom family. CCC gives a κ-countability label relation L_D(d,n) for D. Define

    L_A(a,n) := ∃c (f(a,c) ∧ L_D(c∧¬a,n)).

For a,b in A, functionality of f and the countability property of L_D show that a,b share a label exactly when d_a=d_b, and injectivity makes this equivalent to a=b. Thus A is κ-countable. This is direct composition of represented relations; it uses no selected enumeration, arithmetic recursion, or externally countable family.

### 4. The one required supremum supplies the contradiction

CBC gives an ambient Boolean supremum u of A. By §1, u∈P. It is also the supremum within P.

If u∉A, A has no greatest member. For each a∈A choose some b∈A with a<b; then f(a)≤b≤u. Conversely every upper bound of f[A] bounds A because a≤f(a). Hence u is the supremum of f[A]. Adjoining u at the end of A gives another f-chain, contrary to A's definition as the union of all such chains. Therefore u∈A.

But f(u)>u. For each a<u in A, f(a)≤u≤f(u), while f(u) itself is a member of f[A]. Thus f(u) is the greatest element of f[A], and adjoining f(u) at the end again gives an f-chain. Its membership in A contradicts u being an upper bound of A.

The supposition that X lacks a supremum is false. X was arbitrary, so BC_τ holds.

### Scope and provenance

The only completeness invocation in this proof is the supremum of the represented f-chain A, whose countability has already been established by its disjoint increments. This explains why CBC+CCC can replace the chain-completeness premise in the earlier local upgrade under Relational Choice. The result does not identify algebraic joins with arbitrary pointwise infinitary disjunctions.

Relevant local source conventions are `topics/classicism/background.md`, the Frege countability and Boolean-order definitions; `principles/relational-choice-r.yaml`; and `principles/countable-boolean-completeness-r.yaml`. The CCC definition also occurs in the concurrent infinity lane's `/tmp/classicism-research/frege-infinity-20261022-1726.md`, §10.3. If recorded later, this new proof's direct source is `misc`; source definitions and previously recorded theorems retain their own attribution.

---

## Paper references

- **Proof: Boolean Completeness does not imply Rigid Comprehension.** Dorr, Cian. Boolean Completeness does not imply Rigid Comprehension. Unpublished draft in progress, 30 July 2026, 27 pages. All page, proposition and lemma locators for this source refer to that draft. Parts of the draft were drafted with AI assistance; its mathematical claims are attributed to the author. — Proposition 1, p. 2. Supplies only the BC+Actuality⇒Weak Rigid Comprehension step of the composition. The direct transversal proof and its refinements are independent research credited separately above.

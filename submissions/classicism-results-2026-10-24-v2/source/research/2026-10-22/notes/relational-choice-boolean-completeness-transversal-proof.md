# Relational Choice and Boolean Completeness imply Transversal Choice

22 October 2026. Original scratch proof by the OpenAI Codex research agents in the extension and quotient lanes, with a separate algebraic audit by the coordinating agent. No human check or Lean formalization is claimed. No map record has been edited. This addresses the existing conjecture `relational-choice-and-boolean-completeness-imply-transversal-choice`, attributed in the map to Zachary Goodsell, 27 September 2026. The proof below is new evidence, not a proof attributed to Goodsell or to a published source.

## Exact claim and conventions

For any type σ, including e, the following instances suffice over C:

* Boolean Completeness at the relational type ρ:=σt.
* Relational Choice with both input and output type ρ.

They imply Transversal Choice at σ. Consequently the full schemata satisfy

    C ⊢ Relational Choice + Boolean Completeness → Transversal Choice.

All hypotheses and the conclusion are unboxed. No Necessity of Distinctness, Actuality, BF, Plenitude, Functionality, or extensional identification of coextensive properties is used. We use the LUB form of Boolean Completeness, equivalent in C to its recorded GLB form. Every set-like collection below is an admitted predicate, and every union or image is given by existential quantification. All order-theoretic reasoning takes place at the evaluation point.

At relational type τ, ≤ is the algebraic Boolean order. For propositions p,q, p≤q is equivalent to □(p→q). At a property type σt, F≤G is equivalent to □∀x(Fx→Gx). The latter is used only when it follows from the algebraic order; no converse-Barcan interchange is made.

## 1. Evaluation preserves represented algebraic joins

Fix x^σ. Evaluation e_x(F):=Fx is an order map B_{σt}→B_t and has the C-definable right adjoint

    r_x(p):=λz^σ.(z=x→p).

Indeed,

    F≤r_x(p) iff Fx≤p.                                  (1)

The formulas ∀z(Fz→(z=x→p)) and Fx→p are logically equivalent by equality substitution and universal instantiation. Logical Equivalence and the definition of algebraic order give (1). This is a theorem of C, valid without ND or BF.

Suppose Q is an algebraic LUB of a represented family C^{ρt}. Then Qx is a LUB in B_t of the represented evaluation image

    V_x(p):=∃F(CF∧p=Fx).

It is an upper bound because F≤Q implies Fx≤Qx. If p bounds every Fx with CF, (1) makes r_x(p) an upper bound of C; hence Q≤r_x(p), and Qx≤p by (1). Thus evaluation preserves this join. This argument does not separately assume Boolean Completeness at t.

## 2. A chain-complete poset of partial transversals

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

## 3. Every nonfull partial transversal has a strict extension in P

Say

    Full(F):=∀x∃y(Rxy∧Fy).

Suppose P(F) and ¬Full(F). Choose x whose actual R-cell contains no F-instance. Put

    q := ∀z(Fz∧(Rxz∨Rzx)→z=x),
    G := λy.(Fy∨(y=x∧q)).                              (4)

Actually q is true: actual symmetry of R makes either R-direction describe x's cell, and that cell has no F-instance. Actual reflexivity gives ¬Fx. Hence Gx is true and Fx false, so G≠F. The defining formula gives F≤G by a theorem of C; thus F<G.

Also P(G). For arbitrary actual u,v, expand Gu∧Gv into four cases under the box. If both conjuncts come from F, the required implication follows from P(F) at u,v. If both come from the new summand, u=x=v. If exactly one comes from the new summand, q rules out a distinct old F-member related in either direction to x. These are logical implications using equality substitution and instantiation of q; they do not require R to be an equivalence relation at other worlds. Consequently □(Gu∧Gv∧Ruv→u=v), and universal generalization gives P(G).

The two R-directions in q are deliberate. They avoid using necessary symmetry of R, which is not a premise.

## 4. Relational Choice supplies a progressive functional graph

On entities F,G of type ρ define a serial relation U by the following exhaustive cases:

* If P(F) and ¬Full(F), require P(G) and F<G.
* Otherwise require G=F.

Section 3 proves seriality in the first case; reflexivity supplies the second. Relational Choice at (ρ,ρ) gives an actual functional graph f⊆U. On P this graph is total, single-valued, stays in P, and is progressive: F≤f(F). Here and below f(F) is explanatory notation for the unique graph value, **not** an assumption that the graph is represented by an operation. Every use can be expanded with an existential variable and the graph relation.

Moreover,

    P(F)∧¬Full(F) → F<f(F).                            (5)

It remains to obtain a fixed point of this progressive graph on P. The following lemma is available in C itself.

## 5. Internal Bourbaki–Witt lemma, without Plenitude

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

## 6. Completion of the conjectured implication

Apply the lemma to the poset P of §2 and the functional graph f of §4. Obtain F∈P with f(F)=F. By (5), Full(F). Thus every actual R-cell has an F-instance. Since P(F) implies actual at-most-one membership in each R-cell, F is an actual transversal of R.

R was any actual equivalence relation at any type σ. Therefore RC+BC implies TC in C, with the sharpened instance scope stated at the start.

## 7. Audit summary and limitations

The proof closes the actual-coextension gap by passing to unique **algebraic supremum entities**, not by equating coextensive property codes. The principal technical devices are evaluation's right adjoint, pointwise boxes in the definition of partial transversals, and a fixed-point theorem for functional graphs.

* No optional assumption is necessitated. Every boxed formula is either part of P(F), follows from the algebraic order, or follows from a theorem of C using its rules.
* No box is moved across a universal quantifier. The distinction between ∀xy□ and □∀xy is preserved throughout.
* The selected graph need not be represented by an operation. Relational Choice, rather than Functional Choice or Plenitude, suffices.
* The f-chain construction quantifies only over admitted predicates and uses admitted unions, images, predecessor properties, and intersections. It invokes no externally arbitrary subset or ordinal sequence.
* R is assumed to be an equivalence relation only actually. The symmetric guard in (4) handles other-world failures of symmetry.
* This is a new ordinary mathematical proof, checked by other agents but not yet by a human or a proof assistant. The existing conjecture record and its formalization status have deliberately been preserved.

## 8. Sharpening to Boolean chain completeness

Define ChainBC_τ, within the existing language of C, to say that every represented family of τ-entities totally ordered by the algebraic Boolean order has an algebraic LUB. This is weaker on its face than BC_τ.

The proof in §§1–6 only needs ChainBC_ρ: the family C in §2 is a chain, and no other Boolean join is assumed to exist. Therefore the exact stronger claim is

    C ⊢ RC_{σt,σt} + ChainBC_{σt} → TC_σ.              (7)

At the full-schema level, RC+ChainBC is in fact equivalent to RC+BC. One route is (7), followed by the recorded TC⇒Zorn. Given any represented S⊆B_τ, its property of upper bounds is nonempty (it contains 1), and every represented chain of upper bounds has an infimum by ChainBC and Boolean complementation. That infimum is still an upper bound of S. Apply Zorn to this property in the reverse Boolean order, using the standard invalid-code padding if the recorded whole-type formulation is required. Obtain a minimal upper bound u. For every other upper bound v, u∧v is another upper bound below u, so minimality gives u=u∧v, that is u≤v. Hence u is the required LUB.

The quotient lane supplies an even more local argument, requiring only RC_{τ,τ}+ChainBC_τ. For a fixed represented S let

    P(b):=∀u(UpperBound_S(u)→b≤u).

This cut contains 0 and is closed under represented chain joins. If b∈P is not an upper bound of S, choose x∈S with x≰b; then b∨x∈P and b<b∨x. RC selects a progressive functional graph on P, strict unless its input is an upper bound. The fixed-point lemma yields b both below every upper bound and itself an upper bound, hence a LUB of S. Thus

    C ⊢ RC_{τ,τ} + ChainBC_τ → BC_τ.                  (8)

This local upgrade uses no Boolean complements: the same argument works for an internally represented bounded join-semilattice with represented binary joins and joins of represented chains. It explains structurally why Relational Choice removes the apparent gap between Boolean chain completeness and Boolean completeness in the conjecture's premise set.

### Technical further weakening

The self-contained fixed-point proof in §5 calls the completeness premise only for the union A of all f-chains, which it has already proved internally well-ordered, and for the empty chain/least element. The LUB assertions in the definition of an f-chain are hypotheses on that chain and are inherited by the union; their existence is not independently assumed for every possible predecessor family. Consequently all the preceding results remain valid if ChainBC_τ is weakened to the existence of LUBs only for represented families which the Boolean order itself internally well-orders. This is an internal well-order condition, not a schema ranging over externally standard ordinals. The chain-complete formulation remains the simpler main statement.

## 9. Immediate corollaries and scope of new evidence

The recorded implications TC⇒RC and TC⇒Zorn/Well-Ordering now show that, in the presence of BC, Relational Choice, Transversal Choice, Zorn, and Well-Ordering are equivalent. This is a new consequence of the proof, not something already present in the unchanged derived map. Necessitating the discharged C-implication also gives □RC+□BC⇒□TC, with no unboxed premise being necessitated.

At the graph level, the ordinary Boolean homomorphism extension proof in `retraction-extension-lane.md`, §1, now needs only RC+BC: the new theorem supplies Zorn, and the maximal partial homomorphism is already a total single-valued relation. An **operation** representing that graph still requires Plenitude. No graph-to-operation upgrade is being silently inferred from RC+BC.

The recorded `full-two-object-chain` supplies a concrete check on this distinction. It satisfies □Relational Choice and □Rigid Comprehension, hence □BC, but its root proposition {identity at W0} is distinct from bottom and becomes bottom after the arrow W0→W1. Thus ND_t fails at the root, and Plenitude fails by the recorded implication Plenitude⇒ND. RC+BC therefore does not supply the operation representation that the graph-level extension theorem lacks. This is existing model evidence, not a new countermodel construction.

### Final witness normalization: necessary partiality

There is a simple optional strengthening of the final witness. For arbitrary R and T define

    Pur_R(T)(x):=T(x)∧∀y(T(y)∧Rxy→x=y).

C proves, as a logical theorem about this displayed term,

    □∀xy(Pur_R(T)(x)∧Pur_R(T)(y)∧Rxy→x=y).

Indeed, at any point the first conjunct at x supplies the universal condition, while the first conjunct at y supplies T(y). If T is an actual partial transversal, its defining at-most-one condition also shows Pur_R(T) and T are actually coextensive. Therefore the actual transversal obtained in §6 can be replaced by a witness F which is necessarily partial under a full outer □∀, while still meeting every actual R-cell exactly once. No BF or additional choice/completeness instance is used.

This is a FINAL witness normalization only. It does not strengthen P in §2: the algebraic chain-join argument there still establishes only pointwise boxed independence, and its quantifier-scope warnings remain essential. The same normalization shows directly that the all-type Transversal Choice schema is equivalent to its version requiring necessarily partial witnesses.

## Consolidated handoff and subsequent refinements

The live exact-scope index for this research lane is `structural-lane-handoff.md` in the same directory. In particular, the independent audit sharpened the choice premise to RC_(σt,σ) by constructing an explicit guarded progressive operation; its proof is in `rc-guarded-progressive-operation.md`. The index also records the separately audited countable-completeness/CCC bridge and countable Boolean-type finiteness results. None of these scratch additions changes the repository's records or generated state.


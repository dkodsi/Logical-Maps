# RC alone versus TC: higher-type and Henkin-construction audit

OpenAI Codex research subagent, 22 October 2026. New mathematical arguments and conditional results, not database edits, a countermodel, a literature claim, or Lean verification. RC means Relational Choice throughout.

## Status

The unrestricted implication RC⇒TC is not settled here. Three useful restrictions emerge:

1. A large natural countermodel class is ruled out: in every one-object **symmetric ideally-full finite-pinning model**, RC at (τt,τ) forces some finite pin stabilizer to act trivially on the whole τ-domain. That supplies canonical codes for every actual subset of τ and proves TC at τ. If the individual domain is the pinning carrier, the individual instance gives the stronger statement that the symmetry group has a finite base. This applies beyond the all-surjection cases with Boolean Completeness and includes the single-individual variants; see §1.4.
2. Any RC/TC separator has a specifically definable internally well-ordered chain of algebraic partial selectors with **no algebraic supremum**. Completeness for represented well-ordered chains already suffices, not just completeness for arbitrary chains.
3. Any uniform **operation-valued** coding of actual coextension classes, even at arbitrarily high relational output type and using chosen RC witnesses as parameters, implies Actuality. The recorded RC+¬Actuality model therefore rules out that entire form of finite higher-type strategy. Relation-valued coding is not ruled out and is exactly where the open issue remains.

A fourth, finite-range lemma quantifies how badly an arbitrary chooser must fail on copies of one cell in a separator.

## 1. A no-go theorem for symmetric ideally-full finite-pinning constructions

### Hypotheses

Use the one-object version of Dorr's symmetric ideally-full construction, as spelled out in `topics/classicism/writeups/symmetric-infinite-classes.md`, §The model and §Notation and basic facts. Let I be both the individual set and the pinning carrier; M a monoid of arrows acting on I; and G⊆M a group of permutations acting as the symmetry group. Relational domains contain **every** symmetric intension pinned by some finite subset of I. The relevant formulas are

    (h·A)_k = A_(k∘h),
    A_(g∘w) = g·A_w              (g∈G),

and pinning by N means h·A=h'·A whenever h,h' agree on N. Evaluation is at the identity arrow. All higher-type actions are those supplied by the construction.

No assumption that M consists of all surjections is used below. No BC premise is used. The individual-domain/pinning-carrier identification matters: this argument is not asserted for single-individual variants whose arrows and pinning sets live on an auxiliary infinite set, or for multiobject categories. The theorem does use ideal fullness, including the presence of intensions defined externally from stabilizer fixed sets; it is not claimed for arbitrary small Henkin subdomains.

### Lemma 1.1: the individual-property selector forces a finite base

Assume the RC instance which selects an individual from every nonempty individual property: an actual functional S below

    U(A,y) := Ay ∨ ¬∃z Az.

This instance follows from RC at (et,e). Let N be a finite set pinning S. For a finite T⊆I write

    G_T = {g∈G : g fixes T pointwise},
    Fix(G_T) = {a∈I : every g∈G_T fixes a}.

Define a property intension A by

    A_w := I \ Fix(G_(w[N])).                         (1)

This intension is admitted:

* It is pinned by N. If h,h' agree on N, then (k∘h)[N]=(k∘h')[N] for every k, so A_(k∘h)=A_(k∘h'). Thus h·A=h'·A.
* It is symmetric. Since G_(gT)=g G_T g^{-1}, its fixed set is g Fix(G_T). Hence A_(g∘w)=g A_w.

In particular

    A_1 = I \ Fix(G_N).

Every g∈G_N fixes S and A as entities, by pinning. If A_1 is nonempty, the selector supplies y∈A_1 with S(A,y) at the identity. Symmetry of S transports this to S(g·A,g·y) at the corresponding extension, and pinning of S at g (g agrees with the identity on N) returns it to the same actual extension. Since g·A=A, actual functionality gives g·y=y. This holds for every g∈G_N, so y∈Fix(G_N), contradicting y∈A_1.

Therefore A_1 is empty: every g∈G_N fixes every individual. Since G is literally a group of permutations of I, G_N={1}. Thus N is a finite base for G.

This argument remains valid if Fix(G_N) is infinite. Adding successor operations within classes, infinitely many named defaults, or other qualitative structure does not repair the obstruction in an ideally-full construction: (1) simply excludes the *entire* pointwise-stabilizer fixed set, rather than only the finitely many originally pinned points.

### Lemma 1.2: a finite base gives actual extensional fullness at every type

Suppose G_N={1} for a finite N. Fix any external subset E of tuples from the actual domains of an admitted relational type. Define its intension B by

    B_w := g·E, if there exists g∈G with w|N=g|N;
           ∅,  otherwise.                            (2)

Such g is unique: two candidates differ by an element of G_N. Hence (2) is unambiguous. It is pinned by N, since its value depends only on w|N, including after precomposition. It is symmetric: w|N=g|N iff (h∘w)|N=(h∘g)|N for h∈G, with the negative case preserved as well. Its extension at the identity is E. Ideal fullness therefore puts B in the appropriate domain.

The proof works at arbitrary relational type, since G acts on every tuple domain. Thus every actual relation extension has a representative.

### Corollary 1.3: this class cannot separate RC and TC

Under full RC, first use Lemma 1.1, then Lemma 1.2. In the ordinary ZFC metatheory, every actual equivalence relation has an external transversal set, and Lemma 1.2 represents it immediately. Thus TC holds.

The use of external choice can also be avoided if desired: the construction (2) canonically represents each external actual subset by a unique prescribed intension. Given an actual equivalence relation, form these canonical intensions for its actual cells; the relevant RC property-selector chooses once from each canonical cell intension. Its chosen-element set is a transversal and (2) represents that set. This uses the assumed internal RC rather than a separate metatheoretic choice principle.

This no-go covers the stated one-object symmetric ideally-full finite-pinning construction with base individuals, even when its arrow monoid does not provide BC. It is different from the existing full hereditarily symmetric hierarchy argument: here the special excluded-fixed-set intension (1), plus pinning, directly forces a finite group base.

### 1.4 Stronger, type-local theorem: the individual/pin-carrier restriction is unnecessary

The preceding finite-*base* conclusion needs the carrier identification, but the no-go for RC versus TC does not. The following stronger formulation was independently reached by the coordinating agent and this auditor.

Keep a one-object pinning carrier I, monoid M, symmetry group G, and the symmetric ideally-full hierarchy. Let τ be ANY admitted type; its domain D_τ need not be I. The induced action of G on D_τ is by bijections, because transport by g^{-1} is inverse to transport by g.

Assume RC at (τt,τ), and let S select from every nonempty τ-property. Let finite N⊆I pin S. For finite T⊆I, put

    Fix_τ(G_T) := {a∈D_τ : every g∈G_T fixes a}.

Define the τ-property intension

    A_w := D_τ \ Fix_τ(G_(w[N])).                     (3)

It is N-pinned exactly as in Lemma 1.1: h|N=h'|N implies (kh)[N]=(kh')[N] for every k. It is symmetric because the group representation on D_τ gives

    Fix_τ(G_(gT)) = g·Fix_τ(G_T),

using G_(gT)=gG_Tg^{-1}. This requires invertibility only of g, never of w. If w collapses members of N, w[N] is simply the finite image set; all the equations remain valid. Ideal fullness at τt admits A.

Every g∈G_N fixes S and A by pinning. If A_1 were nonempty, S would choose y∈A_1. Symmetry and pinning return S(A,y) to S(A,g·y) at the actual point; functionality forces g·y=y for every g∈G_N, contradicting y∈A_1. Hence

    G_N acts pointwise trivially on D_τ.              (4)

It need not act trivially on I. Therefore (4) covers single-individual variants with a separate infinite pinning carrier.

For any actual subset E⊆D_τ define

    B^E_w := g·E, if w|N=g|N for some g∈G;
             ∅,   otherwise.                         (5)

The matching g need not be unique, but (5) is well-defined: if g_1,g_2 match, g_2^{-1}g_1∈G_N, which acts trivially on every member of D_τ by (4). Thus g_1·E=g_2·E. Pinning and symmetry follow exactly as before, and B^E_1=E. Ideal fullness therefore admits B^E as a τ-property. The assignment E↦B^E is an externally specified canonical construction: identical subsets yield literally identical intensions.

Now let R be any actual equivalence relation on D_τ. For each actual cell E, apply the ALREADY OBTAINED S to its nonempty canonical property B^E; let y_E be the unique selected element. The set T={y_E:E is an actual R-cell} exists by ordinary Separation/Replacement and consists of exactly one member of each cell. No metatheoretic choice axiom is used: S and the canonical (5) determine y_E uniquely. The admitted property B^T is the required transversal.

Thus, within this model class,

    RC_(τt,τ) implies TC_τ,

for each admitted τ separately. Full RC implies full TC. No common finite N for all types is asserted or needed. The earlier finite-base theorem is the special case τ=e with D_e=I and faithful permutation action.

This remains a ONE-OBJECT theorem. For a multiobject category, the target domain in A_w varies with w and the stabilizer/conjugation construction needs an additional coherent family of groups; no such generalization is claimed here. Nor is the theorem asserted for smaller Henkin subdomains: its decisive admissibility premise is ideal fullness at τt.

### Precise obligation for a smaller Henkin tower

A viable symmetric countermodel must omit at least one intension of the form (1), for every candidate global selector support N that leaves some individual movable. Merely showing that the seed language has Skolem functions is insufficient: after adjoining a choice graph S, closing the next stage under all **symmetric finitely pinned** intensions immediately admits (1) and destroys RC. A genuinely smaller comprehension-closed Henkin domain could omit (1), because the external operation T↦Fix(G_T) need not be internally definable. Preserving that omission while adding selectors for every newly represented serial relation is the real extension lemma still needed.

## 2. Failure of TC produces a represented well-ordered missing join

Fix an actual equivalence R at type σ and put ρ=σt. Define

    P(F) := ∀x y □(Fx∧Fy∧Rxy→x=y).

Assume RC at (ρ,ρ) and suppose R has no transversal. The guarded-extension construction from the audited RC+BC proof uses no BC: every P-member has a strict algebraic extension in P. RC therefore supplies a progressive actual functional graph f:P→P with no fixed point.

Define an f-chain to be an admitted internally well-ordered C⊆P such that every x∈C is the algebraic supremum **within P** of the graph image

    {f(y): Cy and y<x}.

This definition does not assert that arbitrary joins exist. A singleton containing bottom is an f-chain. Comparison of f-chains uses only the uniqueness of the suprema asserted in their defining conditions. Therefore the existential union

    A(x) := ∃C (C is an f-chain and Cx)

is itself an admitted internally well-ordered f-chain. These are the comparison and union portions of the bare-C proof, which do not use chain completeness.

**Claim:** A has no ambient algebraic supremum in B_ρ.

If it had supremum u, evaluation's right adjoint and the two implication-adjunction steps from the partial-selector audit would put u in P. Thus u is also its supremum within P. The final two extension arguments of the fixed-point proof then apply: if u∉A, adjoin u after showing u=sup f[A]; if u∈A but u<f(u), adjoin f(u). Both contradict A's definition as the union of all f-chains. Hence f(u)=u, contrary to strict progressivity.

This is stronger than the bare statement that BC fails. Every RC/TC separator contains a missing join for a **represented internally well-ordered** family, canonically described from R and the selected progressive graph. No external transfinite iteration is required to form A; all quantification is over admitted properties of ρ.

**Conditional consequence.** RC at (σt,σt) plus the assertion that every represented algebraically well-ordered family at σt has a supremum implies TC at σ.

The same argument sharpens the previously established RC+ChainBC⇒BC reduction: at any relational τ, use P(b):=“b lies below every upper bound of the given family X,” and a strict progressive graph b↦b∨x at every b that is not already an upper bound of X. The f-chain union is well-ordered. If every represented well-ordered family at τ has an ambient supremum, that supremum belongs to P and yields a fixed point, hence sup X. Thus, under RC at (τ,τ), completeness for represented well-ordered chains is already equivalent to BC at τ.

This concerns internal well-ordering, quantified over admitted subproperties. It does not assume that an internal well-order is externally well-founded. A Henkin construction cannot appeal silently to external transfinite recursion to fill its joins.

## 3. Uniform higher-type operation codes would prove too much

The existing quotient notes prove that operation-valued canonicalization of actual coextension classes implies Actuality. The argument in fact permits an arbitrary admitted relational code type κ, not merely the same property type.

Suppose there is an operation q:t→κ satisfying

    q(p)=q(r) iff (p↔r)                    actually.   (3)

Define T(p):=(q(p)=q(⊤)). Then T(p)↔p actually. Necessity of Identity makes every true T(p) necessary. Put

    a := ∀p(T(p)→p).

Actually a is true. If p is actually true, then □T(p). The bare-C necessary universal-instantiation implication gives □(a→(T(p)→p)); combining yields □(a→p). Thus a entails every actual truth, i.e. Actuality.

Consequently any proposed uniform finite higher-type construction that turns an RC selector, or finitely many higher-type RC selectors, into an **operation** assigning equal code entities exactly to actual coextension classes would imply Actuality. Instantiate the construction on constant properties c_p=λz.p to obtain (3).

The recorded finite-support permutation model satisfies RC (indeed □RC) and fails Actuality; see `models/finite-support-permutations.yaml` and its group arguments. Thus no such unrestricted operation-valued construction follows from RC. This is a semantic obstruction to an entire strategy, not only the familiar failed row-code argument.

This does **not** rule out a functional *relation* assigning canonical representatives. That graph may fail to be represented by an operation. Indeed Transversal itself supplies such graph-valued canonicalization, and TC can hold while Actuality fails in the same finite-support model. A proposed proof must retain that distinction.

## 4. A finite-range reduction for an arbitrary chooser

Let S be any actual property-selector obtained from RC at (σt,σ). For an actual equivalence relation R and each x define

    M_x(y) := ∃A^{σt} [ (∀z(Az↔Rxz)) ∧ S(A,y) ].      (4)

The extension of M_x is nonempty and contained in x's cell. If Rxx', then M_x and M_x' are actually coextensive. This is true although their predicate entities need not be identical.

**Lemma.** If every M_x is internally Frege-finite, then R has a transversal.

Reason: bare C rigidifies every internally finite property, as proved in the existing scratch analysis `quotient-abstraction-lane.md`, §13.1. A rigid representative K_x of M_x is unique as an entity. Equivalent x,x' have coextensive M-properties, so their rigid representatives are identical. Apply the same selector S to K_x. These choices agree on each R-cell and lie in it, giving a transversal. All witnesses can be handled relationally; no operation assembling the K_x is needed.

**Countermodel restriction.** If RC holds and R has no transversal, then for *every* property-selector S there is some R-cell for which the choices made across all intensional copies of that cell form an internally nonfinite set. It is insufficient for the chooser merely to make two different decisions on coextensive inputs: uniformly finite ambiguity could be removed by rigidification.

One may iterate the saturation operation in (4) a fixed finite number of times, each time selecting from all property codes coextensive with the preceding range. The ranges remain nonempty, nested, and class-invariant in extension. If some fixed finite iteration produces internally finite ranges for every cell, the same rigidification argument gives a transversal. Therefore a separator must resist every such fixed finite compression for every selector. This supplies a concrete test for a proposed finite higher-type normalization, though it does not prove that any compression step succeeds.

## 5. What remains unresolved

No smaller Henkin tower satisfying all RC instances and failing TC has been constructed. The exact missing construction theorem would add selectors at every type while preserving a moving R-class with no admissible transversal, excluding stabilizer-complement intensions such as (1), and omitting the represented well-ordered supremum forced by §2. Conversely no finite higher-type relation construction has been found that removes the necessarily infinite chooser ambiguity of §4 without creating an operation-valued canonicalizer forbidden by §3.

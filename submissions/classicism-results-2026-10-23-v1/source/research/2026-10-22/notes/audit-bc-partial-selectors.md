# Hostile audit: Boolean partial selectors for RC + BC ⇒ TC

Audit by OpenAI Codex research subagent, 22 October 2026. This is a new mathematical audit of the scratch proof `.reproduction/classicism-research/relational-choice-boolean-completeness-transversal-proof.md`, not a published attribution, human check, formalization, or database edit.

## Verdict

The partial-selector construction is valid in the fixed relational-type framework C. In particular, I find no gap in (i) evaluation's adjoint, (ii) closure of the boxed-pair predicate under represented algebraic chain suprema, or (iii) the guarded strict extension. The self-contained functional-graph Bourbaki–Witt argument in the scratch proof also survives the independent check below. Subject to the usual correctness of C's recorded Boolean-algebra and Intensionality theorems, this supplies a mathematical proof of the existing conjecture RC + BC ⇒ TC, with no extra modal hypothesis.

The precise sufficient instances are BC at ρ = σt and Relational Choice at (ρ,ρ), for TC at arbitrary σ, including e. Here RC always means **Relational Choice**, not Rigid Comprehension.

## Recorded baseline and scope

Read `topics/classicism/AGENTS.md`, `topic.yaml`, the Framework/Notation/choice/order portions of `background.md`, the principles `relational-choice-r`, `transversal-choice-r`, `boolean-completeness-r`, `identity-necessary-r`, and the existing conjecture record `relational-choice-and-boolean-completeness-imply-transversal-choice`. That record is presently conjectured with no proof. The proof considered here is new evidence; it is not extracted from that record.

Relevant standing facts are:

* Every relational type is a Boolean algebra under the algebraic order.
* At σt, F≤G iff □∀z(Fz→Gz); at t, p≤q iff □(p→q).
* H-theorem equivalences can be used under the rules of C; equivalences derived from optional actual assumptions cannot simply be boxed.
* Equiv(R), Relational Choice and the requested transversal are actual, unboxed assertions.
* All families used below are admitted predicates. No arbitrary external collection is silently substituted for one.

## 1. Evaluation's adjunction is sound

Fix any actual x of type σ. Let e_x(F)=Fx and r_x(p)=λz(z=x→p). Then

    F≤r_x(p) ⇔ □∀z(Fz→(z=x→p)) ⇔ □(Fx→p) ⇔ Fx≤p.

The middle equivalence follows from the H theorem

    ∀z(Fz→(z=x→p)) ⇔ (Fx→p).

Left to right uses z=x and reflexivity. Right to left uses equality substitution. This is a theorem with F,x,p free, not an inference boxed under an optional assumption. Thus neither BF nor ND is being used, and the possible appearance of future entities does not invalidate the argument. The bound variable z ranges over the local domain wherever the theorem is evaluated, and x remains a legitimate argument there.

If Q is an algebraic supremum of a represented C-family, then Qx is the algebraic supremum of its represented evaluation image V_x(p):=∃F(CF∧p=Fx). For any proposed bound p, the adjunction takes all inequalities Fx≤p (for current CF) to F≤r_x(p), then Q≤r_x(p), then Qx≤p. This proof needs no completeness premise at t. It proves that the relevant join exists at t using the one already obtained at σt.

## 2. Chain completeness of P is sound

Set

    P(F) := ∀x y □(Fx∧Fy∧Rxy→x=y).

The order is the actual algebraic Boolean order, which is antisymmetric on entities. Let C collect P-members and be a chain in that order, and let Q be its ambient supremum supplied by BC at σt.

Fix actual x,y and put k=(Rxy→x=y). For current F,G in C, comparability gives

    Fx∧Gy≤k.

If F≤G, then Fx≤Gx and the assertion follows from P(G) at the actual x,y. If G≤F, use Gy≤Fy and P(F). This is an actual case split between algebraic inequalities, not a claim that the chain predicate or its members remain a chain at every world.

For fixed current F in C, every Gy lies below Fx→k. By §1, Qy is their supremum, hence Fx∧Qy≤k. Now every current Fx lies below Qy→k; a second application of §1 gives Qx∧Qy≤k. Therefore

    □(Qx∧Qy∧Rxy→x=y).

Generalize over actual x,y to get P(Q). No infinite distributivity axiom was presumed: the two steps are the finite Boolean adjunction a∧b≤c iff b≤a→c applied to the join's universal property. The proof uses neither □∀xy nor any interchange ∀□⇒□∀. Empty C causes no exception: its supremum is bottom, and the same universal-property argument works.

The chosen definition of P is consequential. Strengthening it to □∀xy(...) would demand control over nonactual argument pairs and would not be established by this proof. Replacing algebraic order by actual inclusion would destroy uniqueness of supremum *entities* and undermine the fixed-point construction. Neither change is made here.

## 3. The guarded strict extension is sound

Assume P(F) and an actual x whose R-cell has no F-instance. Define

    q := ∀z(Fz∧(Rxz∨Rzx)→z=x),
    G(y) := Fy∨(y=x∧q).

Actual symmetry makes q true: either R-direction at the evaluation point places z in x's missed cell. Actual reflexivity gives ¬Fx, and therefore Gx∧¬Fx. Consequently G≠F by ordinary substitutivity of identity. The H theorem Fy→G(y), universally closed and used through the algebraic-order characterization, gives F≤G. Thus F<G; no extensionality axiom is needed to infer nonidentity from a difference of actual instances.

For the P assertion, fix arbitrary actual u,v. There is an H theorem, uniformly in the free parameters,

    (Fu∧Fv∧Ruv→u=v)
        → (Gu∧Gv∧Ruv→u=v),

with G and q expanded as above. The proof is a four-case Boolean expansion:

* Both old summands use the displayed antecedent.
* Both new summands give u=x=v.
* If u=x and q, while Fv and Ruv, instantiate q at v and use Rxv to get v=x.
* If v=x and q, while Fu and Ruv, instantiate q at u and use Rux to get u=x.

Necessitate this H theorem and combine it with the already supplied boxed antecedent from P(F). This yields the required box for G. **The actual truth of q is never necessitated.** At another world the new summand is present only if q is true there, which is exactly when its local universal constraint protects the extension. Identity collapse is harmless: the cases use local equality substitution, and q can turn false where a conflicting old member would appear. No necessary symmetry, reflexivity, transitivity, or distinctness has been inferred from their actual counterparts.

The two R-directions in q are essential to this particular uniformly valid proof: using only Rxz would leave the case with v=x unsupported where R is asymmetric.

## 4. The graph interface is sound

The serial relation on the *whole* ρ-domain asks for a strict P-extension on nonfull P-inputs and asks for the input itself otherwise. Section 3 proves seriality. The (ρ,ρ) Relational Choice instance therefore gives an actual total single-valued subrelation f. Restricted to P, its graph remains in P, is progressive, and is strict at each nonfull input.

Nothing here promotes an actual functional graph to an operation. Formulas for images are ∃y(Cy∧f(y,z)), and all occurrences of f(y) in prose can be expanded with a graph variable and its actual uniqueness assertion. The graph is required to respect actual identity of input entities, which ordinary identity substitution provides. It need not respect actual coextension of input properties, and the proof never claims that it does.

## 5. Independent check of the fixed-point lemma

I checked the self-contained f-chain proof in the scratch file, in addition to the recorded Lewin translation's warning about coextension. Its use of f-chains avoids that warning because it applies the graph to the predecessor *entities*, then uses unique suprema of the resulting actual graph images.

An f-chain is an admitted internally well-ordered property C⊆P satisfying: every x∈C is the supremum in P of {f(y): y∈C, y<x}. This condition is a formula about a supremum; it does not require a choice operation assigning suprema. The singleton of the least element satisfies it.

For comparison, the shared initial segment I of two f-chains is defined by common membership and actual coextension of predecessors. It is initial in each chain. If both complements are nonempty, their least members c,d have predecessor extensions exactly I. Their graph-image extensions consequently coincide, so the supremum property and antisymmetry give c=d as entities. This contradicts their exclusion from I. This step equates neither predecessor predicate codes nor graph-image predicate codes.

The existential union A of all f-chains is an admitted property. Comparison makes it a chain. The standard least-member proof uses the admitted intersection of any tested subproperty with one f-chain containing one of its members. This suffices for internal well-ordering and requires no external well-foundedness. For each x∈A its predecessors coincide in extension with its predecessors in any f-chain containing x, so A satisfies the f-chain condition.

Let u=sup A. If u∉A then A has no greatest member. For each x∈A there is y∈A with x<y, whence f(x)≤y≤u by the f-chain condition at y. Progressivity shows that every bound of f[A] bounds A, so u=sup f[A]. Adjoining u gives an f-chain larger than the union of all f-chains, a contradiction. Hence u∈A. If u<f(u), then f(u) is the largest element of f[A]: for x<u the f-chain condition at u gives f(x)≤u, while the value f(u) itself belongs to f[A]. Adjoining f(u) again gives an f-chain contradicting the upper-bound property of u. Thus f(u)=u.

All tested subproperties, differences, intersections, unions, graph images, and singleton adjunctions are admitted comprehension terms. The proof needs neither choice of a family of witnesses nor an externally indexed transfinite sequence. This is sufficient to complete RC+BC⇒TC using §4.

## 6. Limits of this audit

This is an ordinary mathematical audit, not Lean verification or a human referee report. No database record, generated export, or source proof has been edited. The RC-alone conjecture remains unsettled by this argument: BC is used to turn represented chains into unique algebraic supremum entities. Actual existential unions provide only coextensive upper bounds, not those unique entities.

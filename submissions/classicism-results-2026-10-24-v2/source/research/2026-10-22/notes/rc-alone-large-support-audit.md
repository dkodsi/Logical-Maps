# Relational Choice and larger supports: a controlled obstruction audit

OpenAI Codex research note, 22 October 2026. Ordinary mathematics only. This does not construct a model of C or settle Relational Choice ⇒ Transversal Choice. It continues the ruled-out semilinear seed in `rc-alone-skolem-seed-audit.md` and the finite-support obstruction in `rc-alone-shear-obstruction.md`.

## 1. What changes when supports become infinite

Keep the latter note's individual domain M=V⊕Q, H=Qh, named c=(v₀,0), addition/order/H intensions, exact standard-natural predicate N_h, and shear automorphisms g_f(v,q)=(v,q+f(v)). Suppose a chooser S is fixed by the subgroup G_A fixing an arbitrary, possibly infinite, set A of individuals. Then

    Fix_M(G_A) = span_Q(h,c,A).

The linear-algebra equality does not require A to be finite: a linear functional separating a vector outside the indicated span gives the converse, in the ordinary ZFC metatheory. But the previous proof's **definability** of that span used a finite tuple of parameters. Merely increasing the permitted support cardinal therefore removes that particular definability argument.

There is an immediate conditional no-go at every support size:

> If the exact intension F_A for M minus span_Q(h,c,A) is admitted and fixed by G_A, and this complement is nonempty, no actual functional chooser S fixed by G_A can choose from all nonempty admitted predicates.

Indeed its choice at F_A would be fixed by G_A, contradicting membership in F_A. Thus ideally full symmetric domains still fail, regardless of whether supports are finite, countable, or of size below an uncountable cardinal. Any escape requires a genuinely restricted domain omitting the relevant intension, not only a larger support ideal.

## 2. A chooser defines a countable independent sequence

There is a further consequence of the seed's arithmetic closure which is useful for testing a restricted-domain construction. Assume S is an actual functional choice graph for

    U(P,y) := Py ∨ ¬∃z Pz.

All functions below are relational shorthand, and all new predicates are supplied by C's lambda constructions. The argument uses no forbidden function type with output e.

From the earlier paired-ancestral proof, QMult(x,y) says exactly that y is a rational multiple of x. For P of type et and a of type e define the deterministic term

    Join(P,a) := λz ∃p q (Pp ∧ QMult(a,q) ∧ z=p+q).

Let P₀ be the canonical lambda term defining span_Q(h,c). Define

    Step(P,P′) := ∃a (S(λy ¬Py,a) ∧ P′=Join(P,a)).

At the actual point S is functional, so Step has exactly one successor at every P; it is not claimed to be functional at future worlds. Externally form the ordinary finite iterates Pₙ and their choices aₙ. Whenever M has infinite Q-dimension, the actual extension of Pₙ is span_Q(h,c,a₀,…,aₙ₋₁), and aₙ is outside that span.

The finite iteration is internally represented, even though its length is unbounded. Define Iter(n,P) as membership of (n,P) in every admitted relation T of type e(et)t which contains (0,P₀) and is closed under

    (u,Q) ↦ (u+h,Q′) whenever Step(Q,Q′).

For each standard m, external finite induction gives Iter(mh,Pₘ). Conversely the admitted finite formula

    T_m(u,P) := [∨_{j=0}^m (u=jh ∧ P=Pⱼ)] ∨ u>mh

contains the base and is successor-closed, because Step is actually deterministic. At first coordinate mh it contains only Pₘ. Hence Iter(mh,P) iff P=Pₘ. Since N_h is exactly the standard natural multiples, the lambda term

    L_S(y) := ∃n P (N_h(n) ∧ Iter(n,P) ∧ Py)

has actual extension

    span_Q(h,c,a₀,a₁,…).

It is a countable-dimensional subspace and its **intension** is fixed by every automorphism fixing S and the named seed intensions/parameters. Each Pₙ and aₙ is fixed by the same group, by actual functionality and finite induction.

If L_S is a proper subspace, S also selects a point a_ω from its complement. This point is fixed by the same group and lies outside the entire countable span. The construction can be restarted with the enlarged finite list of named parameters or with the predicate L_S as an additional parameter.

This is a real extra burden on a proposed chooser, but it is **not** a contradiction for a chooser whose stabilizer fixes an uncountable-dimensional subspace. Nor does it prove a contradiction merely because the fixed subspace is countable-dimensional: the particular countable sequence need not exhaust it. A countable-dimensional space can contain a proper countable-dimensional subspace, and adding one further independent vector does not change its cardinal dimension.

## 3. The exact equivariant-selection condition

For any group K acting on input and output domains, and any K-invariant serial relation U, a K-equivariant selector exists exactly when every input x has a witness y in its U-fiber fixed by the stabilizer K_x, provided external orbitwise choices are available. Necessity follows from functionality. For sufficiency, choose one representative x from each K-orbit and one K_x-fixed witness y; define the value at kx to be ky. The fixed-point condition makes the definition independent of k.

In a support construction one applies this with K=G_B for the proposed selector's enlarged support B. This is an external graph theorem. A C-model construction must additionally prove that an appropriate **intension** for that graph is admitted, has the stated support, and respects the identity and logical-equivalence requirements.

More seriously, the condition must hold on the **completed** input domain. A selector satisfying it for today's predicate codes need not extend after comprehension with that selector as a parameter adds tomorrow's predicates. The L_S construction above is a concrete example of this feedback: it creates a new invariant property using S itself. Adjoining selectors first and closing formulas afterward does not establish all-type Relational Choice.

A sufficient preservation theorem would therefore have to ensure, uniformly through closure, that every new nonempty input fiber has a witness fixed by the stabilizer of its final code together with the proposed selector support. No such theorem has been established for the semilinear/shear seed, countable supports, or a below-κ support ideal.

## 4. Why extracting all of S's support is not automatic

The range of S on all predicate codes is all of M, since singleton predicates occur. It therefore does not identify S's support. Restricting S to predicates built from already recovered fixed points gives the countable closure in §2, not a proof that every fixed point is recovered.

The external set of elements definable from S is fixed pointwise by its stabilizer. That observation alone does not make the set an admitted predicate. Definability ranges over formulas of arbitrarily high finite simple type. A satisfaction construction for a fixed finite collection of sorts, if successfully supplied, takes place at a higher type; the predicate it produces and the new value selected from its complement need not belong to the language whose definable closure it describes. A uniform truth or coding theorem spanning the entire unbounded type hierarchy is an additional obligation, not part of the finite-span argument.

Consequently there is presently neither a verified large-support construction nor a general theorem that the chooser itself defines its entire stabilizer fixed set. The safe conclusion is narrower: this semilinear seed with finite supports, and the support constructions that admit the exact moved-element intensions, are ruled out; larger supports in genuinely restricted Henkin domains remain an unproved route, with the completed-domain stabilizer-witness condition above as the critical preservation target.

## 5. Externally fixed reservoirs and the Skolem-syntax trap

A more controlled variant fixes an externally chosen large subspace W₀ pointwise and uses automorphisms over W₀. Then

    Fix_M(G_A) = (W₀ + span_Q(proj_V A)) ⊕ Q.

If W₀ is not itself represented by an admitted predicate or internally available enumeration, the finite-span complement from the original no-go can have many fixed witnesses in W₀. The algebraic obstruction is therefore genuinely removed at that point. This is a candidate invariant, not a constructed model.

Ordinary first-order Skolemization is not a ready-made preservation theorem for it. In a first-order expansion, one can externally add a function selecting witnesses from each serial relation. But if the selecting terms can occur in the object language and can be lambda-abstracted at every relational output type, they give **Functional Choice**, not just Relational Choice. The proved local chain is

    Functional Choice ⇒ Plenitude ⇒ Actuality,
    Functional Choice ⇒ Relational Choice,
    Actuality ⇒ Transversal,
    Transversal + Relational Choice ⇒ Transversal Choice.

I verified this through the proved-only Engine and the records defining Functional Choice and Plenitude. Thus a construction intended to refute TC cannot admit an internal ε-operation returning arbitrary relational-type entities. External witness labels may be used in a metatheoretic construction, but their evaluation must not silently become a typed operation in the object language. Admitting only the selector graph avoids that immediate implication; it does not prove the needed closure properties.

There is a second, separate nonconservative step. Adding a new graph symbol to an ordinary first-order structure can preserve its old reduct. Reifying that symbol as an element of an already quantified relational type, and then closing under lambda terms involving it, enlarges the domain of the old higher-order quantifiers. Old formulas about every predicate can change truth. The first-order conservative-extension theorem says nothing about that enlargement.

A possible preservation condition would assert that every admitted nonempty predicate with finite presentation parameters A has a suitable witness in W₀+span(A), with enough of the presentation recoverable from its intensional identity for equivariant choice. The semilinear first-order seed has a parameter-wise witness property of this kind. Neither the quotient of syntax by H-equivalence nor all higher-type quantifier closure has been shown to preserve it.

Making the fixed-point objects into a full elementary submodel of a known C+TC model is not a solution: TC then transfers. Nor can one simply assume a many-sorted elementary fixed-point structure satisfying C+RC+¬TC as the starting point; that assumes the unresolved consistency problem. A useful compactness argument would need explicit models for the finite fragments containing the no-transversal assertion, the requested relational-choice instances, and all relevant lambda/quantifier constraints. No such finite-fragment family is supplied here.

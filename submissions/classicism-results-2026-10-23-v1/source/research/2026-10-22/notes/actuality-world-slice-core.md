# Ordinary extensional mathematics in an actual-world slice

Research theorem, 22 October 2026 (`misc`). The world-slice construction was proposed by the choice lane and developed here. It is a LOCAL interpretation in fixed C, not a claim of necessary or globally rigid mathematics. No external fullness, formal verification, or literature novelty is claimed.

## 1. Actuality is localized extensionality

Assume Actuality and choose its witness w. Thus w is true and every current true proposition p satisfies w<=p. Equivalently w is a true propositional atom. This assumption is unboxed; w may become bottom later.

**Localization lemma.** If relations F,G are supported by w, meaning F<=lambda xbar.w and likewise G, and are currently coextensive, then F=G.

The universal coextension proposition forall xbar(Fxbar iff Gxbar) is currently true, so Actuality puts it above w. Necessarily, where w holds the two relations agree on every tuple, including tuples first appearing there; where w fails both relations are false by support. Therefore their necessary universal coextension holds, and Intensionality gives identity. No BF or separate movement of a quantifier under a box is used: Actuality applies to the already universally quantified true proposition.

Conversely, suppose w is true and the localization conclusion holds even just for propositions. For any currently true p, the supported propositions w and w∧p are both true, hence coextensive, so w=w∧p and w<=p. Thus w witnesses Actuality. Accordingly Actuality is exactly extensionality localized below some true proposition; its nullary instance suffices, and all-type localization follows.

## 2. The supported hierarchy

Let the target truth value called true be w, and false be bottom. They are distinct now. Define H_e(x):=w, so every current individual belongs to the target individual domain. For tau=sigma_1...sigma_n t, recursively define

    A_tau(xbar):=w and conjunction_i H_sigma_i(x_i),
    H_tau(F):=w and F<=A_tau.

For the empty tuple A_t=w. Since w is an atom, H_t currently consists exactly of bottom and w. Every relational domain is nonempty, containing its bottom object and its supported top A_tau. Every H and A is w-supported. These definitions are finite metalinguistic recursion on the original allowed relational types; there is no quantification over types and no function type ending in e.

A current core relation F at sigma tau is supported on H_sigma times the support for tau. For any fixed current core a, its section F(a) therefore entails A_tau. It belongs to H_tau. This proves application closure without a rigidity argument: support, rather than TwoVal or rigidity, is the defining condition.

If two current core relations agree on all current core tuples, they agree on all current ambient tuples because they both vanish outside A_tau. The localization lemma then makes them identical. Thus the target has ordinary extensionality, with inherited literal identity of its objects.

All these are assertions about the current interpreted domains. At a future point with not w, every H-domain is empty and w equals bottom. No necessary inhabited interpretation is claimed, and no future membership is substituted into a current defining equivalence.

## 3. Comprehension, lambda abstraction, and truth operations

For a translated target formula phi* use

    F:=lambda xbar . A_tau(xbar) and phi*(xbar).

This is supported on A_tau by a logical theorem, hence is a current core relation. On current core tuples A_tau is true, so it has exactly the required current extension. This proves full intrinsic comprehension in the Henkin sense.

For a relational-valued abstraction lambda x.T, make T's output tuple explicit and use

    lambda x ybar . A_(sigma tau)(x,ybar) and T*(x)(ybar).

At a current core x its section is actually coextensive with the intended current core output. Both outputs are w-supported, so the localization lemma makes them identical, proving beta. Eta follows from the same lemma. This verifies the functional types ending in t; output e remains unavailable, just as in the fixed framework.

Truth and falsity in the target are w and bottom. Negation is relative complement within w, supported on its target input domain; for example its current core action is p↦w∧not p. Conjunction is similarly supported and agrees with p∧q on core truth inputs. These operations have values bottom or w on current core inputs, because every proposition below the true atom w is one of those two.

Equality at target sort sigma is the available supported relation

    Eq_sigma(x,y):=w and H_sigma(x) and H_sigma(y) and x=y.

On current core inputs this is w exactly when the objects are identical, and bottom otherwise. It does not replace identity of objects by mere coextension; the localization lemma established that actual coextension of core relations already implies literal identity.

The universal quantifier at sigma is represented by

    Q_sigma(P):=w and H_(sigma t)(P)
                    and forall x(H_sigma(x)→P(x)).

It is supported on the core predicate domain, and on a current core P it is true exactly when P holds of all current core sigma-objects. It is therefore the correct target quantifier. This explicitly checks its function type and avoids treating an unsupported ambient quantifier as a core operation.

These clauses prove a compositional interpretation of extensional Henkin higher-order logic, in the fixed relational-type fragment, over all current individuals. The target predicates include a representative of every available ambient current individual-relation extension: simply cut the original relation by the corresponding A_tau. External subsets absent from the ambient Henkin model are not thereby added.

## 4. Choice

If ambient Relational Choice holds, it transfers. Given a serial core relation, extend it to noncore inputs with a fixed core default, choose an ambient functional subrelation, and intersect the chosen graph with its core product support. The resulting w-supported graph has the same current choices and is a core relation. Its current functionality and seriality are immediate.

For relational outputs, form the relation whose instance at (x,ybar) says that the uniquely selected output Y holds of ybar, and intersect with the operation's core support. At every current core x the resulting section is coextensive with Y; both are w-supported, so they are identical. This gives the corresponding core choice operation. Individual outputs remain represented by functional binary graphs.

Thus Actuality+Relational Choice interprets ordinary extensional Choice. Functional Choice of the ambient intensional system is not required.

## 5. Exact quantified Infinity transfer

Take the target base to be all current objects of an original type sigma, with H_sigma^base(x)=w. For sigma=e this is the preceding construction. Let P be the core domain of properties of that base, and B its core cardinality domain, with ν=(sigma t)t. Define

    h(Z)(X):=w and P(X) and Z(X).

This is supported on P and hence belongs to B. For a current core X, the raw deletion X-y is already w-supported; it is a current core property and is exactly the target deletion, by the localization lemma. Therefore h carries original Frege zero to core zero and commutes with successor on every current Z: the two core outputs have the same current extension on core X, and both vanish outside P, so localization gives literal identity.

Pulling a core inductive predicate back along h shows that h maps original natural cardinalities to core natural cardinalities. Conversely, the core predicate

    I(Y):=w and B(Y) and exists Z(N(Z) and h(Z)=Y)

is supported on B, contains core zero, and is closed under core successor. Core induction therefore shows that every core natural cardinality has an original natural preimage. This is the same image/pullback argument as in the earlier core notes, now using w-supported comprehension and the localization lemma. It requires neither Choice nor external fullness.

The core universal property is U:=lambda x.w. It is currently coextensive with the ambient universal property top_sigma. Original finite cardinalities respect current coextension (the recorded Lemma A in `topics/classicism/writeups/possible-infinity-t-and-bf-t-imply-axiom-of-infinity-t.md`). Hence for N(Z),

    Z(top_sigma) iff Z(U) iff h(Z)(U).

Combining this with the surjectivity on natural cardinalities proves the exact equivalence of ambient AxiomOfInfinity_sigma and the target's quantified Axiom of Infinity over the base of all current sigma-objects. For sigma=t this is a new individual sort of ALL propositions, not the target Boolean truth sort {bottom,w}.

Consequently Actuality+Relational Choice+AxiomOfInfinity_e already interprets extensional Henkin relational HOL with Choice and its quantified Infinity axiom over all current individuals. The proof does not assert injectivity of h on intensional natural-cardinality objects.

## 6. What the stronger constructions add

This interpretation is confined to the actual-world slice. Its true value w and every supported relation can collapse to bottom later; it supplies no global persistence claim.

The GC construction in `gallin-extensional-core.md` instead uses globally TwoVal representatives and the ambient endpoints bottom/top. GC is needed for that canonical globally bivalent quotient, not for the mere local extensional interpretation proved here. The ND+RP rigid-domain construction gives genuinely rigid domains, a different stability conclusion. No implication ordering between these sufficient assumptions is being asserted here.

For a concrete separation, the recorded full two-object double-retraction model has Actuality but fails Strong Actuality and therefore GC. It consequently has this local world-slice core while lacking a globally bivalent evaluator and the GC canonicalization. The record is `topics/classicism/models/full-two-object-double-retraction.yaml`; use its exact construction and proved verdicts rather than treating the local interpretation as evidence for GC.

## 7. Canonical quotient and local Boolean completeness

The projection at each interpreted relation type is the explicit operation

    C_tau(X):=A_tau and X.

It is the unique current core relation agreeing with X on all current core arguments. Existence follows from its defining support; uniqueness is the localization lemma. It is an idempotent retraction onto the core domain. Its kernel is exactly current coextension on the core arguments. For relations on the base individual sort, those arguments include all current individuals, so its kernel is ordinary current coextension on the whole base domain.

The construction is independent of a choice of actual atom. Two currently true atoms have a nonzero meet and must be identical; hence the witness w is unique, and all the recursively defined supports and projections are determined by it. This is a mathematical uniqueness claim about the supplied witness, not a claim that w is denoted by a closed pure term.

C_tau preserves finite Boolean operations, taking the target complement relative to A_tau. For example C_tau(X∧Y)=C_tau(X)∧C_tau(Y) and C_tau(¬X)=A_tau∧¬C_tau(X). These are Boolean identities. No general naturality under arbitrary higher-type application is claimed: an ambient higher relation can distinguish coextensive inputs before normalization.

There is also a stronger local completeness result. At any original relation type tau, let c(w) be the constant relation with value w, and consider the Boolean interval of all F<=c(w). For any available ambient family P of such relations, its join in this interval is

    J(P)(xbar):=w and exists F(P(F) and F<=c(w) and F(xbar)).

For a current family member F, Actuality gives w<=P(F), and F is supported by w. Therefore F<=J(P). If Y in the interval is any current upper bound of the family, the entire universally quantified assertion that its current members are bounded by Y is true now. Actuality puts that assertion below w. At every future tuple satisfying J(P), w and the existential witness therefore imply Y. Thus J(P)<=Y. This proves the least-upper-bound property, including entirely new future witnesses in the displayed join. No BF, BC, RC or external fullness is used.

The same argument works inside any core interval [bottom,A_tau], replacing c(w) by A_tau and cutting the displayed union by A_tau. Meets follow by relative complement. Thus these intervals are complete for every family represented in the ambient language, even when the ambient Boolean algebra lacks Boolean Completeness.

Projection preserves every existing ambient represented join as well. If L is an ambient least upper bound of a family and Y<=A_tau bounds all projected members A_tau∧F, then Y∨¬A_tau bounds all original members. Hence L<=Y∨¬A_tau and A_tau∧L<=Y. The other inequality follows because A_tau∧L is an upper bound of the projected family. This last preservation argument is a general Boolean-algebra fact and needs no Actuality; Actuality supplies the existence of all the represented joins in the local interval.

A narrow search for localized/interval completeness in the result and writeup records found no matching theorem. This is a statement about the inspected database, not literature novelty.

## 8. Atoms, represented cardinal comparisons, and well-orders

The interval [bottom,c_tau(w)] is also atomic, and its atoms have an explicit description:

    a_(xbar):=lambda ybar . w and ybar=xbar.

Each such relation is nonzero because it holds of its current tuple xbar. If a nonzero G lies below it, G cannot be currently empty: otherwise localization would make G bottom. Any current member must equal xbar, so G is coextensive with a_(xbar), and localization makes them identical. Conversely every nonzero supported F has a current member xbar; Actuality and tuple identity give a_(xbar)<=F. Thus every interval atom is exactly one localized tuple-haecceity. Distinct current tuples give distinct atoms. In a core interval [bottom,A_tau], restrict xbar to current core tuples.

The localized haecceity construction itself is already the proof of `actuality-implies-actual-profile-r` (Classicism, section 2.2, note 31, p.25). The added conclusion here is its assembly with local completeness and extensionality into the explicit complete atomic interval presentation. Completeness is for represented families; this does not turn a Henkin domain into a full external powerset.

There is an exact preservation theorem for ordinary extensional second-order structure on the current individual domain. Replace each available individual relation R by its world-slice C(R). Any formula using individual equality, applications of those relations, and first-order or relation quantifiers has the same current truth value in the original structure and the slice, provided relation equality is read extensionally rather than as ambient intensional identity. Prove this by structural induction: atomic extensions and individual identities agree; every available original relation has a slice with the same current extension, and every core relation is itself an available original relation, so the quantifier ranges cover precisely the same represented extensions.

In particular the following are preserved exactly for represented individual predicates and binary relation graphs:

- being a function, injection, surjection, or bijection between specified current extensions;
- existence of a represented equinumerosity, injection, or surjection;
- linear order, well-foundedness, and well-ordering, with well-foundedness quantified over the available nonempty unary predicates;
- the induction principle for an available relation or operation graph.

For example a represented order is well-founded just when every represented nonempty subset has a minimal member. The ambient subsets and the slice subsets have the same current extensions by the projection, so both directions follow, with no assumption of external full powersets. This supplies a precise transfer of represented well-orders and ordinary cardinal comparisons, rather than a claim about arbitrary external relations.

The restriction on relation identity is necessary: two ambient relations can have the same current extension but remain distinct, while their slice representatives are identical. General intensional formulas are therefore not covered by this preservation theorem. The quantified Infinity transfer in section 5 was proved separately precisely because it uses the higher-order cardinality apparatus.

# Audit of the one-variable profile root

Original mathematical audit, 22 October 2026. This audits only the root-domain and action-closure obligation in §2 of `research/2026-10-22/strong-possibility-obstructions.md`; it preserves that file. The separate atomicity repair is in `parent-profile-atomicity-audit.md`. This is an agent audit, not named-human or proof-assistant certification.

## Verdict and exact assumptions

The restricted root construction closes under application, abstraction, and every typed quantifier. No fatal closure gap was found. The components must be genuine action models of C, with their original domains and arrows, rather than arbitrary truth-valued structures. Their action on every pure term must obey the usual transport/substitution lemma. The standard action-model completeness/background already cited by the parent supplies components witnessing every C-consistent pure sentence; this note does not independently reprove that literature theorem.

The definition of a profile uses equality of component **denotations**, not merely equality of their actual truth values. For a type σ, put

    b_T(V,a) := [[T(z)]]_V[z:=a]

for pure T with z its only possible free variable. Denotations may themselves be higher-type intensions. Equality in B_σ is equality of these values for every pointed component object (V,a). At type e every such term is z in the fixed relational type system, so the singleton individual domain and its z-profile agree.

## Action and landing

For h_(V,a):o→V, send a root relational object (A,b_T) to b_T(V,a). For an original component arrow k:V→V', term naturality gives

    k·b_T(V,a) = b_T(V',k·a).

This proves compatibility with k h_(V,a)=h_(V',ka), and landing is automatic: b_T(V,a) already belongs to the original component domain. No condition on the root extension A is required because no nonidentity arrow enters the root.

To compare with the set-of-tuples presentation of action intensions, let the extension at h_(V,a) be the actual extension of b_T(V,a), and let the extension at the identity be A. This representation is injective. If two profiles have the same extension at every pointed object, then at every further component arrow k they still have the same extension, by naturality and inclusion of (V',ka) among the indexed points. Component objects are intensions on all such arrows, so their denotations agree. Thus identifying profiles componentwise does not introduce an unnoticed quotient mismatch.

## Application

Write σ=αβ with β relational. For F=(A,b_T) at type αβ and a root argument x with profile b_U, define application by

    F x = (A_x, b_(T U)),

where A_x is the current-extension fibre. The result lies in D_β(o), since T(z)U(z) is a pure one-variable term of type β. This is independent of the representatives T and U by component application congruence. For an individual argument x, U is z. The same calculation proves preservation of application along each root arrow.

## Abstraction: the point that needs to be explicit

Let M(y,p_1,...,p_m) be a term whose free parameters p_j have root values with pure profiles T_j(z). Rename bound variables to avoid capture. Form the pure term

    L(z) := λy.M(y,T_1(z),...,T_m(z)).

Its z-profile belongs to B_(αβ). Its root extension is the set of all root tuples making the body true, using the actual root parameter values and the root domains for its bound quantifiers. This extension is permitted because the first coordinate of D_(αβ)(o) is an unrestricted powerset. Pair this extension with b_L.

The bound variable y must remain symbolic when forming L. One must **not** obtain b_L by first replacing y with the profile of a root value and then abstracting a function on the root domain. In particular, the singleton root's one possible individual argument would then erase component variation. The action-intension semantics evaluates the abstraction at each target over that target's whole argument domain, and the displayed syntactic construction does exactly that.

For β, root β-reduction follows in the first coordinate by taking the relevant fibre and in the profile coordinate by component β-reduction/substitution. η follows by equality of the whole root extension and by component η. This establishes the needed term-closure induction without assuming Functionality or extensionality at the root.

## Quantifiers and logical constants

At the root, the actual coordinate of ∀x^α φ is true exactly when every x∈D_α(o) satisfies φ there. Its profile is the pure term ∀x^α φ with only the free root parameters replaced by their T_j(z). In each component the quantifier therefore ranges over the full original D_α(V), not only the image of the root domain. That distinction is intentional and is compatible with C; imposing surjectivity of root transport would wrongly add a Barcan-like requirement.

Equivalently, the primitive quantifier object has its ordinary universal-testing root extension and its pure quantifier profile; application then gives the same clause. The Boolean constants and typed identities are treated similarly. Identity's root extension is literal equality of the whole root objects. The component identity profile is the corresponding pure equality predicate. Forward transport preserves identity, though it may merge distinct root objects.

All root domains are sets and are defined recursively on type: the argument types of a relational type are proper subtypes. Each profile set is countable because the pure language is countable; no enumeration or selector of profiles is needed for closure. Every term uses only finitely many parameters, whose pure profiles can be simultaneously substituted while retaining the same one free individual variable z.

## H and Logical Equivalence

The actual truth, Boolean, identity, application, and quantifier clauses validate H by the standard term-closure argument for action models, with β and η checked above. For the additional Logical Equivalence schema, take an actual H-theorem φ↔ψ with its permitted free variables. The root truth sets of the two abstractions agree by H soundness. After substituting the pure profiles for the finitely many free root parameters, the corresponding abstractions are identical in every component C-model by Logical Equivalence there. Their profile coordinates therefore agree. Hence the two root abstractions are literally identical. This uses the original H-theoremhood condition, not equivalence derived from optional assumptions.

Consequently the construction satisfies C at the root, while the original components remain unchanged.

## Two simplifying checks

The root fails F without needing an infinity argument. The proposition p=(true,bottom-profile) is true there and differs from top=(true,top-profile), since some component exists and its top differs from bottom. Thus current truth does not collapse propositions to top. In particular every A_n=F∧E_n has false actual coordinate at the root.

For a C-consistent closed pure sentence P, choose a component point where P is true. Its root profile differs from bottom, so P is non-bottom at the root, regardless of P's actual coordinate there. This verifies the required pure possibility instance directly. It does not claim Strong Possibility at the root.

Together with the separate finite-table/necessitation repair for A_n's profile identity, this closes the stated root-domain proof obligation. No claim about signature expansion or new semantic completeness is added.

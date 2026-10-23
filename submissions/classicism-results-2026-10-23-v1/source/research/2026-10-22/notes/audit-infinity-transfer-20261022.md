# Independent audit and sharpening: core Infinity and natural-cardinality transfer

22 October 2026. OpenAI Codex research-agent mathematics; no named human checking or Lean verification. Direct audit targets: `/tmp/classicism-research/rigidity-actualization.md` §§17–19. No main database edits. This report supplies an evaluator-free inverse and checks impredicative induction, overflow, and the finite-powerset argument.

**Verdict.** The stated proofs in §§17–19 pass, but their hypotheses can be substantially weakened. C5 alone gives the full natural-cardinality isomorphism with the ordinary rigid core over *all* entities of any original type σ, and therefore the equivalence of the quantified Infinity axioms. Actuality, BE, Atomicity, Choice, and boxed Actuality are unnecessary for that bridge. For a proper rigid subdomain D, C5 still gives the finite-cardinality surjection and the corresponding finiteness/Infinity equivalence, but generally not injectivity.

The independent Frege lane had already reached the C5 e-core bijection via numerical null collapse in `frege-infinity-20261022-1726.md` §§19–20. After finding the weakening I read those sections. The added contribution here is a direct evaluator-free lift by rigid coextension, valid at every counting type, which proves injectivity without splitting realized and overflow cases. The necessary source fact that numberhood persists is already Goodsell's recorded Lemma 3; it is not new.

## 1. Exact language and hypotheses

Fix any original type σ, possibly e or t. Put α=σt and ν=(σt)t. Work in C plus C5, which here means boxed ND at every type. The original relational type restrictions remain fixed. No function type ending in e or in a newly interpreted individual sort is introduced.

The core individual sort is all original σ-entities. Its property domain is

    P(X) := Rigid(X),                    X:α.

Its cardinality domain is

    B(Y) := Rigid(Y) ∧ Y≤P,              Y:ν.

Under C5, the universal property of σ is rigid; sections of rigid relations are rigid; supported hereditary-core domains are rigid; and a relation is rigid iff each of its current application values is top or bottom. BF is available at every type and necessarily. These are the exact C5 facts used in `rigidity-actualization.md` §§3, 9, and 13; they do not require Actuality.

Write N(Z) for original FiniteCardinality_σ. Write Nc(Y) for the interpreted core FiniteCardinality predicate, supported on B. Its inductive predicates range over rigid predicates on ν supported on B. Core zero and successor are

    0c(X) := P(X) ∧ ∀u ¬Xu,
    Sc(Y)(X) := P(X) ∧ ∃a [Xa ∧ Y(X−a)],
    (X−a)(u) := Xu ∧ u≠a.

These are core entities, and Sc preserves B. One can use intrinsic core comprehension, or directly note that for rigid X all the application and identity values are bivalent and BF preserves bivalence through the displayed quantifiers.

## 2. Numberhood is already persistent in C

The following is existing background, not a new conclusion of the representation:

    C ⊢ ∀Z [N(Z)→□N(Z)].

It is Lemma 3 in `writeups/countable-boolean-completeness-implies-necessity-of-arithmetic.md`, before any use of Countable Boolean Completeness, and is used by the proved `c5-implies-necessity-of-arithmetic` record. For completeness, apply N's induction to W(Z):=□N(Z). Necessitation gives W(0), and necessitating the C theorem that N is successor-closed gives W(Z)→W(Suc Z). Thus every N-member satisfies W. Necessitating the universally closed theorem makes N a persistent relation, with the official outer box.

Under C5 a persistent relation is rigid, so N has settled membership. In particular every proposition N(Z) is top or bottom, including for arbitrary nonstandard Z. This is why the image predicate below can be admitted directly in the core without actualization.

## 3. Raw restriction and its commuting equations

Define the available original operation q:νν by

    q(Z)(X) := P(X) ∧ ZX.

For arbitrary Z, q(Z) need not be rigid. Nevertheless C5 proves the identities

    q(0)=0c,
    q(Suc Z)=Sc(q(Z)).

The first is definitional. For the second, at any point where X is rigid, each X−a is rigid. Thus the extra conjunct P(X−a) inserted by q is redundant inside the successor existential. Outside P(X) both sides vanish. The proof works at every accessible point, because C5 is necessary. Necessary coextension, not merely current coextension under an optional premise, gives identity by C's Intensionality.

Induction on original N now proves B(q(Z)) for N(Z): q(0) is core zero and Sc preserves B. To prove Nc(q(Z)), let V be any core inductive predicate and use the original induction predicate

    U(Z) := B(q(Z)) ∧ V(q(Z)).

The commuting equations make U inductive. Therefore N(Z) entails Nc(q(Z)). No assertion that N-members are externally standard has been made.

## 4. Surjectivity without BE or Actuality

Form the actual image predicate

    I(Y) := B(Y) ∧ ∃Z [N(Z) ∧ q(Z)=Y].

I is already a core predicate on B under C5. B-membership and N-membership are bivalent; equality is bivalent by NI and ND. BF makes the existential bivalent as well. Consequently I is rigid; its explicit B conjunct gives support. No evaluator E, Rigid Comprehension, or unproved external-subset closure is needed.

I contains 0c. If I(Y), take its original N-preimage Z. N is successor-closed and q commutes with successor, so I(Sc Y). Hence core induction gives Nc(Y)→I(Y). Together with Section 3:

    Nc(Y) ↔ ∃Z [N(Z) ∧ q(Z)=Y]       for core Y.

This is the exact surjectivity theorem needed for the quantified Infinity transfer. It applies to genuinely impredicative N and Nc, including models with nonstandard internal naturals.

## 5. An evaluator-free lift by rigid coextension

Define ℓ:νν by the ordinary finitary lambda term

    ℓ(Y)(X) := ∃R^α [Rigid(R) ∧ Coext(X,R) ∧ YR],
    Coext(X,R) := ∀u^σ (Xu↔Ru).

This operation is available in C. It does not select a rigid representative. It existentially tests all such representatives. Where a rigid coextension exists it is unique, by the C theorem that coextensive weakly rigid relations are identical. If X has no rigid coextension, the displayed proposition is false; the construction does not assume every X has one.

Under C5:

    ℓ(0c)=0,
    ℓ(Sc Y)=Suc(ℓ(Y))             whenever B(Y),
    q(ℓ(Y))=Y                     whenever B(Y).

### Zero

ℓ(0c)(X) says that X is coextensive with a rigid empty property. This is equivalent to X being empty: use the rigid bottom property for one direction, and coextension for the other. The equivalence holds at every point, hence gives identity of the cardinalities.

### Successor, forward direction

Suppose ℓ(Sc Y)(X). Choose a rigid R coextensive with X and an a with Ra and Y(R−a). Then Xa. Under C5, R−a is rigid and is coextensive with X−a. It witnesses ℓ(Y)(X−a), and a witnesses Suc(ℓ(Y))(X).

### Successor, reverse direction

Suppose Xa and ℓ(Y)(X−a). Choose rigid Q coextensive with X−a and satisfying YQ. In particular ¬Qa. Let H_a(u):=(u=a) and put R:=Q∨H_a. Haecceities are rigid in C, and finite joins of rigid relations are rigid in C. Thus R is rigid and is actually coextensive with X.

Under C5, R−a is rigid. It is coextensive with Q: away from a this follows from the definition of R, and at a both are false, using ¬Qa. Coextensive rigid relations are identical, so R−a=Q. Hence Ra and Y(R−a), making Sc(Y)(R) true. R witnesses ℓ(Sc Y)(X).

This local proof works at every future point with the transported core parameter Y. B(Y) is necessary, and C5 is necessary. Therefore it establishes necessary coextension of ℓ(Sc Y) and Suc(ℓ(Y)), and hence the required identity. It never invokes Rigid Comprehension at the evaluation point or at any future point: the sole new representative is the explicit finite join Q∨H_a.

### The qℓ retraction

If X is rigid, every rigid R coextensive with X equals X, while X itself is a witness. Therefore ℓ(Y)(X)↔YX. Outside the rigid-property domain, q(ℓ(Y)) vanishes, and so does the supported core Y. This again holds necessarily for a fixed core Y, giving q(ℓ(Y))=Y.

## 6. Full natural-cardinality isomorphism under C5

Use original N-induction on

    K(Z) := B(q(Z)) ∧ ℓ(q(Z))=Z.

The zero case follows from q(0)=0c and ℓ(0c)=0. If K(Z), the commuting equations give

    ℓ(q(Suc Z))
      = ℓ(Sc(q(Z)))
      = Suc(ℓ(q(Z)))
      = Suc Z.

The core-membership conjunct is preserved by Sc. Hence every original natural cardinality satisfies ℓq(Z)=Z. In particular q is injective on N, without an Infinity assumption and without a separate overflow argument.

Section 4 gives, for each core natural Y, an original natural Z with q(Z)=Y. Then ℓ(Y)=Z is original-natural. Together with qℓ(Y)=Y, q and ℓ restrict to mutually inverse zero/successor-preserving bijections between N and Nc.

This strengthens the original §19, which constructed a different inverse from atomic worlds under boxed Plenitude. That world-lift proof remains correct; it is simply unnecessary for the numerical isomorphism. It also strengthens the weaker hypothesis in original §17: the image predicate can be admitted by rigidity of N, without BE.

## 7. Quantified Infinity and proper rigid subdomains

The universal σ-property is rigid under C5. For N(Z), therefore,

    q(Z)(top_α) ↔ Z(top_α).

Surjectivity gives

    ∃Z [N(Z) ∧ Z(top_α)]
      ↔ ∃Y [Nc(Y) ∧ Y(top_α)].

Negating proves equivalence of the original Axiom of Infinity at σ with the translated ordinary core Axiom of Infinity over all σ-entities. Thus C5+AI_e already interprets extensional relational Henkin HOL with its quantified individual Infinity axiom. Choice remains separate.

For any nonempty rigid D:κt replace P by P_D(X):=Rigid(X)∧X≤D and use raw q_D(Z)(X):=P_D(X)∧ZX. The same zero/successor and rigid-image argument proves

    core-Finite(D) ↔ ∃Z [FiniteCardinality_κ(Z) ∧ ZD],

already under C5. Emptiness and the successor witness may be restricted to D because each admitted X is supported on D.

**Do not extend the injectivity claim to proper D.** For example, in a full model with infinitely many κ-entities and singleton D, infinitely many distinct original natural cardinalities restrict to the same empty/overflow cardinality of D. Correspondingly the lift ℓ_D restricted to representatives supported on D does not commute with the unrestricted ambient successor: adjoining an element outside D breaks that equation. This is a useful scope check.

## 8. Audit of the finite-powerset argument

The argument in original §18 passes for general extensional Henkin domains. Here are the internal induction obligations explicitly.

Call A adjunctively finite if it belongs to every available predicate on properties that contains empty and is closed under X↦X∪{a}. Original Frege-finiteness is equivalent to this condition in extensional HOL:

- Frege→adjunctive: induct on N(n) with the property ∀A(nA→AdjFinite(A)). At a successor, remove the displayed member a, apply the induction hypothesis, then adjoin a. Zero counts exactly empty by Extensionality.
- Adjunctive→Frege: the available class ∃n(Nn∧nA) contains empty. To adjoin a, retain the same cardinality if a already belongs to A; otherwise use Suc(n). This class is therefore inductive.

Adjunction induction proves finiteness of subsets, finite unions, and images of available functional relations. No function type ending in the individual sort is needed: the image is defined by an existential relation. Partial functional relations work too, since one newly adjoined input contributes either no output or one output.

For the power domain P(A), the empty case is a singleton. At A∪{a}, every subset either already belongs to P(A) or is obtained by adjoining a to a member of P(A). The latter construction is an available functional graph. Thus the new power domain is a union of two finite available images. This proves Finite(A)→Finite(P(A)) by internal induction.

Conversely, the singleton predicates form an available subset of P(A). The relation taking each singleton predicate to its unique member is an available functional graph, and its image is A. Hence finite P(A) implies finite A.

All steps concern the available Henkin power domain. No external powerset fullness, external standardness of finite cardinalities, or Choice is used.

## 9. Atomic worlds and the Actuality distinction

The final result of original §18 retains its stated hypothesis C5+Atomicity_t. That package supplies boxed Plenitude and therefore boxed Actuality. The graph p↦(w↦Atom(w)∧w≤p) identifies original propositions with the available core power domain of the atomic-world sort. Its inverse needs an actual true atom at each point, so boxed Actuality is relevant to that graph argument; it was not relevant to Sections 2–7 above.

The graph itself belongs to the multi-sorted core: atomhood and algebraic order have bivalent values under C5, and BF turns their formula into a rigid supported relation. This is a direct admissibility argument, not an assumption that arbitrary external graphs exist.

Using the finite-powerset theorem and the C5 subdomain bridge gives

    AI_t ↔ ¬∃Z [FiniteCardinality_t(Z) ∧ Z(Atom_t)]

under C5+Atomicity_t. Choice is unnecessary. An atomless C5 model has no such nonempty atomic-world sort, so the result cannot be obtained by merely dropping Atomicity from this *world* statement.

## 10. Nonstandard and finite-overflow checks

None of the arguments replaces N by the external sequence of numerals. Both image directions use the actual impredicative induction predicates. A model may have nonstandard internal naturals.

Nor is the bottom cardinality confused with zero. In a full model with exactly m individuals, the standard numeral m+1 is the bottom cardinality and all subsequent numerals coincide with it. Zero still counts the empty property. The core has the same overflow behavior. The equations ℓq=id on N remain valid in that finite case; they do not imply successor is injective. The C5-only inverse handles the overflow case automatically.

In the singleton case, for example, the three natural cardinality entities are zero, one, and the bottom overflow entity. The latter maps to the bottom overflow entity of the singleton core, while zero maps to core zero. This is fully compatible with failure of Infinity and with the isomorphism theorem.

## 11. Status and provenance

The original actualized-image and atomic-world-lift proofs are valid under their original assumptions. The cleaner C5 proof above removes assumptions; it does not retroactively attribute the new lift to their cited literature. The raw C5 bridge and numerical injectivity were also independently obtained in the ongoing Frege research lane, with different proofs. Numberhood persistence and C5 arithmetic necessity were already recorded source-backed facts. No claim of literature novelty or external verification is made.

# Finite C5 cells: pointed categoricity and forced atoms under Strong Possibility

22 October 2026. Original ordinary-mathematics extension developed during the independent profile audit by an OpenAI Codex research agent. No named human check, Lean verification, or literature novelty claim. Direct source of this extension: this note; background profile construction: `profile-root-construction-20261022.md`, audited in `audit-profile-20261022.md`. No database edits.

## 1. Exact closed sentences

Let

    K := □∀p^t q^t [p≠q→□(p≠q)].

This single closed pure sentence is the type-t instance of boxed ND. The proved record `necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r` makes it equivalent over C to the C5 schema. Let E_r^σ say that type σ has exactly the fixed external positive integer r many entities.

For positive m,k put

    B_(m,k) := K ∧ E_m^e ∧ E_(2^k)^t.

All these are ordinary finite closed pure sentences. No infinitary conjunction of type instances is hidden in K.

**Theorem.** For every positive m,k:

1. B_(m,k) is C-consistent and pointed-complete: for each pure formula P(z) with at most the free individual variable z, C proves B_(m,k)→∀z P(z) or C proves B_(m,k)→∀z ¬P(z).
2. C proves B_(m,k)→□B_(m,k).
3. There is a single pure-Max model satisfying Atom_t(B_(m,k)) for all m,k simultaneously, with internally countably many propositions.
4. Pure Strong Possibility entails Atom_t(B_(m,k)) for every m,k.

For k=1 these cells reduce to the original finite Fregean cells F∧E_m. The cases k>1 add non-Fregean cells with finitely many propositional atoms/worlds.

## 2. Finite full Boolean-valued structures witness consistency

Take an m-element individual set I and a k-element world set S. Interpret D_e=I, D_t=P(S), and every admitted function type στ by all functions D_σ→D_τ. Logical connectives are the Boolean operations on P(S); quantifiers take intersections/unions over their fixed domains; identity is top or bottom according to literal identity; evaluate at any world s∈S.

All domains are finite, by induction on type. The usual compositional interpretation validates H and its contextual βη axioms. If two formulas are H-equivalent, they agree at every world under every assignment, so their abstractions are literally equal functions: C's Logical Equivalence holds with its original theoremhood condition. Literal stable equality validates C5. This model satisfies B_(m,k) at every world.

This is a finite full Gallin-style structure, not a claim that the action category representing it is uniquely determined. Different categories may present the same local typed structure.

## 3. Every B-cell has the same local typed structure

Fix any object in any C action model satisfying B_(m,k). C5 supplies BF and Functionality at every admitted type. Let d_σ be the size of its local σ-domain.

Inductively,

    d_e=m,  d_t=2^k,  d_(στ)=(d_τ)^(d_σ).

First, Functionality makes application inject each entity of type στ into the function it induces from D_σ to D_τ. If the lower domains are finite, this already bounds d_(στ) by the displayed finite number.

Conversely every such function is available. Enumerate D_σ as a₁,…,a_r and let its desired values be b₁,…,b_r of the relational output type τ. Form a finite Boolean case distinction

    λx . ⋁_(i=1)^r [ lift_τ(x=a_i) ∧_τ b_i ],

where lift_τ turns a proposition into the corresponding constant τ-relation. Under C5 each equality mask at x=a_j is literally top or bottom: NI settles true identities and ND settles false identities. Thus the displayed operation takes exactly b_j at a_j. No operation with output e is used. It realizes the desired function, proving the reverse cardinal bound and fullness.

This establishes full function domains, not merely all actual truth extensions. The distinction is essential when k>1.

## 4. Logical constants are fixed by the finite structure

The proposition domain, with its C Boolean operations, is a finite Boolean algebra of size 2^k, hence isomorphic to P(S) for a k-element set S. Its actual truth map is a Boolean homomorphism into 2, so it is evaluation at one unique atom of this finite Boolean algebra.

Typed equality takes top for equal entities and bottom for unequal entities, by NI and ND. It remains to check the quantifier values, rather than assuming their actual truth clauses determine proposition entities.

Let a₁,…,a_r enumerate an arbitrary local type σ. For every current x, some identity x=a_i is true and therefore necessary. Thus

    ∀x □⋁_i(x=a_i).

BF_σ gives □∀x ⋁_i(x=a_i). At every future point the transported tuple therefore remains exhaustive. For each current X:σt the ordinary quantifier laws, inside the box, give

    □[(∀x Xx)↔⋀_i X a_i].

Hence C's Intensionality identifies the universal-quantifier value with that finite Boolean meet. Existential quantification is the finite join. The same argument applies to every type, since every local type was shown finite.

Application and lambda abstraction are already the ordinary full-function operations by β and Functionality. Consequently the entire local typed logical structure is isomorphic to the finite full Boolean-valued structure in Section 2, preserving actual truth.

Any bijection of the m individuals extends recursively through all function domains. Any permutation of the k Boolean atoms extends through those domains too; choose it to carry the designated actual atom to the designated actual atom of the comparison structure. These extensions preserve equality, application, lambda interpretation, finite meets/joins, and the Boolean connectives. For any two chosen individual markers, the individual bijection may send the first to the second.

Thus all pointed B_(m,k)-objects have the same pure theory. For each pure unary formula P(z), its truth is either uniformly true or uniformly false at all such objects and markers. Completeness of the C action-model semantics yields the stated pointed-completeness alternative. This is a semantic completeness argument about a fixed finite sentence, not an algorithmic assertion that the entire theory is supplied in advance.

## 5. Stability of each cell

K implies □K by 4. Under K, a finite enumeration of either e or t remains exhaustive by the BF argument above, and its finitely many distinctness statements remain true by ND. The transported tuple therefore witnesses the same exact finite cardinality at every accessible point. Hence

    C ⊢ B_(m,k)→□B_(m,k).

Distinct pairs (m,k) give incompatible exact-cardinality sentences. Therefore B_i∧B_j=bottom in C when i≠j. At a point satisfying B_i, stability makes B_i=top as an entity, so every other B_j is literally bottom there. This last entity-level observation will permit the independent-pattern construction in Section 7 even though B_i need not be Fregean.

## 6. Profile atoms and Strong Possibility

Use the singleton pure-profile root audited in `audit-profile-20261022.md`. Root propositions are pairs consisting of an arbitrary actual truth bit and a pure unary profile T(z). At every B_(m,k)-point, P(z)'s truth is uniform by pointed categoricity. Since every component object and arrow is included, descendant truth separation turns this uniformity into the assertion that the profile of p∧B_(m,k) is either bottom or the profile of B_(m,k).

The actual root proposition domain is countably infinite, so E_(2^k)^t is false there. Thus B_(m,k) and p∧B_(m,k) have actual bit zero. Consequently p∧B_(m,k) is literally either bottom or B_(m,k). The finite full component in Section 2 witnesses its nonzeroness. It is an atom. The same root works for every positive m,k and retains the already audited internal Ctbl_(e,t)(top_t) witness.

Atom_t(B_(m,k)) is a closed pure universal Boolean combination of identities, after expanding Boolean order. The proved-in-research universal-identity reflection lemma says ◇ne U→U for every such U. Its Max-consistency just established therefore lets Strong Possibility infer Atom_t(B_(m,k)). No consistency of Strong Possibility itself is assumed.

These are additional necessary conditions on Strong Possibility. They do not imply Strong Possibility has only these atoms, has an actual atom, or is inconsistent.

## 7. Arbitrary atomic/atomless patterns across the finite C5 cells

The earlier arbitrary-pattern construction extends to the whole countable grid of pairs (m,k).

Fix any external subset S of that grid. For each cell index i outside S introduce countably many auxiliary propositional profile symbols d_(i,j). For each underlying pure component include all expansions independently interpreting d_(i,j) as B_i or bottom throughout that component. These symbols only define root domains; the final model is the pure reduct and its Maximalism reference theory remains original C.

At a B_i-point with i∈S, every auxiliary symbol is bottom as an entity by Section 5: its associated cell differs from i. Thus every profile reduces at such a point to a pure unary profile, and pointed categoricity makes B_i atomic exactly as above.

For i∉S, take any nonzero p≤B_i. Its actual bit is zero, and its finite-syntax profile uses only finitely many auxiliary symbols. Choose a fresh d_(i,j). A component arrow witnessing p is a B_i-point. Toggle just the fresh auxiliary interpretation between B_i and bottom, retaining the underlying component and every symbol in p's profile. The two expanded components make p∧d_(i,j) and p∧¬d_(i,j) respectively nonzero. They are disjoint parts of p. Hence B_i is atomless, not merely non-atomic.

Only countably many profile symbols are involved, so root proposition profiles remain countable. The same freely admitted root graph gives internal countability. Therefore every requested atomic/atomless pattern for the finite C5 cells is relatively consistent with pure Max and internal countability.

The extension works because these cells are stable and pairwise exclusive, making other-cell auxiliary propositions literally bottom at a chosen cell. Mere disjointness or mere current falsity would not supply this entity-level fact for arbitrary formulas.

## 8. Relation to the original Fregean cells

E_2^t implies the Fregean Axiom: top and bottom are distinct, exhaust the two propositions, and their actual truth values differ. Conversely F supplies exactly those two propositions and implies C5. Hence B_(m,1) is equivalent over C to F∧E_m.

For k>1, B_(m,k) has 2^k propositions and k Boolean atoms in its full finite structure and refutes F. Thus the theorem is a genuine extension of the finite-extensional cell family, while using the same original profile construction and original pure reference language.

## 9. Explicit pure Barcan counterinstances forced by Strong Possibility

The non-Fregean cells yield a concrete counterinstance, sharpening the earlier schema-level Barcan obstruction. Fix, for example, B:=B_(1,2), whose points have one individual and four propositions. Define the closed pure predicate

    Φ(p) := B→(p=top ∨ p=bottom).

Pure Strong Possibility proves

    ∀p □Φ(p),       ¬□∀p Φ(p).

For the first statement, Atom(B) makes each current p satisfy B≤p or B≤¬p. Each such algebraic inequality is necessary. At any later point where B holds, the already proved B→□B makes B=top; the first alternative therefore makes p=top, and the second p=bottom. Thus every current p necessarily satisfies Φ(p).

For the second, pure Max supplies ◇B. At a B-point there are four propositions, whereas top and bottom account for only two, so some p is neither. Thus Φ fails of a proposition there. This gives the displayed strict failure of BF_t for one fixed pure predicate. No appeal to an unspecified Max+¬Atom consistency witness is needed for this particular counterinstance.

The example transfers to **every relational input type with no free object parameters**. For σ=ρ₁…ρ_nt define the closed pure maps

    c_σ(p):=λx̄.p,
    r_σ(X):=∀x̄ X[x̄].

The empty tuple gives the identity maps. H's vacuous-quantifier laws, including its nonemptiness theorem at each type, make r_σ(c_σ(p))=p a theorem of C. Thus t is a closed-pure split retract of every relational σ; an evaluation tuple need not be chosen.

Put Φ_σ(X):=Φ(r_σ(X)). The first displayed statement gives ∀X□Φ_σ(X). At the B-point choose a nonbivalent proposition p and X=c_σ(p); the retract equation makes Φ_σ(X) false. Hence

    Pure SP ⊢ (∀X^σ □Φ_σ(X)) ∧ ¬□∀X^σ Φ_σ(X)

for each relational σ. It also supplies explicit pure Functionality counterinstances at any such input σ and any relational output τ: take the constant-top operation and the operation X↦lift_τ(Φ_σ(X)). They have equal values at every actual X but are distinct operations, since their identity would make Φ_σ hold necessarily of every X.

Semantically, if a root satisfying Atom(B_(m,k)) has an arrow to a B_(m,k)-point, every proposition in the image of that root transport is top or bottom there. Both values occur, so the image contains exactly two propositions although the target contains 2^k. For k>1 the other 2^k−2 target propositions have no root preimage under that arrow. This is the precise finite-domain obstruction exhibited by the counterinstance; it is not an assumption that all entities are globally present.

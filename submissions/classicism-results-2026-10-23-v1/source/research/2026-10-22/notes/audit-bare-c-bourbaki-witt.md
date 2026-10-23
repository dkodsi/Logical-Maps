# Independent audit: Bourbaki–Witt for represented functional graphs in C

22 October 2026. Audit by an OpenAI Codex research subagent. This is an ordinary mathematical audit, not a claim of human checking or Lean verification. No database record or repository source was edited.

## Verdict

**Pass, with the exact hypotheses below.** The fixed-point bridge needed by the proposed proof of Relational Choice + Boolean Completeness ⇒ Transversal Choice is available in bare C. It does not use Transversal Choice, Functional Choice, Plenitude, rigid comprehension, BF, or necessitation of an optional premise. The decisive condition is that the relevant order is antisymmetric with respect to actual entity identity, so that an actual family has at most one supremum **as an entity**. It is insufficient that suprema be unique merely up to actual coextension or preorder equivalence.

This audit concerns the fixed-point bridge. The separate algebraic proof that the chosen partial-transversal poset has chain suprema, and the modal proof of its strict extensions, remain independent obligations.

## Sources inspected

* `topics/classicism/AGENTS.md`, `topic.yaml`, and the Framework, Notation, order/choice definitions, and Conventions in `background.md`.
* `principles/ordinary-comprehension-r.yaml`, `relational-choice-r.yaml`, `transversal-choice-r.yaml`, `boolean-completeness-r.yaml`, and `zorn-r.yaml`.
* `results/classicism-implies-ordinary-comprehension-r.yaml` and `classicism-implies-intensionality-r.yaml`.
* The entire local write-up `writeups/transversal-choice-r-implies-zorn-r.md`, especially its four (E) steps. This write-up translates Jonathan Lewin, “A Simple Proof of Zorn’s Lemma,” *American Mathematical Monthly* 98 (1991), pp. 353–354. The published paper itself was not needed or independently consulted here; the audited reasoning is explicitly displayed in the local write-up.
* Section 5, and its surrounding definitions, of `/tmp/classicism-research/relational-choice-boolean-completeness-transversal-proof.md`, as it stood during this audit.

The theorem below is a new explicit specialization/adaptation of the displayed local proof. It is not attributed to the cited paper as a theorem about C.

## 1. Exact internal theorem

Fix any admitted type ρ, a predicate P of type ρt, a relation ≤ of type ρρt, and a relation S of type ρρt. Everything below is asserted at the evaluation point.

Assume:

1. ≤ is a reflexive, transitive and antisymmetric order on the P-instances.
2. Every admitted property C of type ρt whose actual extension is a chain contained in P has a least upper bound in P. This includes the empty property.
3. For each x in P there is a unique y in P with S(x,y). We may either require S to have no other outputs on P-inputs, or define its restriction S_P(x,y):=P(x)∧P(y)∧S(x,y). Only the restricted graph is used.
4. For x,y in P, S_P(x,y) implies x≤y.

Then there is x in P with S_P(x,x).

No represented operation of type ρρ is assumed. This matters if ρ=e, where that operation type is forbidden, but the graph type ρρt remains admitted. In the intended application ρ=σt, and even there no operation extraction is needed.

Empty-chain completeness already supplies a least P-instance b. Thus the explicit least-element assumption in the draft’s lemma is redundant, though harmless.

## 2. The supremum relation is extensional in its property argument

For an admitted C define

    Chain_P(C) := C⊆P and ≤ totally orders C,
    UB_P(C,s) := P(s) and ∀x(Cx → x≤s),
    Sup_P(C,s) := UB_P(C,s) and ∀v(UB_P(C,v) → s≤v).

All displayed abbreviations expand to formulas and hence to admitted predicates by ordinary comprehension / lambda abstraction. No operation returning a supremum is introduced.

If Sup_P(C,s) and Sup_P(C,t), then s≤t and t≤s, and both s,t are in P; antisymmetry gives s=t. This is actual identity. It licenses ordinary identity substitution in the graph S_P.

If C and D are actually coextensive, then Chain_P(C) iff Chain_P(D), and Sup_P(C,s) iff Sup_P(D,s), for each s. This is direct substitution of biconditionals into the material universal clauses. We never infer C=D.

In particular, coextensive chain predicates have the same supremum entity. No boxed coextension, NI, ND, or Intensionality is invoked for that inference.

## 3. An extensional strict-upper-bound selector without choice

Suppose toward contradiction that S_P has no fixed point. By progressivity, S_P(s,y) gives s<y, where x<y abbreviates x≤y and x≠y. (For a partial order this agrees with ≤ plus failure of the reverse order.)

Fix b in P, for example the supremum of the empty chain. Define a graph T on chain predicates and P-elements by

    T(C,y) :=
      [Chain_P(C) ∧ ∃s(Sup_P(C,s) ∧ S_P(s,y))]
      ∨ [¬Chain_P(C) ∧ y=b].

T is represented by a lambda term of type (ρt)ρt. It is total and single-valued at the evaluation point: a valid chain has a supremum by assumption, unique by antisymmetry, and S_P has a unique value there; otherwise b is its unique value.

T is invariant under actual coextension of C. Both Chain_P and Sup_P are invariant, and the same supremum variable serves in the existential clause. Indeed the formula T(C,y) ↔ T(D,y) follows directly from C≡D without even applying uniqueness; uniqueness is needed to establish functionality of T.

If Chain_P(C) and T(C,y), then every x with Cx satisfies x≤s<y, so x<y. Thus T is precisely the extensional strict-upper-bound selector required by the local Lewin argument. It was defined from a functional graph and unique suprema, without an additional use of any choice principle.

## 4. Relativizing the displayed Lewin proof to P

Use the local Lewin proof with these adjustments only:

* Every conforming property A is required to satisfy A⊆P.
* ≤ is required to be a preorder only on P, and every object mentioned in order reasoning belongs to P.
* The selector is T above. All its values belong to P.
* A conforming property is well-ordered by ≤ and satisfies T(Pred(A,x),x) for each of its instances x, where Pred(A,x):=λy(Ay∧y<x).

Every subsequent construction remains inside P. Predecessor properties, differences, intersections, and singleton extensions are admitted predicates by lambda abstraction. The union

    U(x):=∃A(Conf(A)∧Ax)

is an admitted predicate by quantification over the already-admitted type ρt. It is not an external union indexed by a metatheoretic proper class. No assumption that every external subset is represented is used.

The comparison lemma, downward-closure lemma, proof that U is conforming, and proof that U enlarged by T(U) is conforming use only the restrictions already listed. Reflexivity and transitivity are never needed for objects outside P. The selector output stays in P, so its addition preserves the extra A⊆P clause.

For completeness, the four (E) moves in the local proof become:

1. If Pred(A,z)≡Pred(B,y), then T(Pred(A,z),z) and T(Pred(B,y),y) imply T(Pred(A,z),y); functionality gives y=z.
2. If Pred(U,x)≡Pred(A,x), then T(Pred(A,x),x) gives T(Pred(U,x),x).
3. If U′=U∪{x} and Pred(U′,x)≡U, then T(U,x) gives T(Pred(U′,x),x).
4. If u∈U and Pred(U′,u)≡Pred(U,u), then T(Pred(U,u),u) gives T(Pred(U′,u),u).

Each is licensed by the actual-coextension invariance proved in §3. No identity of predicate codes is asserted.

The local proof therefore constructs U′ conforming and containing the chosen x strictly above U. By the definition of U as the union of all conforming predicates, x∈U, contradicting x<x. The no-fixed-point hypothesis is false.

## 5. Independent check of the draft’s self-contained f-chain proof

The draft also gives a direct proof and does not rely only on the adaptation above. I checked its substantive steps:

* An f-chain C is an admitted predicate, well-ordered internally, satisfying: every x∈C is the P-supremum of the admitted image of its strict predecessors under S_P. The graph image is λz∃y(Cy∧y<x∧S_P(y,z)). No function term is hidden.
* The singleton of the least element is an f-chain: its strict predecessor image is empty.
* For two f-chains C,D, the common-predecessor agreement property I is admitted. If x∈I, any earlier member y in either chain lies in both; predecessor equality at x, transitivity, and restriction below y give predecessor equality at y. Thus I is an initial segment of both.
* If both differences C\I and D\I are nonempty, their internally least members c,d have predecessor extension exactly I. The graph images are then actually coextensive; unique-supremum identity gives c=d, putting c in I, contradiction. This uses the genuine antisymmetry of P, not extensionality of property entities.
* Existential union over f-chains is admitted. Comparability by initial segment gives both totality and internal well-foundedness of the union. For any member x, its predecessors in the union have the same extension as its predecessors in any f-chain containing x, so its defining LUB property transfers.
* If u is the supremum of the union A and u∉A, then A has no greatest member. For each x∈A there exists a later y∈A, so S_P(x,f(x)) and the f-chain condition at y give f(x)≤y≤u. This is a succession of ordinary existential-elimination arguments, not a simultaneous selection requiring choice. Progressivity makes every upper bound of the graph image an upper bound of A. Consequently u is the supremum of that image, and A∪{u} is another f-chain, a contradiction.
* Now u∈A. If u<f(u), then f(u) is the greatest member of the graph image of A: for x<u in A, the f-chain condition at u gives f(x)≤u≤f(u), and f(u) is itself in the image. Therefore A∪{f(u)} is another f-chain, again a contradiction.

The self-contained proof passes on the same exact assumptions. The notation “C=I or D=I” in its comparison paragraph should be read as actual coextension / equality of displayed extensions, not identity of property entities; the following prose already makes this intended meaning explicit. Writing C≡I or D≡I would remove a small presentational ambiguity, but no mathematical gap follows.

## 6. Why this does not prove the stronger choice implication by itself

The proof cannot simply be run on the poset of ordinary partial transversals ordered by actual inclusion: that is only a preorder on predicate entities, and coextensive predicates can be distinct. Its suprema would then be unique only modulo coextension, and a merely functional S could distinguish the different supremum entities.

The proposed RC+BC argument instead uses algebraic Boolean order. That is genuinely antisymmetric as an order on the admitted relation entities. The proof must establish represented chain completeness for its special property P with respect to that order. Once that is proved, the fixed-point bridge adds no hidden strength.

Nothing here establishes that Relational Choice alone supplies those chain suprema. Therefore this audit does not settle Relational Choice ⇒ Transversal Choice without the extra completeness premise.

## 7. Dependency checklist

* All assumptions, all chain predicates, and all fixed-point conclusions are actual and unboxed.
* No optional premise is inserted into a theoremhood-restricted Logical Equivalence or necessitation rule.
* Every needed family is an ordinary formula at an admitted relational type.
* No quotient set, external set of ordinals, Replacement, arbitrary external subset, or transfinite recursion is used.
* No chosen functional graph is converted into an operation.
* Every identity used between order elements comes from partial-order antisymmetry or ordinary graph functionality. No actual coextension of property entities is silently promoted to identity.
* The empty-chain clause supplies inhabitedness and the fallback b.

This is a positive audit of the fixed-point component, conditional on its explicitly stated hypotheses, not a claim that every other component of the proposed RC+BC proof has been audited in this document.

# Reversible semilattice separation from invariant congruences and order actions

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–7, unpaginated.

Reversible meet separation has an intrinsic obstruction at the level of admitted relations: a nontrivial equivalence which respects current truth and is invariant under the admitted automorphisms. There is a largest such equivalence, and it is automatically a meet congruence. On a chain it is convex. This yields a positive atomless theorem: an order-primitive action on the interior of a bounded dense chain, with both truth values represented there, supplies reversible meet separation.

The action hypothesis concerns admitted automorphisms with whole-operation identities. It does not assume that every external order permutation is admitted. An explicit full-function rational-chain model satisfies the theorem and fails C. A restricted translation subgroup in that same model shows that order primitivity is weaker than order 2-homogeneity as an action hypothesis.

## 1. Exact language and the admitted group

Work in H, retaining the fixed abbreviations T for Top and B for Bottom. Assume **BMeet**: primitive conjunction is associative, commutative and idempotent, and

$$
p\land T=p,\qquad p\land B=B.
\tag{1}
$$

Write p≤q for p∧q=p, and p<q for p≤q and p≠q. These are output identities, so BMeet supplies a bounded meet-semilattice. Its bounds have opposite truth values by the H truth clauses.

Put I:=λp.p and define composition by the admitted lambda term. As in [Reversible meet characterization](reversible-meet-characterization.md), let

$$
M(E):=(\lambda p,q.E(p\land q))
       =(\lambda p,q.Ep\land Eq).
\tag{2}
$$

Let G be an admitted predicate of type (tt)t satisfying the following conditions:

1. GI is true, and GE and GF imply G(E∘F).
2. GE implies M(E).
3. For every E with GE, there is an admitted F with GF and
   E∘F=I and F∘E=I.

Both inverse equations and (2) are whole-operation identities. The quantifiers range over admitted observers. This is a group of admitted operations in the sense needed here; no simultaneous choice of inverses is required. The full class Aut_M is one example. A subgroup defined by additional restrictions is allowed when those restrictions have the stated closure properties.

Every member of G is an order isomorphism. Meet preservation gives monotonicity, and its admitted inverse gives the reverse order implication. Surjectivity and uniqueness of the two bounds then give

$$
ET=T,\qquad EB=B.
\tag{3}
$$

Thus acceptance of T and rejection of B need not be separately imposed on this group.

The separation principle is

$$
S[G]:=\forall p,q\left[
p=q\leftrightarrow
\forall E\,(GE\to(Ep\leftrightarrow Eq))\right].
\tag{4}
$$

No preservation of negation, disjunction or any quantifier is included in G unless expressly added. In particular the quantification used to define a relation below does not assert that the observers preserve that quantifier.

## 2. The largest invariant congruence compatible with truth

Define the admitted relation

$$
R_G(p,q):=\forall E^{tt}\,[GE\to(Ep\leftrightarrow Eq)].
\tag{5}
$$

This is one lambda-defined relation of type ttt. The use of all members of the admitted predicate G is ordinary object-language quantification.

A relation U is **truth-compatible** when

$$
\forall p,q\,[U(p,q)\to(p\leftrightarrow q)],
\tag{6}
$$

and **G-invariant** when, for every E with GE,

$$
\forall p,q\,[U(p,q)\leftrightarrow U(Ep,Eq)].
\tag{7}
$$

These are material conditions on admitted relations. Equality of their higher-type objects is not being inferred from coextension.

**Proposition 1.** R_G is an equivalence relation, is truth-compatible and G-invariant, and is a meet congruence. It is the largest G-invariant truth-compatible admitted equivalence relation, ordered by inclusion of current extensions. It is also the largest admitted meet congruence having these two properties.

**Proof.** Equivalence follows from equality of truth profiles. Identity belongs to G, so (5) implies p↔q. For invariance, assume R_G(p,q) and GE. For any H with GH, closure gives G(H∘E), hence HEp↔HEq. This proves R_G(Ep,Eq). Apply the same argument to an admitted inverse of E for the converse.

Suppose R_G(p,q) and R_G(r,s). For every E with GE, the full meet identity gives the output identities

$$
E(p\land r)=Ep\land Er,\qquad
E(q\land s)=Eq\land Es.
$$

The H conjunction truth clause and the two profile agreements make these outputs materially equivalent. Thus R_G(p∧r,q∧s), proving the congruence condition.

Finally, if U satisfies (6)–(7) and U(p,q), invariance gives U(Ep,Eq) for every GE, and truth compatibility gives Ep↔Eq. Therefore U(p,q) implies R_G(p,q). This proves maximality; the proof of this inclusion does not even require U to be an equivalence. ∎

Consequently, over H+BMeet with the displayed group assumptions,

$$
\boxed{
\begin{aligned}
S[G]
&\longleftrightarrow
\text{every admitted G-invariant truth-compatible equivalence is equality}\\
&\longleftrightarrow
\text{every admitted G-invariant truth-compatible meet congruence is equality}.
\end{aligned}}
\tag{8}
$$

Here “is equality” means that the relation has precisely the pairs p=q as its current extension. The reverse implications use the particular admitted relation (5), so (8) does not assume that an external intersection of relations is admitted.

There is also a semantic quotient interpretation. The external quotient of the proposition domain by R_G inherits meet and the G action. It embeds faithfully in the sets of admitted group members by

$$
[p]\longmapsto\{E:GE\text{ and }Ep\text{ is true}\}.
\tag{9}
$$

Meet becomes intersection. Acting on p by H replaces the displayed set by its inverse image under right composition E↦E∘H. This states the representation and its compatibility with the action. It does not assert an admitted quotient type, a set of all external subsets, or an identity of higher characteristic operations. Reversible separation says exactly that this canonical quotient has not identified distinct propositions.

## 3. The exact convex obstruction for chains

Now assume the meet order is linear. A relation U on a specified part of the order is **convex** when every equivalence class is order-convex: if p≤r≤q and U(p,q), then U(p,r).

Truth is an upper segment of the meet order. Indeed p≤q and p true give p∧q=p true, so q is true. Every E in G is an order isomorphism. If p≤r≤q and R_G(p,q), the outputs Ep and Eq have the same truth value and Er lies between them. Upward closure of truth gives the same truth value for Er. Therefore R_G is convex.

Proposition 1 now has the chain formulation

$$
\boxed{S[G]\ \longleftrightarrow\quad
\text{there is no nontrivial admitted G-invariant, truth-compatible
convex equivalence}.}
\tag{10}
$$

“Nontrivial” here means that some distinct pair is related. The universal relation is not truth-compatible because T and B have opposite truth values. Convexity is an additional structural description of the maximal obstruction, not an assumption on arbitrary truth predicates.

For the next statements, suppose the bounded chain is dense: whenever p<q there is r with p<r<q. Put

$$
J(p):=B<p<T.
\tag{11}
$$

All equivalence, invariance and convexity conditions can be restricted to J by guarding their variables with J. These are still formulas about admitted relations. Equation (3) makes J invariant under G.

**Proposition 2.** On a bounded dense chain, (10) remains exact when the obstruction is sought only on J. In particular, if R_G is equality on J, then it is equality on the entire proposition domain.

**Proof.** A nontrivial admitted G-invariant truth-compatible equivalence on J lies inside R_G on J by the same maximality argument. Conversely the restriction of (5) is an admitted convex equivalence on J, so absence of the obstruction makes that restriction equality.

Suppose B and an interior p nevertheless agreed under every group member. All Ep would then be false by (3). Density supplies r with B<r<p. Since Er≤Ep, every Er would also be false. Hence R_G(r,p), contradicting equality on J. Similarly, if an interior p agreed with T, choose p<r<T. Every Ep would be true, and Er≥Ep would be true too, again contradicting equality on J. Identity itself distinguishes B and T. These are all remaining pairs. ∎

The endpoint argument uses interior predecessors and successors. Full density is a natural sufficient order assumption and is retained in the theorem below; it is not asserted to be minimal.

## 4. Order primitivity gives an atomless sufficient condition

Say that the admitted G action is **order-primitive on J** when every admitted G-invariant convex equivalence on J is either equality or the universal relation on J. This condition concerns the order and admitted action. It makes no reference to truth.

Assume also an interior truth contrast:

$$
\exists b,a\,[J(b)\land J(a)\land\neg b\land a].
\tag{12}
$$

Necessarily b<a, since truth is an upper segment.

**Theorem 3.** Over H, a bounded dense meet chain, an admitted group G as in §1, order primitivity on J, and (12) imply S[G]. In particular they imply separation by reversible whole-operation meet observers, fixing both bounds.

**Proof.** The restriction of R_G to J is an admitted invariant convex equivalence. It is not universal: identity belongs to G and distinguishes the witnesses b,a from (12). Order primitivity therefore makes it equality. Proposition 2 supplies equality on the entire domain, which is S[G]. ∎

This proof assumes neither an atom nor a least true proposition. It uses neither C, NI, ND, BF, Plenitude nor a Choice principle. Inverses and composition are supplied by the explicit admitted-group hypothesis; they are not inferred from external order symmetries.

A convenient stronger hypothesis is **order 2-homogeneity on J**:

$$
\forall p<q\text{ in }J\;\forall u<v\text{ in }J\;
\exists E\,[GE\land Ep=u\land Eq=v].
\tag{13}
$$

It implies order primitivity. If an invariant equivalence relates distinct p<q, (13) sends that pair to every u<v. Invariance and reflexivity make the relation universal. Thus (13) and (12) suffice. For an interior pair one can also see separation directly by sending it to b<a across the truth cut. The primitivity theorem does not require the stronger two-point motion in (13).

## 5. A full-function atomless H model below C

Take singleton individuals and proposition domain

$$
D_t=(\mathbb Q\cap[0,1])\setminus\{1/2\},
\qquad p\text{ true}\Longleftrightarrow p>1/2.
\tag{14}
$$

At every allowed relational arrow type take the full set of functions between the corresponding domains. There are no hidden arguments: admitted and outer domains coincide. Application and abstraction are ordinary function application and abstraction. Set

$$
p\land q=\min(p,q),\qquad
p\lor q=\max(p,q),\qquad
\neg p=1-p.
\tag{15}
$$

The removal of 1/2 makes negation truth-correct and keeps it an involution of the domain. Interpret each universal quantifier by 1 if all of the predicate's admitted instances are true, and by 0 otherwise. Interpret each existential quantifier analogously. Identity at every type returns 1 for actual equality and 0 for inequality. All these total operations belong to their full function domains.

The ordinary truth clauses hold. Actual equality gives reflexivity and Leibniz substitution; the full function interpretation gives contextual beta and eta; quantifiers range over exactly the admitted domain. The H soundness argument is the full-domain specialization of [Local tiers and models](local-tiers-and-models.md), §1. Functionality holds at every type because functions have no unobserved arguments. This explicitly verifies the higher-type and admission requirements, rather than relying only on a proposed proposition algebra.

The fixed abbreviation a=∀p p has value 0. Hence T=a∨¬a has value 1 and B=a∧¬a has value 0. The meet order is the bounded dense chain (14). It has no meet atoms, its true segment has no least member, and its false segment has no greatest member.

Every order automorphism of this chain fixes 0,1 and preserves min and max as full operations. Both it and its inverse are admitted by the full function domains. The interior is a countable dense linear order without endpoints. Any increasing correspondence between two ordered pairs extends to an order automorphism: enumerate the unused points on each side and alternately extend the finite increasing partial bijection, choosing the next image or preimage in the required nonempty interval. Density and absence of endpoints permit every step. Taking the union gives a bijection of the entire interior, and fixing 0,1 extends it to (14).

Thus the full admitted order-automorphism group satisfies (13). The elements 1/4 and 3/4 give (12). Theorem 3 proves reversible whole M separation. The same witnesses preserve primitive V as full operations, so the model also satisfies joint reversible M+V separation, with endpoint fixing. Full Functionality lifts these propositional results to full relational separation.

C fails. For example p=1/4 gives

$$
p\lor\neg p=3/4\ne1=T,
\tag{16}
$$

whereas H proves the material equivalence of excluded middle and T, and C's Logical Equivalence rule would identify them. No negation or quantifier preservation is claimed for the separating automorphisms. The model therefore shows that this atomless reversible semilattice theory does not entail C.

## 6. A primitive admitted subgroup which is not 2-homogeneous

The same full-function model also exhibits a strict distinction between the two action hypotheses used above. Choose an external order isomorphism φ from the interior J of (14) onto the ordered rationals. It exists by the same enumerated extension argument. For each rational r define

$$
E_r(p)=\varphi^{-1}(\varphi(p)+r)\quad(p\in J),
\qquad E_r(0)=0,\quad E_r(1)=1.
\tag{17}
$$

Every E_r and its inverse E_{−r} is an admitted full meet/join automorphism. Let G be a predicate whose true members are exactly these operations. Such a predicate is admitted in this particular model because its higher function domains are full; it can return 1 on the specified set of operations and 0 elsewhere. The construction makes no general claim that an external subgroup can be named in an arbitrary Henkin model, and it does not require an object-language choice of all the E_r.

This action is order-primitive, even with respect to external convex equivalences. To see this in rational coordinates, suppose an invariant convex equivalence relates x<y and put d=y−x>0. Translation invariance relates z to z+d for every rational z, and convexity relates every point between them. Given arbitrary s<t, choose a positive integer n with nd≥t−s. Transitivity along the n intervals of length d relates s to s+nd; convexity then relates s to t. The equivalence is universal. If no distinct pair is related, it is equality. This proves the required admitted version as well.

The action is not order 2-homogeneous: every translation preserves the rational difference φ(q)−φ(p), so ordered pairs with different differences cannot be matched. Nevertheless Theorem 3 applies to this admitted subgroup and gives S[G]. Its members also preserve max, so these restricted witnesses separate for the joint meet/join signature. This demonstrates the usefulness of the primitive-action criterion without replacing it by full two-point homogeneity.

## 7. Scope, duals and relation to the atom theorem

The maximal-congruence construction in §2 works on arbitrary bounded meet-semilattices, not only chains. Chain geometry makes that obstruction convex and gives the new sufficient criterion. In the atom-bearing region, the earlier [exact atom characterization](reversible-meet-characterization.md), §§2–4, describes the same separation requirement by atomisticity, a true atom and transitivity on atoms. The present theorem supplies a different positive region with no atoms at all. It does not claim that order primitivity is necessary for reversible separation on every chain or semilattice.

There is a dual join version. Assume primitive disjunction is a bounded join-semilattice, define its order by p∨q=q, and replace full M automorphisms by full V automorphisms. Truth is again an upper set, the orbit-truth equivalence is a join congruence, and on a dense chain the same convexity and endpoint arguments apply. A group preserving both full operations gives their joint separation by the same proof. Merely knowing pointwise preservation of an omitted primitive operation does not establish its whole-operation identity.

All primary statements use full M or full V and whole inverse equations in the hypotheses. Thus no Functionality is needed to upgrade a pointwise order permutation silently. There is also a pointwise version, obtained by using admitted operations with pointwise preservation and inverse equations throughout. Passing from that version to whole identities requires the relevant local Functionality instances, as in [Typed separation](typed-separation-and-classicism.md), §2. Full relational separation has the usual additional all-type Functionality requirement; the full-function model supplies it directly.

All relation and action quantifiers are at the displayed admitted types. There is no object-language quantification over types, no boxed claim, no assertion that arbitrary quotients or subsets are represented, and no implication that Plenitude by itself supplies reversible meet separation. The [six-element asymmetric-atom model](reversible-meet-characterization.md), §6, retains its contrary verdict.

## 8. Sources

The maximal invariant congruence, exact convex obstruction, admitted order-primitivity theorem and rational-chain constructions are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–7, unpaginated.

The fixed H language and type system are [the topic background](../../source/topics/classicism/background.md). The explicit model soundness is the full-domain instance of [Local separation tiers and models](local-tiers-and-models.md), §1, direct source `misc`; the current argument provides the new domain, operations and action verdicts. [Truth profiles and connective reducts](truth-profiles-and-connective-reducts.md), §§1–3, gives the earlier general set representation. [Reversible meet separation and atoms](reversible-meet-atomicity.md), §§2–6, and [its exact atom characterization](reversible-meet-characterization.md), §§2–6, give the distinct atom-bearing results. [Typed separation](typed-separation-and-classicism.md), §2, gives the stated higher-type factorization.

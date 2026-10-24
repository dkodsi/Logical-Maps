# Reversible separation from convex blocks and finite lattice factors

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–7, unpaginated.

Reversible separation can be reduced to a local action without requiring the entire action to be primitive. On a chain with an admitted invariant convex equivalence, the exact requirements are transitivity on its blocks and separation by the stabilizer of the block crossed by the truth cut. For a bounded distributive lattice with a fixed finite central partition, the corresponding requirements are transitivity on the factors and separation inside its unique true factor.

The two reductions concern admitted groups of observers with whole-operation identities. Full-function models give an imprimitive lexicographic chain and a non-chain finite product of atomless chains. Both satisfy joint reversible meet/join separation and fail C. Neither construction identifies lattice factors with proposition atoms.

## 1. Language, groups and local separation

Work in H, retaining the fixed abbreviations T for Top and B for Bottom. Initially assume **BMeet**: primitive conjunction is associative, commutative and idempotent, and

$$
p\land T=p,\qquad p\land B=B.
\tag{1}
$$
Write p≤q for p∧q=p and p<q for p≤q and p≠q. These are identities of proposition objects. Truth is an upper set: if p≤q and p is true, then the H truth clause for conjunction makes q true.

Put I:=λp.p and use the admitted lambda term for composition. An admitted predicate G of type (tt)t is a **whole-meet automorphism group** here when:

1. GI is true, and GE and GF imply G(E∘F).
2. Every E with GE satisfies

   $$
   M(E):=(\lambda p,q.E(p\land q))
         =(\lambda p,q.Ep\land Eq).
   \tag{2}
   $$
3. Every E with GE has an admitted F with GF and E∘F=I=F∘E.

Both inverse equations are whole-operation identities. Members of G are order isomorphisms and fix T and B. This follows from meet preservation, the admitted inverse, and uniqueness of the bounds; see [the invariant-congruence and order-action theorem](reversible-semilattice-order-actions.md), §1.

The separation formula is

$$
S[G]:=\forall p,q\left[
p=q\leftrightarrow
\forall E^{tt}(GE\to(Ep\leftrightarrow Eq))\right].
\tag{3}
$$
For an admitted invariant predicate U of propositions and an admitted subgroup K, write **Sep(K,U)** for the same formula with p,q restricted to U. No new type for U is introduced. Group closure and inverse existence are always assertions about admitted operations, not about external permutations which might fail to belong to a Henkin domain.

## 2. Exact reduction along convex blocks

Assume the meet order is a bounded dense chain, and put

$$
J(p):=B<p<T.
\tag{4}
$$
Let $\mathcal B^{ttt}$ be an admitted relation whose current extension is an equivalence relation on J. Assume its classes are convex, it is invariant under G, and each class has neither a first nor a last member. Explicitly, the latter two assumptions are

$$
\forall E,p,q\,[GE\land J(p)\land J(q)\to
 (\mathcal B(p,q)\leftrightarrow\mathcal B(Ep,Eq))],
\tag{5}
$$
$$
\forall p\in J\;\exists u,v\in J\;
[\mathcal B(p,u)\land\mathcal B(p,v)\land u<p<v].
\tag{6}
$$
All relations here are evaluated materially. Coextension is not identified with equality of the relation objects. Density and convexity make every block a dense chain, and (6) gives its lack of endpoints.

For a proposition c∈J define the admitted predicates

$$
C_c(p):=J(p)\land\mathcal B(c,p),
\qquad
G_c(E):=GE\land\mathcal B(c,Ec).
\tag{7}
$$
The second is the setwise stabilizer of the first. Indeed (5) shows that E sends the block of c onto the block of Ec. It follows that G_c contains I, is closed under composition, and contains an admitted inverse of each of its members. These statements use only the displayed admitted predicates and the original group assumptions.

Say that the block of c **crosses the truth cut** when

$$
\operatorname{Cross}(c):=
\exists a,b\,[C_c(a)\land C_c(b)\land\neg a\land b].
\tag{8}
$$
Necessarily a<b. Say that G is **transitive on blocks** when

$$
\operatorname{BlockTrans}(G,\mathcal B):=
\forall p,q\in J\;\exists E\,[GE\land\mathcal B(Ep,q)].
\tag{9}
$$
This is an ordinary formula about proposition and observer variables. It does not quantify over a quotient domain of blocks.

**Lemma 1: uniqueness of a crossed block.** At most one block crosses the truth cut. If C_c does, every block below C_c is entirely false and every block above C_c is entirely true.

**Proof.** Distinct convex classes in a linear order are ordered: every point of one lies below every point of the other. If a∈C_c is false and b∈C_c is true, every point in a lower block lies below a and is false; every point in an upper block lies above b and is true. This also proves uniqueness. ∎

**Lemma 2: local separation gives motion to both truth values.** If Sep(G_c,C_c), then every x∈C_c can be sent to a true proposition and to a false proposition by members of G_c.

**Proof.** Choose y<x<z in C_c using (6). A local separator of y,x must send y to a false proposition and x to a true one: order preservation excludes the opposite truth pattern. A local separator of x,z sends x to a false proposition and z to a true one. The two required automorphisms need not be the same. ∎

**Theorem 3: convex-block reduction.** Under the assumptions of this section,

$$
\boxed{
S[G]\ \longleftrightarrow\
\exists c\in J\,[\operatorname{Cross}(c)\land
\operatorname{BlockTrans}(G,\mathcal B)\land
\operatorname{Sep}(G_c,C_c)].}
\tag{10}
$$
Equivalently, for any specified c whose block crosses the truth cut, S[G] is equivalent to the last two conditions in (10).

**Proof, forward.** Pick two distinct points in one block; these exist by (6). A global separator sends them to different truth values, so their image block crosses the cut. Fix c in that block C.

For any block D, choose two distinct points of D and globally separate them. Their image block crosses the truth cut and hence is C by Lemma 1. Thus some member of G sends D onto C. Given two blocks, compose such a map for the first with an admitted inverse of such a map for the second. This gives (9).

If p,q∈C are distinct, a global separator sends them to different truth values. It therefore sends C to a crossed block, which must be C itself. The separator belongs to G_c. This proves Sep(G_c,C_c). The equal-input direction follows by substitution.

**Proof, reverse.** First suppose p,q are distinct interior points in the same block. By (9), send that block to C_c. The two images remain distinct; a local separator in G_c separates them. Composition gives a member of G separating p,q.

If p<q belong to different blocks, send the lower block to C_c. The image of q is above C_c. By Lemma 2 a member of G_c sends the image of p to a false proposition. It keeps the image of q above C_c, where every proposition is true by Lemma 1. The composite separates p,q.

For an interior p and B, send p's block to C_c and use Lemma 2 to make its image true. The same construction makes the image of p false when comparing p with T. Every group member fixes the bounds, and I separates B from T. These exhaust all unequal pairs. ∎

The no-endpoint assumption on each block is used in Lemma 2 and in obtaining distinct points in every block. No choice function selecting a map for every block is used: each argument chooses only the finitely many witnesses needed for the pair under consideration.

## 3. Primitive stabilizers and an imprimitive chain model

Say that G_c is **order-primitive on C_c** when every admitted G_c-invariant convex equivalence on C_c is either equality or universal there. This is a condition on the stabilizer's action on the block itself, which has no endpoints. It is not an invocation of a bounded-chain theorem on an incorrectly bounded subdomain.

**Corollary 4.** Suppose the assumptions of §2 hold and each block stabilizer is order-primitive on its block. Then

$$
\boxed{S[G]\ \longleftrightarrow\
\operatorname{BlockTrans}(G,\mathcal B)
\land\exists c\in J\,\operatorname{Cross}(c).}
\tag{11}
$$
**Proof.** Necessity is Theorem 3. For sufficiency choose a crossed block C_c and define the admitted relation on it

$$
R_c(p,q):=C_c(p)\land C_c(q)\land
\forall E\,[G_c(E)\to(Ep\leftrightarrow Eq)].
\tag{12}
$$
The argument of [the order-action theorem](reversible-semilattice-order-actions.md), §§2–3, relativizes to C_c: this is an invariant convex equivalence. Invariance uses admitted compositions and inverses, and convexity uses order preservation and upward closure of truth. It is not universal, because I distinguishes the two witnesses to Cross(c). Primitivity makes it equality on C_c, giving local separation. Apply Theorem 3. ∎

The assumption that every stabilizer is primitive can be weakened to primitivity of the crossed block's stabilizer. The displayed version keeps the structural action premise independent of which block currently crosses the truth cut.

Here is a full-function H model where this genuinely uses an imprimitive group. Take singleton individuals and proposition domain

$$
L=\{B,T\}\ \cup\
\bigl((\mathbb Q\times\mathbb Q)\setminus\{(0,0)\}\bigr),
\tag{13}
$$
with B least, T greatest, and the interior ordered lexicographically. Declare an interior point true exactly when it is lexicographically greater than (0,0); let T be true and B false. Interpret conjunction and disjunction by minimum and maximum. Negation exchanges B,T and sends (i,j) to (−i,−j). Removing (0,0) makes this negation truth-correct.

At every allowed arrow type take the full set of functions. Interpret each quantifier by T when its ordinary truth condition holds and by B otherwise; equality returns T for actual equality and B otherwise. Application and abstraction are ordinary application and abstraction. Thus the H truth rules, equality rules and contextual beta/eta hold, and Functionality holds at every type. This is the full-domain interpretation described in [Local tiers and models](local-tiers-and-models.md), §1. The fixed abbreviation a=∀p p has value B, so a∨¬a and a∧¬a give the displayed T,B.

Let $\mathcal B$ relate interior points with the same first coordinate, and let G consist of the order automorphisms preserving this block equivalence. The relation and the predicate for this particular subgroup are admitted because all the relevant function domains are full. Every group member preserves minimum and maximum as whole operations and has an admitted whole inverse.

Each block is a countable dense linear order without endpoints, including the zeroth block with its missing point. The group is transitive on blocks: an increasing automorphism of the quotient order Q can send any first coordinate to any other, and order isomorphisms of the countable dense fibers lift it. Such isomorphisms can be obtained by enumerating each fiber and alternately extending finite increasing partial bijections. This is an external construction of members in an explicitly full model, not an appeal to internal Choice in the abstract theorem.

The stabilizer of a block contains every order automorphism of that block extended by the identity outside it. Its action is order 2-homogeneous and hence order-primitive, by the same finite-partial-bijection construction. The zeroth block crosses the truth cut, with witnesses (0,−1) and (0,1). Corollary 4 gives S[G]. The same witnesses preserve both primitive operations, so this is joint reversible M+V separation. All-type Functionality gives its full relational form.

The group G is imprimitive: $\mathcal B$ is a nontrivial invariant convex equivalence on the interior. The statement concerns this admitted subgroup. It does not say that the unrestricted class of all meet automorphisms preserves these blocks; the unrestricted class also separates, simply because it contains the witnesses in G.

The meet order has no atoms, the true segment has no least member, and the false segment has no greatest member. C fails: for any proper interior p, max(p,¬p) is a proper interior element rather than T, although excluded middle is materially equivalent to T in H. No preservation of negation or of quantifiers is claimed for G.

## 4. Exact reduction along a finite central partition

Now assume that the primitive operations ∧ and ∨ make the proposition objects a bounded distributive lattice with the same B,T. These are actual output identities, not merely their truth tables. Let G be an admitted group as in §1 whose members also satisfy

$$
V(E):=(\lambda p,q.E(p\lor q))
       =(\lambda p,q.Ep\lor Eq).
\tag{14}
$$
Fix an **external finite list** e₁,…,eₙ, where n≥1, satisfying

$$
e_i\ne B,\qquad e_i\land e_j=B\ (i\ne j),\qquad
e_1\lor\cdots\lor e_n=T.
\tag{15}
$$
This is a finite central partition in the sense used here: each e_i has complement the join of the other entries. For n=1 the complementary join is B. Assume G preserves this finite set of factor units. For every GE and every i there is j with E(e_i)=e_j. Its inverse shows that these images permute the units. One can name the set by the admitted predicate $P(x):=\bigvee_{i=1}^{n}(x=e_i)$; no finite-set object or internal natural-number quantifier is required.

There is **exactly one true factor unit** w. The finite join in (15) is true, so at least one e_i is true by the H disjunction truth clause. Two true units would have a true meet, contradicting their meet's identity with B. Choosing the true unit is a finite case distinction in this fixed theorem instance, not an admitted selection operation over arbitrary partitions.

For every proposition z,

$$
z\leftrightarrow z\land w.
\tag{16}
$$
This is a material truth equivalence because w is true; it is not the identity z=z∧w. Distributivity and (15) separately give the output identity

$$
p=(p\land e_1)\lor\cdots\lor(p\land e_n).
\tag{17}
$$
Let $U_w(p):=p\le w$, the interval [B,w], and define its admitted stabilizer

$$
G_w(E):=GE\land Ew=w.
\tag{18}
$$
It is a group of admitted whole lattice automorphisms of that interval. Define **FactorTrans** by the finite family of formulas

$$
\bigwedge_{1\le i,j\le n}
\exists E\,[GE\land E(e_i)=e_j].
\tag{19}
$$
**Theorem 5: finite-factor reduction.** Under these assumptions,

$$
\boxed{S[G]\ \longleftrightarrow\
\operatorname{FactorTrans}\land\operatorname{Sep}(G_w,U_w).}
\tag{20}
$$
**Proof, forward.** Separate e_i from B. Every group member fixes B, so the separator sends e_i to a true unit, necessarily w. Thus every factor unit can be sent to w. Composing these witnesses with admitted inverses gives (19).

Suppose x,y≤w are distinct, and let E globally separate them. Both outputs are below Ew, which is some factor unit. If Ew were false, both outputs would be false by upward closure of truth, contradicting separation. Therefore Ew=w and E belongs to G_w. This proves local separation on [B,w].

**Proof, reverse.** If p≠q, (17) implies p∧e_i≠q∧e_i for some i. By (19), choose E sending e_i to w. Injectivity and meet preservation give

$$
Ep\land w\ne Eq\land w.
\tag{21}
$$
These are in [B,w], so a member H of G_w locally separates them. Its meet preservation and Hw=w identify their images with HEp∧w and HEq∧w. By (16), these have the same respective truth values as HEp and HEq. Thus H∘E is a global separator. ∎

The transitivity in (19) is on the finite **factors**, not on proposition atoms. The factors may be infinite and atomless. In the special case that each interval [B,e_i] has only B,e_i, local separation is automatic, and the theorem specializes to the familiar finite atomic case. That special case is not being assumed here.

## 5. Primitive factor actions and a product of atomless chains

Suppose, in addition to the assumptions of §4, that [B,w] is a bounded dense chain and the stabilizer G_w is order-primitive on its open interval (B,w). Then

$$
\operatorname{Sep}(G_w,U_w)
\quad\longleftrightarrow\quad
\exists b,a\,[B<b<w\land B<a<w\land\neg b\land a].
\tag{22}
$$
For sufficiency use the bounded dense-chain order-primitivity theorem from [the order-action note](reversible-semilattice-order-actions.md), §§3–4, with upper bound w. Its proof uses only that the interval's bounds are fixed and have opposite truth values. It does not require w to be the global abbreviation T. For necessity, choose distinct interior points. Their local separator keeps both outputs interior and gives the required truth contrast. Density guarantees such points exist.

Combining (20) and (22) gives an exact criterion using factor transitivity and an interior truth contrast in the true factor. One can assume the structural density and primitivity conditions for every factor, so that these premises do not depend on the current choice of w.

For a non-chain example, fix an external integer n≥2 and set

$$
L_0=(\mathbb Q\cap[0,1])\setminus\{1/2\},
\qquad D_t=L_0^n.
\tag{23}
$$
A vector is true exactly when its first coordinate exceeds 1/2. Interpret ∧ and ∨ coordinatewise by minimum and maximum, and negation coordinatewise by x↦1−x. Let B=(0,…,0) and T=(1,…,1). Take singleton individuals and full function domains at all allowed arrow types. Quantifiers return T or B according to their ordinary truth conditions, and equality returns T or B according to actual equality. As in §3, this gives H and all Functionality, with the displayed fixed abbreviations for the bounds.

Let e_i have value 1 in coordinate i and 0 elsewhere. These form the partition (15), and e₁ is its unique true unit. Let G consist of coordinate permutations composed with independent order automorphisms of the coordinate chains. It is an admitted group in this full-function model, preserves both primitive operations as whole operations, and acts transitively on the factor units. The stabilizer of e₁ includes all order automorphisms of the first factor, acting identically on the others. Its action on (B,e₁) is order 2-homogeneous and hence primitive. The vectors

$$
(1/4,0,\ldots,0),\qquad(3/4,0,\ldots,0)
\tag{24}
$$
give its interior truth contrast. Theorems (20)–(22) supply joint reversible M+V separation; full Functionality supplies the full relational version.

This is a distributive lattice of higher rank than a chain: e₁ and e₂ are incomparable. It has no proposition atoms. For any nonzero vector choose a positive coordinate and a strictly smaller positive rational in that coordinate, setting the others to zero. This gives a nonzero strict lower bound of the original vector. No infinite selection is used for this individual witness.

C again fails. Taking every coordinate of p to be 1/4 makes p∨¬p the vector with every coordinate 3/4, which differs from T. The finite number n counts the externally specified factors; it does not assert internal finiteness of the proposition domain. No negation or quantifier preservation is asserted for the separating group.

## 6. What the reductions do and do not require

The block theorem is an exact theorem for a specified admitted invariant convex relation and specified admitted group. The factor theorem is an exact theorem for a specified finite partition preserved by the specified group. Neither introduces an admitted quotient domain, takes an external intersection to be an admitted predicate, or assumes an internal Choice principle.

In the block theorem, local separators cross the truth cut inside one convex block, while block transitivity moves any other block into it. In the lattice theorem, identity (17) detects a differing component, factor transitivity moves that component into the true factor, and (16) recovers the global truth test. These are different mechanisms with the same local-to-global form. Order primitivity is a sufficient structural way to obtain the local separation; it is not asserted to be necessary in the unrestricted setting.

The primary statements assume whole M, whole V where specified, and whole inverse identities from the outset. There are parallel pointwise statements, but upgrading pointwise laws to equality of composite operations requires the corresponding local Functionality instances. No such upgrade is silently made over H. The general [typed-separation factorization](typed-separation-and-classicism.md), §2, adds all-type Functionality to pass from propositional to full relational separation; both concrete models supply that hypothesis directly.

No C, NI, ND, BF, Plenitude, proposition-atom premise or modal boxing is used in the abstract reductions. The finite list in §4 is external: each fixed n gives its own finite formula instance. There is no object-language quantifier over n, partitions of arbitrary internal cardinality, or types. The examples' full function domains justify their specified actions and predicates only in those explicit models, not in arbitrary Henkin models.

## 7. Sources

The exact convex-block reduction, primitive-stabilizer corollary, finite central-factor reduction, and their two explicit H models are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–6, unpaginated.

The fixed language and type conventions are in [the topic background](../../source/topics/classicism/background.md). The admitted invariant-congruence and primitive-action arguments extended here are [Reversible semilattice separation from order actions](reversible-semilattice-order-actions.md), §§1–7, direct source `misc`. [Local separation tiers and models](local-tiers-and-models.md), §1, supplies the general full-domain H interpretation whose operations are specified in §§3 and 5 above. [The exact atom characterization](reversible-meet-characterization.md), §§2–6, gives the earlier atom-bearing comparison. [Typed separation](typed-separation-and-classicism.md), §2, supplies the stated full relational factorization.

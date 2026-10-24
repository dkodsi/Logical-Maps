# Finite-block symmetry model: even sizes versus powers of two

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the construction choices and new verdicts: `misc`, this note, §§1–8, unpaginated. The underlying symmetric ideally-full model construction is cited separately in §9.

This two-object model satisfies C5 and necessary full ordinary logical separation, but fails full reversible logical separation. Its proposition algebra is atomless at both objects. The obstruction is a closed pure choice sentence whose truth differs between the two objects.

Consequently the established implication is strict:

$$
\boxed{\mathrm{Rev}\ \Longrightarrow\
\mathrm{C5}+\Box\mathrm{OS},
\qquad
\mathrm{C5}+\Box\mathrm{OS}\ \not\Longrightarrow\ \mathrm{Rev}.}
\tag{1}
$$

All observer preservation laws are full composite identities. OS and its boxed form have the full relational scope and every finite external type list. The argument for failure of Rev uses [Rev implies No Pure Contingency](reversible-separation-and-pure-truth.md), not an unproved necessity of the local-conjugacy criterion.

## 1. The two objects and their symmetry groups

Let W and V be countably infinite sets, partitioned as follows:

- W has countably infinitely many blocks of each positive even finite size 2,4,6,8,….
- V has countably infinitely many blocks of each size 2^n for n≥1, and no other block sizes.

Write $\mathcal B$ and $\mathcal C$ for these respective block partitions. Define

$$
G:=\prod_{B\in\mathcal B}\mathrm{Sym}(B),
\qquad
H:=\prod_{C\in\mathcal C}\mathrm{Sym}(C).
\tag{2}
$$

Each group preserves **each individual block setwise**; it does not permute different blocks. It contains all independent choices of permutations within the blocks. These are closed permutation groups: preserving any specified finite block setwise is a closed condition, and the groups are the intersections of those conditions.

Use W,V as the two objects of the symmetric ideally-full action construction. Include every bijection between every ordered pair of objects as an arrow. Use finite pinning at both objects, designated symmetry group G at W and H at V, and exactly the symmetric finitely pinned intensions at every relational type. Individuals are the underlying objects. If a signature expansion is wanted, interpret every nonlogical relational constant by the top element of its type.

The construction is in the fixed relational language. All bijections of individuals used in the proof are external semantic arrows, not object-language functions of type e→e. The originating construction supplies a model of C. Since every arrow has an inverse, its action on each admitted type is bijective; equality is necessary and distinctness is necessary at every type and every object. Thus C5 holds throughout the model. In particular all Barcan instances and Functionality hold throughout it.

## 2. Mutual stabilizer inclusion and necessary ordinary separation

There exist bijections j:W→V and k:V→W such that

$$
jGj^{-1}\subseteq H,
\qquad
kHk^{-1}\subseteq G.
\tag{3}
$$

Here is an explicit general packing argument that proves both assertions. Each source and target partition has arbitrarily large even blocks and infinitely many 2-blocks. Enumerate the source blocks of size greater than two and all target blocks. At each finite stage:

1. Put the next unassigned source block of size greater than two inside a fresh target block of at least that size. Fill its even-sized remainder with previously unused source 2-blocks.
2. Fill the next unassigned target block entirely with previously unused source 2-blocks.

Always use the least unused source 2-blocks in a fixed enumeration. Each finite stage has used only finitely many blocks, so the needed sufficiently large target block and source 2-blocks remain. Every source block of size greater than two and every target block is eventually assigned; step 2 consumes at least one source 2-block at each stage, so every such source block is eventually assigned as well. Choose bijections on these finite pieces. Their union is a bijection that sends each source block inside one target block. Conjugation by it sends every within-source-block permutation to a within-target-block permutation. Apply this argument in each direction to obtain (3).

The [arrow-evaluation representation theorem](../operator-representation.md), §§4–6, applies to precisely this all-bijections, finite-pinning framework. It says that a map b:X→Y satisfying

$$
bG_{X,(S)}b^{-1}\subseteq G_Y
$$

for a finite S supplies an admitted observer evaluating current propositions at b, qualified by the full Boolean and quantifier operation identities at every fixed finite type list. A sufficient separation condition at X is that each target Y has one such comparison bijection with a finite stabilizer.

For each self-target use the identity bijection. For the other target use j or k from (3), with the initial stabilizer restriction empty. To see the separation construction directly, let a nonempty proposition p at X be pinned by P and contain h:X→Y. Approximate j^{-1}h on P by a finite-support permutation π of X and put b=jπ. Then b∈p. On a finite set containing the support of π, the source stabilizer commutes with π, so b still meets the inclusion condition. The representation theorem gives a fully qualified observer accepting p. Applied to Boolean differences, these observers separate all propositions.

Functionality lifts this to every relational output type. The argument works at both objects, for every finite qualification list; every future evaluation is at one of these objects. Hence

$$
\mathrm{OS}\quad\text{and}\quad\Box\mathrm{OS}
$$

hold at both objects, with the boxed schema read instance by instance. The witnesses are admitted observers with full composite identities, not just external evaluations or material homomorphisms.

## 3. Atomlessness

Let p be a nonempty proposition at either source object X, pinned by finite S, and choose h:X→Y in p. Choose a target block D of Y disjoint from h(S), and two distinct points i,j outside S whose h-images lie in D. Choose a point outside D∪h(S), and let τ exchange that point with h(j), fixing h(S) and h(i). Then τh agrees with h on S, so τh∈p as well.

Let q be the proposition that an arrow ends at Y and sends i,j into the same designated Y-block. It is pinned by {i,j} and symmetric under the designated group at Y; at the other target it is false. Hence q is admitted. It contains h and omits τh. Therefore p∧q and p∧¬q are both nonbottom. This splits every nonbottom proposition and proves atomlessness at both objects.

In particular the model lies on the atomless side of [the necessary-separation/one-atom theorem](necessary-separation-and-atoms.md); it does not conflict with that result.

## 4. Extending invariant current relations

We will use the following admission lemma at either object X, with designated group K.

**Lemma.** Let R be an arbitrary external relation on a finite tuple of current admitted domains at X. Suppose R is invariant under the simultaneous action of K_(S) for some finite S⊆X. Then R is the current extension of an admitted relation of the corresponding relational type.

**Proof.** Define its intension at an arrow h:X→Y and a tuple u at Y by the following rule. If Y=X and h|S=g|S for some g∈K, declare it true exactly when ρ(g^{-1})u belongs to R. At all other arrows declare it false. If g'=gv is another witness, then v∈K_(S); invariance of R makes the value independent of that witness. The profile is S-pinned. For μ∈K, replacing h,u,g by μh,ρ(μ)u,μg preserves the value, so it is symmetric; at other targets it stays false. At id_X, take g=id_X, giving exactly R. Symmetric ideal fullness supplies the admitted relation. □

This lemma does not assert arbitrary extensional fullness. The finite-stabilizer invariance is its substantive hypothesis. It will be verified for each relation used below.

## 5. The closed pure sentence MC₆

For X:et let Six(X) say that exactly six individuals satisfy X. It can be written using six existential individual variables, pairwise distinctness, and the assertion that every satisfying individual equals one of them. This uses a fixed external numeral six, not an internal finiteness convention.

For A:(et)t put

$$
\begin{aligned}
\mathrm{DisjointSix}(A):={}&
\forall X\,(AX\to\mathrm{Six}(X))\\
&\land\forall X,Y\,[AX\land AY\land X\ne Y
\to\forall x\,\neg(Xx\land Yx)].
\end{aligned}
$$

Define the closed pure sentence

$$
\begin{aligned}
\mathrm{MC}_6:=\forall A^{(et)t}\bigl[
\mathrm{DisjointSix}(A)\to
\exists R^{(et)(et)}\forall X^{et}\bigl(AX\to{}&
(\exists x\,R(X,x))\\
&\land\forall x\,(R(X,x)\to Xx)\\
&\land\exists x\,(Xx\land\neg R(X,x))\bigr)\bigr].
\end{aligned}
\tag{4}
$$

Thus R must select a nonempty proper subset of each family member. It need not select a single individual or an intensional property object. The only higher-type object requested is the admitted relation R.

Disjointness is stated for distinct intensional family members. Since each member has a nonempty six-element extension, it also ensures that two members with the same current extension are identical. This detail controls the possible movement of intensions in the proof.

## 6. MC₆ fails at the even-block object W

For each six-block B∈$\mathcal B$, let X_B be the canonical rigid property whose extension at h:W→Y is h(B). Formally, its truth profile is

$$
X_B(h,x)\quad\Longleftrightarrow\quad x\in h(B).
$$

It is pinned by B and symmetric at every target, so X_B is admitted. For g∈G, transport gives ρ(g)X_B=X_{g(B)}=X_B, because G preserves B setwise. The current family consisting of all these X_B is therefore G-invariant. The lemma of §4, with empty S, gives an admitted A with exactly that current extension. It satisfies DisjointSix(A).

Suppose an admitted R selected a nonempty proper subset of each member. Let S be a finite pin for R. Choose a six-block B disjoint from S. Every permutation of B, extended by identity elsewhere, belongs to G_(S). Finite pinning and target symmetry make the current extension of R invariant under G_(S). Since X_B is itself fixed by these permutations, the selected subset
$\{x\in B:R(X_B,x)\}$
is invariant under the full symmetric group of B. That group is transitive, so the subset is empty or all of B, contradicting (4). Thus MC₆ is false at W.

## 7. MC₆ holds at the power-of-two object V

Let A be any admitted object satisfying DisjointSix(A) at V. Choose a finite pin S for A and let S0 be the union of the finitely many H-blocks meeting S. This union is finite. The current extension of A is invariant under H_(S0).

Call the six-element current extensions of A's members its cells. They are pairwise disjoint. We first show:

$$
\text{If a cell D meets a block C disjoint from S0, then }C\subseteq D.
\tag{5}
$$

Indeed, if x∈D∩C and y∈$C\setminus D$, the transposition exchanging x,y lies in H_(S0). It carries the property object X with extension D to another A-member with extension $(D\setminus\{x\})\cup\{y\}$. The two extensions differ but overlap in five points. The property objects must therefore be distinct, contradicting A's disjointness. This proves (5), including for cells that also meet S0.

Only finitely many cells meet S0, because they are disjoint and S0 is finite. Call them exceptional cells, and let S1 be S0 together with all their points. By (5), any points they add outside S0 comprise entire H-blocks. Hence S1 is itself a finite union of blocks. There is no iterative or infinite enlargement of the pin.

Every other cell avoids S1 and, by (5), is a union of whole H-blocks. Its size is six, and six is not a power of two, so it contains at least two such blocks. The only possible constituent sizes are 2+4 or 2+2+2. Fix an external enumeration of all H-blocks. For each nonexceptional cell choose its least-index constituent block as the selected subset. This is nonempty and proper. For each exceptional cell choose its least individual in a fixed external enumeration of V; that singleton is also nonempty and proper, and all its points lie in S1.

Define a current relation R(X,x) to hold when AX is true and x is in the subset just selected from X's extension; let it be false otherwise. We verify that this relation is invariant under H_(S1). That group fixes A, hence preserves its current family. It preserves every nonexceptional cell and its selected block, since it preserves every H-block individually. It fixes every point of an exceptional cell. If a family member X were moved to a distinct property object with the same nonempty current extension, those two A-members would violate disjointness; thus this possible intensional ambiguity cannot occur. Equivalently, the selection rule depends only on the extension and is equivariant throughout the family. Outside the family the relation remains false.

The admission lemma of §4 now supplies an admitted relation with exactly this R as current extension, pinned by S1. It fulfills (4). Since A was arbitrary, MC₆ is true at V. The external enumerations merely define a stabilizer-invariant current relation in this semantic proof; no object-language choice principle or admissibility of those enumerations is assumed.

## 8. Failure of reversible separation and of the conjugacy upgrade

The sentence MC₆ is closed and pure. It is true at V and false at W, and there are arrows between the two objects. Therefore at V it is true but not necessary. At W its negation is true but not necessary. No Pure Contingency fails at both objects.

By [Reversible logical separation implies No Pure Contingency](reversible-separation-and-pure-truth.md), full Rev consequently fails at both objects. Together with §§1–3, this gives the announced atomless countermodel

$$
\mathrm{C5}+\Box\mathrm{OS}+\neg\mathrm{Rev}.
$$

There is an explicit failed propositional instance. Take

$$
\Delta=\{t,e,et,(et)t,(et)(et)\}.
\tag{6}
$$

The types e, et, (et)t and (et)(et) are precisely the bound-variable types needed in the expanded sentence MC₆; t additionally covers the fixed endpoint abbreviation and is harmless. By the term-induction proof in the cited No Pure Contingency note, every Good_Δ involution fixes MC₆ as a proposition. It therefore cannot distinguish MC₆ from Top at V, or ¬MC₆ from Top at W.

The [reversible-to-involutive patching construction](../logical-observer-hierarchy.md), §4, preserves the **same** qualification list Δ over the C5 background already present here. Explicitly, if a reversible Good_Δ observer E accepted a false nonbottom d, with qualified inverse F, put c=¬d∧Ed, b=Fc and r=¬(c∨b). Then

$$
T(p)=(c\land Ep)\lor(b\land Fp)\lor(r\land p)
$$

is a Good_Δ involution accepting d. Boolean patching uses only the already listed quantifier laws; C5 supplies any required Barcan and Functionality instances without extending Δ. At V apply this to d=¬MC₆; at W apply it to d=MC₆. A reversible observer distinguishing the corresponding true sentence from Top would accept d, and hence would produce an impossible separating involution. Thus all eligible reversible observers agree on the displayed pair even though the propositions are unequal. Propositional reversible separation for exactly (6) fails at both objects. No assertion that every reversible separation instance fails is made.

The groups also refute the proposed purely group-theoretic upgrade from mutual local inclusion to local conjugacy. Every finite point stabilizer G_(S) retains infinitely many orbits of size six: all untouched six-blocks. Every finite point stabilizer H_(T) has only finitely many six-orbits: untouched blocks have power-of-two sizes, and only the finitely many blocks meeting T can yield new remaining orbits of size six. Conjugation by any bijection preserves orbit sizes and their multiplicities. Thus no G_(S) and H_(T) are conjugate, despite (3).

This last observation explains why the [local chart-swap theorem](local-conjugacy-and-reversible-observers.md) cannot apply across the objects. It is not the argument establishing failure of arbitrary reversible observers; that verdict was obtained independently from the pure-sentence distinction.

## 9. Sources

The finite-block construction, mutual-inclusion packing, atomlessness proof and MC₆ verdicts are new arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–8, unpaginated.

The underlying model family is Cian Dorr, *Boolean Completeness does not imply Rigid Comprehension*, draft of 30 July 2026, Definitions 15–18, p. 8; §3.1, p. 9; Lemma 21, p. 10, recorded in [Symmetric ideally-full models](../../source/topics/classicism/groups/symmetric-ideally-full.yaml). Its ideally-full action antecedent is Bacon and Dorr, *Classicism*, draft of 16 May 2023, Appendix D, pp. 73–79. Those sources supply the semantic framework, not the new block-size choice or its observer verdicts.

The full-operation ordinary-separation criterion used in §2 is [Atomic observers and finite stabilizers](../operator-representation.md), §§4–6, direct source `misc`, unpaginated. The independently established observer obstruction is [Reversible logical separation implies No Pure Contingency](reversible-separation-and-pure-truth.md), §§1–4, direct source `misc`, unpaginated, with its underlying conjugation argument attributed there.

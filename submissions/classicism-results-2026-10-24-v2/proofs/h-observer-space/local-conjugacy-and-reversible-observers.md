# Local symmetry conjugacy supplies reversible logical observers

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the observer construction: `misc`, this note, §§1–6, unpaginated. The originating symmetric-model construction and the earlier one-way representation theorem are identified in §7.

In symmetric ideally-full models with all bijections as arrows and finite pinning, equality of suitable point stabilizers gives an admitted involution that exchanges two neighborhoods of evaluations. This supplies full logical reversible separation in every one-object model in that precise framework, with any designated symmetry group. It also applies to multiobject families with conjugate symmetry groups, or with a finite base for every group.

This is a sufficient model criterion. It does not establish that necessary ordinary separation implies reversible separation. The known criterion for ordinary separation uses one-way stabilizer inclusion; the construction below uses a compatible two-way equality.

## 1. Exact semantic framework

Use the symmetric ideally-full action construction in [the recorded model family](../../source/topics/classicism/groups/symmetric-ideally-full.yaml), with these additional specifications:

1. Every underlying object is a countably infinite set.
2. The arrows from W to V are **all** bijections W→V.
3. Each object V has a designated subgroup G_V of its permutation group. No topological closedness is assumed.
4. At every relational type, the domain consists of exactly the symmetric intensions pinned by some finite subset of the source object.

Individuals are the underlying objects, with the stated arrow action. All arrow maps here are external semantic bijections; no object-language type e→e is introduced. The fixed language is the usual relational language. The pure-language observer conclusion is unaffected by any admissible interpretation of extra nonlogical constants.

Composition of arrows is written multiplicatively, with the rightmost arrow applied first. For a finite S⊆W put

$$
G_{W,(S)}:=\{g\in G_W:g|_S=\mathrm{id}|_S\}.
$$
A proposition p at W is a set of arrows out of W. Its symmetry means that h∈p iff kh∈p for each k∈G_V when h:W→V. A finite pin P means that arrows with the same target and the same restriction to P agree on membership in p. Actual truth at W is membership of id_W.

More generally, a tt intension E at W has a truth profile E(h,q), where h:W→Z and q is a proposition at Z. Finite pinning concerns h, holding its target and q fixed. Symmetry requires

$$
E(\mu h,\rho_t(\mu)q)=E(h,q)
\qquad(\mu\in G_Z).
\tag{1}
$$
For propositions, transport satisfies

$$
k\in\rho_t(\mu)q\quad\Longleftrightarrow\quad k\mu\in q.
\tag{2}
$$
Every arrow acts bijectively on every admitted type, with its inverse arrow supplying the inverse action. Thus C5, all Barcan instances and Functionality hold in these groupoid models. Whole-operation identities are still checked at every future coordinate below; current truth preservation alone would not suffice.

## 2. The local chart hypothesis

Fix W,V, an arrow b:W→V and finite S⊆W satisfying

$$
bG_{W,(S)}b^{-1}=G_{V,(bS)}.
\tag{LC}
$$
Consider two sets of arrows out of W:

$$
\begin{aligned}
C_0&:=\{h:W\to W:\exists g\in G_W,\ h|_S=g|_S\},\\
C_1&:=\{h:W\to V:\exists k\in G_V,\ h|_S=(kb)|_S\}.
\end{aligned}
\tag{3}
$$
Both are symmetric and S-pinned, hence admitted propositions. Assume C_0 and C_1 are disjoint. This is automatic if W≠V; in §5 it follows even when W=V by placing the charts on opposite sides of a proposition. Notice id_W∈C_0 and b∈C_1.

**Local swap lemma.** Under (LC) and disjointness, there is an admitted observer E:tt with E∘E=I as a whole-operation identity, qualified by full Boolean and quantifier identities at every finite list of types. At the actual evaluation it has truth profile

$$
E(\mathrm{id}_W,p)\quad\Longleftrightarrow\quad b\in p.
\tag{4}
$$
The same semantic E satisfies every finite qualification; no infinite conjunction is inserted into the object language.

## 3. Construction and admission

Define E(h,q) by

$$
E(h,q)\quad\Longleftrightarrow\quad
\begin{cases}
b g^{-1}\in q,&h\in C_0,\ h|_S=g|_S,\ g\in G_W,\\
b^{-1}k^{-1}\in q,&h\in C_1,\ h|_S=(kb)|_S,\ k\in G_V,\\
\mathrm{id}_Z\in q,&h:W\to Z\text{ outside }C_0\cup C_1.
\end{cases}
\tag{5}
$$
The arrows tested against q have q's source as their domain, so every case is typed correctly.

**Independence of witnesses.** In the first case, if g'=gu also agrees with h on S, then u∈G_{W,(S)}. By (LC), bu^{-1}b^{-1}∈G_V. Thus

$$
b(g')^{-1}=(bu^{-1}b^{-1})(bg^{-1})
$$
has the same membership in q as bg^{-1}, by q's target symmetry. In the second case, k'=kv with v∈G_{V,(bS)}. The reverse inclusion in (LC) gives b^{-1}v^{-1}b∈G_W, so the same argument applies to b^{-1}(k')^{-1}. Consequently (5) defines a truth profile without choosing representatives of the relevant orbits.

**Finite pinning.** Its branch and all possible witnesses depend only on the target of h and h|S. Hence S pins E.

**Target symmetry.** If h∈C_0 is represented by g and μ∈G_W, then μh is represented by μg. Equations (2) and (5) give

$$
bg^{-1}\mu^{-1}\in\rho_t(\mu)q
\quad\Longleftrightarrow\quad bg^{-1}\in q.
$$
The C_1 calculation replaces k by μk and is identical. Both charts are invariant under their target symmetry groups, so an arrow outside them stays outside. In the default branch, id_Z∈ρ_t(μ)q iff μ∈q iff id_Z∈q. This proves (1). By symmetric ideal fullness, E is an admitted tt object. At id_W, choosing g=id_W gives (4).

## 4. Involution and full logical identities

It is useful to call the observation arrow selected by (5) at h an a_h; choices change no evaluation of a symmetric proposition. For a future arrow r:W→Z, a proposition q at Z and l:Z→Y, application and transport give

$$
l\in(\rho_{tt}(r)E)(q)
\quad\Longleftrightarrow\quad a_{lr}l\in q.
\tag{6}
$$
This formula checks identities on arbitrary q in the future domain, not merely on propositions transported from W.

**The involution identity.** Put h=lr. If h∈C_0 has witness g, its observation arrow is a_h=bg^{-1}. The composite a_hh agrees with b on S, so it lies in C_1 with witness k=id_V. Its next observation arrow can therefore be taken to be b^{-1}. Applying (6) twice tests q at

$$
b^{-1}bg^{-1}l=g^{-1}l.
$$
This agrees with testing q at l, because g^{-1}∈G_W and W is the target of l in this case. If h∈C_1 has witness k, the first observation arrow is b^{-1}k^{-1}. Its composite with h lies in C_0 with witness g=id_W, so the second observation arrow is b. The round trip tests q at k^{-1}l, again equivalent to l by target symmetry. Outside both charts the observation arrow is the identity, and the branch remains unchanged. Thus at every r, for every q and every l,

$$
(\rho_{tt}(r)E)((\rho_{tt}(r)E)q)=q.
$$
These complete future profiles are identical, proving E∘E=I as an operation identity.

**Boolean operations.** Formula (6) evaluates each input proposition at a single arrow. Such evaluation preserves the Boolean set operations and both endpoints. The calculation holds for every future r and every input tuple, giving the full Boolean composite identities.

**Quantifiers at any type σ.** Fix r and l as in (6), and let a=a_{lr}:Y→U. The left side of universal commutation, evaluated at l, says that the transported predicate ρ_{σt}(al)F holds of every σ-object at U. The right side says it holds of every object of the form ρ_σ(a)y with y in the σ-domain at Y. These statements are equivalent because ρ_σ(a) is onto, with inverse ρ_σ(a^{-1}). The existential calculation is the same. It holds for every future r and every F in that future domain, so it proves the full quantifier-operation identities, not only their pointwise truth laws.

Finally every equality proposition is an endpoint, since all arrow actions are injective. E fixes those endpoints, so the equality clauses in the complete Good_Δ qualification hold as well. This completes the local swap lemma at every requested finite type list.

## 5. A criterion that supplies all separators

Assume that for each object V there exist a bijection j_V:W→V and a finite D_V⊆W such that

$$
j_VG_{W,(D_V)}j_V^{-1}=G_{V,(j_VD_V)}.
\tag{7}
$$
Then full typed reversible separation holds at W.

To prove propositional separation, let p≠q and let d be their nonzero Boolean symmetric difference. If d is true, identity already distinguishes p and q. Otherwise choose an arrow h:W→V in d and a finite pin P for d. Extend the finite partial bijection (j_V^{-1}h)|P to a finite-support permutation π of W. Such an extension exists by completing its finitely many partial cycles and paths on the finite union of its domain and image. Set

$$
b:=j_V\pi,
\qquad
S\supseteq P\cup D_V\cup\mathrm{supp}(\pi)
$$
with S finite. Then b agrees with h on P, hence b∈d. Enlarging D_V to S in (7) gives

$$
j_VG_{W,(S)}j_V^{-1}=G_{V,(j_VS)},
$$
by intersecting both sides with the stabilizers of the additional points. Every permutation fixing S pointwise commutes with π, and πS=S. Consequently

$$
bG_{W,(S)}b^{-1}
=j_VG_{W,(S)}j_V^{-1}
=G_{V,(bS)}.
$$
Construct C_0,C_1 from b,S. Since S contains P, every arrow in C_0 agrees, up to target symmetry, with id_W on a pin of d. Hence C_0⊆¬d. Similarly C_1⊆d because b∈d. The charts are therefore disjoint even when W=V. The local swap observer E satisfies Ed at W by (4). Its Boolean identities imply that Ep and Eq have different truth values. The same E qualifies at any specified finite Δ and is its own qualified inverse.

The forward separation implication follows from equality substitution. Functionality, which holds here at every relational type, lifts propositional separation to each higher relational output type by finding a tuple where two unequal relations have unequal proposition values. This proves the full typed separation schema.

## 6. Consequences and the remaining gap

Criterion (7) gives three broad families.

- **Every one-object model in the precise framework of §1, with arbitrary designated group G.** Take j=id and D=∅ in (7). For a particular false d, the proof uses a finite-support permutation b approximating a member of d; after enlarging S to include its support, b commutes with G_(S) and bS=S. It does not try to turn an arbitrary one-way stabilizer inclusion into equality.
- **Multiobject families with conjugate designated groups.** If j_VG_Wj_V^{-1}=G_V, take D_V=∅. Applying the same argument at every object gives reversible separation throughout the model.
- **Families in which every designated group has a finite base.** For any j:W→V, enlarge a finite base of G_W by the preimage of a finite base of G_V. Both sides of (7) are then trivial. Again separation holds at every object.

Thus these families satisfy Rev and its separately boxed schema. They include atomless examples, such as the ordinary finite-support permutation model. No finite-range or endpoint-valued restriction is imposed on the constructed observer.

The earlier representation criterion for an ordinary observer evaluating at b requires only

$$
bG_{W,(S)}b^{-1}\subseteq G_V.
$$
Its positive separation criterion may hold at every object without presenting the compatible equalities (7). The [finite-block symmetry model](finite-block-symmetry-reversible-gap.md) realizes that distinction and independently refutes C5+□OS⇒Rev by a contingent pure sentence. No necessity of (7) for arbitrary admitted reversible observers is asserted. This note excludes the three families above from supplying that counterexample and identifies the local inverse structure used in its chart construction.

## 7. Sources

The new local swap observer, criterion (7) and its consequences are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§2–6, unpaginated.

The semantic construction is Cian Dorr, *Boolean Completeness does not imply Rigid Comprehension*, draft of 30 July 2026, Definitions 15–18, p. 8; §3.1, p. 9; Lemma 21, p. 10, as recorded in [Symmetric ideally-full models](../../source/topics/classicism/groups/symmetric-ideally-full.yaml). The underlying ideally-full action construction is Bacon and Dorr, *Classicism*, draft of 16 May 2023, Appendix D, pp. 73–79. These sources establish the model framework; the observer theorem above is not attributed to them.

The one-way arrow-evaluation representation and the original positive ordinary-separation criteria are [Atomic observers and finite stabilizers](../operator-representation.md), §§4–6, direct source `misc`, unpaginated. The construction above makes both directions compatible and verifies the resulting inverse identity at every future coordinate.

This is an ordinary mathematical theorem about the specified model family. It is not a formal verification or a classification of all models of C5+□OS.

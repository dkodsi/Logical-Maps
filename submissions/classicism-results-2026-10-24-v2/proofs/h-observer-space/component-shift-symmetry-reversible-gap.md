# Component-shift symmetry: pure noncontingency without reversible separation

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new model and observer verdicts: `misc`, this note, §§1–8, unpaginated. The general symmetric ideally-full construction is attributed separately in §§2 and 9.

A one-object symmetric finite-pinning model satisfies C5, necessary ordinary logical separation and No Pure Contingency, but fails reversible logical separation. In fact it satisfies the stronger necessary **qualified left-inverse** separation schema:

$$
\boxed{\mathrm{C5}+\Box\mathrm{SplitMono}
+\mathrm{NoPureContingency}+\neg\mathrm{Rev}.}
\tag{1}
$$
Thus adding No Pure Contingency does not close the established gap between reversible separation and C5 plus necessary ordinary separation. It also does not close that gap after ordinary separation is strengthened to qualified left-inverse separation and its necessity.

The obstruction is a contingent statement with a **rigid binary relation parameter and an individual parameter**. Closed pure sentences remain noncontingent. Reversible observers fix those particular parameters under typewise conjugation, so they cannot detect the resulting proposition distinction.

## 1. Exact scope and the changed arrow family

Use Good_Δ, Rev and SplitMono from [Qualified right-inverse separation](split-inverse-logical-observers.md), §1. Good_Δ uses the full Boolean and quantifier composite identities at the finite external type list Δ, together with the translated equality clauses. SplitMono requires an admitted Good_Δ observer E and an admitted Good_Δ left inverse F with the whole-operation identity F∘E=I. Full separation ranges over every relational output type and every finite Δ; boxes of such schemas are always read instance by instance.

The model below is a new member of the general symmetric ideally-full construction. Unlike [the local-conjugacy sufficient theorem](local-conjugacy-and-reversible-observers.md), it does **not** include all bijections of its underlying set as arrows. That earlier theorem establishes Rev for every one-object model in its all-bijections framework and does not apply here.

We use exactly the following smaller group of arrows. Let

$$
X=\mathbb Z\times\mathbb N,\qquad C_n=\{n\}\times\mathbb N.
$$
On each even-indexed component C_n choose a partition into countably infinitely many blocks of every positive even finite size. On each odd-indexed component choose a partition into countably infinitely many blocks of sizes 2,4,8,16,… and no other sizes. All these choices can be fixed using enumerations of the countable components.

Let G_n be the product of the full symmetric groups of the individual finite blocks in C_n. Put

$$
G:=\prod_{n\in\mathbb Z}G_n.
\tag{2}
$$
Thus G preserves each component and each designated finite block setwise; it does not permute distinct blocks.

Let K consist of all bijections h:X→X for which there is one integer k such that

$$
h(C_n)=C_{n+k}\qquad\text{for every }n.
\tag{3}
$$
Within these prescribed component maps h is arbitrary. Call k its shift. Shifts add under composition and negate under inverse, so K is a group. It contains G. It also contains every finite-support permutation that preserves each component. It does not contain a permutation exchanging a few points in different components while fixing all remaining points.

The category has one object X and arrow group K. Individuals are the elements of X, acted on by these bijections. The designated symmetry group is G. Allowed pins are finite subsets of X, and the admitted relational objects are exactly the symmetric intensions with some finite pin.

## 2. Construction, admission and C soundness

The general one-object symmetric ideally-full construction needs a monoid of maps on its base and a group of permutation arrows inside that monoid; it does not require every bijection to be an arrow. This is the construction used in [Class-reflecting surjections](../../source/topics/classicism/writeups/symmetric-class-reflecting-surjections.md), “The model,” citing Dorr's Proposition 20. The present K and G meet these requirements: K is closed under composition and contains identity, and G≤K is a permutation group. The finite-set ideal is preserved by all arrows and closed under finite unions.

For precision, a relational intension A of type σ₁…σ_mt has a profile

$$
A(h;u_1,\ldots,u_m),\qquad h\in K,\quad u_i\in D_{\sigma_i}(X).
$$
It is symmetric when, for every μ∈G,

$$
A(\mu h;\rho(\mu)\bar u)=A(h;\bar u).
\tag{4}
$$
A finite S pins it when its value, holding $\bar u$ fixed, depends on h only through h|S. Transport is right precomposition:

$$
(\rho(r)A)(h;\bar u)=A(hr;\bar u).
\tag{5}
$$
All profiles satisfying (4) and some finite pin are admitted, recursively at every relational type. This is the profile construction in [Symmetric ideally-full map categories](../../source/research/2026-10-22/notes/rc-symmetric-ideal-full-categories.md), §1, specialized to our one-object group category.

The restrictions remain stable under transport: if S pins A, then rS pins ρ(r)A, because equality of h,h′ on rS gives equality of hr,h′r on S. Left multiplication by G commutes with the right-precomposition calculation in (5), so symmetry is preserved as well. Every ρ(r) is a bijection, with inverse ρ(r⁻¹). The general construction consequently supplies application, lambda abstraction and the logical constants, with C soundness as in the cited one-object theorem. We are applying that general monoid/group theorem with its hypotheses checked, not importing C validity from the different all-bijections model.

We will also use its invariant-current-relation admission lemma. If an external relation A₀ on a finite tuple of current domains is invariant under G_(S), define

$$
A(h;\bar u)\quad\Longleftrightarrow\quad
\begin{cases}
A_0(\rho(g^{-1})\bar u),&h|S=g|S\text{ for some }g\in G,\\
\text{false},&\text{otherwise}.
\end{cases}
\tag{6}
$$
Two possible g's differ by a member of G_(S), so the value is independent of the representative. The branch is S-pinned. Under left multiplication by μ∈G a representative becomes μg, and the two transports cancel in (6), proving (4). At identity the relation has current extension A₀. Every arrow used in this calculation belongs to K because G≤K. This proves admission directly; it does not assume arbitrary extension fullness.

Because every arrow acts bijectively at every type, identities and distinctness are necessary throughout the model. Thus it satisfies C5, all BF instances, and Functionality. We use the usual C5 consequences and the typed separation lifting with precisely these premises.

## 3. One object gives No Pure Contingency

Every closed pure term is natural under the transports (5). For a closed pure proposition P this gives

$$
\rho(r)P=P\qquad(r\in K).
\tag{7}
$$
If P is true at identity, evaluating (7) there says that P is true at every r. Conversely if it is false at identity, it is false at every r. Therefore every closed pure sentence denotes Top or Bottom, and No Pure Contingency holds.

This is also the recorded [one-object No Pure Contingency argument](../../source/topics/classicism/arguments/no-pure-contingency-one-object.yaml), applied after the construction's C soundness has been checked.

This is a statement about **closed pure propositions**. Naturality of a closed predicate does not by itself make its values at arbitrary parameter tuples invariant in truth. We will use an individual parameter and a relation parameter below; the proposition formed with them need not satisfy (7).

In particular, whenever a closed pure separation instance is true in this one-object model, its separately boxed instance is true as well. This will supply the boxes on OS and SplitMono after their unboxed instances have been proved.

## 4. Componentwise comparisons give full ordinary separation

The two finite-block group patterns admit comparison bijections in both directions: the even-size partition can be packed into the power-of-two partition, and conversely. The construction is [the finite-block packing proof](finite-block-symmetry-reversible-gap.md), §2. Both patterns have infinitely many 2-blocks and arbitrarily large even blocks. Assign a source block inside a sufficiently large unused target block, fill the remainder with source 2-blocks, and alternate with filling the next unused target block. This yields a bijection sending every source block inside a target block, hence conjugates the source blockwise symmetry group into the target group. Identical patterns can be matched by a blockwise isomorphism.

Fix an integer shift k. For each n choose such a comparison j_n:C_n→C_(n+k) between its two patterns. Their union j belongs to K and satisfies

$$
jGj^{-1}\subseteq G.
\tag{8}
$$
The countably many comparisons can be specified by the same enumerated packing algorithm in each component. No object-language selection operation is presumed.

Let d be a nonbottom admitted proposition, let h∈d, and let P be a finite pin for d. Choose j with the same shift as h. Then j⁻¹h preserves every component. Its restriction to P extends to a finite-support permutation π preserving every component: complete the finite partial bijection within each of the finitely many affected components. Thus π∈K. Put b=jπ and choose finite S containing P and supp(π). Then b|P=h|P, so b∈d. Every element of G_(S) commutes with π, giving

$$
bG_{(S)}b^{-1}=jG_{(S)}j^{-1}\subseteq G.
\tag{9}
$$
Here is the admitted observer supplied by (9). At a coordinate h′ matching some g∈G on S, observe an input proposition q along bg⁻¹; at all other coordinates observe it at identity:

$$
E(h';q)\quad\Longleftrightarrow\quad
\begin{cases}
bg^{-1}\in q,&h'|S=g|S,\ g\in G,\\
1\in q,&\text{otherwise}.
\end{cases}
\tag{10}
$$
The independence, pinning and symmetry calculations of the arrow-evaluation representation proof use only (9), G≤K and group composition. All selected arrows bg⁻¹ are in K. Hence (10) is an admitted tt object, and at identity it reads the coordinate b.

At every future evaluation, each output coordinate of this observer is evaluation of its input at one arrow of K. Such evaluation preserves the Boolean operations. Every selected arrow acts onto every type, so the universal and existential ranges coincide, proving the **full composite** quantifier identities at every fixed finite list. These are exactly the whole-profile calculations in [Local symmetry conjugacy](local-conjugacy-and-reversible-observers.md), §§3–4; those calculations do not need additional arrows outside the ones displayed. Since this group model has endpoint-valued equality judgments, the translated equality clauses hold as well.

Thus every nonbottom proposition is accepted by a fully qualified observer. Applying this to Boolean differences gives propositional OS, and Functionality lifts it to every relational output type. Section 3 then gives every separately boxed OS instance. This proves C5+□OS in the new model.

## 5. The stronger qualified left-inverse separation

The one-sided shift construction from [Finite-pinning models with left-inverse separation](finite-block-symmetry-left-inverse.md), §§2–5, also remains inside K. We spell out this point because arbitrary cross-component finite permutations would not be allowed.

For b,S as in (9), choose one component C_m and infinitely many of its 2-blocks B₀,B₁,… disjoint from S. Choose x∈B₀ and put S′=S∪{x}. Let ν₀=1 and let ν_n exchange B₀ with B_n, fixing everything else. These permutations preserve every component, so ν_n∈K. They normalize G, because they exchange equal-sized designated blocks. Set α_n=ν_(n+1)ν_n⁻¹ and

$$
U_n=\{h'\in K:h'|S'=\nu_n g|S'\text{ for some }g\in G\}.
$$
The charts are pairwise disjoint, all share the finite pin S′, and α_nU_n=U_(n+1). Define E to observe bg⁻¹ on U₀, α_n⁻¹ on U_(n+1), and identity outside all charts. Define F to observe α_n on U_n and identity outside. The representative-independence of the first branch is (9); all constant shift branches are symmetric because their observation arrows normalize G. Hence both profiles are admitted.

For arbitrary future r,l∈K and arbitrary future input q, the observation formula is

$$
l\in(\rho(r)E)(q)\quad\Longleftrightarrow\quad a^E_{lr}l\in q.
$$
Applying F outside E therefore tests q at

$$
a^E_{\,a^F_{lr}lr}\,a^F_{lr}l.
\tag{11}
$$
If lr∈U_n, F first shifts it by α_n into U_(n+1), where E uses α_n⁻¹. Equation (11) is then l. Outside all charts both arrows are identity. Thus F∘E=I as a whole-operation identity at every future input. The special b branch is never visited in that composition.

Every observation arrow is in K and is invertible, so both observers satisfy all full Boolean and quantifier identities, and the equality clauses, at each finite list. At identity E observes b and accepts the desired d. The same Boolean-difference and Functionality arguments give full SplitMono separation. Its instances are closed pure formulas, so §3 gives □SplitMono. This establishes the positive premises of (1), including the stronger left-inverse package.

## 6. A rigid relation that every reversible observer must fix

The parameter argument has a reusable general form. Fix an external finite list of first-order relational variables R_i of types $e^{n_i}t$, with n_i≥1, and an external finite list of individual variables $\bar x$. Let $P(\bar R,\bar x)$ be a pure formula whose free variables are among these lists. Expand its defined notation and let Δ_P contain the finitely many quantifier types that occur, together with t if needed for the reversible-to-involutive comparison. Define the endpoint condition

$$
\mathrm{End}(\bar R):=
\bigwedge_i\forall\bar y^{\,e}\,
\bigl(R_i\bar y=\top\ \lor\ R_i\bar y=\bot\bigr).
$$
Then full Rev over H implies the following external formula schema:

$$
\boxed{\mathrm{End}(\bar R)\ \longrightarrow\
\bigl(P(\bar R,\bar x)\leftrightarrow
\Box P(\bar R,\bar x)\bigr).}
\tag{12a}
$$
Here the displayed formula is universally closed over the finitely many relation and individual parameters; there is no quantification over formulas or infinite lists of relation types. With no parameters it specializes to No Pure Contingency.

To prove it, recover C5 and qualified involutive separation from full Rev. Every Good_(Δ_P) involution T fixes the individual inputs. At each first-order relation parameter, the conjugation formula therefore reduces to

$$
(T^*_{e^{n_i}t}R_i)(\bar y)=T(R_i\bar y)=R_i\bar y,
$$
where the second equality uses $\mathrm{End}(\bar R)$ and endpoint preservation. The finitely many Functionality instances collect these tuple identities into whole identities T*R_i=R_i. The conjugation term induction in [Reversible separation and pure truth](reversible-separation-and-pure-truth.md), §§2–3, now fixes $P(\bar R,\bar x)$. If P is true, every such T agrees on P and Top; the propositional involutive-separation instance for Δ_P gives P=Top, which is □P. The reverse direction follows from modal reflexivity. Applying the same argument to ¬P also proves that the parameterized proposition is an endpoint. No observer qualification premise is necessitated. Once C5 has been recovered, this proof uses only the indicated finite propositional separation instance and the finitely many Functionality instances needed by the formula.

The restriction to first-order relation parameters is essential to the stated scope: an arbitrary parameter with higher-type arguments need not be fixed by conjugation. We also require endpoint-valued tuples, rather than using an unspecified notion of rigidity.

The following model relation supplies exactly this condition.

Define the admitted binary individual relation R of type eet by the profile

$$
R(h;x,y)\quad\Longleftrightarrow\quad
x,y\text{ belong to the same component }C_n.
\tag{12}
$$
It is independent of h and hence empty-pinned. Every symmetry in G preserves components, so it satisfies (4). Every arrow of K preserves the component equivalence relation, so ρ(h)R=R. Moreover, for any current a,b, the proposition R(a,b) is Top or Bottom: its truth at h is whether ha,hb lie in the same component, equivalent to the original condition.

Let T be a Good_Δ involution. Its typewise lift from [Reversible separation and pure truth](reversible-separation-and-pure-truth.md), §§2–3, leaves individual inputs unchanged. Thus

$$
(T^*_{eet}R)(a,b)=T(R(a,b))=R(a,b),
\tag{13}
$$
since Boolean qualification fixes Top and Bottom. Current Functionality, available in C5, collects the two individual arguments in (13), giving T*_(eet)R=R as a whole object identity. This is the required parameter-fixing assertion; R is not treated as a pure logical constant.

If P(R,a) is a pure formula with only the indicated relation and individual parameters, and Δ contains its quantifier types, the existing conjugation term induction now gives

$$
T(P(R,a))=P(T^*R,T^*_e a)=P(R,a).
\tag{14}
$$
All the typewise quantifier reindexing and whole-identity steps are those already verified in the pure-truth note. Equation (13) supplies the extra parameter case. No arbitrary nonlogical parameter is asserted to be fixed.

## 7. A contingent choice assertion inside one component

Let P(R,a) assert the following relative six-set multiple-choice statement:

> Every pairwise disjoint family A of six-element individual properties whose extensions are contained in the R-class of a has an admitted relation S choosing a nonempty proper subset of each member's extension.

More explicitly, A has type (et)t, S has type (et)(et), and the antecedent says that each X with AX has exactly six satisfying individuals, all satisfying R(a,y), and distinct A-members have disjoint extensions. The conclusion requires S(X,y) to imply Xy, some X-member to satisfy S(X,y), and some X-member not to satisfy it. All occurrences of “six” expand to six individual witnesses, pairwise inequality and exhaustion. No cardinality convention or parameter naming the designated blocks enters the formula.

The quantifier types of this expanded formula lie in

$$
\Delta_0=\{t,e,et,(et)t,(et)(et)\}.
\tag{15}
$$
The harmless t entry is retained for the finite-list reversible/involutive comparison. R:eet is a free parameter, not a quantified variable, so its type need not be added as a quantifier type. C5 handles all equality judgments used in the formula and in the conjugation proof.

### Even components: the assertion is false

Suppose a∈C_n with n even. For each designated six-block B in C_n, define the individual property X_B by X_B(h;y) iff y∈hB. It is pinned by B and is symmetric. Since every element of G fixes B setwise, X_B is fixed as an object by G.

The current family consisting of exactly these X_B is G-invariant. The admission lemma (6), with empty pin, supplies an admitted family A with precisely that current extension. Its members are distinct, pairwise disjoint six-element properties, all contained in the class of a.

If an admitted selector S existed, choose a finite pin N for it and a designated six-block B⊆C_n disjoint from N. Every permutation of B belongs to G_(N), fixes X_B, and fixes the current extension of S. The last assertion follows by combining symmetry with the pin: transporting along such a permutation leaves S as an object and carries its current input/output tuple to the permuted tuple. Thus the selected subset of B is invariant under its full symmetric group. It must be empty or all of B, contradicting the selector requirements. Hence P(R,a) is false.

### Odd components: the assertion is true

Suppose a∈C_n with n odd, and let A be an arbitrary admitted family satisfying the antecedent. Keep a finite pin N for A, including any points outside C_n; enlarge it by a. Within C_n let N₀ include the whole designated blocks meeting N. Keep the original outside-component points as well. This remains finite.

If a family cell D meets a designated block B⊆C_n disjoint from N₀ but omits some y∈B, exchange an x∈D∩B with y. This transposition lies in G_(N₀), so it sends the corresponding property to another A-member. Its extension is a different six-set overlapping D in five points, contradicting disjointness. Therefore every cell that meets an untouched block contains that block in full. This applies also to cells that meet N₀.

Only finitely many cells meet N₀, because their six-element extensions are pairwise disjoint. Adjoin all their points to N₀, retaining all outside-component pins, and call the finite result N₁. Within C_n it is a union of whole designated blocks: any newly added points outside the old block union came from entire untouched blocks by the preceding paragraph. No iteration of a closure operation is needed.

Every remaining cell is a union of whole power-of-two blocks and has size six. It therefore has at least two constituent blocks, of sizes 2+4 or 2+2+2. Select one constituent block using a fixed external enumeration of the designated blocks. For each exceptional cell meeting N₀, select one of its individuals; all its points are in N₁ and are fixed pointwise by G_(N₁).

This defines a current selector relation S₀(X,y), declared false for X outside A and for points outside the selected subset. It is invariant under G_(N₁). Indeed A is invariant under that stabilizer. Each nonexceptional cell extension is a union of blocks fixed setwise by G, and the selected constituent block is fixed setwise. An element of the stabilizer that moves an A-member to a property with the same nonempty extension must fix that property as an object: otherwise two distinct A-members would overlap, contrary to the antecedent. Exceptional cells and their selected individuals are fixed by N₁. The outside-component factors of G_(N₁) preserve A and act trivially on every cell extension in C_n; the same disjointness argument handles their possible action on the property objects. Thus outside-component factors cause no unproved invariance assumption.

Apply (6) to S₀ and N₁. It supplies an admitted selector with exactly that current relation. Each selected subset is nonempty and proper. This proves P(R,a) for every a in an odd component, for all admitted families in the **full global domains**, not only a separately constructed local hierarchy.

## 8. Failure of reversible separation despite pure noncontingency

Choose a in an even component and put p=P(R,a). Section 7 makes p currently false. Choose an arrow h with shift one. Naturality, together with ρ(h)R=R, gives

$$
\rho(h)p=P(R,ha),
$$
which is true because ha lies in an odd component. Thus p is not Bottom.

Nevertheless every Good_(Δ₀) involution fixes p by (14). All such observers therefore reject p and Bottom alike. Propositional involutive separation fails for the exact list (15). Over the ambient C5, the same-list reversible-to-involutive patch turns any reversible observer accepting this false p into a qualified involution accepting it. That would contradict (14). Hence propositional reversible separation also fails for Δ₀. The full Rev schema fails a fortiori.

This proves (1) and in particular

$$
\mathrm{C5}+\Box\mathrm{OS}+\mathrm{NoPureContingency}
\ \not\Longrightarrow\ \mathrm{Rev}.
$$
The necessary left-inverse strengthening in (1) shows that the failure is not repaired by supplying admitted qualified left inverses to the separating observers.

There is no conflict with §3: p is formed using the nonlogical relation parameter R and the individual parameter a. No closed pure sentence changes truth. Nor does this contradict the one-object all-bijections Rev theorem: K deliberately excludes bijections that mix components in an arbitrary way. In this K every finite-support permutation has shift zero, so it cannot approximate a nonzero-shift arrow even at a single point whose image lies in another component. The chosen coarse relation is preserved by every allowed arrow and creates the new parameter obstruction.

This note does not assert that local stabilizer conjugacy is necessary for arbitrary reversible witnesses. Failure of Rev is proved by the fixed-parameter formula (14), independently of that possible representation question. It also does not classify which additional parameter-noncontingency schema would suffice for Rev.

## 9. Sources and mathematical status

The general symmetric ideally-full construction is Cian Dorr, *Boolean Completeness does not imply Rigid Comprehension*, draft of 30 July 2026, Definitions 15–18, p. 8, and Proposition 20, as cited in the existing [Class-reflecting surjections write-up](../../source/topics/classicism/writeups/symmetric-class-reflecting-surjections.md), “The model.” The local source explicitly records the one-object monoid/permutation-subgroup hypothesis. The profile and admission rules are spelled out in [Symmetric ideally-full map categories](../../source/research/2026-10-22/notes/rc-symmetric-ideal-full-categories.md), §§1 and 6.2. The underlying intensional action construction is Bacon and Dorr, *Classicism*, draft of 16 May 2023, Appendix D, pp. 73–79. These sources supply the framework, not the new component-shift model or its observer verdicts.

The mutual finite-block packings and six-set choice proofs are [Finite-block symmetry: even sizes versus powers of two](finite-block-symmetry-reversible-gap.md), §§2 and 4–7. Sections 4 and 7 above verify their use in the restricted arrow group and global component domains. The one-sided inverse profiles and their arbitrary-future cancellation are [Finite-pinning models with qualified left-inverse separation](finite-block-symmetry-left-inverse.md), §§2–5. The parameter-fixing obstruction extends the exact conjugation calculation in [Reversible separation and pure truth](reversible-separation-and-pure-truth.md), §§2–4.

The new component-shift construction, its checked C hypotheses, necessary OS and SplitMono verdicts, rigid-parameter obstruction and resulting nonimplication are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–8, unpaginated.

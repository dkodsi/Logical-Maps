# Idempotent native-Box observers and joins in finite frames

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–7, unpaginated. The full action-model framework and earlier observer theorems are attributed in §8.

Idempotence adds no strength to ordinary logical separation, but it does add strength when the observers must also commute with necessity. The resulting theory is strictly stronger than native-Box separation, remains compatible with failure of C5, and is incomparable with reversible separation. Combining it with C5 gives exactly Extensionality.

There is an exact finite-model explanation. In a full model on a finite rooted partially ordered frame, idempotent native-Box observers that read a point a exist exactly when joining with a is defined everywhere. Such observers separate exactly when the frame is a join-semilattice. A six-point frame distinguishes this condition from native-Box separation alone; a four-point diamond shows that even the stronger condition does not imply the modal linearity principle .3.

## 1. Qualification and scope

Use Good_Δ and BoxComm from [Native-Box logical observers](native-box-logical-observers.md), §1. All preservation equations are identities of the entire composite operations. In particular,

$$
\mathrm{BoxComm}(E):\quad
 (\lambda p.E(\Box p))=(\lambda p.\Box Ep),
\qquad \Box p:=(p=\top).
$$

Add the whole idempotence identity E∘E=E. Write IdemBoxSep(τ,Δ) for separation by the common class of observers satisfying all three conditions. Without indices, IdemBoxSep denotes the full schema over relational output types and finite external qualification lists. It implies BoxSep and therefore recovers C, current BF and Functionality over H. A boxed schema means the separately boxed closed instances.

The earlier [idempotent normalization](../logical-observer-hierarchy.md), §8, proves ordinary OS equivalent to separation by idempotent Good observers. That normalization is not asserted to preserve BoxComm. The models below show that it cannot always do so.

## 2. C5 makes this restriction exactly Extensionality

Over C5, a Boolean observer commutes with native Box exactly when it is currently injective; see [Native-Box logical observers](native-box-logical-observers.md), §3. If an injective E is idempotent, then E(Ep)=Ep implies Ep=p for every p. Functionality collects this into E=I.

Consequently, over C5 every IdemBox-qualified observer is identity. Propositional separation by this class says that material equivalence of p,q entails their identity. This is propositional Extensionality. Together with Functionality, already available over C5, it gives the full relational Extensionality schema. Conversely Extensionality makes identity alone separate at every relational type; identity is Good, idempotent and Box-commuting. Therefore, over H,

$$
\boxed{\mathrm{C5}+\mathrm{IdemBoxSep}
\quad\Longleftrightarrow\quad\mathrm{Extensionality}.}
\tag{1}
$$

The full scope matters in recovering the background over H. The forward argument itself needs only the propositional separation instance once C5 is an explicit premise.

## 3. Full finite-frame observers are coordinate maps

Let P be a finite partially ordered set with least point o. Regard its order as a thin category: one arrow x→y iff x≤y. Take singleton individuals and the full relational action-model domains. For x∈P put ↑x={y:x≤y}. Then
$D_t(x)=\mathcal P(\mathord\uparrow x),$
with truth given by membership of x. Boolean operations are set operations. At any relational type, full objects are arbitrary future truth profiles on admitted argument tuples. Transport along x→y restricts such a profile to the future cone ↑y. Every such restricted profile extends to ↑x by arbitrary values outside ↑y. Thus transport is onto at every admitted type, including the singleton individual type.

The full action-model theorem supplies C. Onto type transport gives BF and Functionality at every point, hence their necessary schemas. Proposition algebras are powersets, so Atomicity_t holds everywhere as well. All these claims concern this explicitly full construction.

An arbitrary observer satisfying the whole Boolean laws induces at each future x a Boolean truth character on the finite powerset D_t(x). Every such character is evaluation at one unique point f(x)∈↑x: a character accepts one atom, since the finitely many atoms join to Top. Consequently every Boolean observer is determined by an inflationary coordinate map f:P→P, with x≤f(x), through

$$
E_f(p)=f^{-1}[p].
\tag{2}
$$

This description covers the whole observer, not just its current action. At a future x and an arbitrary input q⊆↑x, its truth profile is true exactly when f(x)∈q. Conversely any inflationary f defines an admitted full observer by this profile.

Such an observer preserves all quantifiers. At x, its application to ∀z^σ Fz reads the universal at f(x). The translated universal quantifies over z∈D_σ(x) and evaluates F at the transported argument in D_σ(f(x)). Onto transport makes these truth conditions equivalent. The existential proof is the same. Because the comparison covers every future x and every future F, it proves the whole composite identities. The translated equality clauses follow from Boolean qualification over C. Thus in this construction every Boolean observer is Good at every requested finite list; no analogous qualification collapse is asserted for arbitrary models.

At every point, these unrestricted readers separate. For example, to read a from the root choose f(o)=a and f(x)=x elsewhere. No monotonicity is required for ordinary Good. Full Functionality lifts propositional separation to every relational type. In particular every finite rooted-poset model here satisfies □OS.

## 4. Modal preservation and idempotence give joins

At any x, native Box is the universal test on ↑x. Applying the two sides of BoxComm to arbitrary p⊆↑x therefore gives the exact condition

$$
E_f\text{ commutes with Box}
\quad\Longleftrightarrow\quad
 f[\mathord\uparrow x]=\mathord\uparrow f(x)
 \quad\text{for every }x.
\tag{3}
$$

Equality of these sets is necessary because every subset is admitted; it is sufficient at every future input, so it gives the whole operation identity. Condition (3) implies monotonicity: if x≤y, then f(y)∈↑f(x).

Likewise the whole equation E_f²=E_f is exactly

$$
f^2=f.
\tag{4}
$$

For necessity test singleton propositions; for sufficiency compute the truth of the compositions at arbitrary future inputs.

Fix a∈P. Suppose (3)–(4) hold and f(o)=a. Equation (3) at o says the image of f is ↑a. Idempotence makes every point of that image fixed. For any x, inflationarity and monotonicity give x≤f(x) and a=f(o)≤f(x). If y is any upper bound of x and a, then y∈↑a, so f(y)=y; monotonicity gives f(x)≤f(y)=y. Hence

$$
f(x)=x\lor a.
\tag{5}
$$

Thus joining with a exists for every x, and the qualifying reader of a is unique.

Conversely, if x∨a exists for every x, f_a(x)=x∨a is inflationary, monotone and idempotent. Moreover f_a[↑x]=↑(x∨a): the forward inclusion is monotonicity, while for y≥x∨a, choose y itself and use y∨a=y. This proves (3). It supplies an idempotent native-Box Good observer reading a at the root.

To separate propositions at the root, the possible read points must include every a∈P. Otherwise the distinct propositions ∅ and {a} have the same truth under all qualifying observers. Conversely readers at every point distinguish every pair of different subsets. With Functionality this gives every relational separation instance. We have proved:

$$
\boxed{
\begin{array}{c}
\text{The full model on finite rooted P satisfies IdemBoxSep}\
\Longleftrightarrow\
\text{every pair of points of P has a join.}
\end{array}}
\tag{6}
$$

The failure direction is already propositional at Δ={t}; the success direction supplies all types and all finite lists. If P is a join-semilattice, every ↑x is one as well. Hence the same construction satisfies □IdemBoxSep.

Equation (6) is an exact characterization for this model family. It is not an assertion that every abstract model of IdemBoxSep has a finite frame representation.

## 5. A six-point strictness model

Take P={o,x,a,b,c,1}, ordered in four levels

$$
\{o\}<\{x,a\}<\{b,c\}<\{1\},
$$

where every point in a lower displayed level lies below every point in a higher one, and different points in a two-point level are incomparable. The pair x,a has two incomparable minimal upper bounds b,c, so no join. By (6), IdemBoxSep fails at the root.

Nevertheless BoxSep holds. The following table gives one inflationary map for each possible root read point; columns are its input points.

| Reader | o | x | a | b | c | 1 |
| --- | --- | --- | --- | --- | --- | --- |
| o | o | x | a | b | c | 1 |
| a | a | b | c | 1 | 1 | 1 |
| x | x | c | b | 1 | 1 | 1 |
| b | b | b | b | b | 1 | 1 |
| c | c | c | c | 1 | c | 1 |
| 1 | 1 | 1 | 1 | 1 | 1 | 1 |

Each row satisfies (3). For the a-reader, the cone images at o,x,a are respectively ↑a, ↑b, ↑c, and each remaining cone has image {1}. The x-reader is symmetric. For the b-reader, every input below b has cone image {b,1}, and the remaining cones have image {1}; the c-reader is symmetric. Identity and the constant-top map satisfy (3) immediately. Section 3 supplies the whole logical qualification at all types. Their root values range over all P, giving full BoxSep.

This proves the strict implication, over H,

$$
\mathrm{IdemBoxSep}\quad\Longrightarrow\quad\mathrm{BoxSep}.
\tag{7}
$$

The countermodel retains C, □BF, □Functionality, □Atomicity_t and □OS. It does not rely on a failure of the ordinary idempotent-observer normalization.

### The exact two-antichain family

The six-point example belongs to a family with a sharp native-Box threshold. For positive finite integers m,n, let P_{m,n} have four levels: a root, an antichain A of m points, an antichain B of n points, and a top. Every point in a lower level lies below every point in a higher level. In the full model on this frame,

$$
\begin{aligned}
\mathrm{BoxSep}&\quad\Longleftrightarrow\quad m=1\ \text{or}\ n\le m,\\
\mathrm{IdemBoxSep}&\quad\Longleftrightarrow\quad m=1\ \text{or}\ n=1.
\end{aligned}
\tag{7a}
$$

These external integer conditions characterize the specified finite model family. They are not object-language cardinality principles.

For the first equivalence, the cases m=1 or n=1 are join-semilattices, so §4 already supplies the required readers. Suppose m,n≥2 and a Box-commuting reader f sends the root to a∈A. If some b∈B were fixed, monotonicity would give f(x)≤b for every x∈A. For x≠a, inflationarity and the root value also force f(x)≥x,a, hence f(x)=b. The remaining f(a) is either a or b. For every c∈B different from b, monotonicity above such an x and inflationarity force f(c)≥b,c, so f(c) is the top. No input could then map to c: the root maps to a, lower points map only to a or b, and upper points map to themselves or top. This contradicts f[P]=↑a. Thus every upper point must map to top.

All n upper points must nevertheless occur in f[P]=↑a. Their preimages must lie in the m-point lower antichain. Therefore n≤m.

Conversely, if n≤m choose an explicit finite surjection g:A→B. For each a∈A define f(root)=a, f(x)=g(x) for x∈A, and f(y)=top for y∈B or y=top. At a lower point x its cone image is {g(x),top}=↑g(x); at the root it is {a}∪B∪{top}=↑a; at an upper point it is {top}. Thus f satisfies (3) and reads a. Every upper point b has a join with every point, so its join map supplies a reader; identity and the constant-top map read the root and top. All points are read and BoxSep follows.

For the second equivalence, if m,n≥2 any two distinct lower points have n incomparable minimal upper bounds, so P_{m,n} is not a join-semilattice. If either m or n is 1, all pairwise joins exist. Apply (6).

In particular P_{2,3}, a seven-point frame, has no BoxSep. It nonetheless satisfies the full lower bundle OS+□BF+□Functionality+.2, and even □OS+□Atomicity_t+□.2. Only the .2 claim needs checking beyond §3. At any point, if ◇□p holds, some future cone is contained in p, so its common top belongs to p. That top is accessible from every other future point, giving □◇p. This proof applies at every point. Hence the converse from the entire established modal bundle to BoxSep already fails in a finite full model; no infinite symmetry construction is required for this particular comparison.

## 6. The diamond separates .2 from .3

Take the four-point diamond o<a,b<1, with a,b incomparable. It is a join-semilattice, so §4 gives full □IdemBoxSep. It fails C5: the nonzero proposition {o} becomes Bottom at a. It also refutes the following reflexive form of the modal linearity principle .3:

$$
(\Diamond p\land\Diamond q)\to
\bigl[\Diamond(p\land\Diamond q)
 \lor\Diamond(q\land\Diamond p)\bigr].
\tag{8}
$$

Set p={a} and q={b}. Both diamonds in the antecedent hold at o. The only p-point is a, from which no q-point is accessible; symmetrically no p-point is accessible from b. Both disjuncts in the consequent are false.

Thus even necessary IdemBoxSep, with the necessary BF, Functionality and propositional Atomicity already present, implies neither C5 nor .3. Native-Box separation does imply .2 by its distinct theorem; the diamond locates that consequence without a hidden linearity assumption.

Combining this example with (1) gives the following exact comparisons. IdemBoxSep and Rev are incomparable: the diamond refutes IdemBoxSep⇒Rev, since Rev implies C5. Conversely any C5 model of Rev failing Extensionality refutes Rev⇒IdemBoxSep. The existing [two-colour symmetry model](finite-pinning-dedekind-propositions.md), §4, supplies such a model. Furthermore

$$
\boxed{\mathrm{IdemBoxSep}+\mathrm{Rev}
 \ \Longleftrightarrow\ \mathrm{Extensionality}.}
\tag{9}
$$

This conjunction permits different separating observer families. Rev supplies C5; equation (1) then applies. Extensionality supplies both factors.

Endpoint separation is also incomparable with IdemBoxSep, and their conjunction is again Extensionality. The diamond refutes IdemBoxSep⇒End because End implies C5. The terminal two-point cluster in §7 has endpoint separation but fails IdemBoxSep: constant coordinate readers supply the former, while its only idempotent Box-commuting reader is identity. Thus neither of these natural restrictions absorbs the other, even though adding C5 to IdemBoxSep collapses it.

## 7. Idempotent native-Box separation need not persist

For this final example allow a finite preorder, still regarded as a thin category. There are three points o,a,b, with o strictly below the terminal cluster {a,b}, and a≤b≤a. Full profiles at o are arbitrary subsets of these three points. The restriction maps remain onto at every type; the arguments of §3 continue to apply, with ↑a=↑b={a,b}.

Define f_a(o)=a, f_b(o)=b, and let both maps fix a and b. Together with identity they read all three points. Each map is inflationary, idempotent and satisfies f[↑x]=↑f(x). Thus the root has full IdemBoxSep.

At either terminal point, every Boolean observer is still a coordinate map on {a,b}. BoxComm requires its image to be all of {a,b}, because every future cone there is the whole cluster. An idempotent surjection is identity. Hence identity is the only IdemBox-qualified observer there. At a it cannot distinguish the two false propositions ∅ and {b}; at b use ∅ and {a}. The propositional instance at Δ={t} fails throughout the terminal cluster.

The terminal cluster itself has endpoint separation: the two constant coordinate maps read its two points and give outputs either ∅ or the entire cluster. All transports are bijective, so the full logical qualification follows as in §3. This verifies the endpoint comparison used in §6 directly.

Consequently the root satisfies

$$
\mathrm{IdemBoxSep}+\Box\mathrm{OS}
+\Box\mathrm{BF}+\Box\mathrm{Functionality},
\qquad\neg\Box\mathrm{IdemBoxSep}.
\tag{10}
$$

This does not conflict with persistence of each whole idempotence identity. As in the earlier inverse examples, the additional separating power need not persist when parameters and propositions are transported.

## 8. Sources

The new qualification comparison, finite coordinate-map characterization, join theorem and model verdicts are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–7, unpaginated. The explicit finite-frame arguments above are the evidence; no missing graph arrow is used as a nonimplication proof.

The full action-model framework is Bacon and Dorr, *Classicism*, draft of 16 May 2023, §3.5, pp. 58–61; Appendix D, pp. 73–74, recorded in [Full action models](../../source/topics/classicism/groups/full-action-models.yaml). The all-type epic-transport Barcan criterion is Proposition 3.24(ii), recorded in [Full epic Barcan](../../source/topics/classicism/arguments/full-epic-barcan.yaml). The finite coordinate proof specializes the method of [Omega-chain logical observers](omega-chain-surjective-observers.md), §§1–3; unlike the infinite case, principality follows directly from finite Boolean reasoning.

The C5 native-Box/injectivity equivalence is the linked native-Box note, §3. Ordinary idempotent normalization and the Extensionality comparison retain the attribution and scope of the linked hierarchy note, §§2 and 8. The two-colour model retains its own construction and source status. The new examples do not change those earlier proofs or claim formal verification.

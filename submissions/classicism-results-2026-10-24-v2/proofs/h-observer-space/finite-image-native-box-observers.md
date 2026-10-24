# Finite-image native-Box observers and internal finiteness

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new arguments: `misc`, this note, §§1–5, unpaginated. Earlier finiteness and action-model ingredients are attributed in §6.

An actual world changes the effect of requiring native-Box observers to have finite images. With Actuality, finite-image native-Box separation forces the entire proposition domain to be internally finite. Conversely, internal finiteness makes the image restriction redundant. This gives an exact characterization in every full rooted-poset model, including frames of infinite width.

## 1. The fixed-instance theorem

Use $\mathrm{Good}_\Delta$ and the whole-operation qualification BoxComm from [Native-Box logical observers](native-box-logical-observers.md), §1. Thus
$$
 \mathrm{BoxComm}(E):\quad
 (\lambda p.E(\Box p))=(\lambda p.\Box Ep),
 \qquad \Box p:=(p=\top).
 \tag{1}
$$
For an admitted E:tt, put
$$
 \mathrm{Im}(E):=\lambda q.\exists p\,(Ep=q),
 \qquad \mathrm{FinIm}(E):=
 \mathrm{Fin}_t(\mathrm{Im}(E)).
 \tag{2}
$$
Here Fin is internal Frege finiteness, defined in §2. It supplies neither a fixed external bound nor an external enumeration.

Write FinBoxSep(τ,Δ) for separation at the fixed relational output type τ by the common class $\mathrm{Good}_\Delta$∧BoxComm∧FinIm. BoxSep(τ,Δ) has the same definition with FinIm omitted. Without indices these names denote the full schemas over relational output types and finite external qualification lists. No qualification list is required to contain t in the following local result.

For every relational τ and every finite Δ, over C,
$$
 \boxed{
 \mathrm{Actuality}\land\mathrm{FinBoxSep}(\tau,\Delta)
 \quad\longleftrightarrow\quad
 \mathrm{Fin}_t(\mathrm{All})\land\mathrm{BoxSep}(\tau,\Delta),
 \qquad \mathrm{All}:=\lambda p.\top.}
 \tag{3}
$$
Actuality is the unboxed principle
$$
 \exists w\,[w\land\forall p\,(p\to w\le p)],
 \qquad p\le q\ :\!\!\iff\ p\land q=p.
 \tag{4}
$$
The proof does not assume C5, Choice, BF, Functionality or necessary Actuality. The local observer argument uses only Boolean preservation and native-Box commutation. The full $\mathrm{Good}_\Delta$ qualification is retained throughout, without replacing its whole-operation identities by material laws.

## 2. Internal finiteness under images and injective preimages

At type t the [background definitions](../../source/topics/classicism/background.md) are
$$
 \begin{aligned}
 \mathbf0&:=\lambda U.\forall x\,\neg Ux,\\
 \mathrm{Suc}(Z)&:=\lambda U.\exists y\,
 [Uy\land Z(\lambda x.Ux\land x\ne y)],\\
 \mathrm{FiniteCardinality}_t(Z)&:=
 \forall W\,[(W\mathbf0\land
 \forall Y(WY\to W(\mathrm{Suc}(Y))))\to WZ],\\
 \mathrm{Fin}_t(U)&:=\exists Z\,
 [\mathrm{FiniteCardinality}_t(Z)\land ZU].
 \end{aligned}
 \tag{5}
$$
Here U:tt, Z:(tt)t and W:((tt)t)t. All induction predicates below are admitted lambda terms. The arguments are valid already over H and use current identity and ordinary quantified reasoning.

First, membership in a finite cardinality is invariant under current coextension of predicates. Prove by Frege induction on Z that
$$
 \forall U,V\,
 [\forall x(Ux\leftrightarrow Vx)\to(ZU\leftrightarrow ZV)].
 \tag{6}
$$
At zero this follows from the universal emptiness test. At a successor, the same witness y belongs to both coextensive predicates, and their exact deletion predicates remain coextensive; use the induction hypothesis on those deletions. It follows that Fin itself is invariant under current coextension. No identity between coextensive predicates or cardinality objects is inferred.

The empty predicate is finite. If V is finite and Vy is false, adjoining y produces a finite predicate: take a cardinality witness Z for V and use Suc(Z), with deletion witness y and (6). These facts allow the following two internal inductions.

**Injective-preimage lemma.** If an admitted E is currently injective and U is internally finite, then λx.U(Ex) is internally finite.

For the proof let
$$
 W_E(Z):=\forall U\,[ZU\to
 \mathrm{Fin}_t(\lambda x.U(Ex))].
 \tag{7}
$$
At zero the preimage is empty. For the successor, obtain y∈U and ZV with V:=λz.Uz∧z≠y. The induction hypothesis gives a finite preimage of V. If no x satisfies Ex=y, the preimages of U and V are coextensive. Otherwise choose one such x. Injectivity makes it the unique preimage of y, and it is absent from the preimage of V. The preimage of U is therefore the previous finite predicate with exactly x adjoined. In either case it is finite. This establishes the successor step and then (7) at any finite-cardinality witness for U.

In particular, applying the lemma to Im(E) gives
$$
 \mathrm{Inj}(E)\land\mathrm{FinIm}(E)
 \quad\Longrightarrow\quad
 \mathrm{Fin}_t(\mathrm{All}),
 \tag{8}
$$
because every Ex belongs to Im(E).

**Image lemma.** For any admitted E, the image of an internally finite predicate U,
λq.∃x(Ux∧Ex=q), is internally finite.

Use the analogous induction predicate which asserts this conclusion for every U of cardinality Z. The zero case is empty. In the successor step, deleting y gives a finite previous image, and the new image is obtained by adding Ey. If Ey already belongs to the previous image, the two images are coextensive; otherwise this is an adjoining-one-member step. Consequently
$$
 \mathrm{Fin}_t(\mathrm{All})
 \quad\Longrightarrow\quad
 \forall E^{tt}\,\mathrm{FinIm}(E).
 \tag{9}
$$
These proofs take a single existential witness within an induction step. They do not assemble a choice function, assume a standard numeral for an internal cardinality, or replace internal finiteness with external finiteness.

## 3. One accepted actual world makes an observer injective

Work over C, and let w satisfy (4). Let E preserve the Boolean operations and commute with native Box. Suppose Ew is true.

If p is true, w≤p. Boolean preservation makes E monotone, so Ew≤Ep and Ep is true. If p is false, ¬p is true, so w≤¬p; then Ew≤E¬p=¬Ep and Ep is false. Thus E has exactly the current truth profile of identity:
$$
 \forall p\,(Ep\leftrightarrow p).
 \tag{10}
$$
Now suppose Ep=Eq. Boolean preservation gives E(p↔q)=Top. Applying the whole native-Box identity at p↔q yields
$$
 E\Box(p\leftrightarrow q)
 =\Box E(p\leftrightarrow q)
 =\Box\top
 =\top.
 \tag{11}
$$
By (10), □(p↔q) is true. C's Boolean algebra then gives p=q. Hence E is currently injective. Notice that (10) alone would not prove injectivity; the native-Box condition is the step that does so.

Suppose FinBoxSep(t,Δ) and Actuality hold. Since w is true, w≠Bottom. Separation supplies a qualifying E that distinguishes them. Every Good observer fixes Bottom over C, so EBottom is false and Ew is true. This E is injective by the preceding argument and has internally finite image by qualification. Equation (8) gives $\mathrm{Fin}_t(\mathrm{All})$. Forgetting FinIm also gives BoxSep(t,Δ).

The same conclusion follows from any fixed relational instance FinBoxSep(τ,Δ). Indeed, separation at τ implies propositional separation for the same observer class: represent p,q by their constant τ-relations λz̄.p and λz̄.q. Observer agreement on p,q gives agreement on those relations at every argument tuple; their identity, supplied by separation, yields p=q by application to a tuple. The standing nonempty type domains provide such a tuple. This reduction needs no Functionality premise.

Conversely, (9) makes every admitted observer finite-image under $\mathrm{Fin}_t(\mathrm{All})$. Thus BoxSep(τ,Δ) and FinBoxSep(τ,Δ) have the same qualifying class.

It remains to recover Actuality on this converse side. Over C, the true propositions form the admitted nonempty predicate λp.p, closed under conjunction. The internal finite-closure lemma in [Finite semilattice normalization](finite-semilattice-normalization.md), §2, applied under $\mathrm{Fin}_t(\mathrm{All})$, gives a least member w of this predicate. It is true and lies below every true proposition, exactly (4). That lemma is a Frege deletion induction combining a previous lower bound with the deleted true member by conjunction; it uses no external enumeration or Choice. This completes (3).

## 4. Full typed separation over H

At full schema scope the explicit C premise can be recovered. FinBoxSep implies BoxSep, which implies ordinary full OS. The [H transport theorem](typed-separation-and-classicism.md), §3, therefore supplies C, BF and Functionality. The same is true on the BoxSep side. Applying (3) instance by instance gives the exact full-theory equivalence
$$
 \boxed{
 \mathrm H+\mathrm{Actuality}+\mathrm{FinBoxSep}
 \quad\equiv\quad
 \mathrm H+\mathrm{Fin}_t(\mathrm{All})+\mathrm{BoxSep}.}
 \tag{12}
$$
This is an equivalence between the stated full theories. It does not claim that one propositional separation instance recovers C. Nor does it remove Actuality from the left side: the argument needs a qualifying observer accepting one true proposition below all truths.

The finiteness restriction is imposed on each individual observer's admitted image. It is not a bound on the number of observers, a uniform finite range bound, or the assertion that a finite family separates. Equation (12) shows why the restriction nevertheless becomes global finiteness in the presence of Actuality and native-Box preservation.

## 5. Exact classification in full rooted-poset models

Let P be any nonempty set-sized partially ordered frame with a least point o. Use its thin category, singleton individuals, and the full relational action-model construction. As in [Idempotent native-Box observers](idempotent-native-box-observers.md), §3,
$$
 D_t(x)=\mathcal P(\mathord\uparrow x),
 \qquad p\text{ is true at }x\ \Longleftrightarrow\ x\in p.
 \tag{13}
$$
All future truth profiles at relational types are admitted. Transport is restriction to a future cone and is onto at every type. Hence the model satisfies C, BF and Functionality at every point.

At the root, {o} is true and is contained in every true proposition. Thus Actuality holds, with no finite-width or finite-height assumption. Equation (3) applies.

In this particular full model, internal $\mathrm{Fin}_t(\mathrm{All})$ holds at o exactly when the external set $D_t(o)$ is finite. For the nontrivial direction, fullness admits a predicate W on cardinality objects whose current extension is exactly
$$
 \{\mathbf0,\mathrm{Suc}(\mathbf0),
 \mathrm{Suc}^{2}(\mathbf0),\ldots\},
 \tag{14}
$$
where this is the external set of actual denotations of the standard finite iterates. Choose arbitrary future values for W. Its current extension contains zero and is closed under Suc. If Z satisfies the internal FiniteCardinality predicate, its instance at this admitted W says that Z equals one of those actual denotations. A separate ordinary finite induction on n shows that Sucⁿ(0) applies at the root to U exactly when U's current extension has n members: the zero and exact-deletion clauses in (5) give the induction. Hence a witness Z for $\mathrm{Fin}_t(\mathrm{All})$ forces $D_t(o)$ to have finitely many members. Conversely, when $D_t(o)$ has n members, Sucⁿ(0) witnesses $\mathrm{Fin}_t(\mathrm{All})$, and its FiniteCardinality follows by n applications of the defining induction step.

This use of external standard iterates is justified by full model admission. It is not used in the abstract internal proof of §§2–4. Since $D_t(o)$=P(P), its external finiteness is equivalent to finiteness of the frame P.

Consequently, in this specified full-model family,
$$
 \boxed{
 \mathrm{FinBoxSep}
 \quad\Longleftrightarrow\quad
 P\text{ is finite and the model satisfies BoxSep}.}
 \tag{15}
$$
Failure on an infinite frame is already propositional at every fixed finite Δ: Actuality and FinBoxSep(t,Δ) would contradict the preceding finiteness calculation. On a finite frame, every observer has internally finite image, so the two qualified classes agree at every output type and list.

For completeness, the remaining finite-frame condition has an exact coordinate formulation. For each a∈P there must exist a map f:P→P with
$$
 x\le f(x),\qquad f(o)=a,\qquad
 f[\mathord\uparrow x]=\mathord\uparrow f(x)
 \quad\text{for every }x\in P.
 \tag{16}
$$
The finite-frame theorem in the idempotent note, §§3–4, identifies these maps with native-Box logical observers: $E_f$(p)=f⁻¹[p]. Every such observer satisfies all the required whole quantifier laws. Readers at every a separate propositions, and Functionality gives all relational output types. Conversely the distinct propositions ∅,{a} require such a reader. Thus (15) can equivalently be stated as finiteness of P together with (16) for every a.

No classification of arbitrary observers on infinite-width frames is needed for (15). In particular, the finite-width principality argument in [Bounded stabilization](bounded-stabilization-native-box-observers.md), §6, is not being applied outside its stated range.

## 6. Sources

The observer-injectivity argument, fixed-instance equivalence (3), full-H equivalence (12), and finite-image classification (15) are new ordinary arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–5, unpaginated. The internal image/preimage inductions are provided in §2.

The Frege definitions are the map's fixed definitions in the [background](../../source/topics/classicism/background.md) and [Axiom of Infinity at t](../../source/topics/classicism/principles/axiom-of-infinity-t.yaml). Actuality is recorded from Bacon and Dorr, *Classicism*, draft of 16 May 2023, §2.2, p. 25, in [Actuality](../../source/topics/classicism/principles/actuality.yaml). The internal finite-closure lemma is the original argument in [Finite semilattice normalization](finite-semilattice-normalization.md), §2. The native-Box and full typed H-recovery ingredients retain their proofs in the linked notes.

The model construction is Bacon and Dorr, *Classicism*, draft of 16 May 2023, §3.5, pp. 58–61; Appendix D, pp. 73–74, recorded in [Full action models](../../source/topics/classicism/groups/full-action-models.yaml). Onto type transport gives Barcan by Proposition 3.24(ii), recorded in [Full epic Barcan](../../source/topics/classicism/arguments/full-epic-barcan.yaml). The finite rooted-poset coordinate theorem is the new argument in [Idempotent native-Box observers](idempotent-native-box-observers.md), §§3–4.

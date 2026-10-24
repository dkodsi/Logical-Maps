# Internally finite separating families and the proposition domain

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new arguments: misc, this note, §§1–5, unpaginated.

An internally Frege-finite family of observers cannot separate an internally infinite proposition domain. This holds over H, without Boolean qualification, Functionality or Choice. The converse finiteness calculation uses Functionality: operations from a finite domain into a finite codomain form an internally finite class. Together these facts identify reversible separation with finitely many admitted reversible observers exactly with endpoint separation and an internally finite proposition domain.

The two induction arguments use different kinds of information. Observer separation compares the current truth of outputs. The finite function-table argument compares output identities. Neither argument replaces internal finiteness by an external list of members.

## 1. Frege finiteness and the closure lemmas

Fix any object type α. For U:αt write U−a for λx.(Ux∧x≠a), and write U≈V for current coextension, ∀x(Ux↔Vx). The fixed [background definitions](../../source/topics/classicism/background.md) are

$$
\begin{aligned}
\mathbf0_\alpha(U)&:=\forall x^\alpha\,\neg Ux,\\
\mathrm{Suc}_\alpha(Z)(U)&:=
 \exists a^\alpha\,[Ua\land Z(U-a)],\\
\mathrm{FC}_\alpha(Z)&:=
 \forall W^{((\alpha t)t)t}
 [(W\mathbf0_\alpha\land
   \forall Y(WY\to W(\mathrm{Suc}_\alpha(Y))))\to WZ],\\
\mathrm{Fin}_\alpha(U)&:=
 \exists Z^{(\alpha t)t}\,[\mathrm{FC}_\alpha(Z)\land ZU].
\end{aligned}
\tag{1}
$$

All types here are fixed externally. Every predicate used in an induction below is an admitted lambda term.

**Coextension bookkeeping.** Put

$$
\mathrm{Ext}_\alpha(Z):=
\forall U,V\,[U\approx V\to(ZU\leftrightarrow ZV)].
\tag{2}
$$

This holds at zero. If it holds for Z, it holds for Suc(Z): the same chosen a belongs to either coextensive predicate, and their exact deletions remain coextensive. Frege induction therefore proves FC(Z)→Ext(Z), and consequently

$$
U\approx V\quad\Longrightarrow\quad
(\mathrm{Fin}_\alpha(U)\leftrightarrow
 \mathrm{Fin}_\alpha(V)).
\tag{3}
$$

For each induction property P(Z) below one may use the full induction predicate
FC(Z)∧Ext(Z)∧P(Z). FC holds at zero and is successor-closed directly from (1); the preceding argument supplies Ext. This keeps the predecessor's coextension invariance available whenever a deletion predicate is replaced by a coextensive one. It never identifies coextensive predicates or cardinality objects.

We will use the following H lemmas, with their internal proofs.

**Empty predicates, singletons and adjoining.** The empty predicate has cardinality zero. If Fin(U) and Ua is false, then λx.(Ux∨x=a) is finite: choose a cardinality witness Z for U and use Suc(Z), deleting a. Its deletion is coextensive with U, so (2) supplies cardinality membership. If Ua is true, adjoining a changes only the presentation, by (3). In particular every singleton is finite. A predicate with at most one member is finite, by the classical cases that it is empty or has a chosen member a and is coextensive with that singleton.

**Subsets.** If Fin(U) and V⊆U, then Fin(V). Induct on a cardinality Z of U, universally over such U,V. The empty case is immediate. In the successor case delete a∈U, obtaining Z(U−a). The predicate V−a is a subset of U−a and hence finite by the induction hypothesis. If Va is true, adjoin a; otherwise V≈V−a.

**Binary unions.** If Fin(U) and Fin(V), then Fin(U∨V). Induct on a cardinality Z of U, universally over U and every finite V. The empty case reduces to V. At the successor step the induction hypothesis makes (U−a)∨V finite; adjoining a gives a predicate coextensive with U∨V. This proves the step even when a already belongs to V.

**Finite indexed unions.** For an admitted R:αβt and X:αt,

$$
\mathrm{Fin}_\alpha(X)\land
\forall x\,[Xx\to\mathrm{Fin}_\beta(\lambda y.R(x,y))]
\ \Longrightarrow\
\mathrm{Fin}_\beta
 \bigl(\lambda y.\exists x\,[Xx\land R(x,y)]\bigr).
\tag{4}
$$

Induct on a cardinality of X, universally over X and R. At zero the union is empty. A successor deletes a∈X. The union indexed by X−a is finite by the induction hypothesis, and the fibre at a is finite by the displayed premise. The original union is coextensive with their binary union, so the preceding lemma and (3) finish. The argument takes the finite witness for one fibre inside one induction step. It does not choose witnesses for all fibres simultaneously.

These closure proofs need only current identity, its substitution rule, classical quantified reasoning and lambda terms. They use neither C's Logical Equivalence nor an extensionality principle.

## 2. Finite truth profiles separate only a finite class

For U:(tt)t and V:tt define

$$
\mathrm{Sep}(U,V):=
\forall p,q\,
\left[
 Vp\land Vq\land
 \forall E^{tt}(UE\to(Ep\leftrightarrow Eq))
 \ \to\ p=q
\right].
\tag{5}
$$

The family U and the class V are admitted predicates. The observers in U need not preserve any logical operation.

**Finite-profile theorem, over H.**

$$
\boxed{
\mathrm{Fin}_{tt}(U)\land\mathrm{Sep}(U,V)
\ \Longrightarrow\ \mathrm{Fin}_t(V).}
\tag{6}
$$

Use Frege induction on Z at type tt, with property

$$
P(Z):=
\forall U,V\,
[(ZU\land\mathrm{Sep}(U,V))\to\mathrm{Fin}_t(V)],
\tag{7}
$$

and the bookkeeping conjuncts FC and Ext described in §1.

At zero U has no members. The observer-agreement premise in (5) is then vacuous, so any two members of V are equal. The at-most-singleton lemma makes V finite.

For the successor step choose E∈U with Z(U−E). Define

$$
V_+(p):=Vp\land Ep,\qquad
V_-(p):=Vp\land\neg Ep.
\tag{8}
$$

The smaller family U−E separates each of these two classes. Indeed suppose p,q lie in the same one and agree under all members of U−E. For any G∈U, if G=E then Gp and Gq have the same current truth by (8), using equality substitution. If G≠E, G belongs to U−E and agreement is part of the premise. Thus p,q agree under all U and (5) gives p=q.

Apply the induction hypothesis twice, with the same cardinality witness Z for U−E, to obtain Fin(V₊) and Fin(V₋). Their union is coextensive with V. Binary union and (3) prove Fin(V), finishing the induction.

In particular, with All_t:=λp.Top,

$$
\mathrm{Fin}_{tt}(U)\land\mathrm{Sep}(U,\mathrm{All}_t)
\ \Longrightarrow\ \mathrm{Fin}_t(\mathrm{All}_t).
\tag{9}
$$

Only the current truth bits in (8) are used. No identity between true propositions, truth-valued selector, Functionality or choice function is assumed. Equation (9) concerns one internally finite family that separates; it does not assert that every infinite family contains a finite separating subfamily.

## 3. Internally finite evaluation tables

Fix types α,β with β≠e, so αβ is an allowed function type. Let X:αt, Y:βt and V:(αβ)t be admitted predicates. Define

$$
\begin{aligned}
\mathrm{Values}(V,X,Y)&:=
 \forall f\,[Vf\to\forall x(Xx\to Y(fx))],\\
\mathrm{Identifies}(X,V)&:=
 \forall f,g\,
 [(Vf\land Vg\land\forall x(Xx\to fx=gx))\to f=g].
\end{aligned}
\tag{10}
$$

Here the evaluation test is the identity fx=gx. A material biconditional between these outputs, even when β=t, would be a different premise.

**Finite-table theorem, over H.**

$$
\boxed{
\mathrm{Fin}_\alpha(X)\land\mathrm{Fin}_\beta(Y)
\land\mathrm{Values}(V,X,Y)
\land\mathrm{Identifies}(X,V)
\ \Longrightarrow\ \mathrm{Fin}_{\alpha\beta}(V).}
\tag{11}
$$

Frege-induct on a cardinality Z of X. The induction property universally quantifies X,Y,V, assuming ZX, Fin(Y) and the two conditions in (10). Include FC and Ext as before.

If X is empty, the evaluation premise in Identifies is vacuous and V has at most one member.

For a successor choose a∈X with Z(X−a). For each y∈Y define the admitted fibre

$$
V_y(f):=Vf\land fa=y.
\tag{12}
$$

All values on X−a still lie in Y. Moreover X−a identifies V_y: two members agreeing there also agree at a because both values equal y; therefore they agree on X, and Identifies(X,V) makes them equal. The induction hypothesis yields Fin(V_y) for every y∈Y.

Apply (4) to the finite index predicate Y and the admitted relation V_y(f). The resulting union of the V_y is coextensive with V. One direction follows from (12); for the other, Vf gives Y(fa) since a∈X, so y=fa is an index witnessing membership. Equation (3) proves Fin(V).

This proof does not construct functions from arbitrary finite tables. It counts an already admitted function class by its identifying evaluations. In particular no Plenitude, function comprehension beyond the given lambda terms, or Choice is needed.

Let Fun_{α,β} be the stated local Functionality premise
∀f,g[(∀x.fx=gx)→f=g]. Taking both X and Y to be their full domains gives

$$
\mathrm H+\mathrm{Fun}_{\alpha,\beta}\ \vdash\
\left[
\mathrm{Fin}_\alpha(\mathrm{All}_\alpha)
\land\mathrm{Fin}_\beta(\mathrm{All}_\beta)
\ \to\
\mathrm{Fin}_{\alpha\beta}(\mathrm{All}_{\alpha\beta})
\right].
\tag{13}
$$

In particular,

$$
\mathrm H+\mathrm{Fun}_{t,t}\ \vdash\
\mathrm{Fin}_t(\mathrm{All}_t)
\ \longrightarrow\
\mathrm{Fin}_{tt}(\mathrm{All}_{tt}).
\tag{14}
$$

The subset lemma then makes every admitted observer subclass finite, regardless of its qualification.

## 4. The exact reversible-observer region

Let Aut:(tt)t be the admitted predicate

$$
\mathrm{Aut}(E):=
\mathrm{Good}_{\{t\}}(E)\land
\exists F^{tt}\,
[\mathrm{Good}_{\{t\}}(F)\land
 E\circ F=I\land F\circ E=I].
\tag{15}
$$

Before C is recovered, Good is the original full typed logical qualification, with whole Boolean and quantifier identities and the translated equality clauses. Both inverse equations are whole-operation identities. Over C5 this predicate is coextensive with the reduced identity-based guard A in [Reversible fixed propositions](reversible-fixed-proposition-characterization.md), §1. Equation (3), rather than an assumed identity between the guards, makes their finiteness statements interchangeable there.

Rev and End below are the full reversible and endpoint logical separation schemas, over every relational output type and finite external qualification list. FinAll abbreviates Fin_t(All_t).

**Theorem.**

$$
\boxed{
\begin{aligned}
\mathrm H+\mathrm{Rev}
 +\mathrm{Fin}_{tt}(\mathrm{Aut})
&\quad\equiv\quad
\mathrm H+\mathrm{End}+\mathrm{FinAll}\\
&\quad\equiv\quad
\mathrm{C5}+\mathrm{FinAll}\\
&\quad\equiv\quad
\mathrm{C5}+\mathrm{FinBoxSep}.
\end{aligned}}
\tag{16}
$$

The last line retains full finite-image native-Box separation, as in [Finite-image Box reflection](finite-image-box-reflection.md), §4. These are equivalences of the displayed theories; one fixed propositional separation instance is not being used to recover C.

**From the finite reversible family.** Full Rev includes propositional separation by Aut at list {t}. Thus Sep(Aut,All_t), and (9) gives FinAll. Rev already supplies C5. Alternatively, to obtain End directly, identity is a $\mathrm{Good}_{\{t\}}$ observer with internally finite image under FinAll; the established [single finite-image witness theorem](../logical-observer-hierarchy.md), §6, gives End from Rev and that witness.

**From End and FinAll.** End supplies Rev and Functionality. Equation (14) makes the entire tt domain internally finite; the subset lemma gives Fin_tt(Aut). This proves the first equivalence without an external enumeration of observers or propositions.

For completeness, the middle equivalence can be proved internally without appealing to an external finite Boolean algebra.

**Internal minimal-element lemma.** Every nonempty internally finite predicate in an admitted partial order has a minimal member. Frege-induct on its cardinality. The zero case has no nonempty predicate. At a successor delete a. If the remainder is empty, a is minimal. Otherwise choose a minimal b of the remainder by the induction hypothesis. If a is not strictly below b, b is minimal in the whole predicate: the only new possible predecessor is a. If a is strictly below b, a is minimal. A strict predecessor of a would belong to the remainder and, by transitivity, be strictly below b, contradicting b's minimality. This proves the lemma with single existential witnesses inside each step.

Under C5+FinAll, the predicate
λq.(q≠Bottom∧q≤p) is finite by the subset lemma and is nonempty whenever p≠Bottom. A minimal member a is an atom below p: every nonzero q≤a belongs to that predicate, and minimality forces q=a. Hence Atomicity_t holds. The established C5+Atomicity_t characterization gives full End. Conversely End supplies C5. This proves the middle equivalence in (16).

The final equivalence is the already established exact C5+FinBoxSep⇔End+FinAll theorem. No Actuality premise is added: in this region it follows from internal finiteness by the finite-closure argument.

One may replace Fin_tt(Aut) on the first line by Fin_tt(All_tt). The latter implies the former by subset closure; the former together with Rev gives FinAll, and then (14) gives the latter. Thus in this region finiteness of all reversible observers and finiteness of all admitted unary operations coincide, although the qualification in (15) mentions only the reversible class.

### Finite separating families for each schema instance

For any of the original qualification predicates K_Δ, let finite-family K-separation at (τ,Δ) mean that there exists an admitted U:(tt)t such that Fin_tt(U), every member of U satisfies K_Δ, and U separates the τ-objects by their observed material agreement on every argument tuple. This is one finite formula for each fixed relational τ and finite Δ. A different U may be chosen for a different instance; no common family across all types or lists is asserted.

For full schemas over H the preceding lemmas give

$$
\boxed{
\begin{aligned}
\text{finite-family ordinary logical separation}
 &\ \equiv\ \mathrm{OS}+\mathrm{FinAll},\\
\text{finite-family reversible logical separation}
 &\ \equiv\ \mathrm{Rev}+\mathrm{FinAll}
 \ \equiv\ \mathrm{C5}+\mathrm{FinAll},\\
\text{finite-family native-Box logical separation}
 &\ \equiv\ \mathrm{BoxSep}+\mathrm{FinAll}
 \ \equiv\ \mathrm{FinBoxSep}.
\end{aligned}}
\tag{17}
$$

Forwards, forgetting finiteness and using U⊆K_Δ gives the corresponding unrestricted separation instance. Any propositional instance also gives FinAll by (9). More generally a fixed relational instance yields the same conclusion: constant τ-relations associated with p,q reduce U-separation at τ to (5) for all propositions, and a tuple of arguments exists because types are nonempty. This reduction needs no Functionality.

For the converses, each full unrestricted separation schema implies full OS and therefore supplies C, BF and Functionality by the [H transport theorem](typed-separation-and-classicism.md). Under FinAll, (14) and subset closure make the entire qualifying predicate K_Δ internally finite. Take U=K_Δ for the requested instance. The final identifications in (17) use (16) and the full FinBox reflection theorem, respectively.

Thus internally finite separating families are exactly a global finiteness requirement added to the corresponding full separation theory. For Box observers this family restriction has the same full-theory strength as requiring each separating witness to have a finite image. The predicates and proof mechanisms of those two restrictions remain different.

## 5. Scope and comparison

The essential new implication is the H theorem (6). It applies to any internally finite family of arbitrary observers and any admitted class V that the family separates. Whole logical qualification is needed only for the application to Rev in §4.

The converse table theorem (11) also holds over H, with its explicit identifying premise. Functionality enters only when that premise is inferred from agreement on the entire input domain. There is no general assertion that finite source and target domains alone identify operations in bare H.

The finiteness predicates in (16) have no fixed external bound. They do not mean that every observer has a finite image, that each separating pair has some finite family of witnesses, or that the selected witnesses have bounded order. In particular a pair can always be distinguished by a single witness whenever separation holds; (9) instead requires one internally finite U to separate every pair in V.

The region in (16) is strictly stronger than End alone. A full S5 cluster on an infinite set of worlds has endpoint separation, while its full proposition powerset is not internally finite. In that full model the standard-iterate predicate on cardinality objects is admitted, so internal FinAll would force an external finite enumeration, as proved in [Finite-image native-Box observers](finite-image-native-box-observers.md), §5. Conversely each nonempty finite full S5 cluster satisfies (16). Thus the theorem allows arbitrarily large finite proposition domains without providing one fixed external size bound.

Nothing here resolves the remaining injective-versus-split-inverse comparison. The arguments concern current finite families and exact internal finiteness, not an unproved choice of transversals.

## 6. Sources

The finite-profile theorem, finite-table theorem, internal closure and minimal-element proofs, and the finite-observer characterization are original ordinary arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source misc, this note, §§1–5, unpaginated.

The Frege definitions are the fixed [background definitions](../../source/topics/classicism/background.md), with the type-t infinity convention recorded in [Axiom of Infinity at t](../../source/topics/classicism/principles/axiom-of-infinity-t.yaml). That record cites Cian Dorr's suggestion of 19 September 2026 and Bacon and Dorr, Classicism, draft of 16 May 2023, §2.3, n. 47, p. 32. The coextension/image inductions in [Finite-image native-Box observers](finite-image-native-box-observers.md), §2, are earlier original arguments; the needed union and finite-table proofs are supplied here.

Functionality has its source formulation in Bacon and Dorr, Classicism, draft of 16 May 2023, §1.4, pp. 15–16, especially n. 18, recorded in [Functionality](../../source/topics/classicism/principles/functionality-r.yaml). Rev⇒C5, End⇔C5+Atomicity_t and the single finite-image witness theorem retain their proofs in [Logical observer hierarchy](../logical-observer-hierarchy.md), §§3–6. The FinBox comparison is [Finite-image Box reflection](finite-image-box-reflection.md), §4.

The full S5 models use Bacon and Dorr's full action construction, draft of 16 May 2023, §3.5, pp. 58–61; Appendix D, pp. 73–74, recorded in [Full action models](../../source/topics/classicism/groups/full-action-models.yaml). The source construction and the explicitly checked finiteness argument justify the comparison; no general identification of internal and external finiteness is assumed.

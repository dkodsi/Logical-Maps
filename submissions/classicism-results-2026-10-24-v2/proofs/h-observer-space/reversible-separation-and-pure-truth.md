# Reversible logical separation implies No Pure Contingency

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new observer implication: `misc`, this note, §§1–5, unpaginated. The conjugation argument is adapted from the existing [C5 and Atomicity proof](../../source/topics/classicism/writeups/c5-and-atomicity-imply-no-pure-contingency.md), §§4–5; its attribution is specified in §5.

**Over H, full reversible logical separation implies No Pure Contingency.** No atom or Actuality premise is needed. Combined with the previously established bounds, this gives

$$
\boxed{\mathrm{Rev}\ \Longrightarrow\
\mathrm{C5}+\Box\mathrm{OS}+\mathrm{NoPureContingency}.}
\tag{1}
$$
This is an implication, not a characterization. The [finite-block symmetry model](finite-block-symmetry-reversible-gap.md) uses this obstruction to refute the converse from C5 plus necessary ordinary separation: it has a contingent closed pure sentence and fails Rev. The later [component-shift symmetry model](component-shift-symmetry-reversible-gap.md) refutes the converse even with No Pure Contingency added, using an endpoint-valued first-order relation parameter and an individual parameter. Its §6 extends the positive conjugation argument to the precisely stated parameter schema.

## 1. Observer and schema scope

Use Good_Δ, OS and Rev from [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md), §1. Δ is always a finite external type list. Preservation and inverse assertions are identities of the whole displayed operations. An inverse must be an admitted observer qualified for the same list. No infinite conjunction over types is an object-language formula.

Full typed Rev already implies C5 and is equivalent to full typed separation by qualified involutions. These are established implications from the hierarchy note, §§4 and 6. We use them to work in C5 and replace a reversible witness by an involutive witness; the atom-swap construction is not used.

Fix a closed pure sentence P. Let Δ_P contain every type σ for which a primitive quantifier ∀_σ or ∃_σ occurs in P, including occurrences inside its lambda subterms. Expand defined notation first. There are only finitely many such types. The following argument uses the propositional separation instance for that list, with involution qualification

$$
\operatorname{Good}_{\Delta_P}(T)\land T\circ T=I.
\tag{2}
$$
Equality types occurring in P need not be added to the quantifier list: C5 makes all their equality judgments endpoints, and Boolean qualification fixes those endpoints. Only finitely many C5, Barcan and Functionality instances enter the proof for a fixed P. Including additional types, such as t, in Δ_P is harmless but unnecessary for this step.

No Pure Contingency is the sentence schema

$$
P\to\Box P\qquad(P\text{ a closed pure sentence}).
$$
It is not an internal universal quantification over all propositions. Nonlogical constants are excluded; the proof does not assert that an observer fixes arbitrary named propositions.

## 2. Admitted conjugation in the relational language

Fix T satisfying (2). For each relational type τ define an admitted transformation T^*_τ on its objects. At t it is T. At the individual type use the metalevel convention

$$
T^*_e(x):=x.
$$
This is a notation for leaving an individual variable unchanged, **not** an object of type e→e: that type is absent from the fixed relational language. For every relational type σ→τ, define

$$
T^*_{\sigma\tau}(X):=
\lambda y^\sigma.\,T^*_\tau\bigl(X(T^*_\sigma(y))\bigr),
\tag{3}
$$
where T^*_σ(y) is simply y when σ=e. Because τ is relational, every lambda term actually formed in (3) has an allowed type. For relational σ, the map T^*_σ itself has the allowed type σ→σ.

Induction on the type proves

$$
T^*_\sigma(T^*_\sigma x)=x,
\tag{4}
$$
with the individual case interpreted by the convention above. For the arrow step, beta reduction expands the double application; the induction hypotheses at σ and τ cancel the two transformations. Functionality at the relevant relation types identifies the resulting abstraction with X. C5 supplies these Functionality instances through Barcan. Thus each relational transformation is a surjection and an injection on its admitted domain, with itself as inverse; the individual substitution is trivially bijective.

The same calculation gives application compatibility:

$$
(T^*_{\sigma\tau}X)(T^*_\sigma y)
=T^*_\tau(Xy).
\tag{5}
$$
These are identities, not just material equivalences. All lifted objects are explicit lambda terms; no choice of an external domain bijection is made.

## 3. Logical constants and pure terms are fixed

**Endpoints and Boolean connectives.** Boolean qualification fixes Top and Bottom over C. For negation, conjugation gives

$$
T^*_{tt}(\neg)(p)=T(\neg Tp)=\neg T(Tp)=\neg p.
$$
For conjunction it gives

$$
T^*_{t(tt)}(\land)(p,q)
=T(Tp\land Tq)=p\land q,
$$
and likewise for disjunction. Functionality lifts these pointwise output identities to identities of the constants as whole operations. Defined Boolean connectives follow by their C identities.

**Equality.** C5 makes every identity judgment x=_σy equal to Top or Bottom: NI handles x=y, and ND handles x≠y. Therefore T fixes every such judgment. Equation (4) gives

$$
T^*_\sigma x=T^*_\sigma y\ \leftrightarrow\ x=y.
$$
Both identity judgments are endpoints, so this truth equivalence is their actual identity. Consequently

$$
T\bigl(T^*_\sigma x=T^*_\sigma y\bigr)=(x=y).
$$
Successive Functionality instances show that the lifted equality constant is precisely =_σ. At e this uses only the identity substitution; it does not introduce an individual-function type.

**Quantifiers.** Suppose σ∈Δ_P. Conjugating ∀_σ and applying it to G gives

$$
\begin{aligned}
T^*_{(\sigma t)t}(\forall_\sigma)(G)
 &=T\left(\forall y^\sigma\,T(G(T^*_\sigma y))\right)\\
 &=\forall y^\sigma\,T(T(G(T^*_\sigma y)))\\
 &=\forall y^\sigma\,G(T^*_\sigma y)\\
 &=\forall y^\sigma\,Gy.
\end{aligned}
\tag{6}
$$
The second line is the given full quantifier identity; the third uses T²=I. The last line is an identity, as justified below, and Functionality then fixes the entire quantifier operation. Existential quantifiers work identically, or follow by Boolean duality.

To justify the final identity in (6) without promoting a conditional truth equivalence through C's Logical Equivalence rule, let J:=T^*_σ when σ is relational. Functionality collects (4) into the whole-operation identity J∘J=I; NI makes that identity necessary. Prove the ordinary reindexing equivalence under this whole involution identity, discharge it in the universally closed C proof, then necessitate that closed implication and instantiate its parameters using CBF. The necessary whole involution identity supplies necessary coextension of the two quantified propositions. C's Intensionality gives their identity. This uses the necessity of one operation identity, not an unsupported collection of separately necessary pointwise equations. For σ=e, reindexing is just the unchanged bound variable. No optional observer premise is necessitated.

**Term induction.** For any pure term A of type τ whose logical quantifier types are in Δ_P, and any list of its free variables x_i:σ_i,

$$
T^*_\tau(A)=A[T^*_{\sigma_i}x_i/x_i].
\tag{7}
$$
The variable case is immediate, and the logical-constant cases were just proved. The application case uses (5). For an abstraction λy.A, conjugation first substitutes T^*_σz for y; the induction hypothesis transforms that occurrence once more. Equation (4) cancels the two substitutions, giving the desired body. Functionality passes its identity under the abstraction. Free individual variables are unchanged throughout. For the closed proposition P, (7) reduces to

$$
TP=P.
\tag{8}
$$
The proof of (8) uses only the finitely many types and subterms in P. It does not require T to satisfy an object-language qualification at every type simultaneously.

## 4. Separation gives No Pure Contingency

Assume P is true. For every observer T satisfying (2), equation (8) makes TP true; Boolean qualification makes TTop true. Hence every such observer agrees materially on P and Top. The propositional involutive-separation instance for Δ_P gives

$$
P=\top,
$$
which is □P in C. Since P was an arbitrary closed pure sentence, No Pure Contingency follows. Full typed Rev was used to recover C5 and the involutive schema; after that recovery, only the one propositional involutive-separation instance chosen for P is needed.

The same argument at ¬P yields the equivalent schema ◇P→P. This does not imply the Fregean Axiom: it applies to closed pure sentences, not arbitrary proposition parameters. In particular the [finite-support permutation model](../../source/topics/classicism/models/finite-support-permutations.yaml) satisfies Rev and is atomless, so neither atom existence nor Atomicity is a conclusion here.

Together with [Necessary logical separation and one atom](necessary-separation-and-atoms.md), the result explains the boundary of the converse. A countermodel to C5+□OS⇒Rev must be atomless, and a contingent closed pure sentence suffices to prove failure of Rev. The [finite-block symmetry model](finite-block-symmetry-reversible-gap.md) supplies both features. No Pure Contingency is not sufficient as an additional hypothesis: the separate component-shift model satisfies even C5+□SplitMono+No Pure Contingency while Rev fails.

## 5. Sources and mathematical status

The new implication from Rev to No Pure Contingency is by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–4, unpaginated.

The typewise conjugation proof is the reusable middle of [C5 and Atomicity imply No Pure Contingency](../../source/topics/classicism/writeups/c5-and-atomicity-imply-no-pure-contingency.md), §§4–5. Its [record](../../source/topics/classicism/results/c5-and-atomicity-imply-no-pure-contingency.yaml) attributes the underlying theorem to Goodsell and Yli-Vakkuri and the proof sketch to Cian Dorr, 23 September 2026, with permission from Zachary Goodsell, written out by Claude Fable 5.1. The present argument replaces that proof's atom-based construction and separating step by the established reversible-observer principle. The metalevel treatment of the individual identity component is explicit here to preserve the relational type restriction.

The needed Rev-to-C5, involutive equivalence and necessary-OS consequences are in [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md), §§4, 6 and 8. The schema being concluded is [No Pure Contingency](../../source/topics/classicism/principles/no-pure-contingency-r.yaml), as formulated in Bacon and Dorr, *Classicism*, draft of 16 May 2023, §2.2, p. 27. The Functionality bridge is [Barcan implies Functionality](../../source/topics/classicism/results/barcan-r-implies-functionality-r.yaml).

# Finite colour patterns: atomless propositions with no admitted proper injection

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the finite-pin argument and the two-colour model verdicts: `misc`, this note, §§1–5, unpaginated. The underlying model construction and previously proved observer theorems are attributed in §6. This is an ordinary model argument, not a database record or formal certificate.

There is a model of C5 and full reversible logical separation in which propositions are atomless, yet every admitted injective proposition operation is onto. Thus the internal Frege-finiteness premise in the finite observer-collapse theorem cannot be replaced by this condition on admitted injections. The model also gives a useful semantic boundary: when every fixed finite pin allows only finitely many propositions, qualified left inverses are automatically two-sided inverses.

## 1. The exact internal condition

Write

$$
\mathsf D_t:=\forall E^{tt}\left[
 \bigl(\forall p,q\,[Ep=Eq\to p=q]\bigr)
 \to\forall q\,\exists p\,[Ep=q]\right].
\tag{1}
$$
Every operation and proposition in (1) is admitted. This is an internal assertion about injective operations of type tt; it is not an assertion about all external functions on the proposition domain. Nor is it being identified here with a stronger formulation quantifying over arbitrary serial injective relations without an admitted function representing them.

The internal Frege statement Fin_t(All) implies (1), by the finite Dedekind argument recalled in [the fork note](fork-one-sided-inverse-separation.md), §5. The converse fails in the model below. Its failure will be proved using the established finite observer-collapse theorem, not inferred merely from an externally infinite domain.

Under H+$\mathsf D_t$+Fun_{t,t}, any admitted whole left inverse is also a whole right inverse. Indeed, F∘E=I gives injectivity of E. For any q, (1) gives p with Ep=q, and hence

$$
E(Fq)=E(F(Ep))=Ep=q.
\tag{2}
$$
Current Functionality collects these output identities into E∘F=I. If E and F are Good_Δ for the same finite qualification list, they remain so: no witness is replaced. Therefore SplitMono_Δ and Rev_Δ have exactly the same eligible observers under these premises, at every fixed finite Δ. Their corresponding separation sentences coincide at every relational output type. This conclusion alone does not give endpoint separation.

## 2. Finite fixed-pin algebras imply the internal condition

Use the symmetric ideally-full action framework with finite pinning, as specified in [the local-conjugacy note](local-conjugacy-and-reversible-observers.md), §1. At a source object X, a proposition p is a set of arrows out of X. A finite S⊆X pins p when arrows with the same target and the same restriction to S agree on membership in p. Put

$$
B_S:=\{p\in D_t(X):S\text{ pins }p\}.
\tag{3}
$$
This is an external collection used in the semantic proof; it need not itself be the extension of an admitted predicate. Boolean set operations make it a Boolean algebra. Suppose every B_S is externally finite.

**Support-union lemma.** If a finite P pins an admitted E:tt, and S pins p, then P∪S pins E(p).

For an arrow h:X→Y, application has the truth clause

$$
h\in E(p)\quad\Longleftrightarrow\quad
E\bigl(h,\rho_t(h)p\bigr).
\tag{4}
$$
Suppose h,h′ have target Y and agree on P∪S. The transported inputs in (4) are equal as entire proposition objects at Y. To see this, test them at an arbitrary further coordinate l:Y→Z:

$$
l\in\rho_t(h)p\ \Longleftrightarrow\ lh\in p,
\qquad
l\in\rho_t(h')p\ \Longleftrightarrow\ lh'\in p.
$$
The arrows lh and lh′ agree on S, so these truth values agree for every l. Thus $\rho_t(h)p=\rho_t(h')p$. E's P-pinning now makes the two sides of (4) agree. This proves the lemma at arbitrary output coordinates, not merely at the identity arrow.

Consequently, if P⊆S, the current operation E sends B_S into B_S. Suppose E is injective on the whole current proposition domain. Its restriction to the finite set B_S is an injective self-map, hence onto B_S. Given any admitted q, choose a finite S containing both a pin for q and P. Then q∈B_S, so q=E(p) for some p∈B_S. This proves (1).

The only finiteness used is the external finiteness of each fixed-pin algebra. No finite enumeration of the entire proposition domain, admitted predicate for B_S, or simultaneous choice of preimages is required. If current Fun_{t,t} also holds, §1 gives the coincidence of same-list left-inverse and reversible qualifications.

## 3. One object with two infinite colour classes

Take one countably infinite object X partitioned into two disjoint infinite sets A and B. The partition is part of the external model specification; no nonlogical colour predicates are required in the language.

- Arrows are all bijections X→X.
- The designated symmetry group is $G=\mathrm{Sym}(A)\times\mathrm{Sym}(B)$: each symmetry preserves each colour class setwise.
- At every relational type, the domain consists of exactly the symmetric intensions pinned by some finite subset of X. Individuals are X, with the arrow action on X.
- Evaluation is at the identity arrow. If a signature expansion is desired, every nonlogical relational constant may be interpreted as its type's top element.

This is the symmetric ideally-full construction cited in §6, so it is a model of C. All arrows have inverses. Their induced actions at every admitted type are therefore bijective, and C5, all Barcan instances and Functionality hold throughout the model. The arrows and the colour permutation group are semantic data; no forbidden individual-output function type is introduced.

For a finite S⊆X and arrow h, its colour pattern on S records, for each s∈S, whether h(s) lies in A or B. There are exactly $2^{|S|}$ patterns, and each occurs: prescribe distinct images of S in the requested infinite classes, then extend the finite partial injection to a bijection of X.

If two arrows h,h′ have the same colour pattern on S, there is g∈G with (gh)|S=h′|S. Extend the finite partial bijections h(s)↦h′(s) separately within A and B. Symmetry and S-pinning therefore make every p∈B_S give h and h′ the same membership value. Conversely, any set of colour patterns defines a symmetric S-pinned proposition, hence an admitted proposition. Thus

$$
|B_S|=2^{\,2^{|S|}}.
\tag{5}
$$
Every fixed-pin algebra is finite. Section 2 proves that the internal sentence $\mathsf D_t$ holds, although the union of these algebras need not be finite.

## 4. Atomlessness and reversible separation

Let p be any nonbottom proposition, choose a finite pin S for p, and choose h∈p. Take x∈X outside S. The proposition

$$
q_x:=\{k:X\to X\text{ an arrow}:k(x)\in A\}
\tag{6}
$$
is symmetric under G and pinned by {x}, so it is admitted. There are arrows h_A,h_B agreeing with h on S and sending x respectively into A and B: choose the new image outside the finite set h(S), and extend the resulting finite partial injection to a bijection. Both arrows belong to p by S-pinning. Hence p∧q_x and p∧¬q_x are both nonbottom. Since the Boolean operations are the corresponding set operations, this splits p into two proper nonzero parts.

Thus every nonbottom proposition splits; the proposition algebra is atomless. In particular Atomicity_t fails, since Top is nonbottom and has no atom below it.

Full reversible logical separation holds by the one-object theorem of [Local symmetry conjugacy supplies reversible logical observers](local-conjugacy-and-reversible-observers.md), §§5–6. Its hypotheses match this model exactly: one countably infinite object, all bijections as arrows, arbitrary designated symmetry group and finite pinning at every relational type. The theorem supplies admitted involutive observers satisfying the full composite Boolean and quantifier identities for every requested finite list, and Functionality supplies every relational output type. It does not use atoms. Therefore this is the full Rev schema, not just Boolean or propositional separation.

The same framework also gives the separately boxed Rev schema. For the present boundary result, the current full schema suffices. By §1, qualified SplitMono and Rev coincide here, although the domain is atomless.

## 5. Why Frege finiteness cannot be weakened this far

Endpoint separation entails Atomicity_t; indeed over H its full schema is equivalent to C5+Atomicity_t, by [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md), §3. Atomlessness therefore gives failure of endpoint separation in this model.

If Fin_t(All) held, the [internal finite boundary](fork-one-sided-inverse-separation.md), §5, would turn the already established full Rev into endpoint separation. Its proof uses the internally finite image of the identity observer and the one-finite-image-witness theorem. That contradicts atomlessness. Hence Fin_t(All) is false.

The verified profile is therefore

$$
\boxed{\mathrm{C5}+\mathrm{Rev}+\mathsf D_t
 +\text{atomless propositions}
 +\neg\mathrm{EndSep}
 +\neg\mathrm{Fin}_t(\mathrm{All}).}
\tag{7}
$$
This establishes that Rev together with (1) need not imply EndSep, even though (1) still makes every qualified left inverse two-sided. The two consequences of internal Frege finiteness must be kept distinct: its injection-to-surjection consequence suffices for the inverse conversion, whereas the finite-image witness used for endpoint separation is not supplied by (1).

This two-colour example satisfies Rev and therefore SplitMono. The former C5+□OS⇒SplitMono question is settled negatively by [Linear and circular fibre orders](linear-circular-fibre-left-inverse-gap.md): its two-object model has finite fixed-pin algebras and hence (1), but satisfies C5+□OS while failing Rev. Section 1 then also excludes SplitMono. That model uses the finite-pin boundary proved here; its separate pure-sentence obstruction supplies the failure of Rev.

## 6. Sources

The support-union lemma, finite fixed-pin argument, two-colour construction and verdicts (1)–(7) are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–5, unpaginated.

The semantic framework is Cian Dorr, *Boolean Completeness does not imply Rigid Comprehension*, draft of 30 July 2026, Definitions 15–18, p. 8; §3.1, p. 9; Lemma 21, p. 10, as recorded in [Symmetric ideally-full models](../../source/topics/classicism/groups/symmetric-ideally-full.yaml). Its underlying action construction is Bacon and Dorr, *Classicism*, draft of 16 May 2023, Appendix D, pp. 73–79. These sources supply the framework, not the new finite-pin and observer verdicts.

The all-type reversible witnesses are the one-object consequence of [Local symmetry conjugacy](local-conjugacy-and-reversible-observers.md), §§5–6, direct source `misc`. The Frege-finiteness comparison uses [the fork note](fork-one-sided-inverse-separation.md), §5, including its explicitly sourced internal Dedekind lemma, and the endpoint characterization uses [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md), §§3 and 5–6, direct source `misc`.

# Finite-pinning models with qualified left-inverse separation

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new observer constructions and separation verdicts: `misc`, this note, §§1–7, unpaginated. The original model constructions and the already established verdicts used here are cited in §8.

In the [finite-block symmetry model](finite-block-symmetry-reversible-gap.md), every proposition distinction can be detected by an admitted logical observer with an admitted qualified **left inverse**. This holds throughout the model, although reversible logical separation fails. Thus the inverse orientation makes a substantive difference:

```math
\boxed{\mathrm{Rev}\ \Longrightarrow\ \mathrm{SplitMono}
\ \Longrightarrow\ \mathrm{OS},
\qquad \mathrm{SplitMono}\ \not\Longrightarrow\ \mathrm{Rev}.}
\tag{1}
```

The first implication is strict even in a model satisfying C5 and separately necessary SplitMono separation. A second finite-pinning model shows that SplitMono itself entails neither C5 nor necessary OS, BF or Functionality. The later [fork separation theorem](fork-one-sided-inverse-separation.md) proves that the second implication in (1) is also strict, using a different model. Qualified **right-inverse** separation, in contrast, is equivalent to Rev by [the one-sided inverse patching theorem](split-inverse-logical-observers.md).

## 1. Qualifications and the unchanged model

For a finite external type list Δ, write

```math
\mathrm{SplitMono}_\Delta(E):=
\mathrm{Good}_\Delta(E)\land
\exists F^{tt}\,[\mathrm{Good}_\Delta(F)\land F\circ E=I].
\tag{2}
```

Good_Δ requires the full Boolean and quantifier composite identities, together with the translated equality clauses. The equation F∘E=I is a whole-operation identity, not merely an equation between current truth functions. Both maps are admitted and qualified for the same list. The separation schema has the full relational output scope and ranges over all finite Δ.

Use exactly the model of [Finite-block symmetry: even sizes versus powers of two](finite-block-symmetry-reversible-gap.md), §§1–3:

- W has countably many blocks of each positive even size.
- V has countably many blocks of each size 2,4,8,16,….
- The designated group at each object is the product of the full symmetric groups of its individual blocks. Each block is preserved setwise; distinct blocks are not permuted by the designated group.
- Every bijection between every ordered pair of objects is an arrow. At each relational type the admitted objects are exactly the symmetric intensions pinned by a finite source set.

All arrow actions on admitted types are bijective. The existing proofs establish C5, all Barcan instances and Functionality at both objects, atomlessness at both objects, and a contingent closed pure sentence MC₆ which refutes Rev. We change neither the model nor its domains. We construct additional observers already present in those domains.

Throughout this note products of arrows are composed right to left. For a finite S⊆X, let K_(S) denote the pointwise stabilizer of S in the designated source group K. All arrows between individual sets are external semantic bijections, not terms of an object-language type e→e.

## 2. A one-way comparison and infinitely many disjoint charts

Work first at a source object X with designated group K. Let Y be any target object, with designated group L, and suppose b:X→Y and finite S⊆X satisfy

```math
bK_{(S)}b^{-1}\subseteq L.
\tag{3}
```

For this construction it suffices that K is the product of the within-block symmetric groups of a partition having infinitely many 2-blocks. Both source objects of our model have this property.

Choose distinct 2-blocks B₀,B₁,B₂,…, all disjoint from S, and a point x∈B₀. Put S':=S∪{x}. For n≥1 choose a permutation ν_n that exchanges B₀ and B_n by a bijection and its inverse and fixes every other point. Put ν₀:=id_X. Each ν_n normalizes K: it permutes two blocks of the same size, conjugating their full symmetric factors and leaving the remaining factors unchanged. The ν_n need not themselves belong to K.

Define sets of arrows out of X by

```math
C_n:=\{h:X\to X:\exists g\in K,
\ h|_{S'}=(\nu_n g)|_{S'}\}.
\tag{4}
```

The charts are pairwise disjoint. Indeed h∈C_n implies h(x)∈B_n, and the blocks B_n are disjoint. The identity belongs to C₀. Each C_n is invariant under the target group K: for μ∈K,

```math
\mu\nu_n g=\nu_n(\nu_n^{-1}\mu\nu_n)g,
```

and the parenthesized permutation belongs to K. Their definitions, and membership in their union, depend only on the target of h and h|S'. In particular the countably many charts share the **one finite pin S'**. Infinitely many possible values of the pinned individual x do not require an infinite pin.

Put

```math
\alpha_n:=\nu_{n+1}\nu_n^{-1}.
\tag{5}
```

Then α_n normalizes K and sends C_n bijectively to C_{n+1} by left composition. In fact if h agrees with ν_n g on S', then α_n h agrees with ν_{n+1}g there; the inverse calculation gives the converse. Thus

```math
\alpha_n C_n=C_{n+1}.
\tag{6}
```

## 3. The observer and its qualified left inverse

A tt intension at X has a truth profile E(h,q), where h:X→Z and q is a proposition at Z. Define two profiles by

```math
E(h,q)\quad\Longleftrightarrow\quad
\begin{cases}
bg^{-1}\in q,&h\in C_0,\ h|_{S'}=g|_{S'},\ g\in K,\\
\alpha_n^{-1}\in q,&h\in C_{n+1}\quad(n\ge0),\\
\mathrm{id}_Z\in q,&h:X\to Z\text{ outside }\bigcup_{n\ge0}C_n,
\end{cases}
\tag{7}
```

```math
F(h,q)\quad\Longleftrightarrow\quad
\begin{cases}
\alpha_n\in q,&h\in C_n\quad(n\ge0),\\
\mathrm{id}_Z\in q,&h:X\to Z\text{ outside }\bigcup_{n\ge0}C_n.
\end{cases}
\tag{8}
```

Every observation arrow in these formulas has q's source as its domain. In particular the first branch of E reads q along an arrow X→Y, while its source h has target X. The other nondefault branches use arrows X→X. At the actual evaluation id_X, choose g=id_X in (7); hence

```math
E(\mathrm{id}_X,p)\quad\Longleftrightarrow\quad b\in p.
\tag{9}
```

We verify that these are admitted tt objects.

**Independence of the first branch's representative.** Suppose g and g' both agree with h on S', and write g'=gu. Then u∈K_(S')⊆K_(S). By (3), bu^{-1}b^{-1}∈L, and

```math
b(g')^{-1}=(bu^{-1}b^{-1})(bg^{-1}).
```

The two tested arrows therefore agree on membership in q by its target symmetry at Y. No representative is chosen as an additional object-language function. The remaining branches have no representative ambiguity.

**Finite pinning.** The branch and the available first-branch representatives depend only on the target of h and h|S'. Thus S' pins both profiles. The countable definition does not demand an infinitary object-language formula: symmetric ideal fullness admits every profile satisfying the stated symmetry and finite-pinning conditions.

**Target symmetry.** For μ in the designated group at Z, the required equation is

```math
E(\mu h,\rho_t(\mu)q)=E(h,q),
\tag{10}
```

and similarly for F. Proposition transport obeys

```math
a\in\rho_t(\mu)q\quad\Longleftrightarrow\quad a\mu\in q.
\tag{11}
```

On C₀, μ belongs to K and a representative g becomes μg. The new test is bg^{-1}μ^{-1}∈ρ_t(μ)q, equivalent by (11) to bg^{-1}∈q. On a constant-arrow branch, let a be the relevant α_n or α_n^{-1}. The chart is K-invariant, and a normalizes K. The transformed test is aμ∈q. Since aμ=(aμa^{-1})a and aμa^{-1}∈K, target symmetry of q makes this equivalent to a∈q. Outside the charts, target symmetry preserves the default branch, and μ∈q iff id_Z∈q. This proves (10) in every case. Symmetric ideal fullness now supplies the admitted E and F.

## 4. The whole inverse identity at arbitrary future inputs

Call the observation arrows in (7) and (8) a^E_h and a^F_h. The first is defined up to changes that preserve every symmetric proposition's value, as proved above. For an arbitrary future arrow r:X→Z, an arbitrary proposition q at Z, and an output arrow l:Z→U, the application and transport clauses give

```math
l\in(\rho_{tt}(r)E)(q)
\quad\Longleftrightarrow\quad a^E_{lr}l\in q,
\tag{12}
```

and the same formula for F. In particular, applying F outside E tests q at

```math
a^E_{\,a^F_{lr}lr}\,a^F_{lr}\,l.
\tag{13}
```

Put h:=lr. If h∈C_n, then a^F_h=α_n and α_nh∈C_{n+1} by (6). The E branch there has observation arrow α_n^{-1}. Consequently (13) is α_n^{-1}α_nl=l. If h lies outside every C_n, F uses the identity, its transformed coordinate is still h, and E also uses the identity. Again (13) is l.

Thus for every r, every q in its future domain and every l,

```math
(\rho_{tt}(r)F)((\rho_{tt}(r)E)q)=q.
```

The complete future profiles are identical, proving

```math
F\circ E=I
\tag{14}
```

as a whole-operation identity. This is not merely a verification on propositions transported from X. The formula covers arbitrary q at every future object.

The cross-object C₀ branch of E never enters this calculation: F sends each C_n into C_{n+1}, while outside their union it leaves the coordinate unchanged. That is precisely why E may use C₀ to inspect b without losing the left-inverse identity. No reverse equation E∘F=I has been proved or used.

## 5. Full logical qualification and separation

Both E and F satisfy Good_Δ for every specified finite Δ. To verify this, use (12) at every future r and output coordinate l. Each observer evaluates its input at one bijective arrow. Evaluation preserves the Boolean set operations and both endpoints, giving the full Boolean composite identities on arbitrary future input tuples.

For a universal quantifier over any admitted type σ, let a:U→U' be the observation arrow at lr. Evaluating the transported universal at a quantifies over the entire σ-domain at U'. Universally evaluating the transported predicate through the observer quantifies over the image of the σ-domain at U under ρ_σ(a). Those ranges are equal because ρ_σ(a) is onto, with inverse ρ_σ(a^{-1}). The existential calculation is identical with “some” in place of “every.” These calculations hold for every future predicate, so they verify the full composite quantifier identities, not just current material commutation. Every equality proposition is an endpoint because all arrow actions are injective; endpoint fixing gives the translated equality clauses as well.

The same E,F therefore satisfy (2) for every fixed finite Δ. This is a metatheoretic statement about the witnesses; it does not insert an infinite qualification conjunction into the object language.

We now supply (3) for any desired distinction in the two-object model. Let d be a nonbottom proposition at X. If d is currently true, the identity observer and its own left inverse accept it. Otherwise choose h:X→Y in d and a finite pin P for d. The existing packing construction gives a comparison bijection j:X→Y with jKj^{-1}⊆L; use j=id_X for Y=X. Extend the finite partial bijection (j^{-1}h)|P to a finite-support permutation π of X and put b:=jπ. Choose finite S containing P and the support of π. Then b agrees with h on P, so b∈d. A permutation in K_(S) commutes with π, and hence

```math
bK_{(S)}b^{-1}=jK_{(S)}j^{-1}\subseteq L.
```

Apply §§2–4. Formula (9) makes Ed true, and (14) supplies its admitted qualified left inverse. For distinct propositions p,q, apply this to their nonbottom Boolean symmetric difference d. The Boolean identities turn truth of Ed into different truth values for Ep and Eq. Thus SplitMono separation holds at output type t for every finite qualification list.

Functionality, valid throughout this model, lifts the result to every relational output type: two unequal relations have a tuple at which their proposition values are unequal, and the preceding separator distinguishes those values. The converse direction of separation is equality substitution. The construction works at either source object. It therefore proves the full SplitMono schema at both objects and its separately boxed instances:

```math
\mathrm{C5}+\Box\mathrm{SplitMono}.
\tag{15}
```

The box in (15) is read instance by instance, not as an object-language box around an infinite schema.

## 6. Strictness and exact limitations

The underlying model is unchanged. Its previously proved atomlessness and failure of Rev remain valid. Consequently it satisfies, at both objects,

```math
\boxed{\mathrm{C5}+\Box\mathrm{SplitMono}
+\text{atomlessness}+\neg\mathrm{Rev}.}
\tag{16}
```

The implication Rev⇒SplitMono follows by taking the admitted qualified two-sided inverse as a left inverse. Equation (16) proves that implication strict. Forgetting a left inverse gives SplitMono⇒OS. Strictness of this second implication, and failure of necessary OS to supply left-inverse separation, are proved separately by [the fork](fork-one-sided-inverse-separation.md). Section 7 refutes the implications from SplitMono to C5 and necessary OS.

There is also a fixed-list distinction. The existing countermodel proof explicitly refutes propositional reversible separation for

```math
\Delta_0=\{t,e,et,(et)t,(et)(et)\},
```

using the pure sentence MC₆ at V and its negation at W. The new construction supplies SplitMono separation for this very list. Since Δ₀ contains t, the fixed-list right-inverse patching theorem over C+BF identifies SplitEpi separation with reversible separation there. Thus left-inverse and right-inverse separation already differ at this one finite propositional instance, not merely after taking their full schemas.

The model still distinguishes the closed pure sentence across its two objects. Hence left-inverse separation, even together with C5 and its own separately necessary schema, does not imply No Pure Contingency. The left inverse preserves the original information while the observer's actual truth profile inspects another evaluation; a reversible observer cannot make this particular move in the model.

## 7. The all-maps model: SplitMono without necessary Barcan

The same one-sided shift works in a second, unchanged recorded model: [Finite-support action model: N and singleton, all maps](../../source/topics/classicism/models/finite-support-two-object-all-maps.yaml), evaluated at ℕ. Its objects are ℕ and {0}, its arrows are all functions between them, and its domains are ideally full for the ideals of finite source sets. There is no additional target-symmetry restriction. It is a model of C. Its exact definitions and existing verdicts are reviewed in [Logical separation with contingent Barcan](logical-separation-with-contingent-barcan.md), §§1, 3–5.

We prove the new verdict directly from its finite-pinning condition. We do not identify this all-maps model with the groupoid model of §§1–6, and we do not assume that its arbitrary arrow actions are injective or onto.

### A distinguishing split epimorphism

Let d be a nonbottom proposition at ℕ, choose an outgoing arrow h in d and a finite pin P for d. If h:ℕ→ℕ, extend h|P to a surjection b:ℕ→ℕ: leave its finitely many prescribed values unchanged and enumerate all natural-number outputs on the remaining infinite input set. If h ends at {0}, take b to be the unique arrow ℕ→{0}. In either case b∈d and b has a section s in the all-maps category. Functoriality gives

```math
b_\sigma s_\sigma=I_{D_\sigma(\mathrm{cod}b)}
\tag{17}
```

for every admitted type σ. Thus b_σ is onto at every type. This is the already established split-epimorphism observation in the contingent-Barcan note; no stronger claim about arbitrary transports is needed.

Fix a finite S containing P. Choose pairwise distinct points x₀,x₁,x₂,… outside S. Set S':=S∪{x₀}, let ν₀=id, and let ν_n exchange x₀ and x_n for n≥1, fixing all other points. Put α_n:=ν_{n+1}ν_n^{-1}. Define

```math
C_n:=\{h:\mathbb N\to\mathbb N:
h|_{S'}=\nu_n|_{S'}\}.
\tag{18}
```

These are disjoint because h(x₀)=x_n on C_n. They are all S'-pinned, id∈C₀, and α_n C_n=C_{n+1}. This last equality holds for arbitrary functions h, not only for bijections: left composition by the permutation α_n changes the specified finite values exactly as required, and its inverse gives the reverse inclusion.

### Admitted observers and the full inverse equation

For an arrow h:ℕ→Z and q∈D_t(Z), set

```math
E(h,q)\quad\Longleftrightarrow\quad
\begin{cases}
b\in q,&h\in C_0,\\
\alpha_n^{-1}\in q,&h\in C_{n+1},\\
\mathrm{id}_Z\in q,&h\notin\bigcup_n C_n,
\end{cases}
\qquad
F(h,q)\quad\Longleftrightarrow\quad
\begin{cases}
\alpha_n\in q,&h\in C_n,\\
\mathrm{id}_Z\in q,&h\notin\bigcup_n C_n.
\end{cases}
\tag{19}
```

Each branch is determined by the target of h and its values on S'. Both profiles are therefore pinned by S', and ideal fullness admits both tt objects. There is no representative choice or target-symmetry condition here. At id, E has the truth profile of evaluation at b.

The future application formula (12) remains valid in the all-maps action model. Take arbitrary future functions r:ℕ→Z and l:Z→U and an arbitrary proposition q at Z. Put h:=lr. If h∈C_n, F's observation arrow is α_n, its new coordinate α_nh belongs to C_{n+1}, and E's observation arrow there is α_n^{-1}. The composite test in (13) is exactly α_n^{-1}α_nl=l. Outside all charts, both tests are identities. This proves F∘E=I as a whole-operation identity.

In particular neither r nor l was required to be injective. The special b branch may be noninvertible, but the calculation of F∘E never visits it. Only the chart-shifting α_n and α_n^{-1} are canceled.

### Full qualification from onto transports

Every observation arrow in (19) is either b, a permutation, or an identity. Its action is therefore onto at every admitted type: use (17) for b and inverse arrows for the remaining cases.

At each future coordinate, observing a Boolean combination evaluates it at one arrow, so both E and F satisfy the full Boolean composite identities. The full universal/existential calculations in §5 need **surjectivity**, not injectivity, of the observation arrow's type action. They therefore apply to (19) at every type and every future predicate, proving all requested full Q/P identities. The same E,F qualify for each finite list Δ.

The equality-clause justification is different from §5. Equality propositions need not be endpoints in this model, and b may identify individuals. We use instead the established C theorem that Boolean-preserving observers satisfy the translated equality clauses of Good_Δ, as specified in the contingent-Barcan note, §1, and the complete-qualification definition. We do not assert that E fixes equality propositions or reflects identity of inputs. Thus E,F satisfy exactly Good_Δ, and their whole inverse equation gives SplitMono_Δ(E).

For distinct p,q, apply the construction to their nonbottom Boolean symmetric difference. E accepts this difference because b belongs to it, so E distinguishes p,q. Alternatively identity suffices when they already have different current truth values. This proves propositional SplitMono separation for every finite Δ. The recorded BF at ℕ gives Functionality there, which lifts these instances to every relational output type. Hence **full typed SplitMono separation holds at ℕ**.

### The failures at the same evaluation point

The accessible singleton still refutes BF_e, BF_t and Functionality at e,t. The explicit witnesses and their sources are unchanged; see the contingent-Barcan note, §5, and the linked model record. We have therefore sharpened its observer verdict to

```math
\boxed{\mathrm C+\mathrm{SplitMono}+\mathrm{BF}
+\neg\Box\mathrm{BF}_e+\neg\Box\mathrm{BF}_t
+\neg\Box\mathrm{Fun}_{e,t}.}
\tag{20}
```

Full OS implies BF, so necessary full OS would imply necessary BF and is false here. C5 implies necessary BF and is false here as well. Since SplitMono implies OS, its separately necessary schema also fails. Thus SplitMono entails none of C5, necessary OS, necessary SplitMono, necessary BF or necessary Functionality. The separate fork theorem refutes the reverse implication from ordinary or necessary OS to SplitMono. No atomlessness verdict is transferred from the different model of §§1–6.

## 8. Sources

The countable chart constructions, their single finite pins, the whole left-inverse calculations and the new SplitMono separation verdicts are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§2–7, unpaginated.

The exact model, mutual comparison inclusions, atomlessness, contingent MC₆ sentence and failed finite-list Rev instance are [Finite-block symmetry: even sizes versus powers of two](finite-block-symmetry-reversible-gap.md), §§1–8, direct source `misc`, unpaginated. The future-profile formula and full qualification calculation follow the semantic setup in [Local symmetry conjugacy supplies reversible logical observers](local-conjugacy-and-reversible-observers.md), §§1–4, direct source `misc`, unpaginated. The present construction replaces the two-chart swap with a one-sided shift and does not assume local stabilizer conjugacy.

The originating symmetric ideally-full construction is Cian Dorr, *Boolean Completeness does not imply Rigid Comprehension*, draft of 30 July 2026, Definitions 15–18, p. 8; §3.1, p. 9; Lemma 21, p. 10, as recorded in [Symmetric ideally-full models](../../source/topics/classicism/groups/symmetric-ideally-full.yaml). The underlying ideally-full action construction is Bacon and Dorr, *Classicism*, draft of 16 May 2023, Appendix D, pp. 73–79. These sources supply the semantic framework; the new observer verdict above is not attributed to them.

The all-maps model in §7 and its BF/necessary-BF separation originate in Bacon and Dorr, *Classicism*, draft of 16 May 2023, Appendix D, p. 79, paragraph beginning “One particularly interesting result”; its C soundness is the ideally-full construction of Proposition D.4. The necessary-BF_t witness is separately attributed in the [model record](../../source/topics/classicism/models/finite-support-two-object-all-maps.yaml). The model's previous OS verdict and explicit necessary-Functionality witness are [Logical separation with contingent Barcan](logical-separation-with-contingent-barcan.md), §§2–5, direct source `misc`, unpaginated. Section 7 establishes the stronger new observer qualification; it does not reattribute the existing model or its earlier failures.

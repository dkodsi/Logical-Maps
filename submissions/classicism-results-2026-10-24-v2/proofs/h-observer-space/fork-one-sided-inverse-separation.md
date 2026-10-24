# Full three-object fork: logical separation without left-inverse separation

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the observer verdicts: `misc`, this note, §§1–5, unpaginated. The already specified fork and the source of its full action construction are cited in §6. No database record, central map or Lean status is changed.

The full three-object fork satisfies necessary ordinary logical separation but fails separation by qualified left-invertible observers. Together with the previously proved left-inverse models, this settles both strict arrows:

$$
\boxed{\mathrm{Rev}\ \Longrightarrow\ \mathrm{SplitMono}
\ \Longrightarrow\ \mathrm{OS},
\qquad\text{both implications strict}.}
\tag{1}
$$
It also separates necessary ordinary separation from qualified left-inverse separation. The converse separation already has a different model, so those two principles are incomparable.

All qualifications below use full composite operation identities. The failure occurs already at propositional output type and one finite qualification list. The positive ordinary-separation result has every finite qualification list and the full relational output scope.

## 1. The unchanged full fork

Use exactly [Full three-object fork: all Barcan instances without binary families](fork-without-binary-families.md), §§1–2. Its category has objects r,l,h, identity arrows and just two nonidentity arrows

$$
\alpha:r\to l,\qquad\beta:r\to h.
$$
Each object has a singleton individual domain. Use the full action construction in the fixed relational language, with no function types ending in e. The current proposition domains are

$$
D_t(r)=\{0,1\}^3,
\qquad D_t(l)=D_t(h)=\{0,1\}.
\tag{2}
$$
Write a root proposition as p=(p_0,p_l,p_h). Its current truth is p₀, and its transports along α and β are p_l and p_h. Boolean operations act coordinatewise. Root function objects are natural families consisting of a root map and its two compatible leaf maps; every such family belongs to the full domain.

The existing type induction gives joint surjectivity

$$
(\alpha_\sigma,\beta_\sigma):D_\sigma(r)
\longrightarrow D_\sigma(l)\times D_\sigma(h)
\tag{3}
$$
for every admitted type σ. In particular each individual transport is onto. The existing proof consequently gives C, all BF instances and all Functionality instances at every object, including their separately boxed forms at r. These facts are retained without any change to the model.

For a finite external Δ let Good_Δ be the complete logical qualification. Define

$$
\mathrm{SplitMono}_\Delta(E):=
\mathrm{Good}_\Delta(E)\land
\exists F^{tt}\,[\mathrm{Good}_\Delta(F)\land F\circ E=I].
\tag{4}
$$
The inverse equation in (4) is an identity of admitted operations. The negative proof will require only E's full Boolean identities and an admitted left inverse; qualification of that inverse is not needed.

## 2. Three ordinary observers separate every proposition

Define three admitted root observers. The first is identity. The other two have root components

$$
E_l(p_0,p_l,p_h):=(p_l,p_l,p_h),
\qquad
E_h(p_0,p_l,p_h):=(p_h,p_l,p_h),
\tag{5}
$$
and both have the identity map as each leaf component.

These are natural families. For example, α_t(E_l p)=p_l=I(α_t p) and β_t(E_l p)=p_h=I(β_t p); the same equations hold for E_h. Fullness therefore admits the two observers as tt objects.

### Boolean composite identities

Every output coordinate in (5) is one input coordinate. Hence the root maps preserve both endpoints, negation, conjunction and disjunction exactly. Their leaf maps are identities and preserve these operations as well. These calculations verify the complete natural families of the composite operations, so they give full Boolean identities, not merely current truth agreements.

### Quantifier composite identities at every type

Fix any admitted type σ and any predicate F∈D_{σt}(r). Its universal proposition has coordinates

$$
\left(
\bigwedge_{x\in D_\sigma(r)}F_r(x)_0,
\ \bigwedge_{y\in D_\sigma(l)}F_l(y),
\ \bigwedge_{z\in D_\sigma(h)}F_h(z)
\right).
\tag{6}
$$
For E_l, the root truth bit of E_l(∀_σF) is the middle coordinate in (6). The root truth bit of ∀_σ(E_l∘F) is

$$
\bigwedge_{x\in D_\sigma(r)}F_r(x)_l
=\bigwedge_{x\in D_\sigma(r)}F_l(\alpha_\sigma x)
=\bigwedge_{y\in D_\sigma(l)}F_l(y).
\tag{7}
$$
The first equality is the definition of E_l, the second is naturality of F, and the last uses surjectivity of α_σ from (3). The two leaf coordinates also agree because the leaf observer components are identities. At a future leaf, the entire universal-commutation equation is simply the identity equation for the identity observer. Thus the calculation holds on every root input and every future input; it proves the full composite Q_σ identity.

Replacing each meet in (6)–(7) by a join proves the existential identity. Replacing l,α by h,β proves both identities for E_h. Identity itself trivially qualifies. Since σ was arbitrary, these same three observers are Good_Δ for every fixed finite Δ. Over C, Boolean preservation supplies the translated equality clauses in the complete qualification; no claim that the readers fix equality propositions is being made.

### Separation and its necessity

Distinct root proposition objects differ in one of their three coordinates. Identity detects a difference in the root coordinate, E_l detects a difference in the l coordinate, and E_h detects a difference in the h coordinate. Thus for every finite Δ the three admitted Good_Δ observers give propositional separation at r.

Current Functionality lifts this to every relational output type: if two relations are unequal, there is a tuple at which their proposition values are unequal, and one of the three observers distinguishes those values. Equality substitution gives the forward separation implication. No additional observer quantifier type is needed for this argument.

At a leaf the model is an ordinary full extensional type structure, with only two proposition values. Identity is Good_Δ and separates at every relational type. Consequently ordinary full typed separation holds at all three objects. At r we therefore have both OS and its separately boxed schema:

$$
\mathrm C+\Box\mathrm{OS}+\Box\mathrm{BF}
+\Box\mathrm{Fun}.
\tag{8}
$$
Each box in (8) is read instance by instance. No infinite conjunction is placed inside the object language.

## 3. Left inverses and current finite domains

There is a general elementary observation valid in any such typed model. If admitted E,F satisfy the whole equation F∘E=I, then their current application maps e,f on D_t satisfy f(e(p))=p as an equality of proposition objects. Consequently e is injective. If the current D_t is externally finite, e is bijective and f is its inverse as a current set-function.

That finite current calculation alone is not a claim about the two operations' entire future profiles. We do not infer a whole right-inverse identity from current finiteness. The following argument instead computes every possible current Boolean observer in this particular fork that could have a left inverse.

## 4. Every left-invertible Boolean observer fixes the root truth

Let E be an admitted root observer satisfying the full Boolean operation identities, and suppose it has an admitted left inverse. Let e be its current root application map on the eight proposition objects. By §3, e is injective.

Each leaf component of E fixes Top and Bottom. Since its leaf proposition domain has just those two elements, that component is the identity map. Naturality therefore gives

$$
(ep)_l=p_l,
\qquad(ep)_h=p_h
\qquad\text{for every root proposition }p.
\tag{9}
$$
Put

$$
u:=(1,0,0).
$$
Equation (9) makes both leaf bits of e(u) zero. Hence e(u) is either Bottom=(0,0,0) or u. Boolean preservation gives e(Bottom)=Bottom, and injectivity excludes e(u)=Bottom because u≠Bottom. Thus

$$
e(u)=u.
\tag{10}
$$
For every p, meet preservation now gives

$$
u\land e(p)=e(u\land p).
\tag{11}
$$
If p₀=0 then u∧p=Bottom, so (11) makes the root bit of e(p) zero. If p₀=1 then u∧p=u, and (10)–(11) make the root bit of e(p) one. Therefore e preserves the root bit as well as the two leaf bits in (9):

$$
e(p)=p\qquad\text{for every }p\in D_t(r).
\tag{12}
$$
In particular every possible SplitMono observer preserves current truth. The obstruction is the root atom u: any injective Boolean observer must preserve it, and preserving that atom preserves its corresponding truth test.

Now choose d:=(0,1,0). It is distinct from Bottom but currently false. By (12), every SplitMono observer gives d and Bottom the same current truth value. Thus their observed material agreement does not imply their identity. Propositional SplitMono separation fails.

This refutes the instance for Δ={t}, and indeed the same argument applies to every finite Δ, since it used only the Boolean part of Good_Δ. Even allowing an arbitrary admitted left inverse rather than a qualified one would not repair this separation failure. The result does not depend on any unproved necessity of a chart-based observer representation.

## 5. Consequences and limits

At the root the exact new model profile is

$$
\boxed{\mathrm C+\Box\mathrm{OS}+\Box\mathrm{BF}
+\Box\mathrm{Fun}+\neg\mathrm{SplitMono}.}
\tag{13}
$$
Therefore the implication SplitMono⇒OS is strict, even over C with every boxed BF and Functionality instance. In conjunction with the finite-block model from [Finite-pinning models with qualified left-inverse separation](finite-block-symmetry-left-inverse.md), §§1–6, which satisfies SplitMono but not Rev, this establishes both strict arrows in (1). Qualified right-inverse separation remains equivalent to Rev by [the right-inverse patching theorem](split-inverse-logical-observers.md).

The all-maps model in the left-inverse note, §7, satisfies SplitMono but fails necessary OS. Equation (13) supplies the reverse separation. Hence

$$
\mathrm{SplitMono}\not\Longrightarrow\Box\mathrm{OS},
\qquad
\Box\mathrm{OS}\not\Longrightarrow\mathrm{SplitMono}.
\tag{14}
$$
The two non-implications in (14) use two different models. The all-maps model's failures of necessary BF are not transferred to this fork; the fork satisfies every boxed BF instance.

### An internal finite boundary

The finite-domain observation in §3 has an internal strengthening when current Functionality is explicitly available. Let All:=λp.Top and use the database's Frege definition

$$
\mathrm{Fin}_t(\mathrm{All}):=
\exists Z^{(tt)t}\,[\mathrm{FiniteCardinality}_t(Z)\land Z(\mathrm{All})].
$$
This asserts internal finiteness; it does not supply a standard external enumeration. Over H plus this premise, every admitted injective operation E:tt is onto. Here is the exact internal justification. If E were injective but omitted q₀, the admitted relation R(p,q):=(Ep=q) would be serial on All, would never send two distinct inputs to the same output, and would omit q₀. The [recorded Dedekind lemma](../../source/topics/classicism/writeups/pure-possibility-implies-axiom-of-infinity-t.md), Lemma 5, proves by Frege induction that no predicate having a finite cardinality admits such a relation. Apply it to All.

Only that lemma's internal logical argument is used, not the surrounding maximalist or modal premises. Its induction predicate is the admitted λZ.∀U[ZU→U is not Dedekind-infinite]. Zero is immediate. At a successor remove the specified member q: if q has no incoming edge, restrict the relation and retain an omitted point, or use a successor of q when q itself was the omitted point; if q has an incoming edge from p, redirect p to q's successors and then delete q. The resulting admitted relation remains serial and injective on the exact deletion predicate and omits a point, contradicting the induction hypothesis. The displayed proof in Lemma 5 verifies these two cases without Choice, predicate extensionality or an external finite enumeration.

Now suppose F∘E=I. This gives injectivity of E, hence internal surjectivity by the preceding argument. For any q choose p with Ep=q. Equality substitution gives

$$
E(Fq)=E(F(Ep))=Ep=q.
$$
Under the explicit local premise Fun_{t,t}, these pointwise identities identify the whole operations E∘F=I. This is the step absent from a bare current-finiteness argument: here current Functionality, rather than a silent inference about future domains, supplies the identity. No necessity of the finiteness premise is asserted.

Thus under H+Fin_t(All)+Fun_{t,t}, the SplitMono_Δ and reversible qualifications coincide for each finite Δ, with exactly the same E,F. In particular, at full relational scope, SplitMono itself supplies Functionality through ordinary separation. With Fin_t(All) retained as a common premise,

$$
\boxed{\mathrm{SplitMono}\ \longleftrightarrow\ \mathrm{Rev}
\ \longleftrightarrow\ \mathrm{EndSep}.}
\tag{15}
$$
For the final equivalence, Rev recovers C and the identity observer is $\mathrm{Good}_{\{t\}}$ with internally finite image: its image predicate is unconditionally H-equivalent, hence C-identical, to All. The existing [single finite-image witness theorem](../logical-observer-hierarchy.md), §§5–6, turns Rev plus this one witness into endpoint separation EndSep. Conversely EndSep already supplies Rev without a finiteness assumption. The fork remains a countermodel because it has OS but lacks the left-invertible separating witnesses; (15) does not upgrade ordinary OS.

Finally the fork does not satisfy C5. The nonbottom proposition u is distinct from Bottom at r, but both its leaf transports are Bottom. Necessary distinctness therefore fails at r. The fork establishes the broad H comparison OS versus SplitMono in (13). The stronger implication C5 plus necessary OS⇒SplitMono is refuted by the distinct [linear and circular fibre model](linear-circular-fibre-left-inverse-gap.md), §§1–9, whose finite-pin proposition algebras and pure-sentence obstruction supply that result.

## 6. Sources

The full logical coordinate readers, the left-inverse obstruction and the separation verdicts are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§2–5, unpaginated.

The exact fork, its all-type transport sections and its BF/Functionality proofs are [Full three-object fork: all Barcan instances without binary families](fork-without-binary-families.md), §§1–2, direct source `misc`, unpaginated. Its underlying full action construction is Bacon and Dorr, *Classicism*, draft of 16 May 2023, §3.5, pp. 59 and 61, also used by the recorded [full two-object chain](../../source/topics/classicism/models/full-two-object-chain.yaml). The source supplies the general model construction; the new observer verdict is not attributed to it.

The full typed lifting and the C redundancy of translated equality qualification are as specified in [Typed separation and Classicism](typed-separation-and-classicism.md), §§2–4. The other directions of the strict hierarchy and incomparability in §5 retain the direct sources in the linked left-inverse and right-inverse notes.

The internal finite boundary uses the exact Frege definitions from [Background](../../source/topics/classicism/background.md), and the internal Dedekind induction in [Possibility Maximalism (pure) implies Axiom of Infinity (type t)](../../source/topics/classicism/writeups/pure-possibility-implies-axiom-of-infinity-t.md), Lemma 5, unpaginated. Its application to a qualified inverse and the explicit Functionality step are given here. The endpoint conclusion uses [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md), §§5–6, direct source `misc`, unpaginated.

The proof is ordinary mathematics and has received no new Lean formalization. This note makes no database or central-map edits.

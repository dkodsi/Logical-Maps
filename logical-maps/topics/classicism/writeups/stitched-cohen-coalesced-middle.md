# Stitched Cohen model with a coalesced middle world

This existing construction separates necessary propositional strong worlds and propositional Barcan from the higher-type domain control needed for propagation. At the initial world, full Rigid Comprehension holds, together with necessary Relational Choice, necessary Strong Atomicity at t, necessary BF at t and necessary Boolean Completeness at t. The accessible middle world fails Rigid Comprehension and Boolean Completeness at et. The root itself has an atomless interval at (et)t.

The proof below is the complete original §§1–7, independently reviewed for this integration. Its original self-audit status is historical; the new review checks the invariant-name quotient, all-type closure and the exact-image arguments. The unreviewed different variant in original §8 is excluded. The construction uses a ground model and its Cohen-generic extension, as in the recorded stitched Cohen example; it is a relative model construction in that forcing metatheory, not an assertion that an actual generic over the entire ambient universe is available.

## 1. The two terminals and the middle world

Work with a ground universe V and a Cohen extension V[G]. Let A be the full extensional relational-type hierarchy on N constructed in V, and B the corresponding hierarchy in V[G]. Both are one-world models. The entire countable sequence of typed domains and operations of A is a set in V; it is a fixed ground parameter below. There is no need to use V itself as a parameter inside V[G].

In V[G], coalesce A and B at a new world s, with arrows a:s→A and b:s→B. Put D_s,e=N×N and let a,b be the two projections. At a flattened relational type τ=σ̄t let

    D_s,τ = P(D_s,σ̄) × D_A,τ × D_B,τ.

The powerset here is that of V[G]. The three components specify the extension at s and the complete entity at each terminal. The root component is unrestricted. Application, abstraction and transport are the ordinary coalesced-model operations; all outputs still end in t. The terminals' domains are closed under their operations, and the unrestricted s-extension supplies the extension of every abstraction at s. This is the usual direct closure proof for the coalesced sum, not an assertion that the ground terminal contains new subsets.

Let c⊆N be the new Cohen real. At s take a property X of individuals with actual extension

    E=c×{0},

and empty terminal extensions. It is admitted at s.

## 2. Rigid Comprehension and BC fail at s

Suppose a rigid Y were actually coextensive with X. Its A-extension C belongs to P(N)^V. Persistence gives c⊆C.

For every n∉c, let Z_n have universal s-extension, A-extension N\{n}, and universal B-extension. This is admitted. Every current Y-member (k,0), k∈c, necessarily falls under Z_n: it does so at s, at A because k≠n, and at B. Weak inextensibility of Y gives Y≤Z_n and hence C⊆N\{n}. For all n∉c this implies C⊆c. Therefore C=c, impossible because c∉V. Thus Rigid Comprehension fails already for properties of individuals.

This does not by itself prove failure of weakly inextensible comprehension: the persistence step was essential. To prove BC fails, use a separate represented family. At s let F:(et)t have as its actual members the haecceities H_(k,0) for k∈c; choose empty terminal extensions for F. If J were its algebraic least upper bound, the ground set J_A would contain c. Each Z_n above, n∉c, is an upper bound of the whole haecceity family, so J≤Z_n implies J_A⊆N\{n}. Again J_A=c would follow, contradicting c∉V. Thus BC at et fails at s.

There is an exact local criterion behind both failures. Fix τ=σ̄t and let T=D_A,σ̄ be the ground set of argument tuples at A. At s, Rigid Comprehension at τ and BC at τ each hold exactly when V[G] has no new subsets of T.

For comprehension, a rigid representative of an actual extension E must have A-extension aE: persistence gives one inclusion, and the same co-singleton tests, one for each ground tuple outside aE, give the other. Conversely, if aE is represented in A, the exact-image triple (E,aE,bE) is admitted and rigid; B is full in V[G]. The tuple map a is onto and has a fixed section (choose the other components to be bottom, or 0 for individuals). Hence its possible images aE range over all ambient subsets of T. This proves the comprehension criterion.

For BC, if all ambient subsets of T are ground, every represented family has its pointwise union at all three components, including A, and that union is an admitted join. Conversely a new C⊆T can index the S-relations with A-extension {z}, z∈C, and empty other extensions. This family is represented by the unrestricted root component at s. A least upper bound would have A-extension C, by singleton lower requirements and co-singleton upper bounds, impossible. Thus the same criterion decides BC. For τ=t the tuple set T is a singleton and the criterion is automatic; for τ=et it fails at the new real c. This is a construction-specific representability criterion, not a claimed equivalence of the two principles over C.

## 3. A ground set of invariant names

The following elementary forcing device makes the initial world's domains precise. Let Γ be the group of finite bit-flips of Cohen forcing. It is weakly homogeneous: any two finite conditions can be made compatible by flipping the finitely many disagreements. The name for the structure at s is invariant, up to forced equality, because it is canonically defined from the ground parameter A and the extension's full hierarchy B.

Call a name u for an element of D_s,τ invariant when

    1 ⊩ πu=u    for every π∈Γ.

Take such names modulo 1-forced equality. For each type these classes can be represented by a set in V: fix a name for D_s,τ; names forced to be its members have equivalent bounded-rank representatives, obtained by mixing names occurring in it along a maximal antichain. Normalizing a name preserves invariance up to forced equality. Denote this ground quotient set by Q_τ.

Three facts will be used.

1. Equality of two invariant names is decided by 1. If a condition forces equality, move it by weak homogeneity to be compatible with any proposed condition forcing inequality; invariance gives a contradiction. The same applies to any invariant sentence with invariant parameters. In particular two invariant names have equal values in the chosen extension exactly when 1 forces them equal. Thus their ground quotient injects into the actual s-domain.
2. An invariant name forced to belong to a fixed ground set has a single ground value forced by 1. Some condition decides it to be a particular member; the preceding argument promotes that decision to 1. More generally an invariant name for a subset of a fixed ground set is a ground subset, since membership of each ground member is decided by 1.
3. Uniquely defined operations on invariant names have invariant outputs. This includes typed application, the interpretations of formulas and abstractions in the s-model, and the images of ground sets of invariant tuples. Their outputs may be new sets of new entities; only outputs lying in a fixed ground set are asserted to be ground values.

In particular, the A-projection of a Q_τ-value is a uniquely determined member of D_A,τ, and the map Q_τ→D_A,τ is a function in V. The B-projection need not be a ground entity.

## 4. The initial world r

Add r→s; the arrows r→A and r→B are its composites with a,b. There are exactly four worlds, with no arrows back and with a unique arrow between any comparable pair.

Set D_r,e=N×N and let r→s be the identity on individuals. Recursively, in V, put

    D_r,σ̄t = P^V(D_r,σ̄) × Q_(σ̄t).

A root entity is a pair (E,[u]). Its actual extension is E, and its image at s is u^G. The other images are the terminal projections of u^G. Equality at r is literal equality of the two ground components. Equality of invariant-name classes and satisfaction of invariant sentences are decided as in §3.

At low types the tail domains are concrete: Q_t consists of the eight ground truth vectors, and Q_et consists exactly of the triples P(N×N)^V×P(N)^V×P(N)^V. At higher types Q also contains invariant names for new sets, such as the universal property of all s-properties of individuals. It is not merely the old full type hierarchy. These higher names are essential for preserving the full future quantifiers.

Here is the closure check. Application gives an actual extension definable in V from its ground arguments, and its s-component is application of their invariant tail names. For abstraction λx.T(x;p̄), the actual extension is the set of ground arguments satisfying its body in the r-structure; the evaluation is computed recursively in V. Its s-component is the interpretation of that abstraction in the s-model with the invariant tails of p̄, and is therefore an invariant name. Quantifiers at r range over the ground sets D_r,σ, so the root extension remains in V. Quantifiers in the tail range over all the corresponding s-domains, as required; they are not restricted to images of root entities. Boolean operations and identity obey the same construction.

In curried notation the application just described is explicit: if F=(E,[u]), then F(x) has root extension E_x and tail class [u(hx)]. The quotient operations are functions in V, so x↦F(x) is a ground function with the required compatibility. This is why the flattened profile definition respects currying, rather than discarding the future values of a function. No abstraction with individual output is used.

These observations give the induction establishing term closure, β and η, and commutation of terms with every arrow. Two H-equivalent abstractions have equal extensions at r and equal complete s-tails, hence are identical. Thus H and the original Logical Equivalence schema hold. This is a C model; no theoremhood rule is applied under an optional assumption, and no type with output e has been introduced.

The injectivity in §3 is important here: equality of evaluated tails cannot leave two distinct ground codes for the same complete profile. Consequently literal equality and Boolean order in the root agree with equality and pointwise inclusion of the four-world profiles. The exact-image and upper-bound arguments below therefore use the model's actual algebraic order.

## 5. Every root family has exact representable images

Let E∈P^V(D_r,σ̄) be the actual extension of any root relation. Its image hE at s is an invariantly named set of tuples. Its image a(hE) belongs to V: the A-projection of each invariant tuple is decided in V by §3, and E is a ground set. Its image b(hE) is a set of B-tuples in V[G], and the full B-domain admits it.

Consequently there is an s-relation R_E whose three extensions are exactly

    hE,       a(hE),       b(hE).

It is admitted by §1, and its complete name is invariant by §3. Therefore the r-relation

    Y_E=(E,[R_E])

is admitted. At every arrow from r its extension is exactly the image of E. At s its extensions are likewise exactly the images of hE.

An exact-image relation is rigid: persistence is immediate, and any predicate necessarily covering its current members covers their images at every future world. The same argument applies after every arrow. Hence Y_E is rigid and actually coextensive with the original relation. This proves full Rigid Comprehension at r, for all finite argument tuples, including individual and mixed tuples.

The distinction from s is precise. Every root E is a ground set of root tuples, so its A-image is represented in A. At s, the new family c×{0} has A-image c, which A does not represent. Root comprehension gives no representative for this newly available family.

There is a direct BC cross-check at r as well. For a represented family of τ-relations, its actual family F is a ground set. Take the pointwise union of its root extensions and of its complete tail profiles. The root union is in V. The A-union is in V because the A-projection is a ground function on the ground family F; the s- and B-unions are admitted by their full extension components. The resulting tail is invariant. Thus the pointwise union is an admitted least upper bound at r. Applying this to the ground family of haecceities of E gives the same rigid exact-image representative Y_E. At s the new haecceity family from §2 lacks precisely this pointwise A-component.

## 6. Propositional Strong Atomicity, Choice, and the missing BF instance

At s the propositions are all eight truth-value assignments on {s,A,B}. All are ground and have invariant names. Hence r has all sixteen truth-value assignments on {r,s,A,B}. Each singleton world proposition is an atom, and its transport is either the corresponding singleton in a smaller future cone or bottom. It necessarily decides every proposition there. Every nonzero proposition contains a singleton. Thus SL_t holds at every world, and □SL_t holds at r. The same singleton at each evaluation world witnesses Actuality, so □Actuality holds as well.

All arrows are onto at type t and at e. Direct witness lifting therefore proves BF at those types everywhere. At r every actual serial relation is a ground set between ground domains; its seriality is absolute to V, and choice in V supplies a ground functional subrelation. Give that graph any invariant tail, for example bottom. At s use choice in V[G] and its unrestricted root extensions; at A and B use their respective full extensional hierarchies. Therefore □Relational Choice holds.

By contrast BF fails at et along r→s. The actual s-extension of any invariantly named et-entity is a ground subset of N×N, by §3. Thus X from §1, with actual extension c×{0}, is not an image of any root et-entity. Apply §5 to the root family E=D_r,et. Its rigid exact-image representative U:(et)t necessarily holds of every root property of individuals, but at s it omits X. Therefore

    ∀Z^et □U(Z)    but    ¬□∀Z^et U(Z).

This is an explicit failure of BF_et. It isolates the missing higher-type surjectivity; no failure of BF_e or BF_t is being used.

In particular U is actually coextensive with the universal property of root et-entities, but is not identical to it. The universal property's s-tail quantifies over all new s-entities, whereas U's tail is the proper image h[D_r,et]. Root Rigid Comprehension promises the former actual coextension; it does not identify these two complete profiles. This is the precise quantifier step which BF_rel supplied in the positive propagation proof.

There is also a direct check that all-type Strong Atomicity has not slipped into the premises. Let N_s=D_s,et\h[D_r,et], an invariantly named nonempty set. At r take F of type (et)t with empty root extension and an s-tail whose s-extension is N_s and whose terminal extensions are empty. Suppose a nonzero strong world W lay below F. Its only nonempty extension must be at s. Strong deciding at s, tested on singleton s-properties with empty terminal components, forces that extension to be a singleton {x}. Since W's tail name is invariant, singletonhood is decided by 1 and its unique member has an invariant name. Thus x lies in h[D_r,et], contrary to x∈N_s. Hence Strong Atomicity fails at (et)t. This verifies the boundary with the proved all-type Strong Atomicity theorem without appealing to that theorem by contraposition.

In fact F bounds an atomless interval in the root Boolean algebra at (et)t. For any nonzero Y≤F, the same invariant-singleton argument shows that its s-extension contains distinct x,y. An s-entity of type et is a triple of subsets of the fixed ground individual sets N×N, N and N. Hence x,y differ at some world component and some ground individual coordinate. The s-property of et-entities satisfying that coordinate test, with empty terminal extensions, has an invariant name: its definition uses only that ground coordinate and the canonical component maps. Give it an empty root extension. Intersecting Y with it and with its complement gives two nonzero proper parts of Y. Thus the full propositional algebra is finite and atomic while this higher algebra has an atomless interval. The gap between SL_t and all-type Strong Atomicity is substantive even before considering the future splitting of atoms.

## 7. Consequence and source boundary

At r the premises SL_t and Rigid Comprehension hold, but their accessible world s fails Rigid Comprehension and BC. This refutes the two unboxed-to-boxed propagation claims without BF_rel, while leaving the full all-type Strong Atomicity propagation proof intact. It also explains why merely observing BF_rel fail in the earlier stitched Cohen model did not settle the question: that model's only future world was fully extensional and retained comprehension. The middle world here permits new families while one of its branches still has only ground sets.

This does not make BF_rel a necessary condition for boxed comprehension in an individual model. The old stitched Cohen model has □Rigid Comprehension while BF_rel fails. The new model instead shows that BF_rel cannot be omitted uniformly from the sufficient propositional-SL package. Both behaviors are compatible with the unboxed premises; the differing issue is representability of the new future families, not BF failure by itself.

The weaker failure of Rigid Comprehension ⇒ □Rigid Comprehension was already recorded: a fresh proved-only query returns `full-boolean-valued-atom-and-atomless` and qualitative-contrast variants. The proposed gain here is the counterexample retaining propositional Strong Atomicity, indeed its necessity, together with propositional BF. No literature-novelty claim is made.

As a limiting check, trivial forcing removes the obstruction: all s-entities then have ground names, h is onto at every type, all the relevant images and pointwise joins belong to the ground terminal, and the four-world full construction retains comprehension everywhere. The actual Cohen extension supplies exactly the new family excluded by that check. All assertions here are pure; a permitted fixed signature may be interpreted at r and transported without changing them.

Background constructions: Bacon–Dorr, *Classicism*, draft 16 May 2023, Appendix E, Definition E.2, pp.80–83, as recorded in `groups/coalesced-sums.yaml`; Barton–Goodsell, *Continuum Contingency*, draft 14 October 2026, §8, Definition 1 and Lemmas 11–19, as recorded in `models/stitched-cohen-extension.yaml`. The published/unpublished source arguments are not edited. The four-world combination and the invariant-name construction above are new arguments with direct source `misc`, not claimed as the authors' result. This note supplies its own closure and image proofs rather than presuming an unchecked generalization of their stitching theorem.

## Self-audit status

Critical obligations checked in the construction: invariant-name classes form ground sets; equality and ground-valued projections are decided; tail abstraction quantifies over the full new domains; every root family's A-image is ground; the bad middle-world family's A-image is not; and rigidity is verified at all worlds, not just weak rigidity at r. The stronger claim that weak inextensible comprehension fails at s is deliberately not made: its refutation would need a persistence premise that it does not have.

The self-audit is complete. It included a second check of quotient equality versus evaluated equality, the distinction between a tail abstraction's full quantification and its old invariant parameters, the curried application formula, the direct pointwise-join check at r, the concrete missing haecceity join at s, and the higher-type atomless interval. No remaining construction gap was identified in this pass. This remains a proposed ordinary mathematical countermodel, not an independently checked or formally verified record.

A proved-only Engine check of the stated positive package against the failures of necessary Rigid Comprehension, necessary BC and relational BF found no conflict. This is only a check against the existing records. The old stitched Cohen model and both original pinned-root models retain their existing verdicts.


## Integration clarifications and source boundary

The failure of a supremum in §2 also refutes the official GLB form of BC: replace the represented family F by the admitted complement-transformed family X(Z)=F(not Z). A greatest lower bound of X would complement to a supremum of F. No unrepresented external family is quantified in this argument.

The invariant-name argument quantifies over the set of bounded-rank representatives modulo forced equality, and uses finite-bit-flip weak homogeneity only for sentences with invariant names. It does not assert that every object of the generic extension is ground. Whole future tails are retained in the root entities; in particular their quantifiers range over full future domains, not just transported root domains. The exact-image construction is checked at every relational type and every finite tuple, including individuals. Necessary propositional strong worlds may become zero; no necessary nonzeroness is assumed.

The direct proof of BF_et failure and of full Strong Atomicity failure remains in §6. The staged record gives the irredundant stronger failure of all-type Atomicity: the interval bounded by F at (et)t is atomless. Necessary Actuality is also proved directly, and derived from the staged necessary Strong Atomicity verdict. None of these is a failure of propositional Atomicity or of BF_t.

Direct source: OpenAI Codex, prompted by Daniel Kodsi, *Stitched forcing model with a coalesced middle world*, 22 October 2026, §§1–7, unpaginated. Background: Bacon–Dorr, *Classicism*, draft 16 May 2023, Appendix E, Definition E.2, pp.80–83; Barton–Goodsell, *Continuum Contingency*, draft 14 October 2026, §8, Definition 1 and Lemmas 11–19. Those source constructions are not modified or credited with the new four-world combination. Ordinary independent integration review: OpenAI Codex, prompted by Daniel Kodsi, 28 October 2026. No Lean certification is claimed.

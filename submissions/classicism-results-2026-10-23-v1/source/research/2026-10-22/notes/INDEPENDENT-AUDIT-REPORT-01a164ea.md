# Independent audit report — 01a164ea

22 October 2026. OpenAI Codex research chat [research task]. No human check, Lean verification, map edit, or build is claimed.

## Main conclusion

The proposed proof in `relational-choice-boolean-completeness-transversal-proof.md` passes three independent mathematical checks: the coordinating auditor read the whole proof, a second auditor reconstructed the partial-selector and join arguments, and a third reconstructed both fixed-point proofs. We found no mathematical gap. This is new ordinary proof evidence for the existing Goodsell conjecture, not an existing recorded theorem or a claim of literature novelty.

Final exact scope: Boolean Completeness at σt and Relational Choice with input σt and output σ imply Transversal Choice at σ, including σ=e. All premises are actual/unboxed. In fact joins of represented internally well-ordered families suffice. The original proof used RC with input/output σt; the guarded progressive operation below gives the weaker point-choice premise, separately checked by three auditors.

## Decisive checks

1. Evaluation's right adjoint follows from an H theorem with free F,x,p: ∀z(Fz→(z=x→p)) ↔ (Fx→p). It remains valid with future-new z, and does not assume BF or ND.
2. P(F)=∀actual x,y □(Fx∧Fy∧Rxy→x=y). Ambient algebraic chain join Q satisfies this exact pointwise-boxed property using two implication adjunction steps. No step proves or needs □∀xy.
3. The symmetric guard q in the one-point extension gives a uniform logical safety implication at every future world, without transporting actual Equiv(R) or actual truth of q. If an actual cell is missed, q is actually true and the extension is actually strict.
4. The fixed-point theorem uses an antisymmetric order on entities. Coextensive chain predicates therefore have the same unique supremum entity. A functional graph at that entity gives an actually coextension-invariant selector, without TC or Plenitude.
5. The internal union of all f-chains is an admitted existentially defined predicate, internally well-ordered by initial-segment comparison. No external ordinal iteration or full powerset is used.

The only initial notation clarification has now been incorporated: §5 explicitly writes C≡I or D≡I (actual coextension), not identity of predicate codes. The author also added a pointer to the independently proved guarded-operation refinement. Neither issue leaves an outstanding correction in the audited proof.

## Detailed notes

- `.reproduction/classicism-research/audit-bc-partial-selectors.md`
- `.reproduction/classicism-research/audit-bare-c-bourbaki-witt.md`

## Rigid-bottom proof

A separate auditor checked `/tmp/rigid-bottom-cut-proof.md` and reconstructed the modal steps in `.reproduction/classicism-research/audit-rigid-bottom-cut.md`. No gap found. It also proves directly, before Rigid Power, the typed implication SL_σ + RigidComprehension_(σt) ⇒ □SL_σ. The all-schema conclusion is SL+RigidComprehension⇒□SL+□BFrel. The bottom element repairs future collapse into a cut; no □RigidComprehension, ND, or BF is used to construct the rigid cuts. This does not give BF at e.

## Recorded baseline

The initial narrow proved-only Engine query, with optional premises in the queried set and no optional engine background, found no recorded proof, exclusion, or separating model for RC⇒TC or RC+BC⇒TC. A later direct file check at about 20:15 UTC still found the RC+BC record conjectured with empty proof. This chat changed no local record.

## Remaining work

Relational Choice alone⇒Transversal Choice remains unresolved here. Three agents are now testing a fixed-point replacement, a Henkin/Skolem countermodel route, and a higher-type canonicalization route. Further useful results will be appended below or supplied in separate clearly named files.

## Secondary results at 19:10 UTC

The unrestricted Relational Choice⇒Transversal Choice question remains unsettled. These restrictions were established and independently checked:

1. **One-object symmetric ideally-full finite-pinning no-go.** For any admitted τ in this construction, RC_(τt,τ) implies TC_τ. If S chooses from all nonempty τ-properties and finite N pins S, the admitted intension A_w=Dτ\Fix_{Dτ}(G_{w[N]}) forces G_N to act pointwise trivially on Dτ. Hence every actual E⊆Dτ has canonical admitted code B^E_w=gE when w|N=g|N, empty otherwise; this is well-defined even when matching g is nonunique. Existing S chooses from the canonical cell codes, and the chosen set is represented by the same construction. This requires no external AC. It covers auxiliary pin carriers and singleton-individual variants; it is not a theorem about arbitrary multiobject categories or smaller Henkin subdomains. Full proof: `rc-alone-higher-type-audit.md` §1.4.
2. **A separator would omit a represented well-ordered join.** From a failed TC witness and RelChoice one constructs a strict progressive graph on algebraic partial selectors. The admitted union of its f-chains is internally well-ordered and has no ambient algebraic supremum. Thus completeness for represented internally well-ordered Boolean chains already suffices for the main theorem. Same file §2.
3. **Operation-valued canonicalization is impossible from RelChoice alone.** Any operation q:t→κ with q(p)=q(r) iff (p↔r) actually implies Actuality: T(p):=(q(p)=q(top)), a:=∀p(Tp→p); a is true, and every actual true p has necessary Tp by NI, hence a≤p. Constant-property encoding reduces higher-type operation canonicalizers to this case. Known RelChoice+¬Actuality models rule them out. Graph-valued canonicalization remains possible and is precisely the unsolved issue. Same file §3.
4. **Actual-union selector qualification.** A coextension-invariant functional supremum selector for all comparable families in the actual-inclusion preorder is equivalent to Transversal. The proof uses whole coextension classes as comparable families; they are generally NOT identity-antisymmetric TotalOrder chains. Do not omit this qualification. Details: `rc-alone-fixedpoint-obstruction.md`.

A further concrete higher-order obstruction to the semilinear/shear seed is being written. No candidate is being promoted to a C countermodel.

## Concrete restricted-Henkin seed ruled out

`rc-alone-shear-obstruction.md` now supplies a stronger no-go requiring only formula comprehension and finite-support equivariance, not ideal fullness. The semilinear seed M=V⊕Q (lexicographic), H=0⊕Q, h=(0,1), c=(v₀,0), with all Q-linear shears fixing v₀ and finite individual supports, cannot support a global nonempty-property chooser after C closure.

Impredicative ancestry defines exactly the standard multiples N·h; paired ancestry defines n·x for each such standard n. Thus rational multiples and span_Q(h,c,A) are definable for the chooser's finite support A. This span is exactly the pointwise fixed set of the support-fixing shear group. Its nonempty complement is an admitted property entity fixed by the same subgroup, with no subgroup-fixed member. Functionality of the supported chooser is contradictory. The coordinating auditor and two independent subagents checked the argument.

Critical hypothesis: the shear action fixes the seed relation ENTITIES and acts equivariantly on the whole intensional hierarchy. Invariance of their actual extensions alone is insufficient. The proof states this explicitly. The proposed seed report has been marked ruled out; no C countermodel remains claimed.

## Sharpening: a guarded progressive operation from point choice

The BC auditor found, and the coordinator independently checked, a useful refinement: the main theorem only needs Relational Choice with input σt and output σ, rather than input/output σt. Choose a point in a missed actual R-cell for every nonfull F. If S(F,y) is the chosen graph, set

N_F(y) := S(F,y) ∧ ∀z(S(F,z)→z=y) ∧ ∀z(Fz∧(Ryz∨Rzy)→z=y),
g(F) := λy(Fy∨N_F(y)).

This is a genuine admitted operation g:(σt)(σt), constructed by lambda abstraction. The uniqueness guard makes the new summand a singleton at every future world, even if S ceases to be functional there; the compatibility guard protects old F-members. Consequently F≤g(F) is a C theorem and P(F)⇒P(g(F)). Actually, whenever F misses an R-cell, S chooses x in one and both guards are true, so g(F)>F. Thus the fixed-point argument can use an operation directly, without Plenitude or representing the arbitrary chosen graph. This is not an operation-valued canonicalizer of coextension classes and does not imply Actuality.

Exact refinement: RelChoice_(σt,σ) + represented well-ordered Boolean completeness at σt implies TC_σ. Full-schema theorem unchanged. Detailed note being saved as `rc-guarded-progressive-operation.md`.

## Rigid-bottom dependency refinement

A further coordinating audit, confirmed by the rigid-bottom auditor, shows that the BF part gives its box DIRECTLY. Exact typed statement:

SL_σ + RigidComprehension_(σt) + RigidPower_(σt) ⇒ □BF_σ.

Root Rigid Power makes P_A:=λR(RigidR∧R≤A) rigid, hence necessarily rigid. The sealed cover/representation facts are already necessary. At each future world, apply the same weak-inextensibility proof to its locally quantified X and R; this proves BF there. No Tame Rigidity, boxed Rigid Power, future Rigid Comprehension, or transport of root ∀Y□XY is required. Updated exact dependencies are in `audit-rigid-bottom-cut.md` §5. At full schema level, the existing Atomicity+RigidComprehension⇒RigidPower arrow still supplies Rigid Power from SL+RigidComprehension.

## Broader symmetric-category theorem (19:50 UTC)

The one-object restriction in the earlier secondary result has now been removed. In the symmetric ideally-full map-category construction with all symmetric pinned profiles admitted, the local membership-selector instance of RC_(τt,τ) implies TC_τ at every evaluation object. The proof allows multiple objects, noninvertible arrows, collapse of pinning points, return arrows, and auxiliary pinning carriers. It is choice-free in the metatheory. The support need not be finite, conditional on those exact full-admission/profile laws defining a valid model.

For root V and support N of S, take A_w=Dτ(target w) minus the fixed set of the target symmetry stabilizer of w[N]. This forces the root N-stabilizer to act trivially on Dτ(V). For each actual E⊆Dτ(V), its canonical profile B^E_w is gE if w ends at V and w|N=g|N for some root symmetry g, and empty otherwise. The root-target split respects local symmetry and pinning, including after return arrows. Thus every actual subset has a canonical entity code, and the existing selector yields a represented transversal.

The coordinator checked the complete argument against the explicit old/new construction rules. Full statement/proof: `rc-symmetric-ideal-full-categories.md`. This remains a theorem only for the specified full symmetric-profile construction. It does not settle RC⇒TC for arbitrary C-models or sparse Henkin subhierarchies.

## Further scope checks on rigid-bottom result

The sealed covers also give □Strong Actuality via the boxed Strong Leibniz consequence and the existing typed implication. They do not yet prove □Boolean Completeness or □Rigid Comprehension. A future arbitrary family's union of rigid cuts may fail persistence because its indexing family need not persist. Rigid Power supplies a rigid domain of rigid subsets, not rigid comprehension for every current subfamily. No further propagation beyond the proved consequences is claimed; see `audit-rigid-bottom-cut.md` §7.

## Order-free vector seed also obstructed

Removing the order from the rational-vector seed does not save the variant with the full Q-linear automorphism group fixing finitely many named vectors and finite individual supports. Every admitted actual additive endomorphism graph must commute with a finite-codimensional support stabilizer, and this forces it to be q·Id for an actual rational q. Quantifying over these graphs therefore defines exactly rational scalar multiplication; finite support spans and their nonempty moving complements become admitted. A supported membership selector again contradicts equivariance. Three agents checked this argument. Precise statement: `rc-alone-vector-endomorphism-obstruction.md`.

The proof does not cover shear-only symmetry or an externally fixed, unrepresented large subspace W0. Those are possible escape conditions, not constructed models. Neither ordinary first-order Skolemization nor a countable selected sequence establishes the required impredicative all-type closure.

## Recorded symmetric singleton variants

A narrow source audit applies the support criterion to all ten recorded symmetric families. Nine singleton-individual variants fail the proposition-output membership-selector instance RC_(tt,t): each finite pinning set admits a symmetry moving a pinned proposition (usually a collision test). The old/new singleton variant has finite domains at every type at both objects, by a simultaneous finite-profile/trivial-symmetry induction, so it satisfies both □RC and □TC by finite equality-disjunction witnesses. These are scratch mathematical verdicts, not map updates. Exact constructions and proofs: `rc-symmetric-singleton-applications.md`.

## Realizability literature lead checked

Classical realizability has a genuine non-extensional choice principle NEAC, including published NEAC+not-AC examples, whose graph formulation is close to RC. It does not transfer automatically to this question. A two-condition forcing-style realizability calculation gives distinct raw falsity values to two H-equivalent tautologies, so the naive raw-value/literal-identity interpretation fails C's Logical Equivalence. The typed HOL presentation has a separate classical proposition sort and algorithmic formula sort and does not remove the issue. A Boolean quotient would have to prove abstraction/application well-defined and selector descent, among other obligations. No such C interpretation or separator was established. Primary-source formulas, exact sections/pages, and the independent countercalculation are in `rc-alone-realizability-transfer-audit.md`.

## Further independent main-proof check

The rigid-bottom auditor also separately checked `rc-guarded-progressive-operation.md` and affirmed the weaker local RC_(σt,σ) premise, including σ=e. No e-output operation, future functionality, BF, ND, or additional choice instance is hidden. The fixed-point argument requires a new join only for the represented union of all g-chains, already proved internally wellordered; thus represented wellordered Boolean joins suffice.

## Independent check of the concurrent CBC+CCC refinement

The coordinator read `.reproduction/classicism-research/relational-choice-countable-completeness-ccc.md` in full and found no gap in RC_(τ,τ)+CBC_(κ,τ)+CCC_(κ,τ)⇒BC_τ. Disjoint nonzero increments inject the represented union of all f-chains into a represented disjoint family; the exact possibly-multivalued Frege labels compose with this graph. CBC supplies the sole new join. Detailed check: `audit-rc-cbc-ccc-independent.md`. This is another sufficient-premise result, not a settlement of RC alone.

## Exact characterization in the symmetric full-profile class

The category theorem now has a converse and a local well-ordering characterization, independently checked by the coordinator. In ZF, for set-sized domains and support ideals closed under finite unions, the following are equivalent at output type τ:

- The membership-selector instance of RC_(τt,τ).
- A permitted support whose stabilizer fixes every actual τ-entity, together with external well-orderability of Dτ.
- RC_(α,τ) for every admitted input type α.
- An admitted actual well-order of Dτ, initially defined using admitted-property quantification.

Necessity of external well-orderability follows from S on the explicit canonical codes of EVERY external subset. For the converse, choose the well-order-least element of each U-fiber; a stabilizer fixing U and all outputs preserves this graph even if it moves inputs. The invariant-root-relation coding lemma admits the graph. An internal well-order itself forces the stabilizer condition by taking the least member of the moved-element profile; only then does root extension fullness turn it into an external well-order. See `rc-symmetric-ideal-full-categories.md` §§6–7. This characterization remains strictly construction-specific.

## Final categorical transfer check

The categorical literature's Rule of Choice selects base-category arrows and is not the graph-valued Relational Choice of C. Weak hyperdoctrines do not automatically supply C's lambda identities. The concrete Boolean assembly example has a sharper obstruction: with propositions interpreted by the chaotic/constant-realizer two-point object, every permitted relational type is an actual full set-function object, by the adjunction Γ⊣K and product preservation. Thus its natural C reduct is extensional and has TC in the ordinary choice metatheory. The example's failure to extract a tracked numerical operation involves e→e, which the fixed C type system omits. The coordinator checked the exponential calculation independently. Exact sources, proof, and a separate Boolean localic-epsilon obstruction: `rc-alone-categorical-transfer-audit.md`.

## Final unresolved construction obligation

`rc-w0-henkin-extension-obstruction.md` gives a concrete finite-support ultrapower failure and isolates the required support-preserving, individual-hull-preserving typed Henkin extension lemma. No such lemma was established. All claimed positive results above are ordinary mathematical arguments; no RC-alone proof, separating C model, literature-novelty certification, human verification, Lean result, or repository update is claimed.

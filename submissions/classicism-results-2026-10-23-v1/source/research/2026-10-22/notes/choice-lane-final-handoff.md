# Choice/uniformization lane: final research handoff

22 October 2026, approximately 20:35 UTC. Ordinary mathematical research in fixed C, with explicit coding extensions where stated. No repository records were edited and no Lean status was changed. New proofs would have direct source `misc`. “Audited” below means independent AI-agent mathematical checking, not a human or proof-assistant certificate.

## Main exact characterization

`functional-choice-by-sections.md` is the clean final proof note:

    FC ⇔ Actuality + RInv,
    □FC ⇔ □Actuality + SRInv.

RInv says every actually surjective operation between relational types has a pointwise right inverse. SRInv requires the composition identity necessarily, equivalently as literal equality of the composed operation with the identity operation. These meanings must not be conflated. Parent/root and rigidity independently audited the decisive pair-coding/escape-routing argument. The note includes models separating the premises. The rolling `choice-uniformization.md` contains supplementary arguments and superseded explorations; use the clean note for the final statement.

Other exact structural forms in that rolling note:

* Plenitude ⇔ Actuality + pointwise left inverses of all actual injections.
* C5 ⇔ persistence of actual injectivity ⇔ strong left-inverse splitting of all actual injections.
* Persistence of actual surjectivity ⇔ BF at relational types.
* Strong right-inverse splitting ⇔ ordinary right-inverse splitting + BF at relational types.
* Categorical epimorphism is necessary surjectivity, not merely actual surjectivity. Categorical monomorphism must likewise not be silently identified with actual injectivity.

Bare RInv⇒ND and some categorical-splitting implications remain unresolved. Do not turn the successful Actuality+RInv decomposition into an unconditional RInv collapse claim.

## Cleaner actual-truth definitions

`actual-truth-evaluator-ladder.md` gives the strict ladder, with models:

1. Actuality: arbitrary-value truth-fiber evaluator.
2. Bivalent evaluator: ND+Actuality.
3. Globally bivalent actual evaluator: Gallin Comprehension = ND+Strong Actuality.
4. Unique ordinary bivalent evaluator: C5+Actuality.
5. Necessarily some ordinary bivalent evaluator: □Plenitude.
6. One fixed necessarily correct evaluator: Extensionality.

Level 4 is **not** □Plenitude. The atom-plus-atomless Boolean model separates them. Uniqueness among globally bivalent evaluators at level 3 is automatic and weaker than uniqueness among all ordinary evaluators.

`gallin-bivalent-evaluator.md` proves the operator normal form E(p)=(w≤p), unique globally TwoVal normalization Λ at every relational type, Boolean laws, actual-outer-quantifier commutation, and safe boxed absorption. Boxing the outer quantifier of unrestricted commutation was not proved; it is exactly a selected-world relative Barcan issue. Keep that boundary explicit.

## Local extensional mathematics from Actuality alone

The choice lane proposed and independently audited the construction developed by rigidity in `actuality-world-slice-core.md`: cut relations by the unique actual atom w and recursively supported argument domains. Actual coextension of w-supported objects gives literal identity. This interprets extensional relational Henkin HOL over all current individuals; ambient Relational Choice supplies core Choice; the quantified Infinity axiom transfers exactly. No ND or GC is needed for this LOCAL interpretation.

The note also proves internal completeness of every represented Boolean interval below a w-supported top. Future worlds where w fails can collapse the local domains; no persistent global interpretation is claimed. `gallin-extensional-core.md` retains the stronger globally TwoVal construction from GC. Its §8 now gives canonical current-structure isomorphisms between the two cores under GC, by recursive normalization and support; the choice lane independently audited the inverse and application proofs. This identifies their current mathematical content without identifying future domains.

The choice lane independently passed the proof `nd-inextensible-comprehension-implies-weak-power.md`: ND_t + IC_(τt) ⇒ WRP_τ, with no hidden BF or boxed premises.

## Probability: a substantive consistent strengthening and its exact ceiling

`faithful-probability-countable-worlds.md` has two independent audits (principles for §§1–6, rigidity for §§1–8). Under C+□FC+quantified Infinity_e, with INTERNAL Dedekind reals over N_e:

    faithful finitely additive real state on propositions
      ⇔ faithful countably additive real state exists
      ⇔ internally countable atomic worlds
      ⇔ the represented relative ccc.

A given finitely additive state is not automatically countably additive. The proof constructs a replacement. All countability, Archimedean, sequence and supremum assertions are internal; N may be externally nonstandard.

The atom-product normal form sharpens this:

* A faithful state on individual properties ⇔ worlds and individuals both internally countable ⇔ faithful states at every finite individual arity.
* A faithful state on properties of propositions (type tt) ⇔ internally finitely many worlds.
* An all-relational-type state schema contradicts quantified Infinity_e, already at (et)t.

Full Gallin E=W=N supplies infinite models of the propositional and finite-individual-arity principles. Full E=N,W=P(N) refutes the propositional principle; full E=P(N),W=N separates the individual-property principle from it. The full-profile principle WR(N) is incompatible with faithful probability, although finite-pattern independence remains compatible.

`probability-and-world-symmetry.md`, written by rigidity and independently audited by this lane, adds: permutation-invariant faithful probability ⇔ internally finitely many worlds, with unique uniform counting state. A finite-parameter pure term using only proposition parameters and fixed original-core parameters cannot define a faithful probability in an infinite-world model. It is explicitly a term-definability claim, not a claim about arbitrary pointed descriptions.

## Important source correction discovered during the audit

The old/new model's recorded BC-failure witness is an inadmissible external family. See:

* `old-new-boolean-completeness-source-caveat.md` — exact source paths/lines, finite-pinning obstruction, positive et classification, and the principles lane's all-type proof as added during consolidation.
* `old-new-necessary-bc-failure.md` — repaired, admitted failure at the OTHER object O.

The all-type conclusion at the original evaluation point E was independently derived/checked by parent, principles and choice: **BC holds at every relational type at E**. Every relation is determined by two invariant extension components, at id_E and the old inclusion i:E→O. An admitted family pinned N has component unions invariant under the requisite stabilizers, hence those unions define an admitted LUB pinned N.

The recorded ND and IC-failure proofs then yield the substantial separation **ND+BC does not imply Inextensible Comprehension or Rigid Comprehension**, subject to the separately audited model construction and those existing proofs. This replaces, rather than supplements, the unsupported source assertion of ¬BC at E. No source record has been edited.

At O, the admitted family of OLD haecceities has no LUB: an arrow O→E forgets old/new color, and changing an injection away from a finite pin forces a supposed least bound to contain a new individual's image, while that individual's complement bounds every old haecceity. Parent and principles independently audited this proof. Therefore the pointed model has BC_all but ¬□BC_et. The original even-haecceity family at E remains absent.

## Additional useful files

* `endomorphism-splitting-infinity-separator.md`: finite torsor models plus Henkin compactness separate endomorphism inverse splitting from ND, even with necessary all-type Infinity SCHEMA. It does not prove quantified Infinity. Rigidity independently audited.
* `reversible-comprehension-and-algebraic-laws.md`: Plenitude via representation of involutive graphs; BF_rel via persistence of pointwise idempotence or involutivity. Treat these as alternate structural characterizations, not inflated theorem counts.

No literature-novelty claim is made for these algebraic ideas. The useful claims are exact new arguments relative to the database, sharper premise scopes, explicit admitted-family constructions, and the identified source correction.

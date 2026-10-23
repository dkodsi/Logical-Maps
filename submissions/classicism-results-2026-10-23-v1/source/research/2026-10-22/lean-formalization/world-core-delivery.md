# World and actual-core contribution

Current scope: prepare the existing research for delivery, including new Lean
formalizations of its existing proofs. No open conjecture is declared settled.
The current machine-readable evidence is
[`verification-updates/world_actuality_gallin.json`](verification-updates/world_actuality_gallin.json).

## Checked principal results

- **Supported graph normalization.** Under the current `ActualWorld w`
  hypothesis, cutting an admitted graph to its displayed input/output domains
  preserves and reflects seriality, single-valuedness, injectivity and
  surjectivity. Principal declaration:
  `Classicism.Research.ActualityCore.graph_normalization_law.listRule`.
- **Relational-output realization.** A serial single-valued admitted graph
  into the supported relational domain is represented by the explicit
  `Realize` operation, with literal equality to its selected output.
  Principal declaration: `graph_realization_law.listRule` in that namespace.
  Individual outputs stay represented by graphs; no individual-output
  function type is added.
- **Represented predicate transfer.** Quantification over represented
  predicates transfers to supported representatives when the displayed
  predicate is extension-invariant on the input domain. Principal declaration:
  `predicate_transfer_law.listRule`. The supplied well-foundedness predicate
  satisfies that condition. The extension-invariance premise has not been
  removed for arbitrary intensional predicates.
- **Current truth-sort comparison.** For an actual evaluator, the truth
  kernel and the endpoint truth domain have the explicit inverse maps in
  `canonical_truth_bridge.derivable`. This is the nullary comparison; it does
  not claim the full higher-type Gallin comparison.

Exact certificate evidence:
[`checks/20261023T043023549683Z-0cf20b33.json`](checks/20261023T043023549683Z-0cf20b33.json).
The separate whole-module derivation audits check all 28 graph theorems and
all 8 bridge theorems, including composition, identities, selected-output
realization, and represented well-foundedness:
[`checks/20261023T044036874157Z-c349c7c2.json`](checks/20261023T044036874157Z-c349c7c2.json).
That latter manifest also contains an unsuccessful first membership-module
check; its independent graph/bridge successes are not a claim that every
target in the manifest passed. Printed derivation axiom reports include
`propext` and `Quot.sound`; the shallow Classicism gate, relational-type audits
and translated C derivations were checked separately.

Earlier ActualityCore and WorldRepresentation certificates and full helper
audits are recorded in `integration-status.md` and
`checks/20261023T032657816117Z.json`. They remain separate from the continuation.

## Recursive interpretation continuation

`Classicism.Meta.ActualityCoreSyntax` now defines the recursive domain and
support terms on the actual `Ty`/`RTy` datatype, normalizes relational outputs,
bounds higher-domain quantifiers, and translates every constructor of `Term`.
Context renaming of that translation is proved. The syntax and the supporting
translated cut/section rules passed in the second manifest above.

The principal continuation declarations are `translate_member`, stating
membership of every translated term under a core assignment, and
`translate_application`, stating literal preservation of application after
normalization. Their current check/repair status and hashes are in the
machine-readable update; this prose does not mark a prepared theorem checked.
Domain/support substitution laws are a separate syntactic target.

These statements quantify over type codes in the metatheory, while producing
derivations in C at each fixed type. They do not add quantification over types
to the object language. All generated terms are admitted syntax; no external
powerset or full function-space premise supplies a missing closure proof.

The remaining formalization obligations are preservation of substitution of
interpreted terms and beta/eta/delta conversion, construction of the current
extensional Henkin hierarchy from an arbitrary admitted ambient hierarchy,
and the full term/formula truth induction. The higher-type Gallin comparison
also needs the exact globally bivalent normalizer and inverse-map proofs.
These are outstanding formal proofs of the cited research argument, not new
claims that the mathematical questions are open in the literature. Numerical
and real-domain comparison work remains with its separate owners.

## Sources, coverage and reproduction

Full prose proofs:

- [`actuality-world-slice-core.md`](../notes/actuality-world-slice-core.md),
  sections 2--4 and 7--8.
- [`gallin-extensional-core.md`](../notes/gallin-extensional-core.md),
  sections 3--5 and 8.
- [`structural-world-representation.md`](../notes/structural-world-representation.md),
  sections 3--4 and the later evaluator classifications.
- [`structural-algebraic-core.md`](../notes/structural-algebraic-core.md),
  the individually indexed Boolean/world-map/ultrafilter classifications.

[`world-core-coverage-queue.json`](world-core-coverage-queue.json) preserves all
26 original world-algebra keys and their qualifications. The general
representation theorem does not certify all those classifications. Distinct
Boolean retraction classifications are retained alongside, and distinguished
from, the other owner's ordinary functional section/retraction results.

[`world-core-reproduction.txt`](world-core-reproduction.txt) gives the exact
locked-runner commands. Database validation has passed after every edit batch.
No record YAML, generated Statements file, published proof, or Lean verification
flag was changed by this continuation.

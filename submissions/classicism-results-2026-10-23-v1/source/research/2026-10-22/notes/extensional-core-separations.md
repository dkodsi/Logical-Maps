# Local and globally bivalent cores: audited separations

Research audit, 22 October 2026. These use existing recorded models and arguments; no new construction or literature-novelty claim. The core interpretation proofs are in `actuality-world-slice-core.md` and `gallin-extensional-core.md`. Both were independently audited by the principles lane, including the quantified Infinity argument.

## 1. GC, Choice and quantified Infinity without C5 or boxed Functional Choice

Use the generated proved model `full-two-object-retract-individuals-fixed-infinite`. Its source is `topics/classicism/models/full-two-object-retract.yaml`, with the fixed-infinite individual parameter of `groups/full-action-models.yaml`. Work in ZFC and take every individual domain to be N, every individual action to be the identity.

The category has objects 0,1, arrows h:0→1 and j:1→0, with jh=1_0 and hj=k≠1_1. Thus k²=k, kh=h and jk=j. Evaluate the full action hierarchy at 0.

GC holds at every permitted relational type by the recorded coherent-retractions argument. Choose r_(1_0)=1_0 and r_h=j. For every composable x, r_(xg)x=r_g: the only nontrivial checks are jh=1_0 and jk=j. Given the current extension E of any relation, define its replacement at g by r_g(tuple)∈E. Fullness admits this intension. The coherence equation makes both this replacement and its complement persistent, and its root extension is E. This argument works at arbitrary tuple types, not only e.

Fullness gives RC at every object and type: for a current extension E take the exact-image profile g↦gE. It is admitted and has exact-image transport under composition, hence is rigid. In ZFC, every actual serial relation has a set-theoretically chosen functional subrelation; fullness admits an intension with precisely that current extension. This proves Relational Choice at every type and every object, hence boxed RC and boxed Relational Choice.

The quantified Axiom of Infinity at e follows by the exact recorded argument `arguments/infinitely-many-individuals.yaml`, not merely by the finite-bound schema. Extensional fullness admits a property K of cardinalities holding of Z precisely when every property X with ZX has externally finite extension. K contains zero and is successor-closed. Impredicative natural-cardinality induction puts every N_e-cardinality in K. The universal property of N has infinite extension, so no natural cardinality holds of it.

Boxed ND fails. At object 1, the proposition p={1_1} differs from bottom, but k transports p to bottom, since no arrow g has gk=1_1. Therefore the root fails C5 and boxed Functional Choice (the latter implies boxed ND). This is also verified by proved-only Engine closure for the generated model.

BF_t fails already at the root. Every old proposition transported along h has equal values at 1_1 and k, since 1_1h=kh=h. Fullness admits a root predicate Q whose root extension is all propositions and whose extension at h comprises precisely the propositions with equal 1_1/k values. Every current p satisfies □Qp, whereas at object 1 the new proposition {1_1} fails Q. Hence ∀p□Qp but not □∀pQp.

Thus GC + Relational Choice + quantified Infinity_e, even with boxed RC and boxed Relational Choice, does not imply C5 or boxed Functional Choice. It supplies the globally bivalent core without these stronger ambient principles.

## 2. Actuality, Choice and quantified Infinity without GC or ND

Use `full-two-object-chain-individuals-fixed-infinite`, from `models/full-two-object-chain.yaml`, again with N fixed pointwise. The category has only 0→1 besides identities; evaluate at 0. Its full hierarchy has boxed RC, boxed Relational Choice, boxed BF, and quantified Infinity_e. RC, Choice and Infinity have the same proofs just given; the exact boxed BF verdict is recorded for epic arrows and is included in the proved-only Engine closure.

The root proposition w={1_0} is a true atom and witnesses Actuality. Its transport to object 1 is bottom although it is distinct from bottom at 0. Therefore ND_t fails; consequently GC, ambient Functional Choice, C5 and boxed Functional Choice fail. The world-slice core nevertheless interprets extensional Henkin relational HOL with Choice and quantified Infinity over all current individuals.

This separates the local Actuality interpretation from the GC bivalent interpretation. No local interpretation is being silently promoted to a necessary interpretation.

## 3. Audit details for the two core Infinity proofs

In the GC construction, deletion of a core property must be normalized before it is a core property. The identity h(SZ)=S_c(hZ) is justified for extensional Z, and ambient natural cardinalities are extensional by the recorded Lemma A in `writeups/possible-infinity-t-and-bf-t-imply-axiom-of-infinity-t.md`. The inductive pullback therefore includes Ext(Z).

In the Actuality slice, raw deletion of a w-supported property remains w-supported and is already core. Thus h commutes with successor for all Z. Extensionality of ambient natural cardinalities is needed only at the final comparison between the ambient universal property and the core universal property λx.w. In both cases the image-predicate induction proves that every core natural cardinality has an ambient natural preimage; there is no unproved injectivity claim or replacement of quantified Infinity by its finite-bound schema.

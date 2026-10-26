# Simplified Max–Atomicity proof: Lean certified

**Contribution:** Formalization of a simplified proof of an existing result  

Pure Max(C) plus unboxed Atomicity at type t is inconsistent. The new third-order arithmetic proof replaces hereditary-set and Mostowski coding with direct cylinder splitting. This is a new certificate for a simplified proof, not a new inconsistency theorem.

**Lean certified.** The saved Lean 4.33.1 run completed successfully over 99 local modules, including 93 Classicism modules. The final theorem's axiom dependencies are `Classical.choice`, `Quot.sound` and `propext`, with no `sorryAx` or custom axioms.

- [Exact theorem, axiom audit and source hashes](../certificates/max-atomicity-third-order.json)
- [Certified sources and project configuration](../certificates/max-atomicity-third-order-sources.zip)

The theorem is `Classicism.Meta.Research.MaxAtomicityThirdOrderInconsistency.maximalism_atomicity_inconsistent`. It has no additional selector, rigidity or adequacy premise. The matching database result is `maximalist-distinctness-incompatible-with-atomicity-t`; its existing verdict and native certificate remain unchanged.

Original proof: GPT-6 Astra, prompted by Daniel Kodsi. The simplified map proof is attributed to Claude Opus 5.5, prompted by Cian Dorr. New Lean transcription: Codex, 25 October 2026. The receipt identifies the exact upstream proof revision.

All archive-member hashes and the current Classicism source hashes were checked when collecting this update. The source archive omits compiled outputs and historical logs; the complete original certificate remains preserved with its hash recorded in the receipt. No compiler was rerun during collection.

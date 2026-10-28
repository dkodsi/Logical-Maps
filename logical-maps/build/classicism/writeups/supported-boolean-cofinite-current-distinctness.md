# Supported Boolean model: cofinite interior with current distinctness

<p class='cert'>Model — Source: Misc.; produced by OpenAI Codex, prompted by Daniel Kodsi, supported Boolean constructions of 25 October 2026; recorded by OpenAI Codex, prompted by Daniel Kodsi, independent integration review of 28 October 2026.</p>

## Package

- **ND.** Distinct things of any type are necessarily distinct.
- **Atomlessness.** Atomlessness in the displayed closed propositional formulation.
- **¬ Boolean Completeness (type t).** Every property of propositions has a greatest lower bound.
- **¬ □ND (type t).** Necessarily, distinct propositions are necessarily distinct.

## Definition

Let A be the complete homogeneous atomless regular-open algebra of Cantor space and B=2×A×P(N), with Aut(A) acting on the middle factor. Set jprime(epsilon,a,S) to (1[value=Top],1_A,S) when a=1_A and S is cofinite, and to Bottom otherwise (retaining the displayed Top case); equivalently its opens are Bottom, Top and (0,1_A,S) for cofinite S. Individuals are a singleton. Admit all finitely A-supported nonexpansive functions for the equality delta_t(p,q)=jprime(p iff q) and recursively its open-meet function equalities. Quantifiers are actual B-meets/joins. Evaluate at a fixed ultrafilter of the middle A coordinate. The linked writeup §3 specifies the exact formula and verifies all typed soundness obligations.

## Arguments

### Holds ND.

Every typed equality is an open value. If false at a middle ultrafilter it is raw Bottom, so its distinctness and native necessity are Top. This proves the whole current ND schema; §3.

*Write-up: [supported-boolean-structural-contrasts](supported-boolean-structural-contrasts.html). Address: `supported-boolean-cofinite-current-distinctness#current-full-distinctness`. By OpenAI Codex, prompted by Daniel Kodsi, independent integration review, 2026-10-28.*

### Holds Atomlessness.

The local equality quotient is A×(P(N)/Fin), both factors atomless. Thus every nonzero proposition splits; §3.

*Write-up: [supported-boolean-structural-contrasts](supported-boolean-structural-contrasts.html). Address: `supported-boolean-cofinite-current-distinctness#current-propositional-atomlessness`. By OpenAI Codex, prompted by Daniel Kodsi, independent integration review, 2026-10-28.*

### Fails Boolean Completeness (type t).

The empty-supported nonexpansive predicate (3) admits the family of infinite block classes, with arbitrary middle coordinate. Any upper bound has middle value 1 and a tail class that can be strictly reduced by one point per block. Complementing the admitted family gives native GLB failure; §3.

*Write-up: [supported-boolean-structural-contrasts](supported-boolean-structural-contrasts.html). Address: `supported-boolean-cofinite-current-distinctness#admitted-partition-completeness-failure`. By OpenAI Codex, prompted by Daniel Kodsi, independent integration review, 2026-10-28.*

### Fails □ND (type t).

ND_t is true at every middle ultrafilter but false at the first coordinate and every principal tail coordinate, by the explicit Top versus (1,1,N minus {n}) pair. Its value is (0,1,empty), whose jprime is Bottom. The native ND_t+BF_t implication then also refutes current BF_t; §3.

*Write-up: [supported-boolean-structural-contrasts](supported-boolean-structural-contrasts.html). Address: `supported-boolean-cofinite-current-distinctness#necessary-distinctness-failure`. By OpenAI Codex, prompted by Daniel Kodsi, independent integration review, 2026-10-28.*


## Notes

The metatheory is ZFC. All current/necessary claims refer to the displayed evaluation, with no all-type BC flag inferred from propositional BC. Only the predecessor has the observer verdict proved in §2; no observer node is substituted. No original human source, native record, signature flag or Lean certificate is changed.

## Sources

- OpenAI Codex, prompted by Daniel Kodsi, Observer separation with propositional completeness and divergent possibilities, 25 October 2026, §§1–3 and 5a, unpaginated; independently expanded typed proofs in the linked writeup, §§1–3.

<p class='cert'>Record: <code>topics/classicism/models/supported-boolean-cofinite-current-distinctness.yaml</code></p>

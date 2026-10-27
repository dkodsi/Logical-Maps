# Arithmetic propagation: what is already stronger than the observer theorem

Ordinary mathematical audit by OpenAI Codex, 25 October 2026. Fixed framework: relational Classicism C. No native records or formal-verification labels are changed. The principal arithmetic theorem below is already recorded and attributed to Andrew Bacon; the observer comparisons are combinations with the cited research notes, not claims of historical novelty.

## 1. Exact conclusion

For every admitted type σ, put ν=(σt)t and interpret zero, successor, natural numberhood, Sum and Prod by the Frege definitions in [Background](../../../classicism-results-2026-10-24-v2/source/topics/classicism/background.md). Let A be a first-order arithmetical sentence in that exact interpretation. Then:

```math
\boxed{C5\vdash (A\to\Box A)\land(\neg A\to\Box\neg A).}
\tag{1}
```

Equivalently, C5 proves □A∨□¬A. **OS is unnecessary**, and there is no Infinity premise or Iσ guard in (1). This is stronger than the native recorded Necessity of Arithmetic instance

```math
\mathrm{NA}_{\sigma,A}:=
\Box(I_\sigma\to A)\lor\Box(I_\sigma\to\neg A),
\quad I_\sigma:=\Diamond I^*_\sigma.
\tag{2}
```

Here I* says that zero is not a successor and successor is injective on the natural numbers. The record deliberately retains this guard to match Goodsell's formulation. Dropping it in the C5 conclusion is justified by the existing proof, rather than by substituting a different principle.

The exact proved record is [C5 implies Necessity of Arithmetic](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/c5-implies-necessity-of-arithmetic.yaml), with its [detailed proof](../../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/c5-implies-necessity-of-arithmetic.md). Its direct source is Andrew Bacon, *Could the truths of mathematics have been different?*, draft of 9 October 2025, Theorem 4.4, p. 19; Appendix C.1, pp. 10–11 of the separately paginated appendix. The map's transposition to Frege numbers at every type is explicitly documented there.

This does not assert truth invariance for arbitrary chosen arithmetic structures, for second-order arithmetic, or for analytical sentences quantifying over reals. It is the native first-order arithmetic schema.

## 2. Why C5 already does the work

The existing proof has a useful local form. In addition to C, it uses only the modal dual of B, ND at ν, and BF at ν, all currently at the evaluation point. C5 supplies these. Its proof proceeds as follows.

1. **Numbers persist already in C.** In the impredicative definition of N, instantiate the inductive property with λn.□Nn. Zero necessarily satisfies N, and K carries the necessitated successor-closure theorem through the box. Thus Nn→□Nn.
2. **Sums and products persist already in C.** In their recursive definitions, use the relations λi,j.□Sum(m,i,j) and λi,j.□Prod(m,i,j). The recursion clauses and persistence of numberhood prove the necessary versions whenever the free arguments are numbers.
3. **C5 also preserves falsity of these atoms.** For example, possible numberhood implies possibly necessary numberhood by step 1; the dual of B gives current numberhood. Contraposition gives ¬Nn→□¬Nn. The same argument works for Sum and Prod on numbers. NI and NDν handle identity and inequality.
4. **The number quantifiers preserve both sides.** Suppose ∀n∈N B(n) currently. For every n, either Nn and the induction hypothesis supplies □B(n), or ¬Nn and step 3 supplies □¬Nn. Either case yields □(Nn→B(n)); BFν collects these into □∀n∈N B(n). A false universal has a current numerical counterexample; its numberhood and the negated matrix persist, so the failure persists too.

This proves the stronger formula version

```math
\forall\bar n\in N\,
[(A(\bar n)\to\Box A(\bar n))
\land(\neg A(\bar n)\to\Box\neg A(\bar n))].
```

No optional premise is necessitated. The boxes in steps 1 and 2 come from theorems of C; the later steps use the stated current modal premises.

There is also a small positive fragment that requires **C alone**. For formulas built from N, Sum, Prod and equality atoms by ∧, ∨ and existential quantification restricted to N, steps 1 and 2, NI and ordinary necessary existential introduction give

```math
C\vdash\forall\bar n\in N\,
[P(\bar n)\to\Box P(\bar n)].
\tag{3}
```

For the existential step, retain the currently supplied numerical witness: its numberhood persists and the induction hypothesis preserves the matrix. Necessitate the logical existential-introduction theorem to finish. This elementary fragment corollary is not a propagation theorem for arbitrary negations or universal arithmetic claims, and it needs no observers.

## 3. Ordinary OS alone does not preserve arithmetic truth

The [complete Boolean root construction](../complete-boolean-root.md), §5, yields a model satisfying

```math
C+OS+BC_t+\mathrm{RelationalChoice}+\mathrm{Actuality}
 +\neg\mathrm{NecessityArithmetic}.
\tag{4}
```

The arithmetic components are the one-world extensional Henkin models in the recorded [coalesced two-arithmetic construction](../../../classicism-results-2026-10-24-v2/source/topics/classicism/models/coalesced-two-extensional-arithmetics-root.yaml). They satisfy I* at e and disagree about the arithmetical sentence Con(T), for the recursively axiomatized higher-order theory T specified in that record. The new root has both components as possibilities. The complete-root note proves admission of the typed observers, their whole-operation qualification, and separation; this is not an assumption that external evaluation maps are automatically admitted.

At those two accessible evaluations, I holds and the sentence A has opposite truth values. Thus neither box in (2) holds at the root. Also, whichever of A and ¬A is currently true at the root fails to be necessary. Consequently **ordinary OS does not give the general schema A→□A for arithmetic A**. Adding ordinary propositional BC, Relational Choice, and Actuality still does not suffice. The example is necessarily outside C5 by (1).

Already the original two-arithmetic record gives □BF together with arithmetic contingency. Thus replacing OS with BF or even □BF cannot repair the implication. Full Boolean Completeness is different: its recorded route through Countable Boolean Completeness does yield (2), without C5 or OS. The stronger BC assumption here has all-type scope, not just BC_t. In the source proof at a fixed σ, the sole completeness use is for the family of numerical singletons at type νt, counting relative to that same σ; see the [Countable Boolean Completeness proof](../../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/countable-boolean-completeness-implies-necessity-of-arithmetic.md), Lemma 8.

## 4. A principle about necessity is distinct from the current arithmetic claim

If the question instead asks whether the *Necessity of Arithmetic instance itself* propagates, the answer needs C alone:

```math
C\vdash\mathrm{NA}_{\sigma,A}
 \to\Box\mathrm{NA}_{\sigma,A}.
\tag{5}
```

Indeed each disjunct of (2) is boxed. Axiom 4 takes □B to □□B; K applied to necessary disjunction introduction then gives □(□B∨□D). Reason by cases on the two current disjuncts. This is the general persistence of a finite disjunction of boxed claims in S4. Each schema instance is treated separately; there is no infinite conjunction or quantification over sentences.

Equation (5) says that once this necessity principle holds, it continues to hold. It does **not** establish (2) from A, and does not remove the countermodel in (4).

## 5. Proved-only database check and status

On 25 October 2026, `scripts.pmap.load_topic('classicism')` and `Engine` were run with only proved records and empty optional background. The exact current native results were:

| Queried premises | Target | Engine answer |
|---|---|---|
| necessary-distinctness-necessary-r | necessity-of-arithmetic | Entailed directly by c5-implies-necessity-of-arithmetic |
| necessary-barcan-r | necessity-of-arithmetic | Not entailed; separating model coalesced-two-extensional-arithmetics-root |
| boolean-completeness-r | necessity-of-arithmetic | Entailed through boolean-completeness-r-implies-countable-boolean-completeness-r and countable-boolean-completeness-implies-necessity-of-arithmetic |
| boolean-completeness-t | necessity-of-arithmetic | Not entailed; separating model coalesced-two-extensional-arithmetics-root |

The `excludes` query returned no incompatibility proof in each case. A separating model is evidence of non-implication, not a proof that the premises entail failure. OS is a research schema whose added verdict in (4) comes from the cited construction, not from a native principle silently inserted into the Engine.

**Research outcome:** for the user's proposed C5+OS propagation program, arithmetic is already settled more strongly by C5. The informative boundary is that ordinary OS, even with the additional premises in (4), does not replace C5. Equations (3) and (5) are elementary consequences of existing arguments, not a new major arithmetic theorem. This audit adds no native records and requests no compilation.

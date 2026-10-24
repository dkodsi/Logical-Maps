# Countable logical resources and the old Maximalism schema

Research note, OpenAI Codex, 22 October 2026. Original mathematical deductions from the cited recorded arithmetic lemmas; no claim of literature novelty, human checking, or formal verification. The reference theory throughout the old Maximalism schema remains the original finitary Classicism C.

## 1. Arithmetic input and source boundary

The repository's `results/possibility-and-necessity-of-arithmetic-incompatible.yaml` records Goodsell's argument, *Arithmetic is Necessary*, draft 5 June 2024, §6, Theorem 11 and note 14, pp. 24–26. Its input is that the arithmetical consequences of C+I_e form a consistent recursively enumerable extension of Peano arithmetic; the source's Lemma 1 supplies the arithmetic axioms. The definitions of N, zero, successor, Sum, Prod and I are in `topics/classicism/background.md`, lines 74–134. The repository's `writeups/countable-boolean-completeness-implies-necessity-of-arithmetic.md`, Lemmas 2–7, records the supporting elementary arithmetic facts, including I→I*.

The source PDF at https://philarchive.org/archive/GOOAIN returned 403 in this session. This note relies on the explicit local proof and definitions, not on a fresh inspection of that PDF. Its new contribution is the semantic standardness consequence and its infinitary application, not Goodsell's incompleteness argument.

By Gödel–Rosser incompleteness (mere consistency suffices), choose a finitary closed arithmetical sentence G for which both C+I_e+G and C+I_e+¬G are consistent. Old pure Max(C) therefore asserts both ◇(I_e∧G) and ◇(I_e∧¬G).

## 2. Every old-Max model needs a nonstandard numerical world

Consider a classical set-based action/Henkin model of C satisfying old pure Max at a world w. At some reachable world v, I_e holds and its arithmetic disagrees with the external standard natural numbers: choose the G-branch or the ¬G-branch opposite the actual external standard truth of G.

At such a world v, the local Fregean number domain cannot consist exactly of the denotations of the standard numerals 0,S0,SS0,... . If it did, I→I* would make those denotations pairwise distinct, and the PA recursion equations for Sum and Prod would determine their values on every member of that domain to be the ordinary sums and products. Induction on the finite syntax of arithmetical sentences would then identify its arithmetic with the standard structure, contrary to its value of G.

Thus every pure-Max model has a reachable I_e-world with at least one Fregean number not denoted by any external standard numeral. This is an external semantic statement. It is not the internal assertion that a natural number is infinite, and it does not say that the root's own numerical domain is nonstandard. The singleton profile-root construction can have exactly the standard numerals at its root.

A sharper consequence is extensional incompleteness at that world. Let S be the external set of standard-numeral denotations in D_nu(v), where nu=(et)t. No available property W of type nu→t can have extension exactly S at v. Such a W would contain zero and be closed under successor, so the defining impredicative induction clause for N would put every local natural number in W, contradicting the nonstandard number above. Consequently locally full extensions at this single higher type at every reachable world already rule out old pure Max. Full action models are a stronger special case; their failure of Max is also already apparent from necessary Actuality.

## 3. A concrete infinitary enrichment incompatible with old Max

Let C_omega be an enrichment of C allowing the countable disjunction

    W(n) := bigvee_{k<omega} (n = standard_numeral_k)

inside lambda abstraction, with its ordinary classical pointwise truth condition at every world. Retain ordinary higher-order quantification and beta conversion, so lambda n.W(n) supplies an available property. This is substantially less than requiring every semantic set of propositions to have a conjunction.

At every world, W contains zero and is closed under successor: each actual member equals some standard numeral, so its successor equals the next numeral. The impredicative definition of N gives N⊆W. Conversely each standard numeral is a number by finite induction, so W⊆N. Therefore the local natural numbers are exactly the external standard-numeral denotations at every world. At every I_e-world they are pairwise distinct, so the arithmetic there is standard by the PA recursion equations.

Section 2 now gives the contradiction: there is no C_omega model satisfying the OLD pure Max(C) schema. Equivalently, the two old-Max instances ◇(I_e∧G) and ◇(I_e∧¬G), together with this standard-numeral-range comprehension at each world, are already incompatible.

This is a semantic inconsistency result for the stated ordinary infinitary semantics. A syntactic version requires a specified infinitary calculus with adequate countable disjunction rules and the corresponding necessitation/theoremhood conventions. It is not a contradiction of finitary C or finitary Strong Possibility. If the Maximalism side condition is changed to consistency with C_omega, the old two instances are no longer both licensed; that is a different principle and is not refuted by this argument.

## 4. A separate stronger closure principle

If the language/semantics supplies conjunctions of every semantic set of propositions, true exactly when all conjuncts are true and with the usual meet property, conjoining all local truths produces a strongest truth. Imposing this at every world gives necessary Actuality, contradicted by old Max's possible non-Actuality. This simpler observation must not be confused with Section 3: ordinary countable infinitary syntax does not contain a conjunction of an arbitrary semantic family.

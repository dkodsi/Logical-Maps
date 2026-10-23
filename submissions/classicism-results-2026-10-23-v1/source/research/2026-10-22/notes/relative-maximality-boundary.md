# Relative Maximalism and necessary pure truth

Original argument, OpenAI Codex, 22 October 2026. Scratch research only; no database changes, human checking, or Lean verification claimed. The original map's Maximalism always refers to C. This note separately considers the proposed change of reference theory.

Let S be a consistent classical theory extending C, with the ordinary deduction property, and suppose S proves No Pure Contingency: P implies Box P for every closed pure sentence P. Define Max_S to contain Diamond P whenever S+P is syntactically consistent. Call S pure-complete if for each closed pure P, S proves P or proves not P.

**Boundary theorem.** S+Max_S is consistent if and only if S is pure-complete. In the pure-complete case every instance of Max_S is already a theorem of S.

If S is not pure-complete, choose pure P with neither P nor not P provable. The deduction property makes both S+P and S+not P consistent. Max_S therefore supplies Diamond P and Diamond not P. Excluded middle gives P or not P. In the first case No Pure Contingency gives Box P, contradicting Diamond not P; the second case is symmetric. Conversely, if S is pure-complete and S+P consistent, S cannot prove not P, so proves P. Reflexivity gives Diamond P. Thus adding Max_S adds only theorems.

This theorem is metatheoretic and deliberately distinguishes changing Maximalism's reference theory from the original Max_C. It uses no incompleteness theorem or claim that every logical extension is recursively axiomatized.

## A concrete infinite separation for the choice benchmark

Put T=C+Box Functional Choice, and let S add the map's Axioms of Infinity at both e and t. T proves No Pure Contingency, by the existing proved map results. The following closed pure sentence is independent of S in the ordinary semantic sense:

    UQV_e := exists R:et. forall X:et.
               Rigid(X) -> Diamond forall x:e. (Rx iff Xx).

The detailed internal development is in relational-universality-root.md. In a full constant-domain S5 hierarchy with individual set D and world set W, UQV_e holds exactly when there is a surjection W -> P(D): the extension of R at each world is its profile, and rigid X represent all subsets of D.

Work in ZFC. Take D=N. The full model with W=N satisfies S but falsifies UQV_e by Cantor's theorem. The full model with W=P(N) satisfies S and UQV_e, witnessed by the membership field R(n)(A) iff n is in A. All admitted function domains are full, identities are crisp, and choices exist at every point. Both individual and propositional domains are infinite. These two models also admit ordinary arbitrary set-indexed conjunctions with parameterized lambda abstraction.

Consequently replacing Max_C by Max_S does not make maximal possibility compatible with this benchmark. For this S, Max_S is inconsistent. The obstruction is the coexistence of necessary pure truth with independent pure structural choices, here whether all individual qualitative profiles are possible.

The result does not refute the original finitary Max_C by itself, and it does not say that every stronger reference theory remains incomplete. A chosen pure-complete extension can satisfy its own relative Maximalism, but then the maximality schema adds no content.

Inputs: the map's proved No Pure Contingency consequence of Box Functional Choice, and the full S5 constructions used in the companion scratch reports. The new boundary argument should have direct source_id misc if later recorded. No publication-novelty claim is made.

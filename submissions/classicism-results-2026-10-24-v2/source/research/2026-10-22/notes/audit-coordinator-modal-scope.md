# Coordinating audit of modal scope and theoremhood

22 October 2026, OpenAI Codex. New mathematical audit, no Lean/database edits.

I independently read the complete proposed proof and the three subaudits. The mathematical argument passes. This note spells out the potentially fragile interface between the C rules and the Boolean-algebra proof.

## Evaluation adjunction

For free parameters F:σt, x:σ, p:t, higher-order logic H proves

∀z(Fz→(z=x→p)) ↔ (Fx→p).

This theorem is uniform in its parameters; its proof does not use any optional premise. C therefore identifies the corresponding propositions, or equivalently permits replacing either side under the box. With the theorem identifying algebraic entailment at σt with necessary universal implication, this gives

F≤(λz(z=x→p)) ↔ Fx≤p.

The point x need only be an actual parameter. The universal on the left still ranges over all entities available where it is evaluated, so later new entities do not invalidate the equivalence: equality z=x forces the relevant value to be the transported x. No backwards transport of a witness is used.

## Join safety

For each actual pair x,y, the proof establishes Qx∧Qy≤(Rxy→x=y) in B_t. This is exactly □(Qx∧Qy∧Rxy→x=y). Generalizing x,y at the original evaluation point gives ∀xy□(...), not □∀xy(...). The latter stronger predicate is neither claimed nor needed.

Every use of membership CF, of chain comparability F≤G∨G≤F, and of the ambient LUB universal property is actual. Their consequences are algebraic inequalities, which themselves contain the required necessity. There is no inference from an actual fact CF to □CF.

## Guard safety

For arbitrary F,R,x,u,v let q:=∀z(Fz∧(Rxz∨Rzx)→z=x) and G(y):=Fy∨(y=x∧q). H proves the uniform formula

(Fu∧Fv∧Ruv→u=v) → (Gu∧Gv∧Ruv→u=v).

In a cross case, substitute u=x or v=x into Ruv and instantiate q at the old F-instance; both directions in q are necessary because R's symmetry is not a theorem. Hence by theorem necessitation and K, □oldSafety implies □newSafety. The actual premise Equiv(R) is used only to show that q is true and Fx false when x's actual cell is missed, thereby obtaining strictness. Neither q nor Equiv(R) is necessitated.

## Fixed-point interface

All of §5 is ordinary actual higher-order reasoning. Its only identities between order elements follow from antisymmetry or graph functionality. In particular, it uses actual coextension of graph images only to identify their unique LUB entities, and never substitutes coextensive predicates directly into an arbitrary intensional graph.

The shorthand C=I or D=I should be rendered C≡I or D≡I. This is an expository correction; the proof immediately explains the intended actual-coextension meaning.

## Conclusion

At the exact stated instances, C + BC_(σt) + RelChoice_(σt,σt) proves TC_σ. No additional condition was discovered by this audit. BC can be reduced to represented Boolean chain completeness, or even represented internally well-ordered completeness using the displayed f-chain argument.

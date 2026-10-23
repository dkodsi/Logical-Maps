# Coherent progressive operations and the remaining RC-only step

OpenAI Codex research argument, 22 October 2026. Ordinary mathematics only. No database or Lean changes. This note does not prove Relational Choice implies Transversal Choice. It strengthens the diagnosis beyond the ordinary cell-code warning: a specific extension-compatible progressive-operation principle is exactly equivalent to the transversal target, while every finite local coherence demand can already be met.

Fix an admitted type σ, put ρ=σt, and let R be an actual equivalence relation on σ. Write

    F≈G       iff ∀x(Fx↔Gx),
    F⊑G       iff ∀x(Fx→Gx),
    F⊏G       iff F⊑G ∧ ¬(F≈G),
    Part(F)   iff ∀x y(Fx∧Fy∧Rxy→x=y),
    Full(F)   iff ∀x∃y(Rxy∧Fy).

These are ACTUAL relations. In particular ⊑ is not the algebraic Boolean order. All constructions below are admitted lambda terms or relations, and all quantification is over the given Henkin domains.

## 1. Exact equivalence with coherent progress

The following are equivalent in C, for this R:

1. R has an admitted transversal T.
2. There is an admitted operation g:ρ→ρ such that, on Part,

       F≈G → gF≈gG,
       Part(gF),
       F⊑gF,
       ¬Full(F) → F⊏gF.

Only compatibility with ACTUAL coextension of the INPUTS and OUTPUTS is required. No identity gF=gG is asserted. Therefore the Actuality obstruction to operation-valued canonicalization does not rule out (2).

### Forward implication

Given an actual transversal T, define

    (gF)y := Fy ∨ (Ty ∧ ¬∃z(Ryz∧Fz)).

This is an admitted operation. Its actual extension depends only on the actual extension of F. If F is partial, it retains F and adds T's unique point precisely in each previously missed R-cell. Consequently gF is partial and full; it is strictly larger than F whenever F is nonfull. This uses only actual Equiv(R) and the actual transversal property of T.

### Reverse implication

Apply the independently audited preorder Bourbaki–Witt lemma in `/tmp/classicism-research/rc-alone-fixedpoint-obstruction.md`, §§6–7, with Part ordered by actual inclusion and equivalence ≈. Ordinary material union is a least upper bound modulo ≈ of every represented chain. The operation's graph is progressive and congruent modulo ≈, so the lemma gives F≈gF for some partial F. Strict progress then forces Full(F). The cited proof uses saturated f-chains on raw property codes and does not postulate quotient objects or canonical representatives.

The new point here is the exact special-operation equivalence and the finite local correction below; the general preorder fixed-point proof and safety normalization were independently obtained in the other lanes and are not new claims of this note.

## 2. Relation to the guarded algebraic operation

The separate note `rc-guarded-progressive-operation.md` shows that RC_(ρ,σ) gives an admitted operation g preserving

    P(F):=∀x y □(Fx∧Fy∧Rxy→x=y)

and satisfying F≤gF in the algebraic Boolean order, strictly at every nonfull P-input. It does not establish actual coextension compatibility.

C can move from arbitrary actual partial selectors into P without changing their actual extension. Define

    Pur_R(F)(y):=Fy ∧ ∀z(Fz∧(Ryz∨Rzy)→z=y).

A uniform H theorem gives P(Pur_R(F)); indeed the stronger outer-box necessary-partiality statement follows from the same theorem. If Part(F), then Pur_R(F)≈F. Thus composition with Pur_R extends any putative extension-compatible progress operation on P to actual partial selectors, provided compatibility is stated among P-inputs and progress is actual. The equivalence in §1 therefore pinpoints the needed coherence even when starting from the modal-safe poset.

Ordinary union followed by Pur_R represents a LUB MODULO ACTUAL COEXTENSION of a chain of P-extensions. It does not make an algebraic LUB: off the evaluation point, the family predicate can have different members, and Pur_R can turn membership off. That is why the new RC+BC proof still needs algebraic chain completeness, while a hypothetical coextension-compatible progress operation would not.

## 3. Every finite local coherence requirement is satisfiable

Suppose S is an actual functional selector on all nonempty ρ-predicates, totalized arbitrarily on the empty ones. Fix finitely many pairwise noncoextensive nonempty predicates F_1,…,F_n, and choose y_i∈F_i. No additional choice principle is needed for a fixed finite list. Define

    S*(A,y) :=
       [∨_{i=1}^n (A≈F_i ∧ y=y_i)]
       ∨ [∧_{i=1}^n ¬(A≈F_i) ∧ S(A,y)].

Then S* is again an actual total functional selector and is constant, as an individual-valued graph, on every coextension class of every F_i. It preserves S on all other classes. Corrections for distinct classes commute at the level of actual graph extension. The same conclusion for an internally Frege-finite family follows by the usual finite induction with the assertion that a coherent finite correction exists.

For the fixed R, the F_i may be cell codes. Thus finitely many entire families of mutually coextensive cell presentations can be normalized at once. Choosing an ENTIRE local selector graph rather than choosing an individual does not improve this finite existence claim: a local graph can still choose different representatives when selected from two different codes of the same cell.

More explicitly, if H(C,L) says that L is a correct global property chooser which is constant on all presentations of C, then every H-fiber is nonempty by the one-class correction above. RC at the higher output type selects L_C. For C≈D, the two selected graphs L_C and L_D are each internally coherent on the same class, but their constant values need not be the same. Evaluating each selected graph at its own input can therefore still disagree. The whole-local-graph strategy needs an additional cross-fiber agreement assertion; internal coherence inside each selected graph does not imply it.

## 4. What would finish this route

A proof from RC of the compatibility premise in §1, for ANY progressive operation with the other displayed properties, would finish RC⇒TC. The finite correction argument shows that no finite local incompatibility prevents this. Passing from those finite corrections to a single globally coherent admitted graph remains a substantive compactness/completion obligation. Neither ordinary C comprehension nor RC by itself has been shown here to supply that passage.

Conversely, a countermodel must permit every such finite correction and all RC witnesses, yet omit a coherent operation of §1. This is sharper than saying that a naïve chosen cell code can vary: every finite region can be repaired; the obstruction, if one exists, must survive arbitrary finite repairs and higher-type local graph selection.

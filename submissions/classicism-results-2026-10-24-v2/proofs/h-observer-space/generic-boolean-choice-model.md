# The generic Boolean Henkin model satisfies boxed Transversal Choice

25 October 2026. Ordinary mathematical argument by OpenAI Codex. Direct source: `misc`, this note, unpaginated.


## Result

The ordinary-ZFC generic Boolean Henkin construction indexed by `world_algebra.22` in the current v2 submission **cannot separate Relational Choice from Transversal Choice**. It satisfies every unboxed TC instance at every generic world, hence **boxed all-type TC**, including the individual type.

The decisive feature is an admitted rigid wellorder of every type domain. These wellorders are supplied by the ambient full ZFC hierarchy and elementarity. They are not derived here from RC. Their presence is compatible with the construction's atomlessness and failure of Plenitude/Functional Choice: least outputs can be selected by relations without an operation representing their generic-world values as object identities.

## 1. Fixed construction and source dependencies

Use exactly `structural-mixing-models.md`, §31, in the v2 source snapshot:

[Structural mixing models](../../source/research/2026-10-22/notes/structural-mixing-models.md).

Its setup is an atomless complete Boolean algebra B and the full finite relational hierarchy

    A_e = ℕ,       A_t = B,
    A_(α→β) = all functions A_α → A_β      (β ≠ e).

A sufficiently large regular H_θ contains the domains, Boolean operations and the required function spaces and powersets. A countable M ≺ H_θ contains these parameters. The interpreted domains are D_α = M ∩ A_α. Worlds are the specified M-generic ultrafilters on B∩M, with universal accessibility.

The source supplies, and this proof uses, these established construction facts:

* §31.1: ambient functions and witnesses of the relevant sizes lie in H_θ, and elementarity returns witnesses with M-parameters to M; application on D is closed and faithful.
* §31.2: the generic truth lemma identifies Boolean joins/meets of M-coded families with actual existential/universal quantification over D at every generic world. It is not a statement about arbitrary ultrafilters.
* §31.3: formula and lambda denotations with M-parameters are admitted; typed identity is literal, and the interpreted structure satisfies C.

The same quantifier and closure steps have independent earlier audits in `structural-world-representation.md`, §33, and `structural-algebraic-core.md`, §43, in the same v2 source directory. The present note adds the TC verdict; those sections are not cited as if they had already asserted it.

The current question is listed as unresolved in the v2 `CONJECTURES.md`, anchor `rc-tc`. This result excludes the particular generic Boolean candidate; it does not alter that overall status.

## 2. Every restricted domain has an admitted rigid external wellorder

Fix any admitted type α. Ordinary metatheoretic AC supplies a strict wellorder < of the full set A_α. Its Boolean characteristic relation

    w(a,b) = 1 if a<b, and 0 otherwise

belongs to the full relation domain A_(ααt), which the construction places in H_θ. There is no prohibited α→e operation here: w is a curried relation with final output t.

More explicitly, in H_θ there exists w∈A_(ααt) which is 0/1-valued and whose 1-extension wellorders A_α. This is a set-theoretic assertion with the hierarchy and Boolean parameters in M. The selected H_θ contains the relevant subsets of A_α: the source requires enough size for the corresponding full next-type function spaces and powersets. Thus the wellorder assertion is about genuine external well-foundedness, not only a weakened test against M-subsets. Elementarity supplies such a w in M.

Its interpretation on D_α is admitted. At every generic world, w(a,b) is true exactly when its value is 1; the comparison relation therefore remains the same restriction of <. Every restriction of a genuine wellorder to a subset is a genuine wellorder: a nonempty X⊆D_α is also a subset of A_α, and its <‑least element belongs to X⊆D_α. Consequently w externally wellorders D_α.

This argument is type-by-type. It asserts no object-level quantification over types and needs no admitted operation assembling all the wellorders. For each fixed type, the relation w is an admitted object and can be used as a parameter in comprehension.

It is stronger than merely having an internal order which M regards as well-founded. The external least-element fact below applies to every actual class at the chosen generic world, whether or not that actual class is an M-set in the ambient set theory.

## 3. Least members give a transversal at every generic world

Fix a generic world G and an admitted R∈D_(ααt) which is an equivalence relation **at G**. No necessary-equivalence premise is assumed. Using the w supplied above, form the admitted property

    T_R(y) := ∀z [w(z,y) → ¬R(y,z)].               (1)

Formula/lambda closure puts this property in D_(αt). The generic truth lemma makes (1) precisely its displayed ordinary universal condition over D_α at G. The full-domain Boolean meet used to construct its denotation is not silently evaluated by an arbitrary ultrafilter.

For any x∈D_α, its actual R-class

    C_x := {y∈D_α : R(x,y) is true at G}

is nonempty by reflexivity. Let y be its least member under the external restriction of w. If z<y and R(y,z), transitivity with R(x,y) puts z in C_x, contradicting minimality. Hence T_R(y) holds, and R(x,y) holds by construction.

For uniqueness, suppose y,z∈C_x both satisfy T_R. If y≠z, the strict wellorder makes either y<z or z<y. Equivalence of R makes R(y,z) and R(z,y) true at G. In the first case T_R(z) is contradicted; in the second case T_R(y) is contradicted. Thus y=z.

Therefore T_R contains exactly one member of every actual R-class. The argument applies to every R in the admitted relation domain, every admitted α, and every generic world G. It proves

    for each admitted α:  □ TC_α.

In particular it includes α=e. No selecting operation with output e, canonical representative operation on property codes, Actuality, BC or Plenitude has been used.

## 4. Exact RC witnesses are also visible from these orders

For clarity about the strength of choice in this candidate, the wellorders provide a direct uniform graph constructor, in addition to the source's maximal-antichain verification.

Fix admitted input/output types α,β and a default d∈D_β. Such a default exists in this construction: D_e contains 0, and every relational type has its admitted top element. Let w_β be the rigid wellorder of D_β. For every admitted relation U at (α,β), define

    S_U(x,y) :=
       [U(x,y) ∧ ∀z(w_β(z,y) → ¬U(x,z))]
       ∨ [¬∃z U(x,z) ∧ y=d].                      (2)

This is an admitted relation by the same lambda/quantifier closure. At every generic world and each x, a nonempty actual U-row has exactly one least element; an empty row receives exactly the default. Thus the **same graph S_U is necessarily total and functional**.

If U is serial at the evaluation world, the default clause is false there and S_U⊆U there. This proves the precise local, all-type RC conclusion, not merely the existence of some unrelated arbitrary selector. If U is necessarily serial, the containment holds at every world as well, giving the stated modalized relational-choice conclusion. The construction is uniform in U as a relation-valued lambda operation; it does not turn each chosen β-entity into the value of an admitted α→β operation. In particular β=e causes no typing problem.

The source's antichain proof in §31.4 remains valid and is preserved. Formula (2) is an additional direct verification using the wellorder codes whose existence was checked in §2.

## 5. Consequence for attempts to restrict the hierarchy

The generic model's full all-type RC is therefore not the missing part of an RC/TC separator: it also has the forbidden conclusion TC. Any construction retaining its ambient full ZFC hierarchy together with enough elementarity to return these wellorder codes inherits the same obstruction.

One cannot remove the transversal witnesses merely by taking an elementary substructure of this already interpreted C model. Each fixed-type TC sentence is an ordinary many-sorted sentence and is preserved by elementarity. More locally, any proposed restriction which retains the original truth of the existential formula asserting an R-transversal and a witness-extracting quantifier truth lemma must still admit an appropriate witness. This is a limitation of that truth-transfer method, not a general theorem about arbitrary Henkin substructures.

A substantially smaller code hierarchy might omit the relevant wellorders. Nothing here proves C+RC forces those wellorders, and no such omission has been shown incompatible with C+RC. But its proof of all-type RC and lambda/quantifier closure would need to be rebuilt: it cannot simply reuse the full elementary-hull construction while discarding witnesses that elementarity requires.

No further candidate construction or categorical transfer is asserted. In particular, projectivity of a code object alone does not supply the original C interpretation, and failure of a quotient arrow to split is not itself failure of an admitted transversal property. Those existing distinctions remain in force. The present bounded result is the new, fully specified **boxed TC verdict for the generic Boolean Henkin model**, with the exact construction choice responsible for it identified.

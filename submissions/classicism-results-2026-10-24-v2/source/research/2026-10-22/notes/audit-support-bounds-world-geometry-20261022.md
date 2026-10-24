# Independent audit: support bounds and world geometry

22 October 2026. OpenAI Codex ordinary mathematical audit, not human checking or formal verification. Audited `support-bounds-world-geometry-20261022.md` §§1–5, with the model clauses in `countable-support-choice-countermodel-20261022.md` §§1–4 and the earlier finite-support orbit arguments. Main database unchanged.

## Verdict and exact hypotheses

**PASS.** In ZFC, with A an infinite set, the full group Sym(A), a nonempty supported world G-set W, the trivial individual sort N, and precisely all functions/subsets having a support in the stated size ideal, the claimed classifications and tuple boundary hold. The cardinal lower bounds |A|≥κ or |A|≥μ⁺ must remain attached to their respective statements.

For worlds having finite support and |A|≥κ, IC holds at every type and world exactly in these cases:

| Allowed higher supports | Exact positive cases |
|---|---|
| <κ, with wholly trivial world action | Always |
| <μ⁺, μ infinite, with a moving world | Every world is strong |
| <κ, κ a regular limit including ω, with a moving world | Every world is strong and there are <κ world orbits |
| <κ, κ singular, with a moving world | None; IC_t fails |

Here strong means that the world stabilizer is the pointwise stabilizer of its finite least support. In the independent tuple family, with supports ≤μ and |A|≥μ⁺, W=A^{#λ} for λ≤μ satisfies all-type boxed IC exactly when λ<μ; at λ=μ even IC_t fails. No assertion about larger tuple lengths follows.

No repair of a mathematical conclusion is needed. One harmless proof-expansion is to choose the regular-limit reservoir bound μ also ≥|S|, where S supports F; this makes the reuse of the common-reservoir argument literal. The proof already works without that enlargement because S is still <κ.

## 1. Model closure and typing

For every infinite κ, finite unions of <κ supports remain <κ, including at singular κ. The same is true of supports ≤μ. Application sections, parameterized lambdas and the supported quantifier operation consequently remain admitted. Quantifier equivariance, rather than arbitrary external completeness of the proposition algebra, justifies the intersections used as quantifier values.

All singleton worlds are admitted because worlds themselves have allowed supports. A singleton world/argument-tuple relation has a support equal to the finite union of the chosen parameter supports, so all-type Atomicity holds. Literal W/empty identity gives C5. With W infinite, the original domains are infinite and the empty-supported characteristic predicate of the external numeral set establishes standard Frege numbers as in the companion construction. These preliminary arguments use no regularity assumption.

The atom set A is an external symmetry set, not the original individual sort. In particular one cannot treat a∈A as an original output object. The constructions correctly use the injective equivariant coding a↦p_a into D_t, and use p_B∈D_t for larger sets. The counterexample properties are genuine objects of type tt; the selector graph has type σt. An external map W→D_σ is only a device for constructing that graph, so no forbidden e-returning operation is introduced.

## 2. Common reservoir and the tuple boundary

Let S support F, |S|≤μ, choose R⊆A\S of size μ, and set K=S∪R. For a world w with strong support L_w of size <μ, the set R\L_w still has size μ. A support T of an eligible witness has size ≤μ. Therefore its portion outside S∪L_w can be injected into R\L_w while fixing S∪L_w pointwise.

This prescribed partial injection extends to a permutation: the removed domain and range have size ≤μ, whereas |A|≥μ⁺, so both remaining complements have cardinality |A|. The moved witness y has support inside K∪L_w, and remains eligible because the permutation fixes both F and w.

The crucial well-definedness calculation is

    Fix(K) ∩ Stab(w) = Fix(K∪L_w).

Thus a representative's stabilizer fixes y, and transporting y around its Fix(K)-orbit gives a well-defined equivariant selection. It does not matter how many orbits there are: ZFC allows one representative/witness choice per orbit, while every selected value uses the same reservoir K together with its current world's support. For the resulting external map c, the proposition {w:c(w)=z} has support K∪supp(z), and the whole original graph has support K. This proves exactly the globally singleton-fiber subproperty required by IC.

For W=A^{#λ}, the range of each ordered tuple is a strong support of size λ. Hence the positive argument covers all λ<μ, including λ=0 and infinite λ. At λ=μ, stars p_a={w:a∈ran(w)} have singleton supports and are distinct: a μ-element range can contain a while omitting b because |A|>μ. The empty-supported property F(p_a)=W\p_a has nonempty fibers.

Given any proposed selector support S of size ≤μ, choose a μ-tuple whose range includes S. Its eligible selected star p_a has a outside that range. There is a second outside atom b; the transposition (a b) fixes S and the tuple but moves the selected star. This contradicts uniqueness. The argument works even if |S|=μ and does not rely on any internal coordinate symmetry. The strict λ<μ boundary is therefore genuine.

## 3. Finite world supports and the special exact-support lemma

For the full permutation group, two finite supports have supporting intersection. Starting with one finite support and successively intersecting with the finitely many supports needed to remove its nonessential elements gives a finite least support L_w. Every world stabilizer preserves L_w setwise and contains Fix(L_w). Its quotient is therefore some H≤Sym(L_w), yielding the orbit presentation A^{#k}/H. Strongness is exactly H=1. This use of least supports concerns finite-supported worlds only.

On a fixed moving orbit of support size k>0, p_a={w:a∈L_w} is singleton-supported and nonempty. For B,C of size <κ, if a∈B\C, choose a k-element support containing a and avoiding C. A world in the orbit on that support distinguishes p_B from p_C. Thus B↦p_B is injective.

If an allowed support T of p_B omits a∈B, choose b outside B∪T. Such b exists even for singular κ: a finite union of <κ sets is <κ, and |A|≥κ. The transposition (a b) fixes T but takes p_B to the distinct p_((B\{a})∪{b}). Contradiction. Therefore

    T supports p_B and |T|<κ  ⇒  B⊆T.

This is a direct argument for this particular family. It neither asserts nor needs least supports for arbitrary objects with infinite allowed support. All subsequent lower bounds legitimately apply this special lemma.

## 4. Local symmetry obstruction

When H is nontrivial, some H-orbit I of coordinate positions has more than one member. The eligible stars at a world [a_1,…,a_k] are precisely those indexed by its I-coordinates. This is independent of the chosen tuple representative because I is H-invariant. The corresponding property is equivariant; outside the selected world orbit bottom supplies a default witness. Its values are admitted, and every world fiber is nonempty.

For a proposed selector support S<κ, choose all k coordinates fresh from S. A member of H moving the selected coordinate lifts to a finite permutation of those atoms which fixes S and the quotient world. It moves the chosen star, contradicting uniqueness. Thus every nonstrong orbit obstructs IC_t, regardless of the support bound κ. No nontrivial H can escape merely because higher-type supports are infinite.

## 5. Positive finite-world cases

If W is wholly trivial, D_t=P(W) has trivial action, and induction makes every higher domain full with trivial action. Ordinary external choice supplies all the required selectors. This exception is needed even when there are many world orbits.

For κ=μ⁺ with μ infinite, every finite strong support is strictly smaller than μ. The common-reservoir theorem applies to arbitrary witnesses and arbitrary numbers of world orbits. This proves the successor clause without an orbit-count bound.

For uncountable regular-limit κ, with θ<κ strong world orbits and a fixed S<κ, the Fix(S)-orbits on each finite tuple orbit are determined by the positions and values of its coordinates in S. Across all θ original orbits there are at most max(θ,|S|,ℵ₀)<κ such patterns. Choose an eligible witness on each. Regularity bounds the union of these <κ many <κ supports below κ. Choose an infinite μ<κ bounding their sizes and, if desired, |S|.

Every world then has an eligible witness with support size ≤μ, by transporting one of those representatives while fixing S. The reservoir argument applies to these witnesses even though the entire hierarchy may have objects with larger supports. Its output graph has support S∪R<κ. This is the precise local boundedness statement used; the argument does not erroneously replace the whole hierarchy by a ≤μ hierarchy.

At κ=ω, there are finitely many original world orbits and, for finite S, finitely many Fix(S)-orbits. Let r bound the finitely many chosen witness supports and k bound the finitely many world support sizes. A reservoir of r+k points always leaves at least r points outside any current world support. The same permutation-extension and stabilizer proof now yields a finite-supported selector. The source correctly treats this separately; the uncountable maximum-with-ℵ₀ estimate would not prove it.

## 6. Two independent size obstructions

**Regular limit with ≥κ orbits.** Choose κ orbit labels and cofinal positive sizes λ_i<κ, using unbounded finite sizes at κ=ω. At an i-labelled world w, require an output p_B with |B|=λ_i and B∩L_w=empty. The property is empty-supported: orbit labels are invariant, cardinality is preserved, and support-disjointness transports equivariantly. For fixed p_B its value is supported by B; bottom handles the unselected orbits. Positive λ_i avoid any collision with the bottom default.

Each fiber is nonempty. If a selector has support S, uniqueness implies that its chosen p_B at w is fixed by Fix(S∪L_w). This is an allowed support of p_B, so the exact-support lemma yields B⊆S∪L_w. Disjointness from L_w sharpens this to B⊆S. Choose λ_i>|S|. This is impossible. The disjointness clause is indispensable to the uniform ω argument because world support sizes can be unbounded finite.

**Singular κ with a moving orbit.** Let μ=cf(κ)<κ. The displayed construction of μ marked worlds is valid even when the local subgroup H is nontrivial: their least support sets differ, so their quotient worlds differ. Their supports have union S of size μ<κ. Fix(S) fixes every marked world, hence every subset of the marked family and its complement is an admitted proposition supported by S.

Assign cofinal required sizes κ_i<κ to those marked worlds and impose the same disjointness condition. The resulting F is S-supported: permutations fixing S fix each marked world and preserve its label, its finite support, the output cardinality and the disjointness rule. Its values are supported by S, including the bottom default outside the marked family.

For a selector supported by T<κ, the same uniqueness calculation gives B⊆T at marked world i. Choosing κ_i>|T| contradicts its required cardinality. The counterexample F is itself admitted; no union of cofinally large output supports is taken while constructing it. That failed union is instead exactly why a selector cannot exist.

## 7. Additional columns

The FC/RC classification also passes. In a moving finite-support orbit, two worlds with disjoint fresh supports admit a coordinate block-swap interchanging them while preserving their two-element proposition. The only eligible singleton-atom outputs are exchanged. For RC include the evaluation world's finite support among the points fixed before choosing the pair. This ensures preservation of actual truth as well as of the relation. If the action is trivial, fullness supplies ordinary FC and RC.

For uncountable κ and infinite W, countably many chosen singleton-world propositions have a common support of size ≤ℵ₀<κ. Shifting them and fixing all other propositions is an admitted injective nonsurjection of the entire proposition domain. This works for singular κ as well.

At κ=ω, infinitely many world orbits give infinitely many distinct invariant orbit propositions, hence an empty-supported shift. With finitely many world orbits, Fix(S) has finitely many world orbits for every finite S, so only finitely many propositions are fixed by Fix(S). For an injective operation f supported by S and any p supported by T, restriction of f to the finite Fix(S∪T)-fixed proposition set is an injection of that set into itself, hence onto it. Thus p has a preimage and f is globally surjective. This verifies the stated exact Dedekind criterion without an unsupported countable union of finite supports.

## 8. Scope guardrails

The result is a classification of this specified full supported hierarchy under Sym(A), in ZFC. It is not an equivalence valid in arbitrary C models. Infinite world supports are allowed in the separate reservoir/tuple theorem but excluded from the finite-world classification. Strongness and its strict support-size hypothesis cannot be dropped, and a regular-limit orbit bound cannot be carried over to successors. No purity or closed-term definability of stars, orbit labels or marked worlds is needed: the principles quantify over all admitted predicates.

The audit found no unfilled support, type, or cardinality step. Main records and formal statuses remain unchanged.

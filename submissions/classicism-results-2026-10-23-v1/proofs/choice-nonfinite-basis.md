# Functional Choice and ground model extraction

Original mathematical argument, direct source misc; unpaginated.

## 1. Exact conclusions and their boundaries

Keep the admitted types `e`, `t`, and `σ→τ` with relational output `τ≠e`. Set

    F = C + {□FC_(σ,τ) : σ admitted, τ relational},
    ρ₀=e,  ρ_(n+1)=ρ_n t,  A_n=ρ_(n+1),
    T_n = C + □Sel_(A_n).

Here `Sel_τ` asserts an operation selecting from every nonempty available property of τ-objects. All axioms and optional premises have fixed types; an infinite schema is not a finite axiom.

The reviewed negative assertions are:

1. For every finite set Δ of boxed FC instances there is a general C-model satisfying Δ and refuting a further boxed FC instance.
2. For every n there is a general one-world extensional C-model satisfying `□Sel_(A_n)` and refuting `□Sel_(A_(n+1))`.
3. Consequently F has no finite equivalent basis over C. Together with the positive retraction/cofinality argument, `T₀ ⊊ T₁ ⊊ …` and their union is F.

These conclusions do not say that no finite stronger theory entails F. They also do not establish the separate unconditional type-t diagonal/selector separation or a forcing construction over every restricted Henkin structure. Those are distinct questions identified at the end of the original note.

## 2. A direct first-order presentation in the original types

Let `E₂` be the following countable many-sorted first-order theory. There is a nonempty sort `D_σ` for each admitted original type, constants `0,1:D_t`, and an application function

    app_(σ,τ): D_(σ→τ) × D_σ → D_τ

for every admitted arrow. Require that `D_t` consists of exactly the distinct elements 0 and 1. Require function extensionality at every arrow type. Finally, for every first-order formula `φ(x₁,…,x_k,z̄)` in this sorted language, include

    ∀z̄ ∃P:D_(σ₁…σ_k t) ∀x₁…x_k
      (P[x₁,…,x_k]=1 ↔ φ(x₁,…,x_k,z̄)).

The parameter tuple is arbitrary and finite, and φ may quantify over any of the sorts. The case k=0 is allowed. This is a set of first-order sentences, not full external second-order comprehension. The language uses no `e→e` operation or object-language type quantifier.

**Interpretation lemma.** Every model of `E₂` yields an extensional general C-model with two proposition values.

To verify this, induct on the finite type tree. Extensionality identifies each arrow-sort element with its represented function on its input sort, whose values have already been interpreted. This identifies the entire hierarchy with a family of function domains without asserting that all external functions belong to them.

Comprehension represents every definable Boolean-valued relation. It also supplies abstractions with an arbitrary relational output: flatten that output as `τ=β₁…β_r t` and comprehend the Boolean relation on the original bound variables followed by the β-arguments. Repeated extensionality makes the resulting operation unique. In particular, a term `u:τ` depending on a variable `x:σ` has an abstraction represented by the relation

    λx y₁…y_r . u[y₁,…,y_r]=1.

This is an induction on term construction: the value relation for u is already first-order definable at the lambda step. Boolean constants, equality, and quantifier operations are represented by the same comprehension scheme. For example, the quantifier operation at σ is represented by `P ↦ 1` exactly when `∀x:D_σ, app(P,x)=1`.

Application, equality, and all quantifiers therefore have the usual nonempty-domain two-valued reading; beta and eta hold. H is sound. An H-theorem `p↔q` gives the same truth value under every assignment, so extensionality identifies its abstractions. This verifies C's Logical Equivalence rule with its theoremhood restriction. It does not apply that rule to an equivalence established from an optional Choice premise.

The defined box is `p=⊤`. Since `D_t={0,1}`, box and truth coincide in these particular models. No modal rule of C has been strengthened. The construction is a one-world subclass sufficient for separation, not a representation theorem for every C-model.

There is consequently a recursive translation `χ ↦ χ*` of each original sentence to a first-order sentence of `E₂`: define the value of each term by the preceding unique-value formulas, and require the resulting proposition to equal 1. This translation commutes with truth in the resulting general C-model.

## 3. Internal fullness and external satisfaction

Let `N` be a transitive inner model of ZF inside a forcing extension. In N define

    D_e=ω,  D_t={0,1},
    D_(σ→τ)={f∈N : N regards f as a function D_σ→D_τ}.

ZF recursion and Replacement collect the domains and application graphs for all finite type codes into a single set-coded sorted structure. The recursion is over actual finite syntax, not an assumed set of all sets.

This structure satisfies every axiom of `E₂`. For a fixed comprehension instance, all its quantifiers range over specified domain sets in N. Satisfaction for that fixed finite formula is definable in ZF. Separation forms its Boolean relation, and finite currying/Replacement produces the corresponding internal operation. Extensionality and the two-element truth domain are immediate.

The same first-order satisfaction claim holds externally in the forcing extension. Indeed, N and the extension have the same members of each particular domain set and the same application graphs. Induction on the first-order formula therefore preserves truth. This does not assert that the domain sets contain every external function, or that the internal powerset of a domain equals the extension's powerset.

This explicit absoluteness argument is the bridge from an internally full hierarchy to the externally general model. No selector supplied by the outer universe is added to its arrow sorts.

## 4. Ground extraction without a transitive-model hypothesis

The following ordinary forcing lemma isolates the last step.

**Extraction lemma.** Let T be a ground set of sentences in a ground countable first-order language. If a nonempty set forcing proves that a set-coded model of `check(T)` exists, then T is consistent in the ground ZFC metatheory and has a ground countable model.

**Proof.** Suppose instead that the ground contains a finite first-order contradiction proof π from T. This particular proof is a finite sequence of ground formulas. Its logical-rule instances, syntactic calculations, and finitely many facts asserting that an axiom belongs to T persist after forcing. Thus forcing also proves that π is a contradiction proof from `check(T)`. The first-order soundness theorem, applied inside the forcing extension to its proposed set-coded model, contradicts this. Equivalently, using the definable forcing relation throughout, the top condition would force false; the forcing clauses rule that out. Therefore no such ground proof exists. First-order completeness in ground ZFC gives a model of T, and the countable language permits a countable model. QED.

This argument does not assume the existence of a countable transitive model of ZFC or a generic set inside the ground universe. Generic-extension notation is a readable presentation of the forcing-relation calculation. It is also not an appeal to C's own completeness theorem.

Apply the lemma to

    T = E₂ ∪ {δ* : δ∈Δ} ∪ {(¬□Sel_τ)*}.

Sections 2–3 turn the extracted first-order model into the required general C-model. The interpretation preserves the displayed positive axioms and the displayed failure. It need not preserve the original domain cardinalities, literal ground domains, or standardness of internal number objects.

The same lemma accepts a non-effective set T. For the bounded-type-order strengthening in the original note, take the complete set of truths in the chosen ground bounded fragment as the positive sentence set. Include the true negation of each false fragment sentence. The extracted model then agrees on all closed sentences of that fragment, although it need not share the original domains or assignments.

## 5. The forcing hypotheses are actually met

For the finite-fragment construction choose a ground infinite cardinal μ large enough for the finitely many selected domains and their subtypes, put `κ=μ⁺`, and take

    P = Fn(κ×κ,2,<κ).

Regularity of κ makes P closed under descending chains shorter than κ. Ground Choice and the usual decision recursion imply that no new sequence of ground objects of length below κ is added. Thus every selected small function domain is preserved. Also, if `|D_(ρ_m)|=μ`, the domain `D_ν` for `ν=ρ_(m+1)` is preserved because its members are subsets of the size-μ domain, even though `|D_ν|=2^μ`. Fix a ground injection `b:κ→D_ν`.

Use all column permutations and the normal filter generated by stabilizers of finite sets of columns. The symmetric extension is a transitive ZF inner model N. If `a_i⊆κ` is the i-th generic column, the characteristic function `x_i:D_ν→2` of `b[a_i]` is an admitted internal object at `τ=νt`, with name supported by `{i}`. The invariant set `A={x_i:i<κ}` belongs to N. Distinct columns force distinct x_i; extending a condition at a fresh bit position proves this directly.

Suppose an internal selector c for all nonempty internal subsets of `D_τ` has a name supported by finite S. The set `C_S={x_i:i∉S}` has an invariant name under the same stabilizer. Strengthen a condition deciding that c is a function and that `c(C_S)=x_i` for some `i∉S`. Such a decision uses only functionhood and membership in a fixed graph, which are absolute from N to the full extension; it does not assert selection on the latter's larger powerset.

Choose `j∉S∪{i}` absent from the condition's columns. The transposition `(i j)` fixes the names of c and `C_S` and sends `x_i` to `x_j`. It sends the deciding condition p to a compatible condition: at i only p can have entries, at j only the transposed condition can have entries, and elsewhere they agree. The union still has size below κ. The forcing symmetry lemma now contradicts the forced distinction `x_i≠x_j`.

This proves failure of the selector in N. For any preserved output domain, however, its ground well-order is still available in N, and Replacement chooses the least member of every nonempty internal row, including newly present rows. This gives all required Δ instances. It gives the adjacent cutoff by choosing `μ=ℶ_n`: `D_(A_n)` is preserved and well-ordered, while the displayed obstruction occurs at `A_(n+1)`.

The forcing preservation and symmetric-ZF results used here are the standard imports recorded in the original note; their current author-hosted source was checked: Asaf Karagila, [Forcing and Symmetric Extensions](https://karagila.org/files/Forcing-2023.pdf), Theorem 4.16 and Corollary 4.17, printed pp.22–23; Symmetry Lemma 10.8, printed p.48; and Theorem 10.17, printed p.49. These supply the general forcing machinery. The typed coding and extraction application are the local arguments above and in the 22 October note.

## 7. Independent review of the fixed-input theorem

**Premises and target.** Work in ordinary ZFC metatheory and fix one admitted input type σ. Let `B=C+□Plenitude`, let `A` be C or B, and let Θ be a finite set of pure sentences true at a chosen world of the full ground Gallin hierarchy `E=W=ω`. Then

    A + Θ + {□FC_(σ,τ) : τ relational}

has no finite equivalent basis over `A+Θ`. Types are fixed externally; this is not one object-language type-quantified theorem. The target includes its extra base, and the assertion concerns equivalent bases, not finite stronger sufficient conditions. We verify the countermodel for each finite set Δ of the displayed FC instances.

**Cardinals and preservation.** In the ground hierarchy put `D_e=ω`, `D_t=P(ω)`, and take all functions at admitted arrows. Every fixed type domain is infinite and bounded in size by a finite beth number: relational types contain the constant functions obtained from distinct propositions, and function formation raises a common infinite bound λ to at most `2^λ`. Choose `μ=ℶ_m`, `m≥1`, bounding `D_σ`, the output domains of Δ, their subtypes, and every type in the fully elaborated formulas of Θ. Put `κ=μ⁺` and force with

    P = Fn(ω×κ×κ, 2, <κ).

κ is regular in the ZFC ground. Unions prove `<κ` closure, so P adds no sequences of ground elements of length below κ. Induction on the selected types therefore preserves their whole domains: a new function between unchanged domains of size at most μ would have a new graph contained in a ground set of size at most μ.

For `ρ₀=e`, `ρ_(r+1)=ρ_r t`, the ground sizes are `|D_(ρ_r)|=ℶ_r`, including `r=0`. Hence all domains through `ρ_m` are preserved. Crucially, `D_ν` for `ν=ρ_(m+1)` is also preserved: its members have graphs in `D_(ρ_m)×D_t`, a set of size μ, although `|D_ν|=2^μ` exceeds μ. Ground Choice supplies injections `h:ω→D_σ` and `b:κ→D_ν`. No cardinal arithmetic hypothesis such as GCH is used.

Use the group of all independent permutations of the κ columns in each block `i<ω`, and the normal filter generated by pointwise stabilizers of finite sets of columns `(i,j)`. Its hereditarily symmetric names give a transitive ZF model `V⊆N⊆V[G]`. Each preserved domain and its ground well-order belong to N. Form the full internal hierarchy there. Every formula, including one quantifying over enlarged high domains, has its abstraction and quantifier interpretation by Separation and Replacement in N. Thus this is externally a general C-model, not an externally full hierarchy. Its boxes express truth at every world in W.

At any world w, every serial internal relation whose output type occurs in Δ has a selector: choose the least permitted output in that preserved ground well-order and use Replacement. This handles new relations as well as old ones, and proves all of Δ. Induction on the elaborated formulas of Θ preserves their entire proposition denotations, since all domains and operations they use are unchanged. The hierarchy also satisfies B: for a total single-valued relation at w, Replacement gives its unique-output operation. Neither step assumes Choice in N.

**The unavailable selection.** Let `a_(i,j)⊆κ` be the generic column, and at `τ_*=νt` define `x_(i,j)` to take the rigid value W on `b[a_(i,j)]` and the empty proposition elsewhere. Its graph name is supported by `{(i,j)}`; preservation of `D_ν` makes it total. The family

    ⟨B_i : i<ω⟩,   B_i={x_(i,j):j<κ},

has an invariant hereditarily symmetric name. This asserts the internal block family, not an internal enumeration of each block. Distinct columns in one block force distinct objects, by assigning different bits at a fresh position.

Suppose N had a choice function c for this family. A name for c has finite support S, so choose a block i untouched by S. In the generic extension `c(i)=x_(i,j)` for some j. The ordinary truth lemma gives a condition p forcing this graph membership and functionhood. Those assertions about the fixed set c are absolute from N to `V[G]`. Choose `j'≠j` whose column in block i is absent from p; this is possible because p uses fewer than κ columns. The transposition of j and j' in block i fixes the name of c and the ground index i. It sends p to a compatible condition: the moved column was absent, and all other entries agree. Their common extension forces both outputs equal, contradicting their forced distinction. Conditions need not have finite support; only the name of c does.

In N define a rigid relation U from `D_σ` to `D_(τ_*)` by

    U(x,y)=W  iff  [∃i<ω (x=h(i) and y∈B_i)]
                       or [x∉ran(h) and y=bottom_(τ_*)],

and otherwise set its value to the empty proposition. Internal fullness admits U. Every row is nonempty, at every world. If an admitted operation f selected from U at even one world, Replacement in N would form the forbidden choice function `i↦f(h(i))`. Therefore `□¬FC_(σ,τ_*)` holds. The maps h and b are semantic set parameters; no original-language constants, type quantifiers, or individual-valued arrows have been introduced.

**Extraction and the finite-basis contradiction.** The two-valued theory `E₂` of §2 cannot retain this infinite proposition domain. Instead use the countable first-order auxiliary theory `H₀` and explicit Gallin translation in [positive-effective.md](../source/research/2026-10-22/notes/positive-effective.md), §§3–4. It has individual and world sorts, an ordinary two-valued truth sort, application, extensionality, and first-order definable comprehension. Its translated proposition sort is the world-to-truth function sort. That note proves the required interpretation bridge: §3 supplies relational-output abstractions by flattening outputs to the truth sort and using comprehension; §4.1 checks H at every world and then Logical Equivalence by extensionality. This is a proved construction from `H₀`, not an assumed completeness theorem for the original C.

The full auxiliary hierarchy inside N supplies a set-coded model; its translated original hierarchy is canonically isomorphic to the one above. Add to `H₀` the translations of every boxed Plenitude instance, Θ at the named evaluation world, Δ, and `□¬FC_(σ,τ_*)`. Satisfaction for this fixed structure is absolute as in §3. The extraction lemma of §4 gives a ground countable first-order model, whose Gallin interpretation preserves these sentences. This uses neither an assumed transitive set model of ZFC nor an assertion that arbitrary C-models have a Gallin representation.

If finite Γ were an equivalent basis over `A+Θ`, finite derivations of its members would use only finitely many fixed-input FC instances Δ. The extracted model satisfies `A+Θ+Δ`, hence Γ, while refuting another axiom of the claimed target. This contradicts equivalence and proves the stated theorem. Both boxed quantified Infinity axioms may be included in Θ: in the full ground hierarchy, the available predicate of Frege numeral objects makes finite cardinality exactly finite cardinality of the current extension; neither ω nor `P(ω)` is finite at any world. Including their fully elaborated formulas in the preserved fragment retains these actual axioms through extraction, without replacing them by mere external domain infinitude.

**Attribution and limit.** This independent proof review and its extraction explanation have direct source `misc`, this §7, unpaginated; the reviewed claim is [finite-functional-choice.md](../source/research/2026-10-22/followup/finite-functional-choice.md), §12. The imported forcing facts are Karagila, [*Lecture Notes: Forcing & Symmetric Extensions*](https://karagila.org/files/Forcing-2023.pdf), version updated 24 August 2026: Theorem 4.16 and Corollary 4.17, printed pp.22–23 (PDF pp.25–26); Symmetry Lemma 10.8, printed p.48 (PDF p.51); Definitions 10.12–10.16 and Theorem 10.17, printed pp.48–49 (PDF pp.51–52). No Dependent Choice preservation theorem is needed here. This closes the independent-review gap for the stated fixed-input theorem; it supplies neither uniformization in the proposed non-wellorderable real model nor preservation over arbitrary restricted Henkin structures, and is not a Lean certificate.

## 8. Independent review of the input-order hierarchy

**Exact claim.** Put `ord(e)=ord(t)=0` and `ord(σ→τ)=max(ord(σ)+1,ord(τ))`. Let

    I_n = C + {□FC_(σ,η) : ord(σ)≤n, η relational},   n≥0.

In ZFC metatheory the argument of [finite-functional-choice.md](../source/research/2026-10-22/followup/finite-functional-choice.md), §9, proves `I_n ⊊ I_(n+1)`, `⋃_n I_n=F`, and failure of finite axiomatizability of F over each I_n. Adjacent separating models can additionally satisfy both boxed quantified Infinity axioms. The unrestricted outputs are essential: preserving only small output well-orders would not verify I_n.

**Uniform preservation and Choice.** First use `D_e=ω`, `D_t={0,1}`. Structural induction gives `|D_σ|≤ℶ_(ord(σ))`: for an arrow of order k, the input bound is `ℶ_(k−1)`, the output bound is `ℶ_k`, and `(ℶ_k)^(ℶ_(k−1))=ℶ_k`. This covers all finite arities, not merely one tower of types. Set `μ=ℶ_n`, `κ=μ⁺`, and

    P = Fn(κ×κ×κ, 2, <κ).

The first coordinate indexes blocks. Independently permute columns within each block and use stabilizers of supports `S⊆κ×κ` of size `<κ`. The filter is normal and κ-complete because κ is regular. P is `<κ`-closed, and every condition has a permitted support consisting of its `<κ` columns. These are precisely the ZFC-ground hypotheses of Karagila's Proposition 13.4: the resulting symmetric model N satisfies `ZF+DC_<κ`. Finite supports from §7 would not give this conclusion.

Closure preserves all domains of order at most n by induction and the no-new-short-sequences argument, so each retains a ground well-order of cardinality at most μ. In N, `DC_<κ` gives a choice function for every well-ordered family of length below κ. For completeness, reindex by an infinite cardinal λ<κ and apply `DC_λ` to the tree of partial choices on initial segments of λ, including complete choices as maximal nodes. Unions give closure even when λ is singular. A maximal node is complete; a strictly increasing λ-chain has union of domain λ, since no ordinal below the initial ordinal λ contains λ distinct increasing domains. Finite families require only ZF.

Thus, for each internal serial relation with an input of order at most n, reindex its rows by the preserved ground enumeration and choose a member of each row. Replacement yields an admitted selecting operation. The output domain may be new, large, or non-wellorderable; no preservation or well-ordering of it is used. This proves the entire schema I_n. At n=0, `μ=ω` and `κ=ω₁`: e-input relations use countable choice from `DC_ω`, while t-input relations require only finite choice.

**Failure at the next input.** Put `ν=ρ_(n+1)`, `τ=νt`. The domain `D_ν` is preserved because its members are functions on the size-μ `D_(ρ_n)` into `{0,1}`, although its ground size is `2^μ`. Fix a ground injection `b:κ→D_ν`. Code each generic column as `x_(i,j)∈D_τ`, and form the invariant internal family `B_i={x_(i,j):j<κ}`, `i<κ`. Its enumerations by individual columns need not be internal.

If an internal choice function had support S of size `<κ`, some block i would be absent from S. A condition deciding its value `x_(i,j)` uses `<κ` columns, leaving a fresh j' in that block. The transposition of j and j' fixes the function name and i, while taking the condition to a compatible one with distinct forced output. This is the same name-and-condition contradiction as §7, with `<κ` in place of finite support. Hence the family has no choice function. Its rigid characteristic relation, with row B_i at b(i) and the singleton bottom row elsewhere, is serial but has no selecting operation. Therefore `□¬FC_(ν,τ)` holds, with `ord(ν)=n+1`. This proves strictness, including n=0. The preserved ground well-order of `D_ν` also gives `□Sel_ν`, even for newly present properties.

**Infinitely many individuals and propositions.** For the variant `E=W=ω`, replace the size bound by `|D_σ|≤ℶ_(ord(σ)+1)`. Define `π₀=t`, `π_(r+1)=π_r t`; then `ord(π_r)=r` and `|D_(π_r)|=ℶ_(r+1)`. Set `μ=ℶ_(n+1)`, `κ=μ⁺`, `ν=π_(n+1)`, and `τ=νt`. Closure preserves `D_t=P(ω)`, all input domains of order at most n, and `D_ν`, whose functions have size-μ input `D_(π_n)` and unchanged output `D_t`. Its size `2^μ` again supplies b. The same DC argument applies at each world; the rigid counterrelation fails at every world. For n=0 this uses `μ=ℶ₁` and failed input `ν=tt`, so proposition inputs are covered without assuming that the proposition domain is countable.

Both quantified Infinity claims hold directly inside N. At σ=e and σ=t, ZF recursion forms the sequence of Frege numeral objects; its range has a rigid characteristic predicate in the full internal hierarchy. That predicate is inductive, so `FiniteCardinality_σ` contains only numeral objects. Conversely, finite induction makes every numeral satisfy it at every world. Another finite induction identifies numeral k with the properties whose current extension has exactly k members. Neither `D_e=ω` nor `D_t=P^N(ω)` is finite in N; the latter contains all singleton subsets of ω. Thus the universal property has no finite cardinality at any world. This proves the two actual boxed quantified axioms without assuming preservation of every higher domain in their formulas.

**Extraction and relative finite bases.** For the one-world construction retain `E₂`, all translations of I_n, `□Sel_ν`, and `□¬FC_(ν,τ)` in §4's ground extraction. For the infinite-world version use the proved `H₀` interpretation identified in §7 and additionally retain both boxed Infinity sentences. These are countable first-order theories, so extracting the entire I_n schema presents no finiteness obstacle. The extracted models need not retain literal domains, cardinalities, or externally standard numerals; their translated sentences are retained.

For any finite extra set Δ of FC axioms, enlarge μ to `ℶ_m`, `m≥n`, bounding the output domains of Δ and their subtypes as well as the bounded-order inputs. The construction still satisfies I_n by DC and satisfies Δ by choosing least outputs in the preserved ground well-orders. It still fails the higher FC instance with input `ρ_(m+1)`. Finite derivations from F of a proposed finite basis over I_n use such a Δ, yielding the contradiction. Finally, every FC instance has finite input order and every proof is finite, proving `⋃_n I_n=F`.

**Sources and boundary.** This review has direct source `misc`, this §8, unpaginated. In addition to the forcing and symmetric-ZF references in §7, the exact added import is Karagila, [*Lecture Notes: Forcing & Symmetric Extensions*](https://karagila.org/files/Forcing-2023.pdf), Definition 13.1 and Proposition 13.4, printed p.62 (PDF p.65). Its closure convention is closure for chains of length less than κ. No chain-condition preservation theorem, determinacy assumption, or Choice inside N is substituted for that result. No gap was found in the stated §9 claims. This review does not certify the later input/output spectra or resolve either separate question retained in §6, and adds no Lean verification claim.

## 9. Audit conclusion on matched-stage incomparability

Independent review of [finite-functional-choice.md](../source/research/2026-10-22/followup/finite-functional-choice.md), §11, found no gap in its ordinary-ZFC conclusion: for every n≥0, I_n and T_n are incomparable. More precisely, T_n does not entail I₀, while I_n has a model refuting even `□FC_(A_n,A_n)`, hence refuting `□Sel_(A_n)`. These are one-world countermodels with `D_e=ω`, `D_t={0,1}`; no simultaneous proposition-Infinity claim is included.

For the first direction, countably many blocks and finite supports leave the preserved output domain `D_(A_n)` well-ordered, so T_n holds, while the invariant block family has no countable choice function and defeats an e-input FC instance. The fresh-block argument of §7 applies unchanged.

For the other direction, n≥1 uses `μ=ℶ_(n−1)`, `κ=μ⁺`, `λ=2^μ=ℶ_n`, and `δ=λ⁺`. The forcing `Fn(δ×δ×κ,2,<κ)` is isomorphic to `Add(κ,δ)`. Its chain condition is δ-c.c. because `κ^(<κ)≤(2^μ)^μ=λ`. The `<δ` support filter is δ-complete, and every condition has a support of size `<κ<δ`, satisfying the tenacity hypothesis used in the preservation proof. Consequently N satisfies `DC_<δ`. Closure at κ preserves all order-≤n input domains by structural induction on their input-sized sequences; their ground enumerations have lengths at most λ<δ, so the row-selection argument proves the entire I_n schema.

Here `D_ν`, `ν=ρ_n`, is preserved, but `D_τ`, `τ=νt=A_n`, need not be. The required ground injection `d:δ→D_τ^V` remains an injection into `D_τ^N`; no preservation of that whole output domain is assumed. The δ-block family has no choice function and, indexed through d, defeats diagonal FC. At n=0 the separate finite-condition c.c.c. construction has countable supports and gives DC; unchanged base domains suffice for I₀, while a ground injection `ω₁→P(ω)` supplies d. This endpoint uses no negative beth index.

Ground extraction uses E₂ and retains the whole countable I_n schema and the stated failure; the opposite model retains T_n and its failed e-input instance. The precise added imports are Karagila, [*Lecture Notes: Forcing & Symmetric Extensions*](https://karagila.org/files/Forcing-2023.pdf), Theorem 4.9, printed pp.21–22 (PDF pp.24–25), and Proposition 13.6, printed p.63 (PDF p.66). This audit conclusion has direct source `misc`, this §9, unpaginated. It records the existing proof's checked scope, not a new spectrum theorem or a formal verification claim.

## 10. Audit conclusion on diagonal Choice and the tower spectra

Independent review of [finite-functional-choice.md](../source/research/2026-10-22/followup/finite-functional-choice.md), §10, confirms the positive reductions and their use with the reviewed §9 countermodels. For relational α, the pure retraction `r_α:αt→α` satisfies `r_α(H_y)=y`. Applying `FC_(αt,αt)` to the serial relation requiring a haecceity of a member of a nonempty property, and composing with r_α, proves `Sel_α`. The separate transfer `FC_(αt,β)→FC_(α,β)` restricts a selector to haecceity inputs. Haecceity injectivity suffices, including α=e; no individual-valued operation is introduced. Boxed transfers come from necessitating the discharged C implications, not optional assumptions.

With `D_n=C+□FC_(A_n,A_n)`, this yields `D_n⊆T_n⊆D_(n+1)`. The reviewed block model satisfying T_n but failing `FC_(A_n,A_(n+1))` refutes D_(n+1) by the input transfer. Thus `D_n⊆T_n⊊D_(n+1)`, the D_n sequence is strictly increasing, and its union is F. Equality versus strictness of `D_n⊆T_n` is not settled in general. The stated `D₀⊊T₀` determinacy application remains conditional on the original `Con(ZF+AD_R)` hypothesis.

The exact one-world spectrum is also justified:

    FC_(ρ_r,ρ_s) holds iff r≤n or s≤n+1,    r≥0, s≥1.

The positive cases follow respectively from DC for the preserved input or from a preserved output well-order. For every remaining pair, repeated haecceity input transfer and pure retractions on relational outputs transfer Choice down to the failed corner `(ρ_(n+1),ρ_(n+2))`. The r=0 cases belong to the positive range and require no retraction to individuals. The infinite-world π-tower version has the same criterion for r,s≥0, at every world and with boxes. Its retractions have relational outputs throughout. These statements classify the displayed tower pairs; they do not classify arbitrary pairs solely by syntactic type order.

This audit conclusion has direct source `misc`, this §10, unpaginated; its local proof sources are the original note's §§5, 9, and 10 and the forcing imports checked above. No new mathematical resolution or formal verification status is asserted: in particular the negative spectra remain ordinary proof results, and neither separate question in §6 is resolved.

## 11. Review of the fixed-input corollaries

The five corollaries concluding [finite-functional-choice.md](../source/research/2026-10-22/followup/finite-functional-choice.md), §12, follow from the reviewed constructions. All theories below are deductively closed over the fixed C; finite bases consist of finitely many closed formulas at fixed types, not type schemata.

1. **I_n itself has no finite basis over C, for every n≥0.** If finite Γ were such a basis, its derivations from I_n would use finitely many FC instances Δ. In the countable-block, finite-support construction of §7, preserve the output domains of all these instances and their subtypes. Their ground well-orders give Δ regardless of the input types or newly present relations. The same construction, with fixed input e, defeats a further e-input FC instance, which belongs to I_n. The extracted model therefore satisfies Γ and fails I_n, a contradiction. This step does not claim that the countermodel satisfies the whole I_n schema.

2. **No finite set Γ of F-theorems entails any J_σ over C.** Positive cofinality gives an index m with `Γ⊆T_m`. Use §7's infinite-world construction, enlarging its cardinal cutoff to preserve both `D_(A_m)` and `D_σ`, with their subtypes. The retained ground well-order of `D_(A_m)` supplies `□Sel_(A_m)` for every available property, hence Γ. The countable block family still defeats a higher σ-input FC instance. Retain T_m and that failure in the H₀ extraction. The infinite-world choice is essential to cover σ=t: its proposition domain is infinite, unlike that of the one-world countermodels.

3. **Every intermediate theory `J_σ⊆T⊆F` has no finite basis over C.** A finite basis for T would consist of finitely many F-theorems entailing J_σ, contradicting item 2. This does not require a presentation of T by FC instances.

4. **Any nonempty collection of complete fixed-input packages has no finite basis over C.** Its deductive closure lies inside F and contains J_σ for any one input type in the collection, so item 3 applies. The collection may be infinite; nonemptiness supplies the fixed σ needed for that argument.

5. **F has no finite basis over finitely many complete fixed-input packages.** Let K be C plus those packages, and choose n bounding their finitely many input orders, so `K⊆I_n⊆F`. If finite Γ axiomatized F over K, finite derivations of Γ from F would use a finite set Δ of FC instances. Section 8 supplies a model of the entire I_n schema together with Δ while refuting F. It therefore satisfies K and Γ, contradicting the proposed equivalence. The empty collection is already the nonfinite-basis theorem over C.

This independent corollary review has direct source `misc`, this §11, unpaginated. Its proof inputs are the original note's §§5, 9, and 12, with the preservation, symmetry, and first-order extraction arguments checked in §§4–8 here. No additional forcing or determinacy result is invoked. These are ordinary proof conclusions, not new Lean certificates or resolutions of the separate questions in §6.

# Negative Choice hierarchy: audit and formalization boundary

22 October 2026. Independent rereading by the hierarchy author, not independent human checking. This audit preserves the original research and records its mathematical dependencies. It does not certify an independence theorem in Lean.

**Verdict.** The ordinary arguments for nonfinite axiomatizability and the bounded-type-order obstruction survive this audit in the stated ZFC metatheory. The decisive preservation, fresh-column, and first-order extraction steps are sound when spelled out below. The local Lean library does not currently supply the symmetric-forcing infrastructure needed for an end-to-end certificate. A fresh module submits the concrete fresh-column amalgamation calculation and an unconditional finite-support selection obstruction; neither is represented as the complete negative theorem.

## 1. Exact targets and significance

Keep the original relational grammar and C fixed. Let `F = C + {□FC_(σ,τ) : σ admitted, τ relational}`. Type variables here index schemas outside the object language. Let `ρ₀=e`, `ρ_(k+1)=ρ_k t`, and `A_k=ρ_(k+1)`. The targets are external metatheorems:

1. No finite set of fixed-type original sentences axiomatizes F over C.
2. For each `n≥1`, no set of original sentences whose fully elaborated types all have order at most n axiomatizes F over C, even if that set is infinite. Order is `ord(e)=ord(t)=0`, `ord(σ→τ)=max(ord(σ)+1,ord(τ))`.
3. The model theorem supporting both is stronger: at each n a general C-model agrees on every closed formula of that bounded-order fragment with the ground full extensional hierarchy on `e=ω,t=2`, yet fails `□Sel_(ρ_(n+1))`.

The first rules out every alternative finite equivalent axiom package, not merely a finite list of Choice instances. The second rules out replacing unbounded type complexity by any number of axioms at one bounded order. Neither rules out finite sufficient conditions with additional restrictions, and neither is about finitely many unbounded type schemas. The countermodels can be one-world extensional structures: their obstruction concerns internal higher-order selection rather than a need for modal contingency.

These are substantial negative answers. The difficult ingredients are preservation of an entire typed hierarchy, construction of a choiceless internal universe, and extraction of a genuine general model. They do not follow from counting the instances of a schema. No novelty-in-the-literature claim is made.

## 2. Preservation audit

**Finite domain list — passes.** Work in a ZFC ground V and bound the cardinalities of the selected input/output types and their subtypes by `μ=ℶ_m`. Let `κ=μ⁺` and use `P=Fn(κ×κ,2,<κ)`. Regularity of κ is used when taking unions of descending chains of length below κ. The closure-to-distributivity argument takes place in V, where Choice is available. It is not an assertion that closure alone has the same consequences in a choiceless universe.

The forcing adds no functions from any fixed ground set of size below κ into any fixed ground set. For an arrow between already preserved small domains, the graph is a subset of their small ground product; hence it is old. Induction on the actual type tree therefore preserves every selected domain. It also preserves `D_ν` for `ν=ρ_(m+1)`, although that domain has size `2^μ`: its members are functions from the preserved size-μ domain `D_(ρ_m)` into 2. Preserving the members does not require preserving all subsets of `D_ν`. A ground injection `b:κ→D_ν` exists by Cantor and ground Choice; no GCH is required.

**Uniform bounded order — passes, and is genuinely sharper.** In the ground full hierarchy,

`|D_σ| ≤ ℶ_(ord σ)`.

For an arrow of order k, k≥1, its input has size at most `ℶ_(k−1)` and its output at most `ℶ_k`; the function space is bounded by `(ℶ_k)^(ℶ_(k−1))=ℶ_k`. This is a structural induction, so arbitrarily large finite arities cause no exception.

For order bound n set `μ=ℶ_(n−1)` and `κ=μ⁺`. At each arrow of order at most n, the input has size below κ. Once the output domain is preserved by structural induction, a function on that input is a short sequence of elements of a ground set. It is therefore old, **regardless of the size of the output domain**. This preserves all domains of order at most n, not just a finite list. The argument is a uniform recursion over the finite type codes, not an infinite intersection of support subgroups.

The result applies to the intermediate symmetric universe because `V⊆N⊆V[G]`: an internal function in N is already a function in V[G], and all old functions lie in N. Every ground well-order of a preserved domain remains a well-order in N via its ground isomorphism with an ordinal. This justifies choosing from even newly present internal subsets of that domain.

**Formula preservation — passes with full elaboration.** Include the types of logical constants, intermediate application terms, lambda terms, and binders. Common domains imply common application and literal equality. Each relevant Boolean or quantifier operation has its unchanged graph on those domains. Induction on terms and formulas gives equality of denotations under common assignments. There is no need to preserve a type absent from the elaborated formula. Order-zero closed formulas are covered by the order-one case; negation does not raise a bound n≥1.

## 3. Symmetric obstruction audit

Use column permutations and the normal filter generated by pointwise stabilizers of finite sets of columns. Normality follows from conjugating a finite support; binary intersections correspond to finite unions. The standard symmetric-extension theorem yields a transitive `N⊨ZF`. It does not require the filter to be κ-complete or every condition to have finite support.

The column names `a_i⊆κ` have supports `{i}`. At `τ=νt`, encode them by the characteristic functions `x_i` of `b[a_i]⊆D_ν`. Their graph names use ground arguments and the two ground truth values. Thus their hereditary symmetry is explicit; arbitrary intersections of stabilizers are unnecessary. The invariant set `A={x_i:i<κ}` is in N, and distinct columns yield distinct x_i. Preserving `D_ν` ensures the named graphs remain total on the required domain.

Suppose an internal selector c for subsets of `D_τ` has name supported by finite S. Let `C_S=A\{x_s:s∈S}`. Its canonical name is fixed by every permutation fixing S, and its actual chosen value is some `x_i` with i outside S. In V[G], c is still a function and `(C_S,x_i)` still belongs to its graph. Functionhood and membership of this fixed set graph are absolute from the transitive N. The ordinary forcing truth lemma can consequently supply a condition p forcing these two facts.

Choose j outside S, i, and the column projection of `dom(p)`. That projection has size below κ, so such a j exists in the ground. The transposition `(i j)` fixes both parameter names c and `C_S`. Symmetry makes the transposed condition force the chosen value to be `x_j`. The two conditions are compatible: at column i the transposed assignment is empty; at column j the original assignment is empty; elsewhere they agree. Their union still has size below κ. A common extension would force equality of two forced-distinct x-values, a contradiction.

Two possible errors are avoided here. The permutations act on forcing names, **not** as nontrivial automorphisms of the transitive membership structure N. Also, the truth lemma is used for functionhood and graph membership; it does not assert that c chooses from the larger external powerset in V[G]. The selector domain remains the fixed internal powerset `P^N(D_τ)`.

The new `ChoiceFreshColumns.lean` proves the partial-assignment amalgamation directly for arbitrary column, row, and value types. It separately proves the familiar nominal obstruction on natural-number atoms. The latter is an unconditional ordinary metatheorem but is **not** a substitute for the forcing-name argument just audited.

## 4. Full typed semantics and Henkin extraction audit

**Closure at every type — passes.** Inside N use its full function spaces at the admitted arrow types. For each formula, restricted-domain satisfaction is definable in ZF. Separation and Replacement provide lambda abstraction, Boolean operations, and quantifier operations, including formulas quantifying over domains above the preserved fragment. Nonempty relational domains have constant-bottom witnesses. The hierarchy is internally full, but externally generally Henkin. It must not be replaced by ambient Lean function spaces: those would introduce external selection operations absent from N.

H is sound with ordinary equality and beta/eta. Every H-theorem of equivalence holds under every assignment, so the abstractions have identical graphs. That verifies C's actual Logical Equivalence restriction. It does not apply LE to an equivalence derived from optional Choice assumptions. The one-world model has two truth values, making boxes collapse semantically.

**Extraction without a countable-transitive-ground assumption — passes, with the following formal reading.** Let T be the ground many-sorted first-order theory consisting of the auxiliary `H₀` comprehension/extensionality theory, a named world, the singleton-world sentence, the translated desired ground axioms, and the translated selector failure. All of these are a ground set of finite sentence codes. For the bounded-order result take as desired axioms `Σ_n`, the complete set of bounded-order truths of the ground hierarchy. It need not be computably enumerable.

1. In the forcing argument, N's internally full auxiliary hierarchy is a **set-coded** model of T. ZF Replacement forms its countable family of type domains and application operations. The auxiliary sorts e,s,o use `ω,{*},2`; comprehension for formulas mentioning arbitrary sorts follows from Separation and Replacement in N. The original types are interpreted by `e*=e`, `t*=s→o`, and the arrow translation.
2. If a finite first-order contradiction proof from T existed in V, its finite code and all its ground axiom-membership facts would remain valid after forcing. Soundness would contradict the forced model of the checked ground theory T. Equivalently, the forcing relation and the forced soundness argument rule out that ground proof. This is the conventional syntactic use of forcing, not an appeal to the existence of a V-generic set inside V.
3. Thus T is consistent in the ground ZFC metatheory. Ordinary first-order completeness gives a ground Henkin model of T; it does not require T to be effective. In a countable language the model may be taken countable. Extensionality identifies each arrow-sort element with its represented function; comprehension supplies the definable Boolean, quantifier, and lambda operations. The Gallin translation then yields a general C-model, and the singleton-world axiom retains exactly one world.
4. The translated positive axioms and the translated failure survive this construction. **External sameness of preserved domains does not.** For the bounded-order theorem the ground extracted model agrees with the original full model on closed fragment sentences. Since Σ_n includes the true negation of each false fragment sentence, the agreement is two-sided. It need not have the original domains, their cardinalities, common assignments with V, or standard number objects.

This supplies exactly the model used in the nonaxiomatizability conclusion. For a hypothetical finite equivalent basis Γ, finite proofs of its members use finitely many FC instances Δ. The separating model satisfies Δ and hence Γ while failing F. For a hypothetical bounded-order basis Γ, the ground full model makes every member true, so Γ⊆Σ_n; the extracted model satisfies Γ while failing F. Both contradictions keep C fixed and use fixed-type optional formulas.

No defect was found in these steps of §§1–4, 6 and 8 of the original note. This verdict does not audit every later input hierarchy or the separate proposed type-t uniformization construction.

## 5. Available infrastructure and the major obstacle

| Component | Local evidence and boundary |
|---|---|
| Actual C syntax, type order, finite proof support | `Syntax/Types.lean`, `Syntax/Derivation.lean`, `Syntax/ChoiceHierarchyTypes.lean`, `Syntax/FiniteChoiceBasis.lean`; these support the final metatheoretic reduction. |
| Model soundness and model theories | `Semantics/Action*.lean`, `Intensional*.lean`, `IntensionalTheory.lean`; `theory_complete` makes the theory of an existing model complete. It is not a theorem constructing a model of every consistent theory. |
| Existing “symmetric” models | `Semantics/Symmetric.lean`, `Models/SymmetricIdeal.lean`, `Models/SymmetricFull.lean` use Dorr's category/intension pinning construction. They do not provide forcing names, a forcing truth lemma, or a symmetric ZF extension. |
| Boolean-valued semantics | `Semantics/BooleanValued*.lean` interpret higher-order C over a complete Boolean algebra with full external function types and crisp equality. They do not construct Boolean-valued **set theory**, hereditary symmetric names, or the restricted internal arrow domains. |
| Local dependencies | No `.lake/packages/mathlib` checkout or separate forcing/ZF source library was found in the configured project or the narrow temporary-runtime inventory. The manifest pins Mathlib v4.33.1; the serial checker currently accepts local modules plus Init/Lean/Std. This is a local availability finding, not a claim that no such work exists elsewhere. |

Upstream Mathlib's `ZFSet` is a useful construction of sets, but its documented `choice` theorem derives Choice from Lean's ambient Choice; using that full universe would not construct the required choiceless N. Flypitch is a substantial prior formalization of forcing and CH independence, but the inspected project pins Lean 3.4.2 and an old Mathlib revision. Neither source is an import-ready symmetric-extension implementation for this project. No dependencies were installed or ported in this pass.

The major obstacle is therefore foundational, not an unfinished proposition-level implication. An end-to-end proof needs a represented internal set universe, forcing semantics with automorphisms, the hereditary-symmetry construction and ZF closure, followed by a model-interpretation/extraction bridge. Assuming that this construction exists under a `finiteFragmentGap` parameter would merely repeat the earlier conditional reduction. That was not done.

## 6. Concrete dependency roadmap and next certificate

The strongest next **semantic** target is the first adjacent cutoff, before the uniform family:

> In the ordinary metatheory, construct a general one-world C-model with `□Sel_(et)` and `¬□Sel_((et)t)`, using `Fn(ω₁×ω₁,2,<ω₁)` and finite column supports. No finite-fragment-separation or transitive-model-existence premise is to be added.

This is new relative to the submitted formal certificates, not a claim of new mathematics. It isolates the entire hard mechanism with `μ=ω`, while avoiding the extra uniform cardinal induction. It also gives the same model all boxed Plenitude instances, by internal Replacement. It is a meaningful first separation, but **alone does not prove nonfinite axiomatizability**.

An implementation should proceed in these dependency layers, each with an explicit theorem and no assumed output of a later layer:

1. **Internal set model and forcing.** Represent names, valuation or forcing truth, check names, partial-function forcing order, chain closure, dense decisions, and automorphism action. Prove short-sequence preservation in the ground. The submitted fresh-column merge supplies the pointwise compatibility calculation; cardinal bounds and forcing statements remain to be proved.
2. **Symmetric universe.** Define the finite-support normal filter and hereditary symmetric names; prove the inner interpretation satisfies the ZF operations required for the hierarchy. Prove the column graph names and A have the stated supports and forced distinctness. Establish the no-selector contradiction through forcing symmetry. A direct nominal argument on evaluated sets is not sufficient.
3. **Typed interpretation.** Construct every internal type domain, application, equality, lambda and quantifier operations. Prove a semantic satisfaction lemma for actual C syntax and the selector/FC interpretation. Only then invoke the existing soundness or model-theory interface.
4. **Ground extraction or a direct syntactic alternative.** Formalize the auxiliary sorted theory, its translation, first-order proof absoluteness under forcing, and completeness, or prove the required C nonderivability directly in represented forcing semantics. Do not demand a countable transitive model as an extra hypothesis merely to simplify evaluation.
5. **Uniform extension.** Prove the order-based cardinal bound and no-new-short-sequence preservation by structural induction. Define the fully elaborated bounded-order formula fragment and prove satisfaction invariance. Combine the resulting separating models with the already submitted finite-support metatheorem.

The first four layers are a substantial formalization project. In the present dependency state, stopping at this obstacle is preferable to producing an “end-to-end” theorem whose assumptions contain the countermodel construction. The isolated calculation below is complete as a proof submission and reusable once the infrastructure exists.

## 7. New submission and evidence

Fresh file: `topics/classicism/lean/Classicism/Models/ChoiceFreshColumns.lean`.

- `fresh_amalgam`: explicitly constructs a common extension of a partial column assignment and its transposition with an unused column. `merge_domain` proves its domain is precisely the union, leaving no implicit pointwise consistency assumption.
- `no_finitely_supported_selector`: proves there is no selector on predicates on natural-number atoms equivariant under all transpositions outside a finite support. The witness to failure is the complement of that support; the fresh atom is computed by a finite-list bound.
- These are unconditional ordinary metatheorems with built-in Lean foundations, not translated C derivations and not a model of the whole typed language. No new mathematical axiom, `sorry`, finite-gap premise, forcing truth premise, or model-existence premise occurs in the submission.

**READY FOR INTEGRATION; now frozen.** SHA-256: `1ab33f4ad5c9e969a5a157a0b903b6a3b633f533addd31432798ce8173ae5a0e`.

The sole build owner should run, serially:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.ChoiceFreshColumns --timeout 120
```

No compiler, Lake, or dependency-fetch command was run by this author. The module imports only Init. Repository validation passes; that does not check the Lean proofs. Compilation and axiom inspection remain the integrator's responsibility. A successful check certifies only the two ordinary metatheorems above.

The last inspected hierarchy check manifest was `checks/20261023T025339186991Z.json`: the first five hierarchy modules, including finite proof support and type bounds, had successful cached checks; `ChoiceHierarchyPlenitude` failed and the five-module positive realization/diagonal/retraction chain was consequently incomplete. This is a timestamped observation, not a request to change frozen files or a current guarantee about later integration work. No negative hierarchy theorem was certified there.

The original `followup/finite-functional-choice.md` hash remains `d6001822eef38694d28044f0c5c9dbdd7baa71c7215b97c5565373cfcb7a6876`. Existing frozen submissions, YAML and generated statements were preserved. This audit and the fresh module are the only substantive additions in this continuation.

## Sources and locators

- Local original: [finite-functional-choice.md](../followup/finite-functional-choice.md), §§1–4, 5 strictness, 6, 8; [positive-effective.md](../notes/positive-effective.md), §§3–4 for auxiliary Henkin syntax and Gallin translation. Unpaginated. New audit and proof submission: misc.
- Standard forcing infrastructure checked against Asaf Karagila, [*Forcing & Symmetric Extensions*](https://karagila.org/files/Forcing-2023.pdf), updated 24 August 2026: Theorem 2.20, printed p.9; Theorem 4.16 and Corollary 4.17, pp.22–23; Lemma 10.8, p.48; Theorem 10.17, p.49. These support the imported general forcing facts, not attribution of the Choice hierarchy theorem to that source.
- Upstream library boundary: [Mathlib.SetTheory.ZFC.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/ZFC/Basic.html), module documentation and `ZFSet.choice`; [Flypitch manifest](https://github.com/flypitch/flypitch/blob/master/leanpkg.toml), `lean_version` and pinned dependency. Checked 22 October 2026.

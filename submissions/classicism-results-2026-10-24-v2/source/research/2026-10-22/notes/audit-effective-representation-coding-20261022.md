# Audit of effective Gallin representation and equality-only reconstruction

OpenAI Codex (GPT-6), 22 October 2026. Ordinary mathematics, no human-check or Lean claim. Main records unchanged. This audits §§5–6 of `effective-gallin-representation-audit-20261022.md` and investigates removal of its explicit truth-map input.

## 1. Verdict and two coding conditions

**PASS:** the inherited numbering in §5 gives the claimed two-way computation of canonical operational data and the constructed auxiliary complete diagram. The FC transfer in §6 is sound without a hidden use of Plenitude or Actuality to freeze the selected relation.

Two conditions should be stated explicitly:

* Source element numbers must be injective, or must be fixed canonical representatives. If an entity has several aliases and the source term interpreter chooses aliases in an arbitrary uncomputable pattern, its literal output graph can carry information absent from the mathematical structure. Normalize such a quotient presentation before an exact-degree claim.
* “Degree of the code” means the canonical join of domain membership, identity, term-value graphs and truth data, not an arbitrary oracle computing those functions, a program file with irrelevant padding, or a package carrying extra uncomputable bits.

These are coding conditions, not additional mathematical principles. The proposed representation theorem concerns operational diagrams and should not promise to preserve gratuitous information.

## 2. Why inherited numbering works

The translation T(e)=e, T(t)=s→o, T(στ)=T(σ)→T(τ) is syntactically injective with decidable image. In particular no T(σ) is the bare world sort s, so s→o cannot ambiguously be parsed as the translation of an original nonbase arrow. The inverse type parser is effective.

At a translated sort T(σ), label j_σ(a) by the original σ-number a. At other target sorts use tagged ambient-source core labels. The conversion from a translated label to its ambient-source representative is j_σ, and the reverse conversion is k_σ. For original e these are external identity substitution, not terms of the forbidden type e→e.

With this numbering, target application and each formula query are computable from the original operational code using the explicit conversion functions. Conversely the target complete diagram decides the unique value of the auxiliary translation of every original term under a numbered assignment. Application is named; lambda and quantifier values are specified by effective first-order defining formulas. Comprehension gives existence and extensionality gives uniqueness. Search the target output sort for that unique value. Because its inherited label is the original source number, this recovers the original term-value graph literally, not just up to an unspecified renumbering.

Domain membership must be part of the presented diagram convention. Equivalently, in a diagram coding with potential numeral-names at every sort, membership is recovered by whether the reflexive equality for that name is an admissible true diagram sentence. This convention must distinguish invalid names from legitimate false formulas.

The designated truth valuation is recovered using the target constant w₀ and evaluation of j_t(p) there. If w₀ was obtained from the source true atom, this is the exact original truth map. Arbitrary renumberings or arbitrary changes of w₀ support weaker conclusions and are treated below.

## 3. Direct FC transfer: explicit extension and mask

Let R be an auxiliary relation from α to β, with β ending in o, which is serial on the core domains. Let A(x) and B(y) be the original core predicates H_α and H_β, and take a fixed core value y₀ (bottom works when β is relational). The original relation

    U(x,y):=[A(x)∧B(y)∧R(x,y)]∨[¬A(x)∧y=y₀]

is serial over the full original domain r(α). The output r(β) is relational, so original Functional Choice legitimately supplies f:r(α)→r(β). For actual core inputs x, f(x) is already a core β-object and R(x,f(x)) holds.

Write β=β₁…β_no, with n possibly zero. Define

    g(x)[z₁,…,z_n]
       := A(x) ∧ (AND_i H_βi(z_i)) ∧ f(x)[z₁,…,z_n].

This is an admitted original lambda term. At actual core x, the support condition on f(x) makes g(x)=f(x) as an entity: masking does not merely preserve its actual extension, because the core output already vanishes off its rigid support. At a noncore input, A(x) is the literal bottom proposition; therefore g(x) is bottom. All membership masks are bivalent under C5.

At supported arguments the value f(x)[z̄] is bivalent because f(x) lies in H_β. At unsupported tuples the displayed matrix is bottom. Thus every actual tuple has a bivalent matrix value. C5 supplies BF at all argument types, collecting these pointwise stability facts into rigidity of g. Its displayed masks give support, so g belongs to H_(αβ), and on the core it chooses an R-output.

This proves the auxiliary relational-output choice schema. It does not require an auxiliary function with output e or s, and the claim should retain that restriction. The selector f itself need not have been rigid before masking. Only its values on core inputs and their support are used.

## 4. Uniformly find an atom from equality and term interpretation

Assume B=C+□Plenitude, equivalently C5+Atomicity_t. Let K be a code giving canonical numbered domains, equality and parameterized term interpretation, but no truth map.

Under C5, each identity proposition is either ⊤ or ⊥ by NI and ND. Connectives preserve this, and BF makes quantifiers of bivalent matrices bivalent. In particular Atom_t(a) is bivalent for each actual proposition a. Therefore K can decide atomhood by computing the denotation of Atom_t(a) and comparing it to ⊤.

Enumerate the proposition domain and select the first a for which that comparison succeeds. Atomicity and ⊤≠⊥ guarantee termination. This procedure needs no prior access to the model's actual valuation.

Define a new valuation on the unchanged original operational structure by

    val_a(p)=1 ⇔ a≤p ⇔ a∨p=p.

It is K-computable. Atomhood makes it a Boolean truth valuation. C5 makes identities rigid and makes an atom a strong world. For every available predicate X of any original type,

    a≤∀x Xx ⇔ ∀x(a≤Xx),

using modal universal instantiation forward and BF backward. Thus val_a has the required quantifier behavior; the existential clause follows by negation. The original equality, application, beta/eta and term interpretation remain unchanged. This directly gives a BBK valuation at a.

## 5. Why the new pointed model is isomorphic to the old one

B supplies exactly one original true atom w₀. The recorded atom-transposition argument in `writeups/c5-and-atomicity-imply-no-pure-contingency.md`, §§3–4, gives an involution F_t swapping a and w₀, extended by conjugation to every relational type and by the external identity map on individuals. If a=w₀ use the identity automorphism. The extension preserves all logical constants, application and the interpretation of every pure term.

For every original proposition p,

    val_a(F_t(p))=1 ⇔ a≤F_t(p) ⇔ w₀≤p ⇔ val_original(p)=1.

Hence F is an isomorphism from the original pointed pure BBK model to the newly pointed model with valuation val_a. The algorithm need not find w₀ or compute F: its existence proves the isomorphism claim, while the output code is computed directly from K and the first atom a.

**Signature limitation.** This is a pure logical-language isomorphism. An atom transposition need not fix arbitrary named propositions or relation constants. For example, a two-world Gallin model with a named singleton proposition can change that constant's truth when repointed to the other world. Thus the procedure does not promise an isomorphic pointed expansion preserving arbitrary nonlogical constants. It remains valid with constants known to be fixed by the transposition, such as individuals and the appropriate hereditary-core parameters, or with no nonlogical constants.

There is no uniform procedure recovering the *original* designated truth map from the equality-only structure in general: two different atom pointings have the same operational code. Nonuniformly, however, its Turing degree is unchanged, because the finite number of the original true atom w₀ can be hard-coded and val_original(p) is the decidable test w₀≤p. This is the general Actuality observation in `audit-degrees-20261022.md` §9, specialized to B.

## 6. An even more direct auxiliary-diagram construction

The intrinsic auxiliary domains H_α are all rigidly defined. Every auxiliary first-order formula translated with its quantifiers bounded to those domains is bivalent at core assignments, by the induction in the representation report. Consequently its complete truth value can be computed from K by comparing the denotation of its translation to ⊤. The source truth map is not needed for auxiliary satisfaction, including quantified auxiliary formulas.

Thus one may construct the whole auxiliary complete elementary diagram directly from K, designate the uniformly found atom a as w₀, and retain the inherited numbering on every T-image sort. Its original reduct has exactly the original operational structure with the new valuation val_a, and by §5 is isomorphic to the original pointed pure model. The diagram recovers the original operational data with the inherited numbering, so its degree equals the canonical operational-code degree. It also equals the degree of the original full operational-plus-truth data, though that last equivalence need not be uniform without the original true atom's index.

This strengthens the positive model-existence comparison: an equality-and-parameterized-term presentation is enough, uniformly, to produce an isomorphic pointed pure positive model and an auxiliary Gallin representation. It does not weaken the input to mere application tables or a bare action/category reduct, because the atom and bounded-formula tests explicitly need original quantifier/lambda term interpretation.

## 7. Consequences and boundaries

* For B and its pure positive Infinity/Choice additions, explicit truth-map coding is dispensable for uniform *isomorphic model construction*. Every pure optional sentence is preserved by the pointed isomorphism.
* For exact original-numbered truth recovery, supply the original truth map or the index of its true atom. Without one of these, retain the nonuniform degree statement or the isomorphic-reconstruction statement.
* The argument does not apply to arbitrary Max models: they may lack Actuality or Atomicity. The separate Max+Actuality nonuniform recovery theorem remains valid.
* No exact degree spectrum for one fixed isomorphism type is obtained merely from these conversions. The result is a genuinely effective representation theorem under an explicit operational coding convention.

Validation: main records unchanged; the required validator is run after saving this report and its outcome is provided in the accompanying update.

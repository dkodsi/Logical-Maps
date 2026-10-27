# The exact arithmetic theory of pure Maximalism

The existing research note supplies an ordinary proof of

```math
\mathrm{Th}_{\mathrm{arith}}(\mathrm{Max}(C))
=\mathrm{Cn}\bigl(T_{\mathrm{arith}}\cup\mathrm{True}_{\Pi_1}\bigr)
```

Here T_arith is the common ordinary first-order arithmetic consequence theory of C plus weak arithmetic noncollapse and of the boxed-Plenitude and boxed-Functional-Choice packages with quantified Infinity. True Π₁ means truth in the external standard natural numbers. Cn is ordinary first-order deductive closure. The retained proof below writes T for this arithmetic theory; it is not the intermediate modal theory also called T in the comparison paper.

The claim concerns pure Maximalism and actual ordinary arithmetic theorems. It says nothing here about signature Maximalism, Strong Possibility consistency, or truth at every possible arithmetic state. The proof’s extension to current graph-choice principles is retained in §37.9 with its own scope.

**Status.** Ordinary proof supplied in the existing Frege note; no full Lean certificate. The recent independent review of §36 covered positive-package conservativity and did not cover this upper-bound argument. The source dependencies are McLarty’s finite-order interpretation and Bacon–Dorr’s countable BBK completeness. The arithmetic-equality application is the research note’s argument, not a theorem attributed to those papers or a claim of historical novelty.

**Proof source.** [Frege infinity, §37](../source/research/2026-10-22/notes/frege-infinity-20261022-1726.md), including its explicit dependencies on §§18, 24 and 35–36; unpaginated. The mathematical section below is retained unchanged.

## Lean scope and the next substantive obligations

The existing [finite-support module](../source/topics/classicism/lean/Classicism/Syntax/FiniteChoiceBasis.lean) already proves that each derivation uses finitely many optional axioms while preserving the restricted Logical Equivalence premises. The [arithmetic reflection module](../source/topics/classicism/lean/Classicism/Results/Research/FregeArithmeticReflection.lean) identifies the existing arithmetic syntax with its standard Prop-valued reading; its own scope excludes an arbitrary intensional-model truth lemma and a uniform object-C derivation builder. The existing MaxConservativity certificate concerns closed typed identities and consistency, not this arithmetic equality.

A certificate of the equality needs the following additional developments:

1. The precise arithmetic language, standard Π₁-truth predicate and deductive closure, connected to the fixed Frege translation; derive the lower inclusion using Max’s arithmetic noncollapse and true-Π₁ reasoning.
2. The current quotient and number-preserving finite-order set-theoretic interpretation, including nonstandard numbers and the proof-dependent finite powerset bound. The McLarty theorem remains an external dependency of the written argument.
3. An internal, countably coded Henkin/BBK construction from each required consistency assertion, retaining the original H theoremhood restriction.
4. The bounded free-root model, its C-validity, realization of the finite possibility requests, and the Frege-arithmetic isomorphism with the interpreted number domain. Combine these with the finite-support theorem to establish the upper inclusion.

These are substantive interpretation proofs. This presentation update adds no Lean declarations and does not promote a supporting lemma to a certificate of the equality. Formalization is best resumed at these dependencies; the finite-support step need not be duplicated.

## 37. Exact ordinary arithmetic shadow of Pure Maximalism

This is a new metatheoretic argument, not a claim already present in the map. Its scope is the finitary pure theory and its Henkin proof semantics. It uses the current quotient and the number-preserving McLarty interpretation audited in §§35–36, together with an internal finite-component version of the free-root coalescence. It does not identify the higher-order or modal consequence theories. The external source results used are McLarty's finite-order constructible interpretation and Bacon–Dorr's countable BBK completeness; the current quotient, arithmetic preservation, bounded-rank coalescence, and exact consequence-theory equality are new arguments in this research note. This is a mathematical proof audit, not a Lean verification or an assertion of literature novelty. All counting-base changes use the canonical graph isomorphism J_{σ,ρ}; in particular J_{e,t} denotes the comparison of e-counting with t-counting, not a type named et.

Let T be the common first-order arithmetic consequence theory of C+Iσ from §36, and let TrueΠ₁ be the set of all standard-true first-order Π₁ arithmetic sentences. The following equality is between sets of ordinary arithmetic sentences, with deductive closure understood in the ordinary first-order arithmetic language:

    Th_arith(Max(C)) = Cn(T ∪ TrueΠ₁).

In particular this is also Cn(T ∪ TrueΣ₂). The latter reformulation follows because each true Σ₂ sentence has a standard witness leaving a true Π₁ instance, and TrueΠ₁ is contained in TrueΣ₂ after adding a dummy existential quantifier. These observations require no assertion that T itself is Π₁-axiomatizable.

### 37.1 The lower inclusion and the correct initial countermodel

Max proves Iσ and therefore contains T in its arithmetic translation. Section 18 proves that Max proves every true Π₁ arithmetic sentence. This establishes the lower inclusion.

For the converse, suppose an arithmetic sentence A is not a consequence of T∪TrueΠ₁. We first need a C model with the required arithmetic. One must not assume that an arbitrary model of T expands to a C+I model.

Instead the following theory is consistent:

    C + I_e + {P^e : P∈TrueΠ₁} + ¬A^e.

Indeed, if a finite subset were inconsistent, there would be true Π₁ sentences P₁,…,P_k such that C+I_e proves (P₁∧…∧P_k)→A in the arithmetic translation. By the definition of T, that ordinary arithmetic implication belongs to T, contrary to the assumed consistency of T∪TrueΠ₁∪{¬A}. Henkin completeness now supplies a model M of the displayed theory.

Apply the current quotient of §35, with base N_e(M), and then a sufficiently high finite-order McLarty interpretation. For each externally fixed finite rank bound required below this gives a model S of ZFG[n+] plus V=L whose internal ω has the same first-order arithmetic as M's current N_e. In particular

    S ⊨ ¬A and every sentence of TrueΠ₁.

S may be externally ill-founded and its ω may be nonstandard. All remaining constructions are carried out internally in S; they do not replace its ω by the external standard natural numbers.

### 37.2 Reduce a putative Max proof to finitely many component requests

Suppose Max proved A^e by a finite proof π. Use the equivalent Possibility presentation of pure Maximalism. Only finitely many added axioms occur in π, say

    ◇φ₁,…,◇φ_k,

where each φ_i is a closed pure sentence consistent with C. Include in the finite proof fragment every subterm type and every H-proof certificate used to license a Logical-Equivalence instance. Also include the fixed auxiliary derivations used below to verify the Frege Peano clauses and the recursive characterization of Sum and Prod, together with their own expanded subterms and H-certificates; include the full N_e and numeral-orbit definitions even if they were hidden in abbreviations. If the initial proof used the Distinctness presentation, first replace its finitely many used axioms by their finite derivations from the equivalent Possibility schema. This changes only the finite fragment and its eventual rank bound.

Use the consistency predicate of the original typed calculus itself. Its finite proofs are effectively checkable: Logical-Equivalence axiom lines carry their H-proof certificates, and beta-eta identifications can carry finite conversion certificates. All type and term syntax is effective. Thus Con(C+φ_i) is a standard Π₁ sentence. It is true by the side condition on the Max axiom and consequently holds in S.

There is a direct primary completeness source, so no equivalence with a newly invented first-order algebra theory is needed. In the author-hosted *Classicism*, draft of 1 July 2022, §3.1, Theorem 3.2 (pp.44–45) gives countable BBK completeness for H, and the following paragraph applies it to every H-extension. Footnote 64 constructs a complete witnessed extension and then takes typed closed terms modulo provable identity. [Exact 2022 manuscript](https://andrew-bacon.github.io/papers/Classicism.pdf). This differs in date from the 16 May 2023 draft ordinarily used by the map; the locator here deliberately refers to the inspected 2022 version.

### 37.3 Countable component algebras inside the bounded set model

Apply that explicit Henkin construction internally in S to C+φ_i, obtaining a countable BBK model M_i. Expand by a countable supply of witness constants of every type. Recursively decide each next sentence so as to retain consistency, adding a fresh witness whenever required. The consistency tests are arithmetical over ω^S; Separation and recursion/Replacement form the choices and their complete witnessed theory. The internal assertion Con(C+φ_i) ensures that this construction starts consistently and the familiar fresh-constant argument ensures each witness step preserves consistency.

The term interpretation can be coded especially economically. Choose the least-code closed term in each provable-identity class. These representatives form a subset of ω, with a type label for each one. Application takes representatives of application terms; interpretation of a term under a finite assignment is given by substitution followed by taking its representative; and truth is membership in the complete witnessed theory. Their graphs are all coded by subsets of finite powers of ω. The BBK truth lemma is proved by internal induction on term/formula codes. Since the completed theory contains every C axiom and the given φ_i, the resulting model satisfies C+φ_i. No ordinary extensional Functionality axiom is added.

This construction also handles internally nonstandard formula codes when S is nonstandard. In particular S has a coded interpretation satisfying its own required C instances; we are not taking an external standard truth predicate for its arithmetic. The proof theory used here is the original C plus the premise φ_i, with its original H Logical-Equivalence side condition. It is not strengthened by allowing Equivalence applied to φ_i-dependent theorems.

The entire countable typed algebra is therefore coded by sets of natural numbers. A fixed finite number of powersets of ω suffices, along with Separation and Replacement; there is no need to collect full powersets of its infinitely many type carriers. The later root construction uses only the finitely many component domains relevant to π.

Choose one individual a_i of each M_i. There are only finitely many components. The global well-ordering in S is available, although this finite selection itself causes no Choice issue.

### 37.4 The free current root algebra

Build a root with individual domain D_e^r=ω^S and maps π_i^e constantly equal to a_i. These maps need not be surjective. Their role is to give component values to root individual parameters; component quantifiers will still range over the whole component carrier.

Flatten each relational type τ as σ₁…σ_l t, allowing l=0 when τ=t. For the finitely many types required by π and its certificates, define recursively

    D_τ^r = 2^(D_σ₁^r × … × D_σ_l^r) × ∏_{i=1}^k D_τ^{M_i}.

The first factor is the full internal set of current truth functions on the root argument tuples; at t it is simply 2. Each relational root object is thus a pair consisting of an arbitrary current extension and one component object in each M_i. The maps π_i^τ select those component coordinates.

Application is defined by slicing the current truth function and applying the component objects to the component argument values. With all types flattened, this defines partial application as well: a slice is a current truth function on the remaining argument tuple, paired with the corresponding component partial applications. Thus projection compatibility holds by definition.

Boolean constants act on current truth values in the ordinary way and on component coordinates by their component interpretations. A quantifier has current value obtained by quantifying over the whole root sort; its i-th coordinate is the component quantifier over the whole M_i sort. In particular the i-th quantifier is not restricted to the image of π_i^e. Equality has current truth precisely when the root objects are literally equal, while its component coordinate is the component equality value of their projections. Lambda abstraction pairs the current truth function defined by its body with that body's lambda interpretation in each component under the projected parameter assignment.

The clauses are algebraic, so no representation of the components by full action models is needed. They are the direct free-current version of the coalescence construction used in *Classicism*, Appendix E, especially p.83; the use here is a new internal bounded-rank adaptation, not an attribution of this arithmetic-shadow theorem to that source.

### 37.5 C validity and the Logical-Equivalence side condition

The ordinary H rules and axioms hold at the root: logical truth is classical; quantifiers have their full local ranges; beta and eta hold by the application/lambda definitions; and current identity is genuine equality of the constructed objects. Substitution of identical root objects preserves every operation and truth value. The corresponding component clauses hold because each M_i is a C algebra. In particular current coextension of arbitrary intensional objects is never substituted for identity.

For an instance of Logical Equivalence, use its actual H-proof certificate. The H-equivalent bodies agree in current truth under every root assignment, so their lambda abstractions have the same current extension. In each component the same valid H-equivalence makes the component lambda abstractions identical, since M_i satisfies C. The two root abstractions therefore agree in every coordinate and are literally identical. This checks the theoremhood restriction directly; an equivalence merely derivable from φ_i, I_e, or any optional premise is not used as an H-equivalence.

Thus the root interpretation validates the finite C proof fragment in π. It also validates each required ◇φ_i. The i-th coordinate of the root value of φ_i is true in M_i, hence is different from its component bottom value. Accordingly the root proposition denoted by φ_i differs from the root bottom proposition. Since ◇p abbreviates p≠⊥, its current root truth follows. Closed purity is important here: no extra signature constants need simultaneous interpretation through the chosen root individual maps.

### 37.6 The root arithmetic is exactly the internal ω of S

Let b_n be the internal S-recursion

    b_0=0_e,       b_{n+1}=Suc_e(b_n),       n∈ω^S,

using the root zero and successor operations. Replacement forms its range R⊆D_ν_e^r. The root's full current property domain contains a property with extension exactly R, with arbitrary component coordinates, for example component bottoms. This property is currently zero-containing and successor-closed. The definition of N_e therefore gives N_e⊆R.

Conversely, each currently zero-containing successor-closed property contains every b_n, by induction in S on its own ω. This yields R⊆N_e. Hence the root's natural-number domain is exactly the internally represented numeral orbit R. This is an internal-standardness statement relative to ω^S; it does not say that R consists only of externally standard numerals.

Internal finite-cardinality induction shows that b_n counts exactly the root properties whose current extensions have n elements in S. The individual domain is ω^S, so the extension [0,n) is available at et and witnesses b_n for every n. These initial segments and finite pigeonhole distinguish b_m from b_n when m≠n. Thus n↦b_n is a bijection preserving zero and successor between ω^S and N_e at the root.

The full current binary relation domains also contain the graphs of addition and multiplication on this orbit, with arbitrary component coordinates. The same induction used in §24 identifies the source definitions of Sum and Prod with those graphs. Equivalently their current recursion clauses have unique solutions on this internally standard Peano system, and the full current graph witnesses exclude spurious outputs. Therefore every ordinary arithmetic sentence at e has exactly its S-arithmetic value. In particular the root falsifies A^e.

For this upper bound, no infinitude assertion about the root t-domain is required. We deliberately count at e. Other fixed counting types can be reduced to e in Max using its Iσ and I_e and the canonical numerical isomorphism of §13. If an all-type internally infinite root is wanted for another purpose, one may add a coded component satisfying C+Infinity_t, using its additional true Π₁ consistency assertion; that extra construction is unnecessary here.

### 37.7 Why the finite rank bound closes the argument

The finite proof π, its expanded abbreviations, all its subterm types, the logical-constant types appearing in it, and its finitely many H-certificates give a finite list. Enlarge it by the N_e/orbit definitions and the fixed arithmetic-correctness derivations invoked in §37.6, including Peano clauses, Sum/Prod recursion and their uniqueness arguments, with all their own subterm types and H-certificates. If another arithmetic counting base is first reduced to e, include the finite derivation using J_{σ,e} as well. This is still a finite list; the root is not tacitly assumed to validate C instances outside it. A quantifier at σ requires its (σt)t constant type; this is included whenever that quantifier occurs. There is no requirement to iterate such additions for quantifiers that never appear. The component language may contain all types, but its entire term model was coded countably in §37.3.

For the root list, each domain is formed from finitely many already bounded products, a powerset, and finitely many countable component factors. The generous finite powerset bounds from §36.3, enlarged by a fixed coding allowance and by the finite list's maximum type complexity, therefore suffice. The numeral orbit uses Replacement and a subset of an already constructed carrier, rather than a new unbounded type hierarchy. Choose the McLarty rank n at the outset large enough for this finite construction.

Inside the resulting S, every step of π is sound in the root interpretation, all its finitely many Max axioms hold, and A^e is false. This is impossible. Hence no such π exists, establishing the upper inclusion and the displayed exact arithmetic-shadow equality.

### 37.8 Consequences and limits

The description sharpens §36.6: Max adds exactly the deductive effect of all true Π₁ arithmetic sentences to the common effective arithmetic theory of C+I and the boxed-Functional-Choice infinity packages. In particular its added arithmetic is stronger than that effective theory but does not comprise all arithmetic truth.

For a finite Max proof, the argument uses only finitely many extra true Π₁ assertions Con(C+φ_i), corresponding to that proof's finitely many possibility axioms, together with whatever true Π₁ assumptions are present in a countermodel argument. Compactness therefore also gives a finite Π₁ reduction of each individual arithmetic consequence. This is not a uniform effective procedure that decides which possibilities are C-consistent.

The theorem does not turn Max into an effective theory, does not show Strong Possibility consistent or inconsistent, and does not make Max's possible arithmetic states standard-sound. Its conclusion is only about actual ordinary first-order arithmetic theorems. The source-dependent interpretation steps and the internally verified typed Henkin construction are essential; omitting them would leave the upper inclusion unsupported.

### 37.9 Current choice and actual infinity do not enlarge this shadow

The same upper-bound construction validates additional ordinary current mathematics. At the root every internal S-subset of each required argument product is an admitted current extension. S's global well-ordering therefore supplies, for any currently serial relation, a graph selecting one output from each fiber. Give that graph arbitrary component coordinates; its current root truth verifies the corresponding Relational Choice instance. The same method gives a transversal of every current equivalence relation and a well-ordering of every required current domain. These arguments concern graph relations, so they never introduce an inadmissible operation with output e.

The root e-domain is ω^S, and every root numerical cardinality b_n counts exactly n-element current extensions. Its whole e-domain is therefore Frege-infinite. Consequently adjoining any or all of the following schemata to Max leaves its ordinary arithmetic shadow equal to Cn(T∪TrueΠ₁): current Relational Choice, current Transversal Choice, current Well-Ordering, and actual Infinity_e.

One may include actual Infinity at all admitted types as well. For a finite proof using finitely many such instances, add one component M_∞ satisfying C+Infinity_t. The latter theory is consistent in an ordinary full infinite-world model, so its arithmetized consistency assertion is another true Π₁ sentence available in S. The internal typed Henkin construction supplies M_∞. Its t-carrier is infinite inside S: if it had an internal finite size n, finite-cardinality induction in the coded C algebra would make its whole t-domain counted by its n-th numeral, contradicting Infinity_t. Choice inside S then gives an ω-injection into that carrier and hence into the root t-carrier, by holding the root current bit and the other component coordinates fixed. Constant relations inject the root t-domain into every nonempty-argument relational domain. With the root e-domain already ω^S, each required root type is internally infinite, and the internally full current extension domains verify its Frege Infinity sentence.

Thus even Max plus all these current choice and all-type actual infinity schemata has exactly the same ordinary arithmetic theory. As throughout the section, only finitely many instances occur in a proof, so the bounded powerset construction remains adequate. No claim is made here for boxed choice or boxed infinity, for Plenitude, or for rigid/modal comprehension; those require additional compatibility across component coordinates that arbitrary current graph extensions do not supply.

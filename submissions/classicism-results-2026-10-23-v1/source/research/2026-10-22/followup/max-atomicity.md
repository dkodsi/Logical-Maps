# Pure Maximalism and Atomicity: a bounded follow-up

22 October 2026. Ordinary mathematics in fixed C, with ZFC metatheory. Direct source for the lemma below: misc, this note §2. No novelty, human-checking or formal-verification claim. The frozen notes archive is unchanged. **Latest update: §12 links a proposed inconsistency proof, developed during the additional hour; the unresolved verdicts in earlier sections describe the earlier stopping points.**

## 1. Exact question and prior constraints

The primary target is consistency of **C + pure Max(C) + unboxed Atomicity_t**. Pure Max retains its original C-theoremhood/consistency side condition. All-relational-type Atomicity is a stronger, separate target; neither unboxed question is settled here. Both boxed versions are inconsistent with pure Max: C has a model refuting Atomicity_t, so Max gives ◇¬Atomicity_t, contradicting □Atomicity_t. This is already recorded in `maximalist-distinctness-incompatible-with-necessary-atomicity-t`.

The starting constraints are [fresh-constant profile roots, §§12, 14–16](../notes/fresh-constant-profile-root-20261022.md), the [universal-core Henkin presentation, §§6–7](../notes/reflection-universal-core-20261022.md), and the [structural package](../sp-structural-proof-package/README.md). In particular:

- Closed pure named atoms cannot cover the arithmetic region. A prospective model needs unnamed atoms, including nonstrong atoms below ¬Actuality; these must acquire new splitting propositions at their truth locations.
- A Boolean atomic cover alone does not provide the typed logical operations, quantifier clauses and truth locations of a C model.
- No failure of effective axiomatization, Gallin semantics or Actuality is being used as an inconsistency argument.

The focused test was whether elementary compactness can supply the missing new Boolean pieces while preserving all typed logical structure. It supplies relative pieces, but there is an exact obstruction to promoting them to atoms.

## 2. Simultaneous relative-ultrafilter-cell lemma

Let M be any set-sized Henkin C model. For each relational type τ let B_τ be its external Boolean algebra of entities. There is a single elementary extension M ≺ N in the full typed Henkin presentation, including actual truth, and, for every Boolean ultrafilter U on every B_τ, an entity c_(τ,U) in N such that

    c_(τ,U) ≠ 0;
    c_(τ,U) ≤ b       for every b in U;
    c_(τ,U) ≤ ¬b      for every b in B_τ outside U.

Thus each c_(τ,U) settles every OLD entity of its type. Distinct ultrafilters at the same type yield disjoint nonzero cells. Every old nonzero b has at least one such cell below it. If U is principal at an old atom a, its cell is necessarily a. At type t the cell for M's actual-truth ultrafilter can additionally be required true in N.

**Proof.** Use the elementary diagram of M in the many-sorted first-order Henkin presentation. Add one new constant for each indicated cell and the displayed conditions, naming old entities. This is a set of sentences. In any finite subset, assign each new constant the meet of the finitely many old elements required to belong to its ultrafilter. Each meet is nonzero because U is proper; negative membership conditions are treated by including the complementary element, which belongs to U. These choices lie in M and simultaneously satisfy the finite subset and the elementary diagram. For the actual-truth ultrafilter, each finite meet is actually true in M, so the extra truth requirement is also finitely satisfiable. Compactness gives N. Identification along the elementary-diagram embedding makes it an extension of M.

If U ≠ V, choose b in U with ¬b in V; their two cells have zero meet. For old b ≠ 0, the Boolean ultrafilter lemma gives U containing b, and c_(τ,U) ≤ b. Finally, an old atom a remains an atom in an elementary extension. A nonzero cell below a must therefore equal a. All typed logical operations and quantified formulas are preserved by elementarity. If M satisfies pure Max, N does too, instance by instance. ∎

This is a standard compactness argument applied to the present typed presentation. It is **not** an atomization theorem: a relative cell may be split by new entities. Nor does preservation of quantified formulas supply a current-domain witness beneath every nonactual cell; truth at an accessible location can involve that location's new domain.

## 3. Exact obstruction to the proposed upgrade

Suppose b in B_τ is nonzero and its interval is atomless in M. This is the first-order statement with parameter b

    ∀x [0 < x ≤ b → ∃y (0 < y < x)].

Elementarity preserves this very statement in N, with its quantifiers now ranging over ALL entities of N. Consequently **every new relative cell below b still has a nonzero proper part**. No elementary extension of M can add an atom under that old atomless interval. More generally, Atomicity_τ is itself first-order, so an elementary extension or elementary-chain limit cannot change its truth value.

The fresh-constant profile root supplies a concrete application. Its unique root atom r has a nonzero atomless complement b = ¬r. The lemma simultaneously supplies cells for every old ultrafilter concentrated on b, preserves pure Max and the full typed theory, and nevertheless leaves all those cells nonatomic. Hence even realizing every old Boolean choice at once does not repair that model's missing Atomicity_t.

Calling the maps only “logical-operation preserving” does not evade this obstruction if they also preserve actual truth. An embedding preserving every pure term operation, including the quantifier-valued terms, and actual truth is elementary in the original typed language: every formula is a proposition-valued term in its assigned parameters. Forward truth preservation already gives reflection via preservation of negation. Thus this entire class of truth-preserving extension constructions retains the obstruction. The algebra-only embeddings in the universal-core report deliberately omit actual truth; they are not automatically subject to this argument, but that report leaves their Henkin realization problem unresolved.

## 4. Verdict and stopping point

The relative-cell lemma is sound partial progress: all old ultrafilter decisions can be realized simultaneously inside one fully typed elementary extension, preserving Max and old atoms. It isolates why that plausible compactness step falls short. A successful construction would still need a **non-elementary typed atomization** that adds genuine atoms and protects them against all subsequent logical closure, while providing the new local distinctions required below ¬Actuality. No such preservation lemma is established here.

I stopped at this obstacle rather than iterate saturation, repeat the Boolean-cover failure, or reopen the SP construction. No alternative route or infinitary-language extension was pursued. Pure Max + Atomicity_t, and therefore the stronger unboxed all-type target, remain unresolved by this work; the boxed targets remain refuted for the separate recorded reason in §1.

## 5. Renewed pass: Atomicity is preserved by full coalescence

This and the following sections were added during the separately authorized continuation on 22 October. They do not revise the elementary-extension obstruction. New deductions: misc, this note §§5–8; construction background: Bacon–Dorr, *Classicism*, 16 May 2023 draft, Appendix E, pp. 80–83, and the singleton-profile construction audited in [audit-profile, §§2–3](../notes/audit-profile-20261022.md).

Let (M_i,v_i) be a set of pointed C action models, and choose an individual a_i at each v_i. Add one new root o with a singleton individual domain. For each i add a distinguished arrow o→v_i carrying that individual to a_i, and all its composites with old arrows. Keep the old objects and domains unchanged. At each flattened relational type τ = σ_1…σ_k t use the full domain

    D_τ(o) = P(D_σ1(o) × … × D_σk(o)) × ∏_i D_τ(v_i).

The first coordinate is the actual extension at o; the i-th tail is transported to v_i. Interpret application componentwise on tails and by actual fibers at o. Abstraction admits its whole actual extension and takes the corresponding old abstractions as tails. Equality has literal equality as its actual extension and the old equality terms as tails. A quantifier's tail is the old quantifier over the WHOLE old domain. In particular no surjectivity of transport or BF is assumed. Distinct pairs give distinct intensions: the actual coordinate distinguishes them at o, or an old arrow and tuple distinguish unequal tails. These are precisely the full-profile version of the audited C-closure argument: H holds at every object, and H-equivalent abstractions have equal actual extensions and equal old C tails. Thus this is a C model.

As a Boolean algebra, D_τ(o) is exactly the displayed product. A product of atomic Boolean algebras is atomic: a nonzero element has a nonzero coordinate; choose an atom below that coordinate and put zero in every other coordinate. The powerset coordinate is atomic. Consequently, for any specified collection S of relational types,

    all M_i satisfy Atomicity_τ at v_i for τ in S
       ⇒ o satisfies Atomicity_τ for τ in S.

Only Atomicity at the distinguished source points is required. Their accessible worlds may be nonatomic. Conversely, a nonatomic tail interval remains a nonatomic coordinate interval at the full root, explaining the failure of the old full coalescence of arbitrary C-complete components.

The new root also has E_1 and Strong Actuality. Its proposition r = (1,(0)_i) is a true atom, and every nonidentity outgoing arrow sends it to zero, so it necessarily settles every proposition. No all-type Strong Leibniz claim follows.

## 6. An exact single-sentence construction criterion

Let At_S be either Atomicity_t alone or the all-relational-type Atomicity schema; keep the chosen version fixed. Using the bundle's action-model completeness background, the following are equivalent:

1. C + pure Max(C) + At_S is consistent.
2. For EVERY closed pure C-consistent P, C + At_S + ◇P is consistent.
3. At_S adds no new closed pure necessary consequences: if C + At_S proves □Q, then C proves Q.

**Proof.** (1)⇒(2) follows from the fixed pure Max schema. For (2)⇒(1), choose one atomic pointed model witnessing ◇P for each C-consistent closed pure P. There are only countably many such sentences. Coalesce these pointed models by §5. Its new root is atomic at precisely the required types and sees every chosen P-witness through a composite arrow, so it satisfies every pure possibility-Max instance. Equivalence of (2) and (3) follows from completeness and ¬◇P ↔ □¬P: failure of (2) supplies Q=¬P, and failure of (3) supplies P=¬Q. ∎

Moreover the model obtained in (1) may also satisfy **E_1 + Strong Actuality**, without changing the consistency question. This is a relative construction theorem, not a claim that condition (2) or (3) holds. It removes one potential complication: if Max+At_S is inconsistent, there is already a SINGLE C-consistent pure P that cannot be possible from an At_S root. A merely collective obstruction from finitely many individually possible target sentences cannot be the whole explanation, because coalescence combines those targets while preserving At_S.

This criterion concerns unboxed Atomicity. It neither boxes that hypothesis nor substitutes signature Maximalism for pure Max.

## 7. A concrete atomic predecessor of an atomless world

Take the recorded one-individual variant `finite-support-permutations-individuals-singleton`. Its sole object v has an atomless propositional algebra and refutes Actuality. Its arrows are permutations of N; the only individual is fixed. Source: `finite-support-permutations`, Proposition D.5(1), pp. 75–76, with the explicit singleton setting in `groups/finite-support-one-object.yaml`. These verdicts were confirmed using the proved-only Engine.

Put a singleton profile root o above v, using only pure one-individual term profiles, with the arbitrary actual-extension coordinates from the audited construction. For any propositional profile T(a), every old loop h fixes it: h(T(a))=T(ha)=T(a). A loop-invariant proposition in this one-object action model has constant truth at every arrow, so is either bottom or top. Thus the profile Boolean algebra at t is exactly 2, and

    D_t(o) ≅ 2 × 2.

The same profile-substitution argument as before validates C at all types; old quantifiers and old domains remain unchanged. Therefore o satisfies E_1, Atomicity_t, Strong Actuality, and ◇(Atomlessness_t ∧ ¬Actuality). Its atom b=(0,top) becomes top at v, where it is nonatomic. Hence b is a genuine weak, nonstrong atom. The required phenomenon of an atom acquiring new local splits is therefore realizable in a fully typed C construction.

This does NOT give Max, all-type Atomicity, or the unnamed arithmetic atoms required under Max. Its four-element propositional domain already excludes pure Max. It does show that the particular target P = Atomlessness_t ∧ ¬Actuality is not an obstruction to criterion (2) for Atomicity_t. An unchanged nonatomic tail would defeat FULL coalescence; the restricted term-profile root is essential here.

## 8. A sharper possible obstruction: a closed uniform splitter

For F of type tt define the pure formula

    Split(F) := ∀p [p≠0 → (p∧F(p)≠0 ∧ p∧¬F(p)≠0)].

**C proves Atomicity_t → ∀F □¬Split(F).** The outer quantifier is UNBOXED; this does not assert □∀F¬Split(F).

**Proof.** If Split(F) is possible, Atomicity supplies a root atom w below its nonzero proposition. There is a possibility where w is true, and w≤Split(F) makes Split(F) true there. Thus both w∧F(w) and w∧¬F(w) are nonzero there. Neither can have been zero at the root, since equality to zero is necessary by NI. They are therefore disjoint nonzero root parts of w, a contradiction. This uses no BF, Choice, or necessary Atomicity. ∎

Consequently a closed pure operation term F for which C+Split(F) is consistent would refute Max+Atomicity_t: Max makes Split(F) possible, whereas the displayed theorem forbids it. An existentially quantified splitter available only at the future world does NOT suffice, because it need not be the transported value of a root operation. The known fresh-generator splitting arguments likewise do not provide a single closed pure operation that uniformly chooses the fresh generator.

No such closed splitter was constructed in this pass. Section 9 gives a sufficient construction condition and identifies the remaining gap. Original fixed-C consistency remains unresolved; no extended-language result is asserted.

## 9. A sufficient condition using pointed term profiles

There is a useful generalization of §7 that does not require the old model to be atomic. Given a pointed C action model (M,v) and an individual a at v, let B_τ(v,a) be the entities T(a) at v, for all pure terms T(x) of type τ whose only free variable is the individual x. This is closed under pure term operations. It includes the pure quantifier terms; closure does not replace their old domains with B_τ. At relational types it is a Boolean subalgebra of the old entity algebra.

Build a new singleton root with one distinguished arrow to v and all its old-arrow composites. Use arbitrary actual extensions paired with profiles in B_τ(v,a). Under a composite ending at u, the profile of T(a) is T(ha), where h:v→u is that composite's old part. Substitution, abstraction, equality and full old-domain quantification work exactly as in the audited profile construction. Unequal profiles at v are distinguished by a further old arrow, already present among the composites. Thus this restricted-profile root is a C model, and

    B_t(v,a) atomic ⇒ the new root satisfies Atomicity_t;
    M,v satisfies P ⇒ the new root satisfies ◇P.

Indeed the root proposition algebra is 2 × B_t(v,a). The analogous conditional holds at any specified collection of relational types when all corresponding B_τ(v,a) are atomic; atomicity at t alone does not establish that stronger condition.

In particular B_t(v,a) is finite, hence atomic, if only finitely many complete pure one-individual truth theories occur among the pointed states (u,ha) reachable from (v,a). Each profile is determined by its truth value at those states, since proposition identity in the action model is equality of all future truth values. If there are n such truth theories, there are at most 2^n propositional profiles. One concrete sufficient case is a finite-object component with a coherent choice of marker a_u fixed by every arrow: only its finitely many objects need to be considered. No finiteness of the higher domains is assumed. This covers the atomless singleton one-object component in §7 and also one-world Henkin components with infinite individual domains.

Consequently, if every C-consistent closed pure P has some model and marker with atomic B_t(v,a)—finite pointed truth spectrum is sufficient—then §6 constructs pure Max + Atomicity_t. This is a precise **sufficient condition**, not a proof that the required models exist. It differs from the earlier named-cell arguments: the old pointed theories need not be effectively axiomatized or isolated by one closed sentence, and the atoms of the new root need not be old atoms.

The missing step is a representation or modification theorem supplying such a profile algebra for arbitrary P while preserving P. Neither finite-object representation nor finiteness/atomicity of that pointed spectrum has been proved generally. Replacing that requirement with an elementary extension does not help (§3), and imposing arbitrary new profile generators can instead split all prospective atoms. This is the present stopping point: a non-elementary preservation mechanism has been proved for an identifiable class of inputs, but its universal applicability—and hence fixed-C Max+Atomicity consistency—remains unresolved.

## 10. Second continuation: two construction checks

22 October 2026. New arguments below: misc, this note §§10–11. No language extension, database change, Lean work, or claim of independent checking. The additional construction uses the bookkeeping-substitution root of [sp-henkin-minimal, §13.1–13.3](../notes/sp-henkin-minimal-20261022.md), with its component family and tail policy specified anew below. Its C-closure does not require a C-complete family; completeness was needed there only to establish Max.

**Full old quantifiers.** The restricted profile domains in §9 are not asserted to be Henkin submodels of the old object. If a root parameter has profile T(x), then the tail of a formula with that parameter is obtained by substituting T only for the free parameter. Thus the tail of `∀y R(y,T(x))` is that very old formula, with y ranging over the whole old domain. Likewise, the tail of `λy R(y,T(x))` is the whole old abstraction, defined on old arguments outside the transport image. This is a pure one-individual term again. At the new root the quantifier uses the complete new root domain, and its actual extension is admitted independently. These two clauses prove closure; restricting the old bound variable to term-denotations would be an incorrect alternative construction.

**Strong Actuality.** In §5 put r=(1,(0)_i). At the new root, r∧q is either r or zero for every current q. At each strictly future object its transport is zero, which lies below every proposition there, including newly available ones. Therefore `□∀q(r≤q ∨ r≤¬q)` holds at the root, not merely its unboxed version. Since r is actually true, Strong Actuality follows. The only root endomorphism is its identity. Coalescing an assumed Max+At_S model with just that one component already preserves At_S and every Max possibility. Hence adding E_1 and Strong Actuality leaves the consistency question unchanged, exactly as claimed in §6.

## 11. Infinite atomic profiles with standard arithmetic and no Actuality

This supplies a bounded extension of §9 beyond finite pointed truth spectra. It also realizes an arithmetic-support atom which acquires new splits, without assuming Max.

**Theorem.** There is a C model with a point o satisfying

    E_1 ∧ Atomicity_t ∧ StrongActuality ∧ I*_e
      ∧ ◇(E_1 ∧ I*_e ∧ □Fin_e ∧ ¬Actuality ∧ ¬Atomicity_t).

The displayed possible target has infinitely many pointed pure truth theories in its future, but its pure one-individual propositional profile algebra is atomic. At both o and that target, the Fregean natural numbers are exactly the standard numeral denotations, with ordinary zero, successor, addition and multiplication. Every accessible object nevertheless has a finite individual domain, so `□Fin_e` also holds, where `Fin_e := ∃Z(N_e Z ∧ Z top_e)`. Here I*_e and N_e have the fixed definitions in `topics/classicism/background.md`; I*_e does not assert an infinite actual individual domain.

**1. Components and a supported root.** Fix an unbounded set S of positive standard integers; S=N_{>0} suffices. For each n∈S use the full one-world extensional Henkin model H_n on n individuals, with a chosen individual a_n. Background for these ordinary full Henkin models: Bacon–Dorr, *Classicism*, 16 May 2023 draft, §3.2, Definition 3.6 and Proposition 3.7, pp. 47–48, as cited by `models/full-henkin-singleton-base.yaml`. Add a point v with one individual a. Its root endomorphisms are all substitutions of countably many bookkeeping markers d_i by other markers or fixed tokens 0_*,1_*, fixing both tokens. Write M for this monoid. Add one exit α_n:v→H_n for each n, stipulating α_n f=α_n for every f∈M and α_n(a)=a_n. There are no arrows back from a component. These markers and tokens are not constants of the final language.

At a flattened relational type τ=σ_1…σ_k t, an entity at v consists of a family

    R_f ⊆ D_σ1(v)×…×D_σk(v)  (f∈M)

depending only on f's values on some finite set of markers, together with an ARBITRARY tuple (b_n)∈∏_{n∈S}D_τ(H_n). Unlike the cited pure-profile construction, these component coordinates are unrestricted. Define these domains in increasing type complexity. The f-tail has root family g↦R_(g f) and the same tuple (b_n); its finite support is contained in the generic markers occurring in f's images of the original support. Its α_n-tail is b_n. Thus all transports land, and the pairs are injectively represented by their root and component intensions.

Here is the closure check for the changed tail policy. Two root arrows agreeing on all supports of a finite tuple of parameters give equal transported parameter ENTITIES: their extensions agree after every further root arrow, and their component tuples are unchanged. Evaluation of any formula with those parameters is consequently the same at their common target v, with quantifiers ranging over its full domains. For abstraction this holds for every target argument, so the resulting extension family has the union of the parameter supports. Its component tuple is the ordinary component abstraction with the transported parameters, which the unrestricted tuple policy admits. Equality, full target quantifiers, application and Boolean operations obey the same clauses. βη hold as equalities of intensions. H holds locally, and H-equivalent abstractions agree in their extensions at every root arrow and in their component entities. Thus Logical Equivalence holds with its original theoremhood restriction. This is a C model at all types.

In particular EVERY subset of the current argument tuples is an admitted actual extension: use that same extension at every root arrow, giving empty support, and any component tuple. This fact will supply the arithmetic predicates below.

**2. No Actuality at v.** Put r=(1 at every root arrow, zero at every component). For each i let D_i have zero component tuple and root truth `D_i(f)=1 iff f(d_i)=1_*`. These are admitted entities; the token 1_* therefore denotes the root-only pattern r in this construction, not logical top. Any actually true proposition p has finite support F. Choose d_i outside F and change only its image under the identity substitution to 1_* and to 0_*. The two arrows preserve the truth of p and give opposite values to D_i. Hence p∧D_i and p∧¬D_i are nonzero proper parts of p. No actually true proposition is an atom, so Actuality fails. The same argument at any witnessing root arrow shows that the whole interval below r is atomless. Consequently Atomicity_t fails too. We do NOT claim that the entire propositional algebra at v is atomless: its full finite component coordinates have atoms.

**3. The infinite pointed profile algebra is atomic.** Let F be the Fregean Axiom and let E_n say exactly n individuals exist. Pure terms in the sole individual a are fixed by every root endomorphism, so a propositional term T(a) has one constant truth bit across those arrows. Its value at each H_n is also one bit, because H_n is a one-world extensional model. Thus B_t(v,a) embeds as a Boolean subalgebra of

    2 × ∏_{n∈S}2.

F is false at v, since its proposition domain has distinct coextensive propositions, and true at every H_n. Therefore ¬F denotes exactly the root-coordinate indicator r. Each F∧E_n denotes exactly the nth component-coordinate indicator. All these indicators belong to B_t(v,a). Every nonzero profile has a nonzero coordinate and hence contains one of these indicators, which is an atom of B_t(v,a). This proves atomicity. The E_n distinguish infinitely many future pointed theories, so the finite-spectrum hypothesis of §9 genuinely does not apply. The atoms here are atoms of the PROFILE algebra, not necessarily of D_t(v); r is expressly not an atom of the latter.

**4. Standard Fregean arithmetic.** Write ν=(et)t. The numeral denotations 0_e,1_e,2_e,… at v are pairwise distinct: for m≠k choose n∈S at least max(m,k), and a property of exactly m individuals in H_n distinguishes the two cardinalities. Every standard numeral belongs to N_e by finite induction. Conversely the set of precisely these numeral entities is an admitted actual extension of a νt-property W, by step 1. At v, W contains zero and is successor-closed, so the impredicative definition of N_e excludes every other entity. Thus N_e has exactly these standard values. Successor is injective on them and zero is no successor, proving I*_e at v. The actual graphs of ordinary addition and multiplication on these values are likewise admitted relations. Their use in the inductive definitions of Sum_e and Prod_e, together with finite induction, proves that these relations have exactly their ordinary values on N_e.

At H_n the numeral n_e differs from (n+1)_e, while their successors both denote the empty cardinality predicate; both inputs are natural numbers. Hence I*_e is false there. It follows that I*_e denotes r at v. Every object has its actual finite individual cardinality, so Fin_e holds at v and at all H_n, even though the number-domain at v is standard infinite.

**5. The atomic predecessor and its arithmetic atom.** Apply §9 to (v,a). Its new singleton root o has proposition algebra 2×B_t(v,a), which is atomic, and has Strong Actuality by §10. It sees the stated target v. Unbounded finite components still distinguish all numeral denotations at o, and its unrestricted actual extensions repeat step 4, proving standard Fregean arithmetic and I*_e there too. Fin_e holds everywhere accessible from o.

The root proposition w=(0,r) is an atom at o. Its transport to v is r, which has the proper splits from step 2; thus w is nonstrong. More explicitly, at o it is denoted by the closed pure term

    I*_e ∧ ¬Actuality.

Indeed this term is false at o, true at every root endomorphism of v, and false at every H_n. This is an arithmetic-support atom below ¬Actuality that acquires new local splits. No saturation, elementary extension, added object-language constants, or infinitary connectives have been used. ∎

**Scope and remaining gap.** In particular the possible target can be conjoined with any finite list of standard arithmetical truths; step 4 supplies them in one fixed model. This enlarges the input class for §9 to a concrete infinite-spectrum family and reaches the arithmetic region that the earlier four-proposition example did not address. It does not establish the arbitrary-target condition of §6. These models explicitly fail pure Max: the C-consistent sentence `F ∧ I*_e`, witnessed by the full infinite extensional Henkin model, is false everywhere accessible (F fails at both new roots and I*_e fails at every finite leaf). This also explains why their pure named arithmetic atom does not contradict the previous Max obstruction. No all-type Atomicity is asserted. The general unboxed consistency questions remain unresolved; further progress needs a new target-preserving construction beyond this separated component family.

## 12. Extended-hour change of route: a proposed inconsistency proof

The next route strengthens the splitter obstruction to a bounded interval, then uses a rigid complete Boolean algebra in the existing full Boolean-valued construction. The detailed, self-audited argument is saved separately to keep this progress note navigable: [A rigid Boolean algebra route to pure Maximalism versus Atomicity](max-atomicity-rigid-selector.md).

It specifies finite closed pure terms b,F,Q with Q=b∧Split_b(F), proves `C+Atomicity_t ⊢ Q=0`, and supplies a Boolean-valued C interpretation with `Q≠0` true at its designated evaluation. Pure Max(C) includes that very disequality. If the coding argument passes independent scrutiny, this settles BOTH unboxed questions negatively; it does not merely restate the earlier representation gap.

The decisive bridge is a finite typed code for H_(κ+), followed by a presentation-independent selector transferred through the unique isomorphism of a rigid Boolean algebra to a canonical code. The first version uses the canonical L-order. The second, now preferred version uses the concrete Jech–Shelah rigid tree forcing and selects the first branch coordinate that splits the input; it works directly in ambient ZFC and removes the L-order step. The term is pure: no selector constant, type quantifier or infinitary formula is added. The proof note includes the cardinality, crispness, quantifier-domain, typing, uniqueness and designated-truth checks, with primary-source locators for the rigid forcing. No unresolved step was identified in that self-audit. Its status remains a proposed mathematical proof, with no human or independent agent verification and no database or Lean edits.

**Further audit, 22 October 2026.** The [finite selector audit](max-atomicity-selector-audit.md) expands the direct construction into an acyclic library of finite set formulas and checks their typed translation. It proves that the code need only collapse to a transitive universe containing H_(κ+): the row-size clause requiring equality with that segment can be dropped for this route. Its §9 then supplies a shorter algebraic non-theorem certificate using the atomless algebra itself, without the product atom or interval term. The ordinary pointed-model route is retained. Two wording corrections are documented, without changing the proposed conclusion. Independent verification remains outstanding.

The audit's §10 extracts an ordinary countable Henkin model satisfying the specified pure global splitting assertion S_A. Its closed pure propositional denotations, and its one-individual term profiles, are already atomless. This gives a concrete witness against the universal profile condition of §9 and the atomic-predecessor criterion of §6, subject to the same proposed-proof caveat.

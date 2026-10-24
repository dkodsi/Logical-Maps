# Prose proofs and scope of the checked SP/Max modules

These are proof explanations for the supplied formalizations, not additions to the frozen research notes or database verdicts. The [verification ledger](verification-status.md) controls which current sources have passed. Ordinary metatheory is distinguished from a derivation inside C.

## Max identity diagram

Assume Ax is consistent and entails the original Max schema. Let x=y be an identity of closed terms with the required closedTypes restriction. If C does not prove x=y, the definition of Max supplies its negation. A derivation of x=y from C+Ax would therefore contradict consistency. Conversely every C derivation is available in C+Ax. Thus the two theories have exactly the same such identities. Substitution of this equivalence into the definition of relative distinctness gives equality of the two axiom predicates, including their type restriction. Consequently adjoining recomputed distinctness adds no derivations or inconsistency to Ax.

For a finite Boolean combination of these identities, evaluate atoms by C theoremhood. Structural induction constructs a Max derivation of the formula when this Boolean evaluation is true, and of its negation otherwise. The atom case is the preceding Max axiom; negation, conjunction and disjunction use the existing object-language deduction rules. Consistency of an extension rules out the wrong answer. No computability of the evaluation and no existence of a consistent extension is asserted.

Sources: [max-degree.md](../../notes/max-degree.md), sections 4, 11 and 13.3; [MaxDiagram Lean source](../StrongPossibilityConsequencesMaxDiagram.lean).

## Conditional quotient obstruction

Let d be extensive on a Boolean algebra B. Suppose a surjective map f to a Boolean algebra Q preserves meet, complement and d, and its zero kernel is exactly the displayed relative kernel: f(p)=0 iff there exists k in K with d(p) meet k at most g. If r is fixed by the induced d and lies below f(g), choose p with f(p)=r. Then f(d(p) meet not-g)=0. The kernel characterization supplies k with d(d(p) meet not-g) meet k at most g. Extensivity implies (d(p) meet not-g) meet k is at most both g and not-g, so it is zero. Reordering meets gives d(p) meet k at most g. Applying the kernel characterization to p yields f(p)=0, hence r=0.

The separate closure lemmas prove the displayed kernels are downward and finite-join closed under their stated modal assumptions. No quotient map, properness, nontrivial quotient or C/Henkin model is constructed by these results.

For the numerical retraction lemma, j(h(a))=a and injectivity of j on target numbers give h(j(b))=b, since the two target numbers have the same j-image. The explicitly assumed preservation of numberhood makes this an equivalence of the number subtypes. It does not prove preservation of addition or multiplication. The final profile lemma uses its assumed numerical injectivity to pull a numeral name back from the image.

Formal proof: [Algebra Lean source](../StrongPossibilityConsequencesAlgebra.lean). Remaining construction obligations: [family status](../sp-family-status.md), M1, A1, F13 and F15.

## Concrete computability obstruction

Given a purported computable separator S of programs outputting 0 and programs outputting 1 at input 0, define the computable function g(c) to be 1 when S(c), and 0 otherwise. Mathlib's recursion theorem supplies an actual program c whose evaluation is the constant partial computation returning g(c). If S(c), the output-1 condition contradicts S(c). If not S(c), the output-0 condition implies S(c), again a contradiction. This uses actual program codes and their evaluation rather than an assumed inseparability property.

The same fixed-point theorem, applied to any total computable g, produces c whose output at 0 is g(c); hence g cannot avoid every such output. These are unrelativized code-level statements. The bridge to the numbered diagonal phi_e(e), oracle relativization, C arithmetic, finite-trace coding and exact degree/classification theorems remains separate.

Sources: [positive-effective.md](../../notes/positive-effective.md), sections 13–17; [max-degree.md](../../notes/max-degree.md), sections 8–10; [Computability Lean source](../StrongPossibilityConsequencesComputability.lean).

## Explicit infinitary numeral fragment

A frame has a carrier, zero, successor, and an admitted predicate sort. Numberhood is impredicative induction over that predicate sort. The enlarged formula datatype expressly permits an external countable disjunction in an open formula. Comprehension with its beta law therefore realizes the particular predicate bigvee_n(x=numeral(n)) inside the admitted predicate domain. This predicate contains zero and is closed under successor. Applying the definition of numberhood to it shows every number is a standard numeral. Conversely external finite induction shows each numeral satisfies numberhood.

Under the separately stated zero/successor separation and successor-injectivity assumptions on numbers, induction on numeral indices proves that distinct indices have distinct denotations. Each number then has a unique numeral name. In particular an unnamed number excludes this enlarged comprehension resource. The theorem neither adds infinitary syntax to finitary C nor supplies a global interpretation, arithmetic correctness, or an SP inconsistency proof.

Source: [infinitary-standard-numerals-20261022.md](../../notes/infinitary-standard-numerals-20261022.md), sections 2–3; [InfinitaryNumerals Lean source](../StrongPossibilityConsequencesInfinitaryNumerals.lean).

## Schema assembly and finite-proof reflection

The Schemas module first considers precisely the schema of Max-consistent sentences p for which C has an actual derivation of Dp implies p. SP entails every such sentence by its Dp instance and that derivation. Conversely, for an SP instance Dp, consistency of Max+p implies consistency of Max+Dp by the C theorem p implies Dp. The C idempotence certificate makes Dp itself a reflecting sentence. The reflecting schema therefore entails every SP instance. Conditional pure monism separately retains consistency of Max+E1. This module alone does not identify the reflecting schema with a syntactic universal grammar; that is UniversalCore's additional statement.

For finite-proof reflection, extract the finite Max-axiom support of a derivation of p, and call its conjunction Q. Each supporting distinctness axiom reflects ordinary possibility; the conjunction does too, by a C derivation. Discharging the finite assumptions gives a C theorem Q implies p and hence a C theorem possibility(Q) implies p. Only this C theorem is necessitated. In Max, Q itself supplies the witness for BoxNe p. This proves reflection of actual Max derivations without necessitating optional assumptions.

If p is not a Max theorem, the deduction theorem yields consistency of Max+not-p; the corresponding SP instance is not-BoxNe p. Combining this with reflection gives the exact BoxNe and negative-BoxNe theorem diagrams under the explicitly retained consistency hypotheses for Max and SP. No such consistency hypothesis is proved here.

Sources: [reflection-universal-core-20261022.md](../../notes/reflection-universal-core-20261022.md); [sp-diagram-hat-audit.md](../../notes/sp-diagram-hat-audit.md); [Schemas source](../StrongPossibilityConsequencesSchemas.lean); [Reflection source](../StrongPossibilityConsequencesReflection.lean).

## The actual universal grammar

UniversalCore defines finite Boolean matrices of typed identities and closes
them under finite universal prefixes. The identity arguments are arbitrary
admitted typed terms and may themselves contain quantifiers. Finiteness and
universality here describe the outer Boolean-identity matrix and its prefix;
they do not say that all subterms are quantifier-free or identify a first-order
or arithmetic hierarchy class. Structural induction on the matrix
constructs its distinctness-modality stability certificate. Structural induction
on a universal prefix then constructs a C derivation of Dp implies p, using the
existing universal-reflection certificate and explicit renaming/substitution
conversions. It does not assume a Barcan principle.

For any closed p, the formula saying that every nonzero possibility-fixed r
has nonzero conjunction with p is a member of this universal grammar. An actual
C certificate identifies it with Dp. If Max+p is consistent, this normal form
is also consistent with Max, by C's p implies Dp and that equivalence. Thus
the schema of individually Max-consistent universal-grammar sentences entails
every SP instance. Conversely, SP gives Dp for each such universal p, and its
constructed reflection derivation yields p. The equivalence of consistency
follows by entailment in both directions. Neither consistency is assumed or
established by this equivalence.

Source: [reflection-universal-core-20261022.md](../../notes/reflection-universal-core-20261022.md);
[UniversalCore Lean source](../StrongPossibilityConsequencesUniversalCore.lean).

## The finite-disjunction consistency criterion

This argument concerns the existing finite universal grammar and keeps Con(Max)
explicit in the forward direction. The restricted property says that whenever
Max derives the negation of a finite conjunction of universal sentences, Max
derives the negation of at least one conjunct. The empty conjunction is top.

Suppose the universal core is consistent and the property fails for a list L.
Max proves the negation of its conjunction, but proves no negated conjunct.
The deduction theorem makes each extension Max+a consistent. Each a therefore
belongs to the universal core, which proves their conjunction. Under Con(Max),
the universal core entails SP and SP entails Max, so it also proves the
negation of that conjunction, a contradiction.

Conversely, a contradiction from the universal core has finite axiom support
L. Discharge its conjunction to obtain a C theorem negating that conjunction.
Every member of L is universal and individually consistent with Max. The
restricted property yields a Max proof negating a member, contradicting its
individual consistency. Thus the property implies consistency of the core.
Combine this with the two-way SP/core entailment for the stated equivalence.
This proves a criterion; it does not establish that the restricted property
holds. Current compiler acceptance is recorded separately in the ledger.

Sources: [reflection-universal-core-20261022.md](../../notes/reflection-universal-core-20261022.md),
sections 5–7; [sp-failed-disjunction-20261022.md](../../notes/sp-failed-disjunction-20261022.md),
section 17; [Disjunction Lean source](../StrongPossibilityConsequencesDisjunction.lean).

## Closed-identity conservativity

If Max+Ax is consistent, its closed typed identities coincide with those of C
by MaxDiagram. This immediately makes Ax conservative for these identities.
For the converse retain Con(Max) and suppose Ax is identity-conservative but
Max+Ax is inconsistent. Extract finite axiom support and collect its Max
members in K. Write Q for their conjunction. Every remaining supporting axiom
belongs to Ax. Hence C+Ax+Q proves contradiction, so C+Ax proves not-Q.

Each Max axiom reflects ordinary possibility, and the conjunction Q inherits
that reflection. The C certificate for this implication turns not-Q into
Box(not-Q), which is the closed typed identity (not-Q)=top. Conservativity
makes that identity a C theorem, and consequently not-Q is a C theorem. But
Max proves Q from the members of K. This contradicts Con(Max). No consistency
of Max+Ax was assumed in the converse, and no arithmetic or effective-coding
claim enters it. Current compiler acceptance is recorded in the ledger.

Sources: [max-degree.md](../../notes/max-degree.md), section 11;
[theory-space-comparison.md](../../notes/theory-space-comparison.md), section 9;
[MaxConservativity Lean source](../StrongPossibilityConsequencesMaxConservativity.lean).

## Signature splitting of the one-individual Fregean cell

Let c be a constant of a closed relational type. Construct two full
extensional interpretations with singleton individual domain. Interpret every
relational constant as the constantly true relation in the first, and as the
constantly false relation in the second. Both satisfy Fregeanity and the
one-individual sentence. The first satisfies c=top. The second falsifies it:
induction on the relational type, using nonempty argument domains, separates
the constantly false and constantly true relations. Soundness therefore gives
the two C-consistency side conditions for the cell conjoined with c=top and
with its negation.

Max entails the corresponding possibility instances. The existing C
atom-no-split certificate says that an atom cannot have both these possible
parts. Thus signature Max proves that the cell is not an atom. An admitted
signature supplies a constant of a closed relational type, so the conclusion
holds for every admitted signature and remains valid for infinite signatures.
The proof does not supply the separate pure-profile Max+Atom model or prove
the proposed full pure/signature-SP incompatibility. Current compiler
acceptance is recorded in the ledger.

Sources: [audit-signature-to-pure-sp-20261022.md](../../notes/audit-signature-to-pure-sp-20261022.md),
section 3; [audit-profile-20261022.md](../../notes/audit-profile-20261022.md),
section 6.2; [SignatureSplit Lean source](../StrongPossibilityConsequencesSignatureSplit.lean).

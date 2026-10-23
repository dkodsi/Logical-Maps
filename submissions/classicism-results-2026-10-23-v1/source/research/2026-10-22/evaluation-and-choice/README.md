# Evaluation, representation, and Choice: research guide

22 October 2026. This is a guide to the accompanying mathematical notes, not
a database update. Proofs are ordinary mathematical arguments. No novelty,
human certification, or Lean verification is claimed.

Write **T = C + boxed Plenitude**. This is the existing positive core,
equivalently C + boxed ND at all types + Atomicity at all relational types.
The fixed relational type system permits sigma→tau only when tau is not e;
individual functions below always mean represented functional graphs.

## 1. The strongest simplification: one evaluation principle gives T

A weak complete evaluator E:t→t has bivalent values and preserves negation
and propositional universal quantification in current truth:

    ∀p (Ep=⊤ or Ep=⊥),
    ∀p (E(¬p) ↔ ¬Ep),
    ∀F (E(∀p Fp) ↔ ∀p E(Fp)).

**Over C, T is equivalent to saying that every possible proposition is
made true by such an evaluator.** Equivalently these evaluators separate
all distinct propositions. This uses the existing language and introduces
no Choice axiom.

Consequently **boxed Functional Choice is exactly this evaluator-density
principle plus Relational Choice** over C. The two factors are independent:
supported models give T without Relational Choice, while the generic model
below has boxed Relational Choice without T. This gives a direct structural
formulation of the user's preferred stronger theory.

The proof derives ND_t, BF_t and Atomicity_t separately, then uses the
proved recorded implications to recover the all-type core. A weak evaluator
determines a persistently possible atom w with the exact local Barcan
condition

    ∀F[(∀p □(w→Fp)) → □(w→∀p Fp)].

Its canonical replacement E_w(p)=□(w→p) preserves the quantified operation
as an object identity. The original weak evaluator need not do so: an
explicit finite-category example separates the two witness properties.

The density requirement is substantive. Even ND at all types, necessary
Atomicity at all relational types, and necessary existence of complete
evaluators do not imply T. A two-object category with a proper retract gives
all these assumptions and fails BF_t. In full action hierarchies, ND_t means
that every outgoing arrow is split monic, BF_t means every outgoing arrow
is epic, and T means every outgoing arrow is invertible.

Preserving only finite Boolean operations is strictly weaker, even with
substantial Choice. The bundle's existing full Boolean model B=2×A, with
A atomless and truth at the designated atom, admits uniform finite
evaluators and boxed Relational/Intensional Choice while failing T. It also
supports arbitrary set-sized conjunctions with common finite free variables
under the specified local introduction/elimination rules.
These are additional verified verdicts for that known construction, not
record edits. A stronger [generic-world construction](structural-mixing-models.md),
§31, has no atoms at any relational type and fails Functional Choice and
Plenitude at every world, despite the same finite evaluations and relational
Choice. Its full construction is given inside ordinary ZFC.

Read [the synthesis](structural-representation-root.md), §§19–22, and
[the full evaluator proofs](structural-world-representation.md), §§22–28.

## 2. A natural additional axiom: all individual extensions can occur

For R:et, let EU(R) mean that every admitted rigid individual property X
is a possible extension of R. Let S(R) mean that R's world profiles separate
world atoms. These say respectively that the profile map

    Worlds → admitted rigid subsets of Individuals

is onto and one-to-one. Their conjunction for the same R gives an exact
configuration space.

Both are genuine additions even over C + boxed Functional Choice + Infinity.
Full S5 models separate them: with E=ℕ, choose W=ℕ, W=P(ℕ), or
W=P(P(ℕ)). Under boxed FC, separate witnesses for EU and S can be combined
into one exact witness. Without Choice this combination can fail: an
explicit ordered finite-support model has EU and S, even BPI and retractions
preserving well-ordered indexed meets, but has no exact witness.

The type boundary is sharp. EU at any relational argument type is
inconsistent with T, by a diagonal using the injection of world atoms into
that type. The individual instance remains consistent because no such
injection is supplied by T.

There is one important unresolved implication in this research:

    T + EU_e + IC_e  ?⇒  ordinary choice with output type e.

Exact profiles + IC_e do imply that choice principle; EU_e + complete
Ret_t + IC_e also do. The general EU+IC question has not been settled here.
Several broad support constructions were ruled out as counterexamples;
those obstructions are not a proof of the implication.

Read synthesis §§1–8, 13–18; [world representation](structural-world-representation.md)
for transfer and infinitude; and [mixing models](structural-mixing-models.md)
for the explicit countermodels and unresolved boundary.

## 3. Three algebraic levels of Choice

All algebraic objects and families here are admitted, rigidly represented
objects; “complete” means preservation of every admitted family. Both
retraction rows below concern retractions onto INTERNALLY COMPLETE
subalgebras of relational type algebras. They do not quantify over arbitrary
subalgebras such as FinCof inside P(N).

| Requirement over T | Exact strength |
| --- | --- |
| Complete Boolean retractions at all types | Boxed Functional Choice |
| Finite-operation Boolean retractions at all types | Uniform ultrafilter choice, UFC |
| BPI for all represented Boolean algebras | UFC + FineUF; equivalently ACfin + FineUF |

FineUF supplies a fine ultrafilter on the internally finite subfields of
each represented field. It is equivalent to an indexed binary Rado
selection principle with an already supplied table of finite local choices.
ACfin chooses from finite nonempty fibers. The implication
FineUF + ACfin ⇒ UFC has a short proof: take a fine ultrafilter on finite
subsets of the serial relation, choose from each finite covered row, and
push the ultrafilter forward.

The two BPI factors are independent. The FineUF-without-ACfin model is an
explicit pair-flip construction. The reverse direction uses a published
ZFA model of UFC without BPI, transferred carefully into the fixed typed
hierarchy. **That underlying ZFA model is a literature-dependent input,
not reconstructed in these notes.** The direct source is [Howard–Tachtsis,
*On the minimal cover property in ZF* (2014)](https://www.sciencedirect.com/science/article/pii/S016686411400248X), Remark 4. The exact printed
page of that remark was not recovered.

The retraction definitions need only one canonical membership inclusion
per output type. There is no need to quantify over every subalgebra.
There is also an exact categorical comparison for complete maps between
nontrivial complete atomic represented algebras: T makes every object
projective; IC_all makes the proposition algebra injective; boxed FC makes
every object injective.

Preserving every well-ordered indexed meet remains weaker than full
completeness. Such retractions do give choice on fields with a well-ordered
separating family of predicates, including represented reals, but the
ordered-individual construction still fails individual Choice.

A uniform selector of COMPLETE evaluators on nonzero propositions is
different again: it is exactly well-orderability of the world-atom field.
It is stronger than separate Ret_t and independent of IC_all over T.
With EU_e it gives individual-output Choice without IC_e. See
[algebraic §42](structural-algebraic-core.md) for the explicit separations.

Read synthesis §§10–12, 16, 23 and [algebraic core](structural-algebraic-core.md),
especially §§26–41. The [mixing report](structural-mixing-models.md) supplies
the model constructions.

## 4. Infinitary syntax and pure witnesses: useful limits

Allowing countable disjunction with a common finite set of free variables,
and extending the theoremhood rules explicitly, identifies internally finite
Frege cardinals with the standard numeral disjunction. In that declared
extension the Infinity Schema and quantified Frege Infinity coincide.
Without the extension, the pseudo-finite examples show why they differ.

Arbitrary set-sized conjunctions with the same finite-parameter restriction
preserve the support models. Unrestricted independent object names do not:
their supports can accumulate and force much more of the external powerset
hierarchy. The syntax change must therefore be stated, not tacitly assumed.

The ordinary-ZFC generic model above initially handles finitary C. A
separate relative forcing-extension version retains its fully atomless
ordinary-world separation for C_omega, using countably closed forcing that
adds no countable sequences of ground objects. It makes no arbitrary
set-sized-connective claim. For the general finite-evaluation/Choice versus
T separation, the existing full Boolean model already handles arbitrary
set-sized connectives with common finite free variables under those local
rules. Unrestricted infinitary distributivity is not silently added to H
or to the theoremhood premise of Logical Equivalence. See
[world representation §34](structural-world-representation.md).

Simple existential axioms also need not have pure selected witnesses. Under
T there is no pure term selecting a universal individual-extension witness,
or selecting a complete evaluator when at least two worlds exist. Logical
permutations move every proposed selected world. This concerns definability
of a witness, not consistency of the existential axiom.

Read synthesis §§7, 15, 24 and the corresponding detailed companion sections.

## 5. Separate audits of the parent Strong Possibility construction

[The finite-profile atomicity audit](parent-profile-atomicity-audit.md)
supplies the needed pure truth-table elimination and respects the fixed
C-theoremhood restriction on necessitation.

[The root closure audit](parent-profile-root-closure-audit.md) checks
application, symbolic lambda abstraction, target-domain quantifiers and
the explicit Functionality failure. Both remain conditional on the
component-model existence/completeness theorem cited by the parent report.
Neither claims a signature expansion.

## Verification and provenance

The arguments were cross-checked among the three mathematical research
lanes. These are informal audits, not formal verification. Existing result,
model, generated-map and Lean files were left unchanged. Repository
validation is run after each note-edit batch; the final handoff records its
last result. Sources and qualifications are retained in the detailed notes.

Final saved-file check: 22 October 2026. This package contains the synthesis, three detailed companion reports, and two parent-construction audits. The accompanying validation log checks repository record integrity, not mathematical proof correctness.

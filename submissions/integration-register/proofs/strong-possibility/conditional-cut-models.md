# Conditional models with an arithmetically correct initial segment

OpenAI Codex, 26 October 2026. Direct source: `misc`, numbered proof sections below, unpaginated.

Fix either original language separately: pure L, or exactly
L({c:e→t}) without individual names. Write M=Max(C_L), and use B, E♯,
P♯ and c♯ from [the conditional-theory note](conditional-sigma-one-soundness.md).
All arithmetic below is the actual first-order Frege arithmetic, with
extensional arithmetic equality. The additional cuts, predicates and
maps belong to the external model presentation, not the target language.

## 1. A genuine conditional model with a correct arithmetic cut

**Theorem.** There is a countable genuine model N of M+E♯+¬c♯ whose
arithmetic K=Ar(N) has a proper initial segment J such that

    J satisfies true first-order arithmetic,
    J is Σ₁-elementary in K.

Every witness in K to any standard-false Σ₂ arithmetic sentence lies
strictly above every member of J. This holds simultaneously for all
standard-false Σ₂ sentences, not just P♯bottom.

N can additionally satisfy Strong Actuality, ordinary Barcan at every
admitted type, and current Relational and Transversal Choice. These are
properties of the auxiliary model, not additions to the SP reference M.

Here is the construction. Choose a countable genuine M-model A with
Ar(A) satisfying true arithmetic. Such models are already supplied by
[arithmetic-lifting.md, §1](arithmetic-lifting.md#1-statement-with-the-references-kept-separate).
Let Q be M with the displayed structural package. The established
[arithmetic conservation theorem](barcan-arithmetic-conservativity.md#1-exact-theories-and-statement)
says that Q and M have exactly the same arithmetic consequences.
Moreover Q+¬c♯ is Π₂-conservative over M: a proof of Π₂ sentence π
would give Q⊢c♯∨π, hence M⊢c♯∨π by arithmetic conservation, and
then M⊢π by the earlier Π₂ conservation of M+¬c♯ over M.

Consequently the compactness argument of
[conditional-sigma-one-soundness.md, §9](conditional-sigma-one-soundness.md#9-the-arithmetic-embedding-can-always-be-supplied)
works with Q+¬c♯ as its target. A finite Σ₁ elementary diagram has
Σ₂ existential closure, so a contradiction with this target would
give a Π₂ consequence already refuted by the source A. Thus there
are a countable genuine N⊨Q+¬c♯ and a Σ₁-elementary embedding
j:Ar(A)→K. In particular N satisfies the entire E♯ schema. Put

    J = {b in K : b ≤ j(a) for some a in Ar(A)}.

This is an initial arithmetic substructure: bounds from j[Ar(A)] are
closed under successor, addition and multiplication. Gaifman's splitting
theorem gives j[Ar(A)]≺J, so J satisfies true arithmetic and PA.

The needed preservation from J to K also has a direct proof. Let
δ(x,y) be bounded, let b∈J, and suppose K⊨∃x δ(x,b). Choose a with
b≤j(a). In Ar(A), PA's finite collection gives d such that

    ∀y≤a ∀x (δ(x,y) → ∃x'≤d δ(x',y)).                  (1)

For fixed a,d this is Π₁, so j preserves it. Applied in K to b and
its witness, it gives a witness x'≤j(d), hence x'∈J. Bounded formulas
are absolute between the initial substructure J and K. This proves
Σ₁-elementarity; finite tuples of parameters are handled by a common
bound and the same finite-collection argument. Its converse direction
is immediate from bounded absoluteness.

Now let σ=∃u Q(u) be standard-false, with Q Π₁. If K⊨Q(b) and b∈J,
Π₁-elementarity would give J⊨Q(b), contrary to J's true arithmetic.
Thus b∉J; since J is initial, b lies above its whole domain. Taking
σ=P♯bottom supplies such a b and proves that J is proper.

The external splitting theorem is checked in Taishi Kurahashi and
Yoshiaki Minami, *On collection schemes and Gaifman's splitting theorem*,
accepted manuscript, Theorem 2.10, printed p.7. Theorem 2.13 on the same
page also supplies the Σ₁-elementarity conclusion used above; the
argument (1) verifies the particular case directly.
[Manuscript](https://da.lib.kobe-u.ac.jp/da/kernel/0100492302/0100492302.pdf);
[published article](https://doi.org/10.1002/malq.202400021).
The application to the unchanged Classicism theories is the deduction
here, not a result attributed to that paper.

## 2. A pair of genuine typed models sharing this arithmetic segment

The construction can be arranged so that J is countable and recursively
saturated. Expand the external presentation of N by a predicate for J
and take a countable recursively saturated elementary extension of that
expanded structure. Such an extension is obtained by successively
realizing the recursive types over finite parameter sets that are
finitely satisfiable, using compactness and an elementary chain.

Each assertion that J is initial, each relativized true arithmetic
sentence, and each instance of Σ₁-elementarity is a first-order assertion
of the expanded structure. They therefore survive the extension, as do
N⊨M+E♯+¬c♯ and the assertion that the cut is proper. The interpreted
J is recursively saturated: relativize a recursive arithmetic type to
the cut and add membership in the cut before applying saturation.

The arithmetic-lifting theorem now supplies a separate genuine model
A₀⊨M+E₁ with Ar(A₀) isomorphic to J, where E₁ says that there is one
individual. Consequently there are two genuine typed models with

    Ar(A₀) = J ⊊ K = Ar(N),     J ≺Σ₁ K,
    A₀ ⊨ M+E₁+c♯,             N ⊨ M+E♯+¬c♯.          (2)

Their arithmetic inclusion is initial and preserves both signs of every
Σ₁ formula with parameters. This is an arithmetic map between full
models; no map through their higher typed domains has been supplied.
A₀ is not asserted to satisfy E♯. The pair supplies actual structures
on both sides of the proposed lifting problem.

The ambient Barcan property has a useful concrete consequence. For
every p∈N_t and f∈N_(σt),

    p∧∃_σ f ≠ bottom implies
    p∧f(a) ≠ bottom for some a∈N_σ.                   (2a)

Indeed C_L identifies p∧∃_σ f with ∃x(p∧f(x)), and the ordinary
Barcan dual is ◇∃x R(x)→∃x◇R(x). Thus the ambient model supplies
nonzero instances even when its current truth assignment does not make
the existential true. The further requirement in §§3–4 is to choose
such witnesses while preserving the candidate algebra's proof and
truth constraints.

## 3. Subalgebras whose finite diagrams have proof witnesses in J

For each original existential finite-Boolean identity sentence F, write

    P♯F = ∃u Q_F(u),

with Q_F Π₁. Call a finite tuple a of entities of N admissible relative
to J if, for every finite Boolean combination θ(x) of whole typed
identities in the original language,

    N ⊨ θ(a) implies
    N ⊨ Q_(∃x θ)(u) for some u∈J.                     (3)

Closed coefficients and terms in θ remain unrestricted. This definition
concerns entity identities, not current truth values of arbitrary
propositions. Since J is Π₁-elementary in K and has true arithmetic,
(3) is equivalent to

    N ⊨ θ(a) implies M ⊢ ∃x θ(x).                     (4)

Indeed a witness in J is a witness in J to the arithmetic assertion
P♯(∃x θ), which J evaluates correctly. Conversely an actual M proof
has a standard proof code, and its Π₁ correctness statement holds in
J and K. Standard proof codes belong to J.

**Closure lemma.** If a is admissible, adjoining any finitely many term
values t₁(a),…,t_m(a) preserves admissibility. A union of an increasing
chain of admissible subalgebras is admissible.

For the first claim substitute these terms in a proposed Boolean
identity matrix θ. Its truth becomes the truth of θ'(a). A proof of
∃x θ'(x) yields a proof of the required existential statement by term
substitution and existential introduction. Equivalently apply (4).
For a chain, every tested tuple lies in one member. These arguments
include abstraction and the quantifier term operations; closing under
those operations is not the same as meeting the truth clauses for
quantifiers.

There is a nonempty starting subalgebra. Choose one individual a in N
and take all values of original-language terms with a as their only
additional parameter. The harmless one-individual-marker theorem says
that M decides all finite Boolean identities between those terms
uniformly in a. Every finite diagram true here is therefore M-provable,
and so is its existential closure. See
[inductive-witnesses.md, §1](inductive-witnesses.md#1-exact-framework-and-result)
for this input and its separate pure/signature sources.

Thus Zorn's lemma supplies a maximal admissible typed subalgebra of N
containing this starting algebra. It is still countable when N is.
Every such subalgebra has exactly one individual: two distinct ones
would realize ∃x,y(x≠y), which M does not prove because M+E₁ has a
model. This is a family of candidate algebras with unrestricted term
operations, not yet a family of genuine C-models.

## 4. Boolean truth assignments with the required arithmetic

**Theorem.** Let D be any admissible subalgebra from §3. Let Γ be a
set of original closed sentences such that M+Γ is consistent. There
is a Boolean truth assignment on D that respects every literal typed
identity and makes every member of Γ true.

To prove this, in D's Boolean algebra of propositions require the
values of Γ and all signed literal identities with their correct entity
truth values to belong to a filter. Suppose a finite meet were bottom.
Write γ for the finite conjunction from Γ and δ(a) for the finite
conjunction of the correctly signed identities. Then D realizes the EI
sentence

    ∃x [δ(x) ∧ (γ∧δ(x)=bottom)].                      (5)

Admissibility implies that M proves (5). But C_L proves (5)→¬γ:
δ is true at its witness, while the proposition γ∧δ is literally
bottom. This contradicts consistency of M+Γ. The required filter is
therefore proper. Extend it to an ultrafilter. Membership is the required
Boolean truth assignment; a disequality requires the complement of its
equality proposition to belong to the ultrafilter.

In particular take Γ to contain all M-theorems and all standard-true
Π₂ arithmetic sentences. This Γ is M-consistent, using the established
standard-arithmetic M-model. Thus the target's arithmetic truth values
and all literal identities can already be realized together on D.
One may even include all true first-order arithmetic at this stage.
These are Boolean truth assignments, not yet quantified truth models.

There is a precise way to attack the remaining clauses. Let X_D be the
space of all ultrafilters satisfying the preceding constraints, with
Γ=M+TrueΠ₂. It is a nonempty closed subspace of the Stone space of
D's proposition algebra. For each predicate f:σ→t in D define the open
set

    W_f = {U∈X_D : (∃_σ f)∉U}
          ∪ ⋃_(a∈D_σ) {U∈X_D : f(a)∈U}.             (6)

If every W_f is dense in X_D, the Baire theorem gives an ultrafilter
in their intersection: D and the language are countable. The algebraic
inequality f(a)≤∃_σ f already holds in D, so membership in all W_f
gives exactly the missing direction of existential truth. Universal
truth follows by Boolean duality. Together with the literal identity
clauses and the retained abstraction/application operations, this is a
genuine Henkin truth expansion satisfying C_L and Γ.

Section 5 then makes this a full SP model. The density of the W_f has
not been proved. It is now a specific extension task: every finite
Boolean truth condition compatible with the identity and arithmetic
constraints must allow either the existential to be false or one of
its instances to be true. Failure of density for a chosen D would only
reject that candidate, not refute unrestricted SP.

For the consistency question, §8 replaces this fixed-domain sufficient
test with first-stage survival. That weaker test allows a subsequent
Henkin completion to add entities and does not require density throughout
the original space.

## 5. What a truth expansion of an admissible algebra would establish

**Sufficient reconstruction theorem.** If an admissible subalgebra D
from §3 admits a genuine C_L truth expansion on those same domains and
with those same term operations, that expansion is a model of the full
original SP theory.

First it is an M-model. D contains the original closed terms, and its
ground identities and disequalities are those of N⊨M. Any C_L truth
expansion respects literal entity identity, so the original Max axioms
hold.

Next take any original sentence P with M+P consistent. If the expansion
failed DP, it would satisfy H¬P. Use the established identity normal form

    H¬P ↔ ∃r (r≠bottom ∧ r=◇r ∧ r∧¬P=r).              (7)

The right side is an existential finite-Boolean identity sentence F.
Its witness belongs to D, so admissibility gives M⊢F. But C_L proves
F→¬P by (7) and factivity, contradicting consistency of M+P. Thus
every licensed DP holds. No arithmetic identification for this eventual
truth expansion is needed for this proof.

This gives a concrete construction task: enlarge the admissible starting
algebra, or choose a suitable maximal one, so that the full quantified
truth clauses can be realized. Maximality alone has not been shown to
give those clauses. Merely restricting N's existing truth predicate is
not a proof that they hold. In particular the theorem does not assert
that the algebras just constructed already have the required expansion.

## 6. A more local transfer test for a proposed higher-type lift

There is also a way to test a proposed lift of (2) before solving the
whole truth-expansion problem. Suppose A is a genuine M-model, there is
a full typed algebra embedding f:A→N, and an arithmetic embedding
j:Ar(A)→K preserving and reflecting Π₁ formulas. Suppose that, for
every original existential finite-Boolean identity sentence F true in A,
some witness u to Q_F in K lies in j[Ar(A)]. Then A satisfies E♯.

For if u=j(v), Π₁ reflection gives Ar(A)⊨Q_F(v), so A⊨P♯F.
This proves every F→P♯F; by the exact identity normalization in
[conditional-sigma-one-soundness.md, §8](conditional-sigma-one-soundness.md#8-the-exact-identity-fragment-and-a-common-embedding-target),
these are all of E♯. If Ar(A) additionally satisfies TrueΠ₂, the
exact equivalence SP=E♯+TrueΠ₂ makes A a full SP model.

The ambient N already supplies proof witnesses because it satisfies E♯,
and the full algebra embedding preserves the existential identity
instances from A. The extra requirement is that those particular proof
witnesses can be found in the source arithmetic image. Sections 1–2
construct the arithmetic configuration; §3 verifies this requirement
on the starting term algebra and under term closure. Extending it while
meeting unrestricted quantified truth remains the unproved step.

## 7. Genuine extensions and a single universal ambient model

**Extension theorem.** Every admissible algebra D embeds, preserving all
typed term operations, in a genuine model of M+Γ whenever M+Γ is
consistent. The embedding need not preserve an externally chosen truth
assignment on D.

Add external names for D and its full atomic and negated-atomic algebraic
diagram to M+Γ. A finite part δ(d) of that diagram has existential
closure F=∃x δ(x) in EI. By admissibility, M proves F. If the expanded
theory were inconsistent, finitely many of its diagram assertions and
a finite conjunction γ from Γ would give

    M+γ ⊢ ¬∃x δ(x).

This contradicts M⊢F and consistency of M+γ. Compactness supplies
the model and the diagram supplies an injective algebra map. All names
remain external to the original SP language.

In particular D embeds in a genuine M+E₁+TrueΠ₂ model, and even in
one whose arithmetic satisfies all true first-order arithmetic: the
standard-arithmetic singleton M-model proves the required consistency
of these extra sentences. Thus there is a span of full algebra maps

    A_good ← D → N,

where A_good has correct arithmetic and N satisfies the full conditional
theory. A_good has genuine quantified truth; it is not asserted to
satisfy E♯. Any EI sentence true in A_good but unprovable in M has no
witness tuple entirely in the displayed copy of D. This follows directly
from admissibility. The missing property is therefore confined to the
additional entities, rather than to existence of a genuine extension.

There is also a universal choice of the right-hand ambient model.
Take an ℵ₁-saturated elementary extension of the expanded pair (N,J)
from §1, and retain the same notation. It may be uncountable; its cut
still satisfies true arithmetic, is proper and Σ₁-elementary, and N
still has the conditional and structural properties of §1. We continue
to use countable candidate subalgebras.

**Universality theorem.** Every countable typed algebra A for which

    A⊨F implies M⊢F, for every original EI sentence F,   (8)

embeds into this one fixed N. Here A must carry the original typed term
operations; (8) then applies to the finite parts of its algebraic diagram.

Indeed Th(N,J) together with that diagram is consistent: each finite
diagram has existential closure already provable in M and hence in
Th(N,J). Realize the full countable diagram in a model of Th(N,J).
Its enumerated tuple has a complete countable type in the expanded
language. Saturation, or successively realizing its types over the
previously placed finite tuples, places an isomorphic algebraic copy
in N. No identification of an originally chosen individual is required.

If full SP has a model, it has a countable one A, and its algebra
satisfies (8). For otherwise M⊬F with A⊨F would license D¬F, while
C_L proves F↔HF and consequently D¬F↔¬F. This contradicts A⊨SP.
Its embedded algebra is admissible relative to J by §3, and transporting
A's truth predicate gives a genuine SP truth expansion on that copy.
Conversely §5 turns any genuine C truth expansion of an admissible
subalgebra into an SP model.

Consequently, for this fixed saturated pair (N,J), the following is an
exact equivalence, separately for each original reference:

    Con(SP) iff some countable admissible D⊆N
                admits a genuine C_L truth expansion. (9)

Unlike requiring the particular marked term algebra, or an elementary
extension of it, to support truth, (9) does not impose an additional
unproved restriction on possible SP models. The cut J tests proof
witnesses as in §3; it is not asserted to be the actual arithmetic of
the eventual truth expansion of D.

## 8. First-stage survival suffices inside this model family

Fix countable admissible D⊆N. Give every element an external name and
let T_D consist of C_L, the algebraic diagram of D, M, E₁ and TrueΠ₂.
By §7 this is a consistent countable theory. Its complete consistent
extensions form a compact Stone space Y_D. Equivalently use the Boolean
truth assignments of §4 with Γ=M+E₁+TrueΠ₂: every closed expression
in the naming language evaluates in D, and the algebraic diagram fixes
that evaluation. Boolean truth and the C identities make each such
assignment a consistent closed theory. Its genuine Henkin completion
may have additional entities.

For f∈D_(σt), define W_f in Y_D by (6), using the names for f and
its arguments, and put

    Y_D,1 = ⋂_f closure_(Y_D)(W_f).                    (10)

**Theorem.** If Y_D,1 is nonempty, full SP is consistent. It is enough
to show that each W_f is nonempty; density in Y_D is not required.
More explicitly,

    Y_D,1≠∅ iff, for every f,
      T_D⊢∃_σ f implies
      Con(T_D+f(a)) for some a∈D_σ.                   (11)

To prove the first claim, take a licensed SP sentence DP and its
one-variable existential identity counterform F=H¬P from (7).
Every instance of F's matrix at an element of D is false as a literal
identity assertion: a true instance would make M prove F and hence
¬P. The algebraic diagram therefore refutes every named instance.
Its witness open is just the clopen set of theories containing DP.
Thus every point of Y_D,1 contains all original SP axioms. Henkin
completeness gives a genuine SP model, with additional entities allowed.

For (11), use the first-stage compression argument already proved in
[the earlier first-stage note, §§3–4](../../../classicism-results-2026-10-24-v2/proofs/signature-sp-first-stage.md#4-total-deletion-compresses-to-one-globally-empty-witness-open).
Here is why it applies to D and both present languages. If (10) is
empty, compactness gives finitely many clopen conditions p_i covering
Y_D, each forcing an existential ∃f_i while refuting every named
f_i-instance. The predicates and conditions all have values in D.
The disjunction of p_i∧f_i(x_i) has T_D-provable existential closure
and every named tuple instance is refuted by T_D. Individual-sort
requirements cannot cause a failure: E₁ makes their existential
equivalent to the instance at D's sole individual. The remaining
relational tuple variables have the exact C-definable tuple code and
term projections given in the cited proof. D is closed under those
operations. Compressing the tuple produces one predicate f with W_f
empty. Conversely an empty W_f plainly makes (10) empty. Finally,
W_f is nonempty exactly when the existential is not T_D-provable or
some named instance is T_D-consistent. This proves (11).

This uses the previous first-stage theorem; that mechanism is not a new
discovery here. The extension is to the entire admissible model family
with the arithmetic constraints present. Together with §7 it yields

    Con(SP) iff some countable admissible D⊆N
                satisfies the weak witness property (11). (12)

For the remaining direction, a countable SP model embeds algebraically
in N by §7. Its transported truth assignment belongs to Y_D and to
every W_f, hence to Y_D,1. Thus (12) is exact, although (11) for a
particular candidate remains a sufficient test rather than a necessary
condition for SP consistency in general. No survivor of (10), and no
proof of (11) for an unrestricted candidate, has yet been constructed.

## 9. A witness-extension test with a finite refutation certificate

Keep the countable admissible D and consistent T_D of §8. Suppose
T_D proves ∃x F(x), where F may use names for elements of D. Introduce
one fresh name b of the witness type. Form the countable theory

    U(D,F) = T_D + F(b)
      + {¬θ(d,b) : θ is a finite Boolean identity matrix,
                    d is a finite tuple from D, and
                    M ⊬ ∃y,z θ(y,z)}.                 (13)

Each matrix uses only the original language besides its displayed
variables. All parameters in d are existentially closed in its
eligibility test. The reference is the unchanged original M.

**Extension test.** U(D,F) is consistent exactly when D has an
admissible algebraic extension, generated by one additional witness,
inside some genuine model of T_D in which F holds of that witness.

For the forward direction take a model of (13), identify its named
copy of D, and close D∪{b} under the typed term operations. Every
finite identity diagram in this closure pulls back by term substitution
to a matrix θ(d,b). If its existential closure were not M-provable,
(13) would forbid that matrix. Thus the closure is admissible, and
F(b) is true in the genuine surrounding model. Conversely any such
extension satisfies every forbidden-pattern clause of (13), giving
a model of U(D,F).

**Finite-refutation theorem.** If U(D,F) is inconsistent, then the
full original SP theory is inconsistent. Compactness provides a finite
certificate of the following form:

* a finite identity diagram δ(y) true of a tuple in D, so M⊢∃y δ(y);
* a finite conjunction γ of original axioms from M+E₁+TrueΠ₂;
* finitely many identity matrices θ_i(y,z), with
  M⊬E_i for E_i=∃y,z θ_i(y,z);
* proofs in M+γ of

      δ(y) → ∃z F(y,z),
      δ(y) ∧ F(y,z) → ⋁_i θ_i(y,z).                  (14)

To extract it, combine the finitely many diagram assertions and original
axioms used in an inconsistency proof for (13) with those used in the
given proof of ∃F. Rename the finitely many diagram parameters as y
and the new witness as z. Admissibility gives the first bullet.
The finitely many forbidden-pattern clauses give the second implication
in (14). Unused variables can be included in the existential closures
because all sorts are nonempty. Thus M+γ proves ⋁_i E_i.

Full SP entails γ. For each i, M⊬E_i makes M+¬E_i consistent, so
SP entails D¬E_i. Since E_i is EI, C_L proves D¬E_i↔¬E_i.
These conclusions contradict the displayed finite disjunction. This
is a refutation of the full target, not only of a particular candidate.

Equivalently, if SP is consistent, every demand (13) is soluble. There
is also a direct model proof: §7 embeds D into a genuine SP model;
that model satisfies T_D, supplies the required witness, and its whole
algebra is admissible. Its generated subalgebra gives the extension.

The test quantifies over genuine extensions of the diagram. One failed
choice of witness, or failure to extend a particular fixed embedding
inside N, is not an inconsistency proof for (13). The M-nonprovability
conditions in a proposed finite certificate must also be established;
absence of a found proof is insufficient.

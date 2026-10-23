# Audit note: the profile-root atomicity step

Original mathematical audit, 22 October 2026, structural research lane.
This concerns §2 of `research/2026-10-22/strong-possibility-obstructions.md`.
It does not modify that file or contest the construction's already reported
independent audits. The point below is a proof-detail obligation and a
proposed direct resolution.

The argument that `p ∧ A_n` has profile bottom or A_n needs identity of
component propositions at ALL component points. Agreement of actual truth
only at the points satisfying A_n does not immediately establish those
identities: at a point where A_n is false but possible, A_n may be a nonzero
proposition. A proof through the full action representation's separation of
propositions by all future arrow evaluations could resolve this, if that is
the precise component-model semantics used.

There is also a direct finitary syntactic resolution. For every positive n
and pure proposition term T(z) with only one possible free individual
variable, establish the finite extensional completeness lemma:

    either C proves forall z (A_n -> T(z)),
    or     C proves forall z (A_n -> not T(z)).

Reason: under Fregean extensionality and exactly n individuals, every type
appearing in the finite term has a finite full extension domain. Enumerate
the individuals with z first, enumerate each higher type by its finite truth
table, and eliminate the finitely many typed quantifiers. Lambda and
application evaluate by those finite tables. The resulting pure pointed
structure has a fixed truth value, independent of the chosen individual
enumeration. This gives an actual finite derivation of the displayed
conditional theorem, rather than necessitating a premise.

Necessitate that CLOSED C-theorem and apply Converse Barcan, which is
available in C. One obtains, uniformly in z, either

    Box(A_n -> T(z))     or     Box(A_n -> not T(z)).

The Boolean algebra identity criterion then gives respectively

    A_n and T(z) = A_n   or     A_n and T(z) = bottom.

These hold at every component point, including those where A_n is false.
They are exactly the identities required of the root profiles. The argument
uses no BF, ND, optional necessitation, or Strong Possibility consistency.

## Finite-table lemma at referee detail

Here is the finite derivation justifying the lemma. It was independently
checked by the world-representation research agent; that is not a named-human
or proof-assistant certification.

Fix n and T. Work temporarily under F and an enumeration a_1,...,a_n of all
individuals, with the a_i distinct. Only the finitely many types occurring
in T and their constituent types are needed. Define exhaustive lists L_σ
recursively. L_e is the displayed enumeration, and L_t is (top,bottom).
Given the already exhaustive distinct lists at σ and τ, enumerate every
map f from the finite index set of L_σ to that of L_τ. If τ=ρ̄t, represent
its truth table by the term

    λx^σ λz̄^ρ . OR_i [x=L_σ(i) and L_τ(f(i))[z̄]].

Under F, current coextension implies identity at every relational type:
Frege makes a true proposition necessary, and C's Intensionality theorem
then gives the relational identity. This also gives the needed Functionality.
Consequently the displayed table has exactly the chosen values on L_σ.
Different maps have different values at some listed argument and therefore
give distinct operations. Conversely, an arbitrary operation has one listed
τ-value at each of the finitely many listed σ-arguments. Finite case
analysis chooses the corresponding finite table; exhaustive input coverage
and Functionality identify the operation with that table. No Choice schema
or forbidden individual-output operation is used.

Thus every quantifier occurring in the fixed finite term T can be replaced,
inside this conditional proof, by a finite conjunction/disjunction over its
list. Beta reduction, table lookup, equality of list entries and the two
truth values decide the resulting expression. For T(z), choose an individual
enumeration with a_1=z; E_n guarantees such an enumeration. The computation
depends only on the index positions and equality pattern, so its truth value
is the same for every enumeration with that convention. Equivalently, any
permutation of the n names transports all higher truth tables with it.

Discharge F and the finite enumeration, then universally close z. This gives
one of the two CLOSED conditional C-theorems displayed above. Necessitation
is now applied to a theorem of C, not to a theorem with optional assumptions.
Converse Barcan and the Boolean identity criterion give the exact component
identities required by the profile-root argument.

Status: the identity step is resolved by this finite syntactic lemma. This
does not replace the separate obligation to verify all root-domain closure
and action-model clauses, and makes no literature novelty claim.

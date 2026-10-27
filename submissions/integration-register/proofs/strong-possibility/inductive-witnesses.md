# Finitary inductive witnesses at arbitrary relational types

Ordinary mathematical argument by OpenAI Codex, 26 October 2026 (`misc`); numbered sections, unpaginated.

## 1. Exact framework and result

Treat the following languages separately:

* L is the original pure language, with M = Max(C).
* L has exactly Σ={c:e→t}, with M = Max(C(Σ)).

In either case write C_L for its fixed base. Introduce one auxiliary
individual name a, and write C_a=C_L(a). The target SP schema still uses
M-consistency for closed sentences of L; its reference theory is never
changed to the marked theory. All types are the original relational types.

The new result is a witness theorem for finitely specified, possibly
mutually inductive domains at arbitrary relational types. Constructors may
be arbitrary L(a)-terms. Their applicability conditions may contain
arbitrary quantifiers, provided C_a proves those conditions persistent under
ordinary necessity. An unconditional constructor is the special case with
condition top.

For outer existential witnesses restricted to these domains, M has the
finite disjunction property for arbitrary finite Boolean combinations of
whole typed identities. The terms inside those identities are unrestricted.
There is also a uniform ground-witness characterization and a simultaneous
model of the corresponding universal-identity SP fragment. In the unary
signature, all witness opens restricted to these domains have a common
point, even when their remaining truth conditions are arbitrary formulas.

None of these claims removes the restrictions on the outer witnesses.
Neither unrestricted SP theory is settled.

Two previously proved inputs are used throughout:

1. The singleton profile model R_L is a genuine M-model. At a relational
   type τ₁…τ_k t its root domain consists of arbitrary actual extensions
   paired with L(a)-term profiles. In particular every subset of any root
   type is the actual extension of some admitted predicate at that root.
2. In every M-model, after choosing any actual individual a, identities
   between L(a)-terms have exactly their C_a-provable truth values:

       S(a)=T(a) holds  iff  C_a proves S(a)=T(a).

   Thus M decides every finite Boolean combination of these identities,
   uniformly at every a. This is not a decision of arbitrary truth formulas.

For the pure case these inputs are in
[profile construction](../../../classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/profile-root-construction-20261022.md),
§§1–3 and 6, and
[disjunction analysis](../../../classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/sp-failed-disjunction-20261022.md),
§2. For the exact unary signature see
[signature report](../../../classicism-results-2026-10-24-v2/proofs/signature-sp-derivative.md), §§2–3.
The signature report proves the harmless one-individual-name extension
specifically for a signature with no pre-existing individual names.

## 2. Finitely specified inductive domains

Choose finitely many indices i=1,…,r, with relational types σ_i. Types may
repeat. Choose finitely many constructor rules j. A rule has:

* input indices i(j,1),…,i(j,k_j), where k_j is finite and may be zero;
* an output index o(j);
* an L(a)-term f_j of the corresponding curried operation type;
* an L(a)-formula γ_j(x₁,…,x_kj), with just the displayed free inputs,
  for which C_a proves γ_j→□γ_j, universally over those inputs.

All output types are relational, so every displayed operation type is
admitted. Application to a tuple below means left-nested curried application.
An unconditional rule uses γ_j=top. A zero-input rule supplies a guarded
seed. There is no self-reference: the f_j and γ_j are fixed before the
inductive predicates below are defined.

For predicates X_i:σ_i→t, let Cl(X₁,…,X_r) be the finite conjunction,
over rules j, of

    forall x₁ … x_kj,
      (X_i(j,1)(x₁) and … and X_i(j,kj)(x_kj) and γ_j(x₁,…,x_kj))
        -> X_o(j)(f_j[x₁,…,x_kj]).

Define, by an ordinary finite higher-order formula,

    I_i(x) := forall X₁ … X_r, (Cl(X₁,…,X_r) -> X_i(x)).       (1)

The system has finitely many rules, so (1) uses no infinitary conjunction.
The number of possible finite construction trees is externally countable;
they are not added as an object-language disjunction.

Call a finite construction tree C_a-valid when each leaf is a zero-input
rule, its internal vertices apply matching rules to earlier outputs, and
C_a proves every instantiated guard occurring in the tree. Its output is
an L(a)-term at the indicated type. This definition permits different trees
to denote the same entity.

## 3. Closure and persistence are theorems of C_a

The family I is closed under every rule. Given I-membership of the input
tuple and its guard, take any closed family X. Formula (1) puts each input
in its corresponding X_i; closure puts the output in X_o(j). Quantifying
over X proves the required output I-membership. This also proves the seed
cases. Consequently every C_a-valid finite construction tree has
C_a-provable I-membership.

The leastness property is immediate from (1): Cl(X) implies
forall x (I_i(x)→X_i(x)) at every index.

**Persistence lemma.** C_a proves I_i(x)→□I_i(x) at every index.

Put J_i(x)=□I_i(x). Necessitate the universally closed C_a-theorem for
each rule's I-closure. Converse Barcan, a theorem of C, permits its boxed
instances at the current input tuple. Normal modal reasoning gives

    (all □I_input(x) and □γ_j(x)) -> □I_output(f_j[x]).

The stipulated C_a-theorem γ_j→□γ_j therefore proves Cl(J). Leastness
of I gives I_i⊆J_i. All necessitated premises here are whole C_a-theorems;
no optional Max axiom, true guard, or induction hypothesis is necessitated.

Reflexivity supplies the converse. Thus C_a proves

    I_i(x) <-> (I_i(x)=top).                                (2)

This is a material equivalence to an identity condition. It suffices to
rewrite a guarded matrix as a finite Boolean combination of identities.

Positive existential identity formulas are examples of permitted guards:
necessity of identity, finite positive connectives, and transport of an
existential witness prove γ→□γ. This is the earlier positive-persistence
lemma, not an additional restriction on the terms inside an identity.

## 4. Canonicity at the profile root and for named elements

In R_L let D_i be the externally least family of subsets closed under the
actual guarded constructor rules. Explicitly, start with empty subsets,
adjoin outputs of all applicable rules at successive finite stages, and
take the union of those stages. Finite arity ensures that this union is
closed. Its elements are exactly the outputs of finite applicable trees.

For each i choose an admitted predicate P_i whose actual extension is D_i;
the profile may be any available profile, for example top. These choices
are available simultaneously because there are finitely many predicates
and the root admits every actual extension. By construction Cl(P) is
actually true. Formula (1) therefore gives I_i⊆D_i at the root. Conversely,
finite induction on an applicable construction tree, using the I-closure
theorems of §3, gives D_i⊆I_i. Hence

    I_i(R_L) = D_i.                                        (3)

Every applicable tree at this root is in fact C_a-valid. Induct through
the tree. Its earlier outputs are L(a)-terms. A true instantiated guard γ
is persistent by its C_a-theorem, so γ=top is true at R_L. The common
marked identity diagram then makes γ=top, and hence γ, C_a-provable.
This verifies each guard in the finite tree.

**Ground canonicity theorem.** For every L(a)-term b:σ_i,

    C_a proves I_i(b)
      iff some C_a-valid finite output u at index i satisfies
          C_a proves b=u.                                  (4)

For the forward direction evaluate the theorem in R_L. By (3), b equals
the output u of an applicable finite tree. That tree is C_a-valid by the
preceding paragraph. Since both b and u are named, their actual equality
at the root is C_a-provable by the common identity diagram. The reverse
direction follows from the finite-construction membership theorem and
substitution.

There is also uniform canonicity of named membership in arbitrary
M-models: if I_i(b) is true at any chosen a in any such model, persistence
and the common identity diagram make C_a prove I_i(b), so (4) applies.
If C_a does not prove I_i(b), Max's disequality I_i(b)≠top and (2) refute
that named membership uniformly.

This theorem does not say that all unnamed I-elements in every M-model
are finite construction outputs. The profile root is standard for these
inductive domains; arbitrary M-models need not be.

## 5. Mixed-identity extraction and the finite disjunction property

Consider a closed L-sentence

    E := exists a:e exists x₁:σ_i1 … x_n:σ_in,
           (all I_ik(x_k;a) and θ(a,x₁,…,x_n)),              (5)

where θ is any finite Boolean combination of whole typed identities
between L-terms. Terms inside its atoms may contain arbitrary higher-type
quantifiers, lambda abstractions, applications, and both modalities.
Different witness variables may use different finite inductive systems;
their disjoint union is a single finite mutual system. A missing individual
variable can be added vacuously, since individual domains are nonempty.
Additional unrestricted individual witnesses can likewise be allowed:
they all receive a at the singleton root and in the extracted instance.

By (2), (5) is C_L-equivalent to an existential finite Boolean identity
sentence in the original disjunction criterion.

**Theorem.** The following conditions are equivalent:

1. M proves E.
2. R_L satisfies E.
3. There are C_a-valid finite constructor outputs u₁(a),…,u_n(a) for the
   respective domains such that the marked ground matrix θ(a,u₁,…,u_n)
   is true in the common identity diagram.

Moreover condition 3 supplies M-provable witnesses uniformly at every
actual individual a, with C_a-proofs of their inductive memberships.

The implication 1→2 uses R_L⊨M. For 2→3 choose the root's witnesses;
(3) and the valid-tree argument replace each by a finite constructor term
with exactly the same entity value. Thus θ remains true, including every
disequality and every quantified term inside its atoms. For 3→1, the
membership claims are C_a-theorems. The complete marked identity diagram
makes the finite Boolean matrix M-provable uniformly at every a.
Existential introduction supplies E.

**Disjunction corollary.** For any finite list of sentences of form (5),
possibly using different types, systems, and matrices,

    M proves E₁ or … or E_m  ->  M proves some E_j.          (6)

Indeed the single model R_L realizes some branch of the proved disjunction;
the theorem extracts that branch. This proof works independently with
M=Max(C) and with M=Max(C(Σ)). No conservativity between them is invoked.

Neither theorem asserts an effective decision procedure: the mixed ground
diagram includes non-C-provability conditions for negative identities.

## 6. One model realizes all corresponding universal SP instances

Let U be a closed sentence

    forall a:e forall x₁ … x_n,
      ((all I_ik(x_k;a)) -> θ(a,x₁,…,x_n)),                 (7)

with the same allowances on θ and the inductive systems. If Con(M+U),
choose an M+U-model. At every a all C_a-valid constructor tuples satisfy
their guards, so U makes their ground θ-instances true. The common marked
identity diagram transfers every such instance to R_L. By (3), these
tuples exhaust the guarded domains of R_L; hence R_L⊨U.

The same R_L works for all individually M-consistent sentences (7) at
once, without any bound on the types or term complexity appearing among
different sentences. Each individual sentence remains finitary.

By (2), U is equivalent over C_L to a universal finite Boolean identity
sentence. The earlier universal-identity reflection lemma gives D U→U;
factivity of H gives U→D U. Thus R_L satisfies every licensed SP axiom
D U with U of form (7). This is a genuine simultaneous SP fragment model,
separately for each reference theory, not a model of unrestricted SP.

## 7. Unary-signature first-stage witness requirements

Now fix exactly Σ={c:e→t}. Use the notation of
[FIRST-STAGE.md](../../../classicism-results-2026-10-24-v2/proofs/signature-sp-first-stage.md):

    T = Max(C(Σ,a)) + E₁,       K = Stone(T),
    W_F = hat(not exists x F(x)) union union_b hat(F(b)),

where b ranges over all closed marked terms at the witness type. Let U_R
be the complete marked truth theory of the singleton signature-profile
root. For any of the inductive domains above and **any** formula φ(x) of
the marked language, put

    F(x) := I_i(x) and φ(x).                                (8)

If ∃x F(x) is false at the root, U_R belongs to the first part of W_F.
If it is true, (3) supplies a finite constructor term u naming its actual
witness, so F(u) is true and U_R belongs to a named-witness cylinder.
Consequently U_R belongs simultaneously to every W_F of form (8).

In particular, if T proves ∃x F(x), some marked F(u) is consistent with T.
Here φ can have unrestricted higher-type quantification and arbitrary
actual-truth conditions. This is only consistency of a named instance;
unlike §5 it does not claim T proves that instance.

This extends the earlier numerical witness result to all the stated mutual
inductive domains at arbitrary relational types. It does not establish
K₁ nonempty: the same U_R is excluded by the previously established,
unguarded true-atom witness requirement in FIRST-STAGE §6.

## 8. Concrete higher-type instances and the remaining gap

Ordinary Frege natural numbers are the one-sort, unguarded system with
constructors zero and successor. Thus (6) holds for mixed identity
sentences with numerical witnesses, with no restriction on the terms
inside the identities. Finite mutual constructor systems also cover
finite algebraic data at higher types; their outputs need not form a
finite set or be numerical entities.

For an explicit infinite higher-type example, put ν=(et)t and ρ=νt.
Use the closed pure predicate operations F,G from
[masked retraction](masked-retraction.md),
§§1–3. Define I_ρ by the seeds bottom_ρ,top_ρ and the constructors F,G,
binary conjunction and complement. Its profile-root elements are exactly
the entities obtained by finite expressions in those operations.
There are infinitely many: F^n(top_ρ) are pairwise distinct under Max.
If m<n and F^m(top)=F^n(top), applying G^m and using GF=id gives
top=F^(n-m)(top), contrary to top being outside F's range. The new theorem
therefore handles mixed identities with witnesses in a concrete infinite
domain of numerical predicates, not merely finite witness ranges.

In the unary signature a different example takes σ=et, seeds c,bottom,top,
and Boolean and pointwise modal constructors, including both ordinary □
and H. This produces a signature-dependent higher-type witness domain.
Its guarded extraction theorem permits arbitrary quantified terms in the
identity matrix, rather than restricting that matrix to modal polynomials.

The exact unproved step remains removal of the inductive-domain guards.
A proof of an unrestricted existential identity sentence does not thereby
show that its witnesses belong to any of these domains. Nor does the
existence of witnesses for all guarded requirements make the unguarded
witness opens simultaneously compatible. Both implications would require
additional mathematics; neither is used above.

## 9. Sources and check

Published framework and SP formulation: Bacon–Dorr, *Classicism*, draft
16 May 2023, §1.3 and §2.6, p.42. Converse Barcan is recorded at §1.5,
p.19 in
[the CBF record](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/classicism-implies-converse-barcan-r.yaml).
The familiar one-sort persistence induction appears as Lemma 1 of
[the arithmetic write-up](../../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/c5-implies-necessity-of-arithmetic.md);
only that C lemma's method is generalized here, not its later C5 premises.

The new deductions are §§2–7 of this note. Their profile-model and common
identity-diagram inputs are cited in §1. The universal reflection input is
[universal-core analysis](../../../classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/reflection-universal-core-20261022.md),
§§2–7. The concrete F,G operations in §8 are earlier work, explicitly cited
there; the present use is an inductive witness fragment based on them.

The proof was checked directly for zero-input rules, repeated type indices,
empty generated domains, the distinction between actual membership and
whole identity, parameter dependence on a, and the separate Max reference
theories. Repository validation is recorded in REPORT.md; it is an integrity
check, not verification of the mathematical arguments.

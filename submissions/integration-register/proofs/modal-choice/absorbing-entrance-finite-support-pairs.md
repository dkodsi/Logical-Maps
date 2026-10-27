# Absorbing entrance with finitely supported pair intensions

26 October 2026. Ordinary mathematical construction by OpenAI Codex.
Direct source: `misc`, this note, §§1–6, unpaginated. No independent
review, human verification, Lean certification, or literature-priority
claim is made. Work in the fixed relational C, in ordinary ZFC.

## 1. Result

There is an explicit set-sized model of C with

```math
\boxed{IC_{\rm all}+\Box BC_{\rm all}
+\Box\mathrm{Atomicity}_{\rm all}+\Box\mathrm{Actuality}
+\neg\Box IC_e.}
\tag{1}
```

In addition, □BF_e and □ND_e hold. BF_(et), BF_t and ND_t fail at
the root. In particular, the relevant BF_(et) hypothesis in the
positive IC_e propagation theorem cannot be replaced by BF_e.

The construction uses no assumed model of ZF and no metatheoretic
failure of Choice. Its absence of a selector is an explicit finite
support restriction on the admitted intensions. It strengthens
[the choiceless full-model construction](absorbing-entrance-choiceless-group.md),
which remains a separate valid example with singleton individuals
and failure of □IC_t under its stated choiceless metatheory.

## 2. Two independent actions

Use the category with objects r,s, identities, one arrow a:r→s,
no arrows s→r, and endomorphism group ℤ at s. Write its group
operation additively, and impose

```math
k\circ a=a\quad(k\in\mathbb Z).
\tag{2}
```

Thus exactly two arrows leave r: 1_r and a. All group arrows out
of s have the same composite with a. Associativity follows from
addition and the displayed absorbing rule.

The individual domain at both objects is

```math
X=\{A_n^0,A_n^1:n\in\mathbb N\}.
```

Every category arrow acts as the identity on X. Separately, let
$`\Gamma=\{0,1\}^{\mathbb N}`$ act on X by independent swaps:
$`\gamma\cdot A_n^i=A_n^{i+\gamma(n)}`$, modulo 2. This external
symmetry acts trivially on the category, including every arrow k
and a. The ℤ action in the category and the Γ action on admitted
entities are distinct; neither group is identified with the other.

For finite N⊆ℕ, let Γ_N contain the γ that vanish on N. An entity
has support N if Γ_N fixes it. Every individual has finite support.

## 3. The full typed restriction and its C verification

Define the relational domains recursively. For
$`\tau=\sigma_1\cdots\sigma_m t`$, including m=0, set

```math
E_\tau(v)=\coprod_{h:v\to w}\prod_{i=1}^m D_{\sigma_i}(w),
\qquad
D_\tau(v)=\{Y\subseteq E_\tau(v):Y\text{ has finite }\Gamma\text{-support}\}.
\tag{3}
```

The Γ action fixes h and acts componentwise on its local tuple.
All domains are Γ-invariant. Each of their elements has finite
support by construction; the empty relation supplies nonemptiness
at relational types. At t the tuple is empty and Γ acts trivially,
so D_t(v) is the entire powerset of the arrows out of v.

Transport along k:v→w is the usual precomposition of intensions:

```math
(k_*Y)(h;\bar x)=Y(h\circ k;\bar x).
\tag{4}
```

It commutes with Γ and preserves a finite support. For application
the row at h is taken at the transported argument:
$`(Yx)(h;\bar z)=Y(h;h_*x,\bar z)`$. The union of finite supports
of Y and x supports this row intension. Hence application is
admitted and commutes with both transport and the Γ action.

Use the standard full-action truth clauses before restricting the
domains: connectives are pointwise; quantifiers at h range over
the entire specified D_σ(cod h); and the identity proposition of
x,y contains those h for which h_*x=h_*y. For abstraction, evaluate
the body at h with its old parameters transported and its bound
variables assigned arbitrary local arguments.

Every one of these operations is Γ-equivariant. In particular,
quantification is equivariant because Γ permutes each complete
admitted domain. By induction on terms and formulas, the intension
of an abstraction with finitely many parameters is supported by
the union of finite supports of those parameters. It therefore
belongs to (3). This establishes closure under all typed lambda
abstractions and quantifiers, with no bounded-formula or bounded-type
restriction. Transport satisfies the substitution induction, as
in the full action construction.

The H truth clauses consequently hold. An H-theorem equivalence
has the same truth value at every arrow and every local assignment.
Its two abstractions have identical tagged extensions and hence
are the same entity. Thus strict H-only Logical Equivalence holds.
No optional equivalence is used as an LE instance. The restriction
(3) is therefore a model of C.

For propositions, native Box is equality to the full arrow set.
Accordingly, □φ at an object tests φ at every outgoing arrow,
with the full local quantifier domains at the codomain. The finite
number of arrows leaving r does not restrict those local domains
or the number of arrows leaving s.

## 4. Full IC at r and failure of IC_e at s

Fix σ and F∈D_(σt)(r) necessarily instantiated at r. Its two
extensions F(1_r) and F(a) are nonempty. Choose x∈F(1_r) and
y∈F(a), and define

```math
G(1_r)=\{x\},\qquad G(a)=\{y\}.
\tag{5}
```

Each chosen entity has finite support. Their union supports G, so
G is admitted by (3). It entails F and has exactly one instance
at both outgoing arrows. Thus □∃!z Gz holds at r. This proves
IC_σ for every fixed σ, including e, and hence IC_all at r.
No simultaneous selection over all F is asserted. Transport a_*G
is the constant singleton extension {y} over all the ℤ arrows,
so its required further modal behavior is also explicit.

For the failure at s, fix an explicit bijection ν:ℕ→ℤ and define
the intension F:et by

```math
F(\nu(n))=\{A_n^0,A_n^1\}.
\tag{6}
```

Every pair is invariant under Γ, so F has empty support and is
admitted. Every extension is nonempty, giving □∃x Fx at s.

Suppose an admitted G≤F were necessarily uniquely instantiated.
Take a finite support N for G and choose n outside N. Its extension
at ν(n) is a singleton contained in the nth pair. The symmetry
that swaps exactly that pair fixes G, because it belongs to Γ_N,
and fixes the arrow ν(n). It must therefore fix that singleton
extension. But it exchanges its two possible members, which is
impossible. No such G exists, so IC_e fails at s.

The closed IC_e sentence evaluated at a is its value at s.
Consequently □IC_e fails at r, completing the separation in (1).

## 5. Additional verified verdicts

**Necessary Boolean Completeness.** At any relational type τ and
object v, algebraic order is inclusion of the tagged sets in (3).
Given an admitted property P of τ-entities, choose its finite
support N. Its current extension, the family
$`\{Y:P(1_v;Y)\}`$, is invariant under Γ_N. The intersection of
that family, or the full E_τ(v) for an empty family, is consequently
Γ_N-invariant. It is admitted and is its Boolean greatest lower
bound. The argument applies at both objects and every relational
type, proving □BC_all.

**Necessary Atomicity.** Every member of a tagged tuple in E_τ(v)
has finite support. A singleton tagged tuple therefore has finite
support and is admitted. Every nonempty relation contains such a
singleton, which is an atom of the admitted Boolean algebra. This
proves □Atomicity_all.

**Necessary Actuality.** All propositional subsets of the outgoing
arrows are admitted. At each object, the singleton of its identity
arrow is true and entails every true proposition. Hence □Actuality
holds at r. This is a local witness at each object, not a claim that
one fixed root witness transports to every local witness.

**Necessary BF_e and ND_e.** All category arrows are the identity
on the same individual set X. Transport is therefore surjective
and injective at e. Directly, every future individual is already
a current individual, which proves BF_e at both objects, and
distinct individuals remain distinct, which proves ND_e there.

**Failure of BF_(et).** Every root predicate transports along a
to a constant-extension intension at s, by (2). Conversely, a
constant-extension predicate with a finitely supported extension
can be lifted to r by using the empty extension at 1_r. Let Q
hold at 1_r of every root predicate and at a exactly of the leaf
predicates in this transport image. The image is Γ-invariant,
so Q has empty support and is admitted. Every current F satisfies
□QF, but □∀F QF fails: the nonconstant F in (6) is not in the
image at s. Thus the exact BF_(et) used in the positive IC_e
propagation theorem is absent.

**Failure of BF_t and ND_t.** The root proposition domain has
four elements. Transport a maps them onto just the two endpoints
of $`\mathcal P(\mathbb Z)`$; the same image-test argument gives
failure of BF_t. Also, {1_r} and Bottom are distinct at r and
both transport to Bottom at s, proving failure of ND_t and C5.

No RC or MRC verdict is asserted as an additional premise. Full
MRC fails as a consequence of (1) and the independently proved
MRC⇒□IC theorem.

## 6. Sources and status

- The complete typed finite-support construction and separation:
  this note, §§1–5, OpenAI Codex, 26 October 2026, `misc`, unpaginated.
- The absorbing-entrance category and finite-arrow IC proof:
  [the earlier choiceless full-model note](absorbing-entrance-choiceless-group.md),
  §§2–4. This note replaces the metatheoretic choiceless family
  by an explicit restriction on admitted intensions.
- The independent-pair finite-support method and the separate
  classical leaf construction:
  [Classical Henkin leaf with independently swappable pairs](finite-support-pairs-henkin-leaf.md),
  §§1–3. Here the intensions also vary over category arrows.
- Full action truth clauses: Bacon–Dorr, *Classicism*, 16 May 2023
  draft, §3.5 pp. 58–61 and Appendix D pp. 73–74, indexed in
  [full-action-models](../../../classicism-results-2026-10-24-v2/source/topics/classicism/groups/full-action-models.yaml).
  Closure of the finite-support restriction is proved in §3 above;
  it is not attributed to the full-model theorem alone.

# Absorbing entrance to a choiceless group model

26 October 2026. Ordinary mathematical construction by OpenAI Codex.
Direct source: `misc`, this note, §§1–6, unpaginated. No independent
review, human verification, Lean certification, or literature-priority
claim is made. The type system and logic are the fixed relational C.

## 1. Result and metatheory

There is a relative countermodel to

```math
C+IC_{\rm all}\ \Longrightarrow\ \Box IC_{\rm all}
```

More precisely, working in ZF with a sequence
$`(A_n)_{n\in\mathbb N}`$ of nonempty subsets of $`\mathcal P(\mathbb N)`$
having no choice function, the construction below is a full action model
with a distinguished object r satisfying

```math
\boxed{IC_{\rm all}+\neg\Box IC_t}
\tag{1}
```

It also satisfies necessary all-type Boolean Completeness, necessary
all-type Atomicity, and necessary Actuality. Its individual domain is
a singleton at every object. Neither all-type RC nor all-type BF is
asserted. In fact BF_t fails at r.

This is a relative-consistency construction, with the same
ZF+$`\neg AC_\omega(\mathbb R)`$ hypothesis used by the existing
choiceless full-action models. The construction and proofs below use
no additional metatheoretic Choice. If one works externally with a
set-sized model of that theory, its internally full domains give the
corresponding external Henkin model of these fixed standard formulas.
They need not be externally full powersets.

The mechanism is that r has only two outgoing arrows, although its
reachable object s has infinitely many outgoing arrows. Composition
identifies all the latter arrows after the entrance from r. Current
IC is choice over the outgoing arrows of the current object; it does
not impose the same choice requirement at every reachable object.

## 2. Category and full typed domains

Take two objects r,s and hom-sets

```math
\mathrm{Hom}(r,r)=\{1_r\},\quad
\mathrm{Hom}(r,s)=\{a\},\quad
\mathrm{Hom}(s,r)=\varnothing,\quad
\mathrm{Hom}(s,s)=\mathbb Z
```

Composition in $`\mathbb Z`$ is addition, with identity 0, and

```math
g\circ a=a\qquad(g\in\mathbb Z)
\tag{2}
```

Together with the identity laws these give an associative category:
the only mixed nontrivial associativity check is
$`(g+h)\circ a=g\circ(h\circ a)=a`$.
At both objects take one individual, fixed by every arrow.

Use the ordinary full relational action construction. Explicitly,
for a relational type $`\tau=\sigma_1\cdots\sigma_k t`$, including
$`k=0`$, its entities at an object v are all sets of tagged tuples

```math
D_\tau(v)=\mathcal P\!\left(
\coprod_{h:v\to w}\prod_{i=1}^k D_{\sigma_i}(w)\right)
\tag{3}
```

Thus an entity X assigns an arbitrary extension X(h) at every arrow
out of v. The domains are built by induction on the fixed finite type
expressions. Powerset, Separation and Replacement suffice in ZF;
all domains are nonempty, with the empty relation available.

For $`k:v\to w`$, transport is precomposition:

```math
(k_*X)(h;\bar x)=X(h\circ k;\bar x)
\tag{4}
```

For an application Xx, its extension at h is the corresponding row
of X(h) at the transported argument $`h_*x`$. Explicitly,
$`(Xx)(h;\bar y)=X(h;h_*x,\bar y)`$. The same clause iterates for
curried application. Transport respects application by associativity.

The value of an abstraction $`\lambda x\,B`$ at h and a local
argument b is the truth value of B at the codomain of h, with the old
parameters transported along h and x assigned b. Fullness of (3)
admits that intension. Boolean operations are pointwise, local
quantifiers range over the entire domain at the codomain, and the
identity proposition of x,y contains exactly those h for which
$`h_*x=h_*y`$. Evaluation at an object is truth at its identity arrow.

These clauses verify the ordinary H axioms and substitution by the
standard induction on terms. If an equivalence is an H theorem,
its two sides have the same truth value at every arrow and every
local assignment; their abstractions therefore have identical tagged
extensions in (3). This verifies strict H-only Logical Equivalence.
No equivalence obtained from IC or a metatheoretic choice hypothesis
has been used as an LE instance. Hence this is a model of C.

At t, $`D_t(v)`$ is the powerset of the arrows out of v. The defined
$`\Box p=(p=\top)`$ is true at v exactly when p contains every arrow
out of v. Consequently $`\Box\varphi`$ tests the evaluation of the
closed formula at all those arrows, with local quantifiers at their
codomains. In particular an arrow can introduce new quantified
entities even when many later arrows have the same composite with it.

## 3. Full Intensional Choice at the entrance

Fix any admitted type $`\sigma`$, including e, and any
$`F\in D_{\sigma t}(r)`$ such that $`\Box\exists x Fx`$ holds at r.
There are exactly two outgoing arrows from r, so this says precisely
that the two sets

```math
F(1_r)\subseteq D_\sigma(r),\qquad
F(a)\subseteq D_\sigma(s)
```

are nonempty. Choose one member x of the first and one member y of
the second. This is a two-set choice, provable in ZF; no choice over
all F or over all types is being made.

Define the admitted G by

```math
G(1_r)=\{x\},\qquad G(a)=\{y\}
\tag{5}
```

Then G≤F by pointwise inclusion. At both outgoing arrows G has
exactly one local instance, so $`\Box\exists!z\,Gz`$ holds at r.
This proves IC_σ, for each fixed σ, and hence full IC at r.

There is no requirement that $`a_*x=y`$. Also, (2) makes a_*G the
constant extension $`\{y\}`$ over the group arrows out of s. It is
therefore necessarily uniquely instantiated at s too. This checks
that the chosen root witness has the full required modal scope.

The proof is the current-object version of the recorded finite-arrow
IC argument. Finiteness of the arrows at every reachable object is
needed for that argument to establish necessary IC; it is not needed
for the current IC assertion just proved.

## 4. Failure of Intensional Choice at the group object

Fix an explicit bijection $`\nu:\mathbb N\to\mathbb Z`$. For
$`C\subseteq\mathbb N`$, let $`p_C=\nu[C]`$, a proposition at s.
Transport by g on these propositions is

```math
g_*p=\{h\in\mathbb Z:h+g\in p\}
\tag{6}
```

It is invertible, with inverse transport by -g. Define an admitted
property F of propositions at s by prescribing every extension:

```math
F(\nu(n))=\{\nu(n)_*p_C:C\in A_n\}
\tag{7}
```

Replacement and Separation define this intension without choosing
any member of any A_n. Each extension is nonempty, so
$`\Box\exists p Fp`$ holds at s.

Suppose IC_t supplied G≤F with $`\Box\exists!p Gp`$. At each
$`g=\nu(n)`$, the extension G(g) would be a singleton $`\{q_n\}`$,
with $`q_n=g_*p_{C_n}`$ for a unique $`C_n\in A_n`$. Recover it by

```math
C_n=\nu^{-1}[(-\nu(n))_*q_n]
\tag{8}
```

Uniqueness and Replacement in ZF then give the function
$`n\mapsto C_n`$, contradicting the choice-failure hypothesis.
Therefore IC_t fails at s. This is the recorded returning-arrow
choiceless obstruction, specialized to the group $`\mathbb Z`$.

The entrance a reaches s. The closed IC_t formula evaluated at a
is precisely its evaluation at s, since it has no transported free
parameters. Thus $`\Box IC_t`$ fails at r. Together with §3 this
proves (1).

## 5. Additional verified properties and the missing Barcan premise

Every domain (3) is a powerset Boolean algebra. Given any admitted
property of its entities, the intersection of its current members
is an admitted greatest lower bound, with the usual full universe
for the empty intersection. Singleton tagged tuples are atoms.
These arguments use no Choice and hold at both objects and every
relational type. Hence □BC_all and □Atomicity_all hold at r.

At either object the singleton proposition consisting of its
identity arrow is true and entails every true proposition. It is
an Actuality witness. This proves □Actuality at r, without asserting
that the same witness transports to an Actuality witness elsewhere.

BF_t fails at r. Its four propositions are the subsets of
$`\{1_r,a\}`$, and (2) transports every one of them to either
$`\varnothing`$ or $`\mathbb Z`$ at s. Define X:tt at r to hold of
every proposition at 1_r and exactly those two propositions at a.
Then every current p satisfies □Xp. But □∀p Xp is false, because
the proposition $`\{0\}`$ at s satisfies neither endpoint test.
Thus this model does not contradict the BF-only IC propagation
theorem in [barcan-persistence.md](barcan-persistence.md).

The proposition $`\{1_r\}`$ and Bottom are distinct at r and have
the same transport at a. Consequently ND_t, and therefore C5, fail
at r. The countermodel addresses bare C.

## 6. Sources and exact verification status

- The absorbing-entrance category, its use for current IC versus
  necessary IC, and the complete argument above: this note, §§1–5,
  OpenAI Codex, 26 October 2026, `misc`, unpaginated.
- Full action construction: Bacon–Dorr, *Classicism*, 16 May 2023
  draft, §3.5 pp. 58–61 and Appendix D pp. 73–74, as indexed by the
  [full-action-models group](../../../classicism-results-2026-10-24-v2/source/topics/classicism/groups/full-action-models.yaml).
- The choiceless metatheory and its relative-consistency scope:
  that group's `no-countable-choice-reals` parameter.
- Failure of IC from a countable choiceless family and returning
  arrows: [countable-choice-reals-full](../../../classicism-results-2026-10-24-v2/source/topics/classicism/arguments/countable-choice-reals-full.yaml),
  the existing ordinary argument by Claude Opus 5.5 at Cian Dorr's
  direction, 8 October 2026. Section 4 gives its full specialization.
- Finite-arrow choice without AC:
  [intensional-choice-finitely-many-arrows](../../../classicism-results-2026-10-24-v2/source/topics/classicism/arguments/intensional-choice-finitely-many-arrows.yaml),
  8 October 2026. Section 3 separates its current and necessary scope.

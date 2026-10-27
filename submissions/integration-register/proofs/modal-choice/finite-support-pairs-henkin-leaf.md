# Classical Henkin leaf with independently swappable pairs

26 October 2026. Ordinary mathematical proof by OpenAI Codex.
Direct source: `misc`, this note, §§1–4, unpaginated. No independent
review, human verification, Lean certification, or literature-priority
claim is made.

## 1. Purpose and construction

This gives an explicit set-sized classical extensional Henkin model
H of the fixed relational C in ordinary ZFC, with a serial relation
on its individual domain having no admitted functional subrelation.
It can be used as the leaf of
[the free-root countermodel](free-root-choiceless-henkin-leaf.md).
No assumption that a set-sized model of ZF exists is needed.

Let the individual domain be the disjoint union

```math
D_e=\{L_i:i\in\mathbb N\}\ \sqcup\
\{A_i^0,A_i^1:i\in\mathbb N\}.
```

Take the group $`G=\{0,1\}^{\mathbb N}`$ under coordinatewise
addition modulo 2. Every g fixes every label L_i and sends
$`A_i^\epsilon`$ to $`A_i^{\epsilon+g(i)}`$.
Let $`D_t=\{0,1\}`$ with trivial G-action.

For a finite $`N\subseteq\mathbb N`$, write G_N for the subgroup
whose members vanish on N. An entity is supported by N if G_N fixes
it. Every individual has finite support: labels have empty support,
and an option A_i^ε has support {i}.

Inductively, for every admitted function type στ, where τ≠e, let

```math
D_{\sigma\tau}=
\{f:D_\sigma\to D_\tau:
 f\text{ has a finite support under conjugation}\},
\tag{1}
```

where

```math
(g\cdot f)(x)=g\cdot f(g^{-1}\cdot x).
\tag{2}
```

The domains are G-invariant: conjugating a finitely supported
function preserves finite support (the group here is abelian).
Every domain is a set. They are nonempty: recursively take the
constant Bottom-valued operation at each relational type. There
is only one evaluation world; application is ordinary function
application, and quantifiers range over these specified domains.

## 2. Typed closure and C

The Boolean operations on D_t are invariant. Literal equality at
every type is invariant under the group action. The universal
quantifier of type (σt)t is invariant, because every g permutes
D_σ, and is therefore an admitted function with empty support.
The same holds of the existential quantifier. Their curried
versions and the identity predicates have the required admitted
types; no operation whose output type is e is introduced.

For abstraction, take a term with finitely many parameters and
choose a finite support N for the whole parameter tuple. The
interpretation of terms is equivariant, by induction on the term,
since the logical constants are invariant and application respects
the action. Consequently the function denoted by λx B is fixed
by G_N and belongs to (1). Each of its values is already in the
required codomain by the same induction with x assigned an
arbitrary admitted argument. Thus all lambda abstractions and
quantifiers, including those with higher-type parameters, are
interpreted in the displayed hierarchy.

These are ordinary classical Henkin semantics with actual equality
of functions, so H holds. If two formulas are H-equivalent, their
truth values agree at every assignment. Their lambda abstractions
are pointwise equal actual functions and hence identical.
This verifies strict H-only Logical Equivalence and therefore C.
It also verifies all-type Extensionality. Since the proposition
domain is 2, native Box, defined as equality to Top, is truth.

This argument is the elementary finite-support construction itself;
it does not appeal to the existence or consistency of an entire
Fraenkel–Mostowski or choiceless ZF universe.

## 3. A serial relation without a selector

Define the relation U:eet by

```math
U(L_i,y)\quad\Longleftrightarrow\quad
y=A_i^0\ \lor\ y=A_i^1,
```

```math
U(A_i^\epsilon,y)\quad\Longleftrightarrow\quad y=L_0.
\tag{3}
```

The entire relation is invariant under every independent pair
swap, and its rows have finite support. Its curried function is
therefore an admitted entity of type eet with empty support.
It is serial.

Suppose S:eet were an admitted total functional subrelation of U.
Choose a finite support N of S and an index i outside N. Let g
swap the two options of pair i and fix every other pair. It fixes
S and L_i. The unique S-output y at L_i belongs, by (3), to
$`\{A_i^0,A_i^1\}`$. Invariance of S then makes g·y another
S-output at L_i. But g·y≠y, contradicting functionality.

Thus H fails RC_(e,e). No external failure of Choice is involved:
the obstruction is admission of the selector in the Henkin domain.
In particular an external choice of one member of each pair exists
in ZFC, but its graph has no finite support and is not admitted.

## 4. Intensional Choice and use in the free-root model

For each fixed admitted property F that is inhabited, take a
witness x and its singleton haecceity λy(y=x). Its support is
contained in a finite support of x, so it is admitted. It entails
F and is uniquely instantiated. Box is truth here, so this proves
full IC, and also □IC, in H. As in every classical extensional
one-world Henkin model, all BF instances and full observer
separation hold as well; identity is the separating observer.

Use this H in the full-current-extension root construction. The
proofs there depend only on H being classical extensional Henkin,
its admitted serial U having no admitted functional subrelation,
and its full IC. All have now been checked explicitly. Accordingly
that countermodel is an ordinary ZFC construction satisfying

```math
RC_{\rm all}+TC_{\rm all}+\Box IC_{\rm all}
+\Box BF_{\rm all}+\Box OS_{\rm full}+\Box BC_t
+\mathrm{Actuality}+\neg MRC_{e,e}.
```

This replaces the first version's extra existence assumption on
a choiceless ZF-based Henkin leaf. The published Henkin model
record has not been altered; this is a separate construction.

Sources: the direct source for the complete construction and
argument is this note, §§1–4, `misc`, unpaginated. The comparison
model is [Henkin without Relational Choice](../../../classicism-results-2026-10-24-v2/source/topics/classicism/models/henkin-without-relational-choice.yaml),
whose own stated set-theoretic hypothesis remains unchanged.

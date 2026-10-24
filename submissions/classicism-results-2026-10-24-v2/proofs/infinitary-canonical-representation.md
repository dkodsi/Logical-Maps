# Canonical representation and fullness under C5

Original mathematical development by OpenAI Codex at Daniel Kodsi’s request, 23 October 2026, source `misc`; extracted from §5 of the atomic-joins development.

## 5. C5 needs only propositional Atomicity for fullness

The following finitary implications are already proved in the records:

$$
C5\Rightarrow BF_{\rm all},\qquad
\mathrm{Atomicity}_t+BF_{\rm all}
 \Rightarrow\mathrm{Atomicity}_{\rm all},
$$

$$
C5+\mathrm{Atomicity}_{\rm all}
 \Rightarrow\Box\mathrm{Plenitude}_{\rm all}.
\tag{5.1}
$$

Here C5 is **boxed ND at all types**. Consequently
$C5+\mathrm{Atomicity}_t$ and $\Box\mathrm{Plenitude}_{\rm all}$
are equivalent over C. The reverse implication follows from the recorded
boxed-Plenitude consequences. This removes the all-type Atomicity assumption
from the starting package, while retaining the full all-type AAJ scheme.

Consider the represented domain at
$\tau=\sigma_1\cdots\sigma_n t$, and put

$$
X_\tau=W\times D_{\sigma_1}\times\cdots\times D_{\sigma_n},
\qquad W=\mathrm{At}(B_t).
$$

The ☐Plenitude representation has literal typed identity,
constant domains, pointwise truth operations, extensional application, and
principal worlds. Its evaluation maps an object $R$ to

$$
\beta_\tau(R)=\{(w,\bar a):w\le R[\bar a]\}.
\tag{5.2}
$$

This representation can be reconstructed from a set-sized ordinary typed
Henkin model of C satisfying C5 and propositional Atomicity. An independently
given Gallin presentation is not an additional premise. Take the current
identity quotients as the constant domains and take their proposition atoms
as the world set. The essential checks are as follows.

- At any propositional atom $w$, the test $w\le p$ respects finite
  Boolean connectives because an atom lies below exactly one of $p,\neg p$.
  Current propositional Atomicity makes these tests jointly separate
  propositions.
- For any admitted predicate $F$,
  $w\le\forall x Fx$ iff $\forall x\,(w\le Fx)$. One implication is
  necessary universal instantiation. For the other, BF combines the
  pointwise necessities $\Box(w\to Fx)$ into
  $\Box\forall x(w\to Fx)$, which is equivalent by an H-theorem to
  $\Box(w\to\forall x Fx)$. Thus the canonical worlds satisfy the
  quantifier clause using exactly the current domain, not a presupposed
  external full domain.
- A typed equality $x=y$ holds at every canonical world if true currently,
  by NI. If false currently it is false at every canonical world by C5's ND.
  Application is well-defined on the identity quotients by substitutivity.
- The atom test for $\Box p$, whose original definition is $p=\top$,
  is true exactly when every atom test for $p$ is true. This follows from
  the preceding identity clause and Atomicity. It gives universal S5
  accessibility on the canonical world set.
- If two relational entities have the same support (5.2), atomic separation
  gives equal values at every current argument tuple. NI, BF, and C's
  Intensionality identify the entities. Thus the support representation is
  faithful; it does not assume actual-coextension Extensionality.
- Boxed Plenitude supplies Actuality, hence a unique current true atom
  $w_0$. For each proposition $p$, current truth is equivalent to
  $w_0\le p$: the Actuality witness entails every current truth, and the
  reverse implication is T. This is the designated point for the canonical
  representation. The same argument, together with the quantifier and
  application clauses, gives the truth lemma for original formulas with
  parameters by induction.

Finite lambda closure supplies the singleton tensors used below. These
checks give the principal-world general Gallin presentation, or its original
typed reduct, without adding a world sort to the original object language.
They are the external reading of the established
[world representation, §§2–4](../source/research/2026-10-22/notes/structural-world-representation.md).
An arbitrary Stone representation may add nonprincipal ultrafilter points;
that is not the reconstruction used here. Equally, the claim is a semantic
representation theorem for the specified Henkin models, not an assertion
that a syntactic theory alone comes with external domains or a complete
infinitary proof calculus.

Each point $(w,\bar a)$ has its singleton tensor
$\lambda\bar x.(w\wedge\bar x=\bar a)$. For an arbitrary external
$U\subseteq X_\tau$, AAJ at $\tau$ gives the join $b$ of
these singleton atoms. Certainly $U\subseteq\beta_\tau(b)$. If a point
$z$ belonged to the latter but not to $U$, subtracting its admitted
singleton would leave a strictly smaller upper bound of the same family.
This contradicts leastness. Thus $\beta_\tau(b)=U$.

It follows that every relation domain is the full powerset of its
world–argument points. If $f:D_\sigma\to D_\tau$ is any external
function, take the subset of $X_{\sigma\tau}$ specified by the supports
of its values. Surjectivity of $\beta_{\sigma\tau}$ supplies an
admitted operation with that support; injectivity of $\beta_\tau$
identifies each value with $f(x)$. Hence every such function is admitted.

This proves the sharpened form of the canonical
[fullness theorem, §6](full-gallin.md):

$$
C+C5+\mathrm{Atomicity}_t+\mathrm{AAJ}_{\rm all}
\quad\models\quad
\text{full principal-world Gallin semantics}.
\tag{5.3}
$$

Equivalently the initial finitary package can be
$C+\Box\mathrm{Plenitude}_{\rm all}$. Within its canonical
representation, the following conditions are equivalent:

1. Every external family of atoms at every relational type has a join.
2. Every external family of arbitrary entities at every relational type has
   a join, or equivalently a meet.
3. Every external subset of each world–argument product is represented.
4. The original relational function hierarchy is externally full.
5. **External Comprehension:** for every original type $\sigma$, including
   $e$, every external subset $S\subseteq D_\sigma$ is the actual
   extension of some admitted property $R^{\sigma t}$.

Condition (5) has a short proof of equivalence which does not presuppose the
full reconstruction. Given AAJ and $S\subseteq D_\sigma$, take the join
$R$ of all tensor atoms

$$
\lambda x.\,a\wedge x=s
\qquad(a\in\mathrm{At}(B_t),\ s\in S).
\tag{5.4}
$$

This is one external family at type $\sigma t$. For $s\in S$, every
propositional atom lies below $Rs$, so Atomicity at $t$ gives
$Rs=\top$. If $y\notin S$, each $s\in S$ is distinct from
$y$, necessarily so by ND. Consequently every tensor (5.4) lies below
$\lambda x.x\ne y$. Join leastness gives
$R\le\lambda x.x\ne y$, and evaluation at $y$ gives $Ry=\bot$.
Thus $R$ represents exactly $S$. Its true and false instances are
necessary; the baseline BF/S5 laws make it a rigid property. Alternatively,
the baseline Rigid Comprehension theorem rigidifies any current extension.
So requiring a *rigid* property in (5) is equivalent as well.

Conversely, let $(a_i)_{i\in I}$ be any external family of atoms of a
relational type $\tau$. External Comprehension at the input type
$\sigma=\tau$ gives $X^{\tau t}$ whose current extension is exactly
the family range. C5 plus propositional Atomicity already entails the
recorded internal Boolean Completeness schema. Its LUB form applied to
$X$ is precisely the requested join of the external atom family. This
includes the empty family. Thus (5) implies AAJ without assuming a property
code for the family before applying External Comprehension.

The conceptual simplification in (2) removes the restriction to atoms;
Atomicity is exactly what makes that removal valid. Condition (3) describes
the same strength as unrestricted external powerset comprehension, while
(5) states it without worlds or Boolean order. These
are semantic equivalents of the all-type infinitary scheme, not the
recorded internally quantified Boolean Completeness principle. Fullness
conversely gives the joins directly. The base sets may be finite; neither
quantified Infinity axiom is needed.

External Comprehension is a semantic schema about external subsets. It is
not the internally quantified sentence “every admitted property has an
admitted coextension,” which is trivial. Nor does it assert that all
coextensive properties are identical: distinct intensions can have the same
extension at the current world. Requiring a rigid representative does not
collapse modality.

In ZFC, at any world and for any serial relation from $D_\sigma$ to a
relational output domain $D_\tau$, external Choice supplies a selecting
function. Fullness admits that function at the original type $\sigma\tau$.
It witnesses the Functional Choice instance at that world. The argument
works at every world, proving $\Box FC$ at all admitted instances.
This is not necessitation from an optional local premise: the reconstructed
full model directly satisfies FC throughout its world set. Over ZF, the
external choices used here require their corresponding set-theoretic choice
principles.

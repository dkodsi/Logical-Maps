# The omitted numerical cut in a pure SP construction

Original mathematical argument, direct source misc; unpaginated.

## Fixed question and hypotheses

Keep the original finitary pure language, the relational type system of C, and
the source's fixed independent arithmetic sentence

```math
G=\forall x\,P(x),\qquad P(x)\equiv\exists y\,\delta(x,y),
```

where the displayed form is a PA-equivalent Sigma-1 presentation with bounded
arithmetic matrix $`\delta`$. Tuples can be encoded in the fixed arithmetic
interpretation. This is a normal-form presentation of the source's sentence,
not a replacement independent sentence. The pure translation is $`G^\#`$.

The unresolved question remains

```math
\mathrm{Con}(\mathrm{Max}(C)+U_G+D(\neg G^\#)).
```

The source established $`G^\#\leftrightarrow U_G`$ under $`I_e`$, which Max
entails. Its local embedding criterion makes the question equivalent to the
existence of genuine Max models $`M,N`$ and an embedding

```math
j:\mathrm{Alg}(M)\longrightarrow\mathrm{Alg}(N),
\qquad M\models G^\#,\quad N\models\neg G^\#.
```

Here Alg includes every pure term operation at every admitted type, including
quantifier-valued terms, but omits external actual truth. All conclusions below
are conditional on such an embedding. Its existence is not established.
Write $`A=\mathbb N_e^M`$, $`B=\mathbb N_e^N`$, and use $`j`$ also for the
induced numerical embedding. These are the arithmetic reducts at the actual
evaluation points. They satisfy PA under $`I_e`$. Arithmetic function notation
in this note refers to those reducts; it does not add function types ending in
$`e`$ or new constants to C.

## Check of the stronger numerical constraint

For every $`a\in A`$, PA finite collection and $`M\models G^\#`$ give a
$`c\in A`$ such that

```math
M\models \forall x\le a\;\exists y<c\;\delta(x,y).                 \tag{1}
```

This is actual finite collection even when $`a`$ is externally nonstandard.
PA proves it by induction on $`a`$: choose a witness at zero, and at the
successor enlarge the previous bound to exceed the new witness. The induction
is an ordinary PA argument under the displayed totality hypothesis. No optional
Max or G premise is necessitated.

The matrix in (1), with parameters $`a,c`$, is bounded. The source's bounded
arithmetic rigidity lemma turns its truth in M into the literal proposition
identity

```math
I_M\wedge [\forall x\le a\;\exists y<c\;\delta(x,y)]_M=I_M.
```

The full-term map preserves this identity. Since $`I_N`$ is actually true,

```math
N\models \forall x\le j(a)\;\exists y<j(c)\;\delta(x,y).           \tag{2}
```

Consequently every number $`b\in B`$ for which
$`N\models\neg P(b)`$ satisfies

```math
                     j(a)<b\quad\text{for every }a\in A.          \tag{3}
```

This is stronger than saying that a counterexample is outside the image.
It rules out every numerically cofinal candidate embedding. The proof can also
be expressed using preservation of the Sigma-1 finite-collection formula, but
the displayed identity proof makes the retained modal premise explicit.

PA's least-number principle gives a least counterexample $`b_0`$ in N.
Every source image is strictly below $`b_0`$. Existence of this least
counterexample uses ordinary induction in N, not an external well-ordering of
its possibly nonstandard numerical domain.

## The omitted numerical cut

Define externally

```math
K=\{b\in B:\text{ for some }a\in A,\ b\le j(a)\}.
```

Then:

1. K is a proper initial segment of B, contains $`j[A]`$, and every member
   satisfies P in N. Properness follows from (3): $`b_0\notin K`$.
2. K contains zero and is closed under successor. If $`b\le j(a)`$, then
   $`b+1\le j(a+1)`$.
3. K is closed under addition and multiplication. Bounds $`b\le j(a)`$,
   $`d\le j(c)`$ give $`b+d\le j(a+c)`$ and $`bd\le j(ac)`$, using
   arithmetic preservation and monotonicity in N.
4. K has no greatest element, by successor closure. Its nonempty complement
   has no least element either: if $`d`$ were the least member of
   $`B\setminus K`$, then $`d>0`$, its predecessor would belong to K, and
   successor closure would put d in K.

In particular $`b_0`$ is not the first number beyond the image's downward
closure. There are numbers outside K below $`b_0`$, and P holds at each of
them by minimality of $`b_0`$. A candidate cannot introduce a first new
numerical element over K and place the counterexample there.

These are external descriptions. They do not assert that K is an admitted
entity, a model of PA, or an elementary substructure. No such claim is needed
for the obstruction below.

## No admitted image predicate or cut predicate

**Proposition.** Neither $`j[A]`$ nor K can be the actual numerical extension
of an admitted target predicate of type $`\nu_e t`$.

**Proof.** Suppose an admitted predicate W has

```math
N\models W(b)\quad\Longleftrightarrow\quad b\in j[A]
\quad(b\in B).
```

Since j fixes zero and preserves successor, W is true of zero and is closed
under successor on actual numbers. The number-induction principle in N,
available for every admitted property, therefore gives
$`N\models\forall b\in\mathbb N_e\,W(b)`$. This contradicts
$`b_0\notin j[A]`$. The same proof applies to K because it contains zero
and is successor-closed, while $`b_0\notin K`$. QED.

The predicate's values at nonnumbers are irrelevant. The argument needs only
the actual extension on the number domain, not a proposition identity or a
necessary truth claim about W. It also excludes a definition of either set by
any original-language formula with arbitrary target parameters: lambda
abstraction would supply the prohibited admitted predicate.

Thus any proposed full many-sorted construction must omit these particular
external sets from its admitted predicate domain at N. A policy allowing every
actual subset of the numerical domain fails immediately. This obstruction
applies even when M already has nonstandard arithmetic; omitting only the
external standard-numeral set is insufficient. It does not show that a suitable
restricted Henkin domain is impossible.

## Audit of the diagram route

The local one-way criterion and the positive-operation-diagram argument in the
source survive the following checks.

* Every finite piece of the operation diagram translates to finitely many
  identities between actual pure terms with named parameters. Those terms may
  contain quantifiers. NI makes a true diagram equation top at the source.
* For the embedding criterion, the finite conjunction of diagram disequalities
  and finitely many Max axioms is true, nonzero, and diamond-fixed. D(P) makes
  its conjunction with P nonzero. This proves finite consistency while keeping
  the optional finite Max conjunction inside the formula.
* For the positive-diagram quotient criterion, omitting diagram disequalities
  obtains a homomorphism, not an embedding. The one extra condition that the
  named p remain nonzero only protects that p. Joint separation by many such
  homomorphisms yields an algebraic product embedding, not a genuine Henkin
  truth structure.
* Compactness here is for the full many-sorted Henkin presentation of C, with
  its truth and quantifier clauses. A compactness argument in the algebraic
  reduct alone would not justify either genuine-model conclusion.

This audit identifies no correction to those source arguments. It also gives
no way to turn their quotient or algebraic product into the required M.
In particular the new omitted-cut conditions are necessary conditions on
genuine endpoints, not a truth lemma for an algebraic completion.

## Boundary and sources

The two-axiom consistency problem is still unresolved. The new construction
test is: a candidate embedding must be numerically bounded, and its target must
omit both the numerical image predicate and its proper downward-closure
predicate. No claim about full SP consistency, a failed pure-Max disjunction,
or a new Lean certificate is made.

Direct source for the deductions in this note: `misc`, this note. Inputs:

* [Strong Possibility follow-up](../source/research/2026-10-22/followup/strong-possibility.md),
  “An effectively specified arithmetic sentence independent of Max”, “Max
  already decides the first arithmetic level”, and “End-of-hour boundary and a
  concrete next target”: exact G, bounded rigidity, and the U_G presentation.
* [The one-way frontier](../source/research/2026-10-22/followup/strong-possibility-one-way.md),
  §§1, 3–4 and 7–9: numerical transport, exact local criterion, and distinction
  between the quotient and genuine-model obligations.
* [Arithmetic write-up](../source/topics/classicism/writeups/countable-boolean-completeness-implies-necessity-of-arithmetic.md),
  Lemmas 2–7: number induction, necessary numberhood, and conditional rigidity.
  The Countable Boolean Completeness step, Lemma 8, is not used here.
* [Universal-core note](../source/research/2026-10-22/notes/reflection-universal-core-20261022.md),
  §6: the full term-operation and Henkin signatures used by the diagram audit.

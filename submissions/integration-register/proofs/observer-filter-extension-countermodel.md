# Discrete-profile finite-partition model: necessary logical separation without ultrafilter extension

26 October 2026. Ordinary mathematical research by OpenAI Codex. Direct source:
`misc`, this note, §§1–8, unpaginated. This is a complete typed countermodel
construction, not a native database record or a Lean certificate.

## 1. Exact result

The discrete-profile finite-partition model satisfies every separately boxed instance of full logical observer separation, but has an admitted proper propositional filter without any admitted ultrafilter extension:

```math
\mathrm C+\Box\mathrm{OS}\not\models\mathrm{UFE}_t.
```

Section 5.1 verifies the whole Boolean and quantifier identities for the separating observers. The failure concerns admitted filters and predicates in the model.

For an admitted predicate $`F^{tt}`$, put

```math
\begin{aligned}
\mathrm{Filter}(F):={}&F\top\land\neg F\bot\\
 &\land\forall p q\,[(Fp\land Fq)\to F(p\land q)]\\
 &\land\forall p q\,[(Fp\land p\le q)\to Fq],\\
\mathrm{Ultra}(U):={}&\mathrm{Filter}(U)
                  \land\forall p\,(Up\lor U(\neg p)),\\
\mathrm{UFE}_t:={}&\forall F^{tt}\bigl[\mathrm{Filter}(F)\to
 \exists U^{tt}(\mathrm{Ultra}(U)\land
                    \forall p(Fp\to Up))\bigr].
\end{aligned}
\tag{3}
```

Here $`p\le q`$ is the map's algebraic entailment order. Filter in (3)
means a proper filter. An ultrafilter is a proper filter deciding each
proposition or its complement; it does not mean merely maximal among an
externally selected collection of admitted predicates. All predicate
inclusions concern current truth, rather than equality of predicate objects.

The construction works in ordinary ZFC metatheory. The failure is internal
admission: it does not deny that external nonprincipal ultrafilters exist.

## 2. Leaves and their finite typed hierarchy

Take a root r and one terminal leaf for each $`n\in\mathbb N`$. There is an
arrow from r to each leaf and no other nonidentity arrows. At every leaf use
the same full classical relational type hierarchy:

```math
L_e=\{*\},\qquad L_t=\{0,1\},\qquad
L_{\sigma\tau}=L_\tau^{L_\sigma}\quad(\tau\ne e).
\tag{4}
```

Every $`L_\sigma`$ is finite and nonempty, by induction on its type. The
function types are exactly the map's permitted types; no type with output e
is added.

Let $`G=\mathrm{Sym}(\mathbb N)`$. A finite partition $`\mathcal P`$
of $`\mathbb N`$ is a finite collection of disjoint nonempty cells with
union $`\mathbb N`$. Write

```math
G_{(\mathcal P)}:=\{g\in G:gC=C\text{ for every }C\in\mathcal P\}.
\tag{5}
```

Thus support fixes the cells as sets, not pointwise. Every permutation
inside a cell remains available. Finite intersections of such stabilizers
contain the stabilizer of the finite common refinement.

The group is an external symmetry used to define the admitted domains. Its
elements are not additional accessibility arrows or individual-valued
operations in the object language.

## 3. All root domains and their symmetry

Define the root domains and their G-actions recursively on type complexity.
Set $`D_e=\{*\}`$, with trivial action and the unique projection to each
$`L_e`$. For a relational type
$`\rho=\sigma_1\cdots\sigma_k t`$, let a root object be a pair

```math
a=(a_0,a_1),\qquad
a_0:\prod_{i=1}^kD_{\sigma_i}\longrightarrow\{0,1\},
\qquad a_1:\mathbb N\longrightarrow L_\rho,
\tag{6}
```

where $`a_0`$ is invariant under $`G_{(\mathcal P)}`$, acting
simultaneously on its arguments, for some finite partition $`\mathcal P`$.
The profile $`a_1`$ is arbitrary. The action is

```math
(g a)_0(\bar x)=a_0(g^{-1}\bar x),\qquad
(g a)_1(n)=a_1(g^{-1}n).
\tag{7}
```

All argument types in (6) have lower complexity than $`\rho`$, so the
recursion is well-founded. These are sets of objects, not proper classes.
Every domain is nonempty: choose a constant current table and a constant
leaf profile.

Since $`L_\rho`$ is finite, the nonempty fibers of any profile $`a_1`$
form a finite partition of $`\mathbb N`$. Refining this partition with a
support for $`a_0`$ gives a single partition whose stabilizer fixes both
components of a. Formula (7) transports a support partition to its image
under g, and therefore defines an action on each admitted domain.

When k=0, the current table is simply a bit and the profile a subset of
$`\mathbb N`$. Consequently

```math
\boxed{D_t=\{0,1\}\times\mathcal P(\mathbb N),\qquad
       g(\varepsilon,S)=(\varepsilon,gS).}
\tag{8}
```

Current truth is the first coordinate. Truth at leaf n is membership in S.
In particular every subset S is admitted as a proposition profile, supported
by its two-cell partition, after any empty cell is discarded.

Application is defined by current table sections and profile application.
For a of type $`\sigma\rho`$ and x of type $`\sigma`$,

```math
(ax)_0(\bar y)=a_0(x,\bar y),\qquad
(ax)_1(n)=a_1(n)(\pi_{n,\sigma}x),
\tag{9}
```

where $`\pi_{n,\sigma}x=x_1(n)`$ at relational types and is the unique
map at e. A common refinement of supports for a and x supports the current
section, so application is admitted. It is equivariant under (7).

Each $`\pi_{n,\sigma}:D_\sigma\to L_\sigma`$ respects application and
is onto. More strongly, every profile $`s:\mathbb N\to L_\sigma`$ lifts
to a root object: use s as its second component and a constant-false current
table if $`\sigma\ne e`$. At e there is just the unique profile. This
surjectivity is a fact about the construction, not an extra axiom.

## 4. Logical constants, abstraction, and C soundness

At the root, every primitive logical constant has its standard current
truth operation on the admitted domains and its constant classical operation
profile from (4). Thus conjunction, disjunction and negation act on (8) by
the product Boolean operations. The fixed abbreviations yield

```math
\top=(1,\mathbb N),\qquad \bot=(0,\varnothing),
\qquad
(\varepsilon,S)\le(\delta,T)
\quad\Longleftrightarrow\quad
\varepsilon\le\delta\text{ and }S\subseteq T.
\tag{10}
```

Equality at every type has current truth equal to literal equality of the
admitted objects. Its profile at n is equality of their images in
$`L_\sigma`$. Equality's current truth table is invariant under every g,
and its logical-operation profile is constant; hence the equality constant
is admitted. This includes individual equality.

For $`F\in D_{\sigma t}`$, interpret the two primitive quantifiers by

```math
\begin{aligned}
(\forall x^\sigma Fx)_0=1
 &\Longleftrightarrow\forall x\in D_\sigma\ F_0(x)=1,\\
(\forall x^\sigma Fx)_1(n)=1
 &\Longleftrightarrow\forall z\in L_\sigma\ F_1(n)(z)=1,
\end{aligned}
\tag{11}
```

and analogously with existential quantification. The current quantifier
tables are G-invariant because g bijects each admitted domain; their profiles
are constant classical quantifier operations. They are therefore admitted
at every type. A current quantifier and its leaf quantifier range over their
respective domains; no identification of these domains is assumed.

For an abstraction $`\lambda x.A`$, its current table evaluates the body
under root assignments to x and any remaining arguments. Its profile at n
is the ordinary full classical abstraction evaluated under the leaf images
of the free parameters. This is an admitted object. Indeed, finitely many
free parameters have a common finite support partition. Induction on terms,
using the equivariance of the logical constants and application, makes the
current table invariant under its stabilizer. The resulting leaf profile
has values in the finite set $`L_{\sigma\rho}`$, so is an allowed profile
and has a finite fiber partition.

The same term induction proves that projection to a leaf commutes with
term interpretation. Beta holds in the current tables and the classical
leaf functions separately, hence as equality of root pairs. Eta holds for
the same reason: the two components are actual tables and actual finite
functions. Arbitrary contextual beta/eta conversions consequently hold as
identities. Terms with output e are variables or constants and cause no
additional closure issue.

These facts verify H at the root and each leaf: the logical truth clauses
are classical, quantifiers range over nonempty admitted domains, identity
truth is literal equality, and conversion is exact. Its quantifier-rule
side conditions are respected by these semantics.

To verify C, suppose H proves $`P\leftrightarrow Q`$. Under every admitted
root assignment their truth values agree by H soundness. The current tables
of any corresponding abstractions of P and Q therefore agree. At every
leaf the H theorem is valid under all assignments in the full classical
hierarchy, so the leaf abstractions are equal functions. Both components
of the root abstractions are thus equal, verifying exactly C's unconditional
Logical Equivalence schema. The same argument permits residual free
parameters. It never identifies abstractions merely from an equivalence
under optional assumptions.

This supplies the full typed completion of the propositional algebra (8).
It is not merely a Boolean algebra with a chosen truth ultrafilter.

## 5. Admitted Boolean observers separate propositions

The identity observer I is admitted. For every $`n\in\mathbb N`$, define
an admitted observer $`E_n`$ by

```math
(E_n)_0(\varepsilon,S)=\mathbf1_{n\in S},
\qquad (E_n)_1(m)=\mathrm{id}_{\{0,1\}}
\quad\text{for every }m.
\tag{12}
```

Its current table is fixed by the stabilizer of the partition
$`\{\{n\},\mathbb N\setminus\{n\}\}`$, and its profile is constant.
Thus it belongs to $`D_{tt}`$. By (9),

```math
E_n(\varepsilon,S)=(\mathbf1_{n\in S},S).
\tag{13}
```

Evaluation at n commutes with intersection, union and complement. Section 5.1 verifies the corresponding whole-operation identities and quantifier laws for E_n and I.

For distinct $`(\varepsilon,S),(\delta,T)`$, if
$`\varepsilon\ne\delta`$, I distinguishes their current truth values.
Otherwise $`S\ne T`$; any n in their symmetric difference gives a witness
$`E_n`$. Thus these observers distinguish every pair of propositions at the root.

There is no assumption that all external set-functions on propositions are
admitted. The explicit observers (12) are enough.

### 5.1. The same witnesses give necessary full ordinary logical separation

Here ordinary logical qualification means preservation of the three Boolean
primitives and the primitive quantifiers at any finite specified list of
types, together with translated equality reflexivity and substitution:

```math
\begin{aligned}
R_\sigma(E)&:\quad\forall x^\sigma\,E(x=x),\\
L_\sigma(E)&:\quad\forall x^\sigma y^\sigma F^{\sigma t}
 [E(x=y)\to(E(Fx)\to E(Fy))].
\end{aligned}
```

Full typed separation observes the proposition outputs after all current
arguments of a relation have been supplied. Qualification requires identities between the whole composite
Boolean and quantifier operations. The equality clauses remain the displayed translated R/L clauses;
equality reflection is not asserted.

Fix n and a type $`\sigma`$. The current truth of
$`E_n(\forall x^\sigma Fx)`$ is
$`\forall z\in L_\sigma\,F_1(n)(z)`$. The current truth of
$`\forall x^\sigma E_n(Fx)`$ is
$`\forall x\in D_\sigma\,F_1(n)(\pi_{n,\sigma}x)`$.
They agree because $`\pi_{n,\sigma}`$ is onto. The existential clauses
agree for the same reason. At every leaf, $`E_n`$ is identity, so the
corresponding leaf composite operations agree too. The two-component
criterion (6) therefore identifies the whole quantifier composites, not
just their current values. The whole Boolean composites agree by the same
criterion and the elementary membership calculations in §5. These witnesses
also fix Top and Bottom as objects.

The current truth of $`E_n(x=y)`$ is equality of the leaf images at n.
Consequently $`R_\sigma(E_n)`$ is true, and literal equality substitution
in the classical leaf hierarchy proves $`L_\sigma(E_n)`$. These arguments
apply to every admitted type, including e. I satisfies all the same laws.

Now let X,Y be distinct root objects of any relational type. If their
current tables differ, a root argument tuple witnessing that difference
is distinguished by I. Otherwise their profiles differ at some n. The
full classical leaf functions then differ on a complete leaf argument
tuple. Lift its finitely many entries to root arguments by the surjectivity
of the corresponding projections. On that root tuple, $`E_n`$ distinguishes
the proposition outputs. This proves full typed logical separation for
every finite qualification list at the root. It uses no inference from
current coextension to identity.

At each terminal leaf, identity alone has all the logical qualifications
and separates every relational type. Thus each universally closed OS
instance is true at the root and every leaf, giving it the proposition
value $`(1,\mathbb N)=\top`$. Its box, defined by identity with Top, is
therefore true at the root. This establishes $`\Box\mathrm{OS}`$, understood
as the schema of separately boxed finite instances, without necessitating
an optional premise.

## 6. An admitted proper filter with no extension

Define $`F_*\in D_{tt}`$ by

```math
(F_*)_0(\varepsilon,S)=1
 \quad\Longleftrightarrow\quad\mathbb N\setminus S\text{ is finite},
\qquad
(F_*)_1(n)=\mathrm{const}_0.
\tag{14}
```

Its current table is invariant under every permutation, so has the
one-cell support $`\{\mathbb N\}`$; its leaf profile is constant.
Therefore it is admitted. Its current extension is a proper filter by
(10): it contains Top, excludes Bottom, is closed under meet, and is
upward closed. The current bit of its argument is deliberately irrelevant.
In particular

```math
F_*(0,\mathbb N)\quad\text{and}\quad
F_*(0,\mathbb N\setminus\{n\})\quad(n\in\mathbb N)
\tag{15}
```

are true. Thus neither the root truth reader nor any single-leaf reader
extends the filter.

Suppose an admitted U were an ultrafilter extending $`F_*`$. Its current
truth set $`\mathcal U\subseteq\{0,1\}\times\mathcal P(\mathbb N)`$
is an ordinary proper ultrafilter of the product Boolean algebra, by the
exact clauses of (3). Since $`(0,\mathbb N)\in\mathcal U`$, it rejects
the complementary root atom $`(1,\varnothing)`$. Hence

```math
\mathcal V:=\{S\subseteq\mathbb N:(0,S)\in\mathcal U\}
\tag{16}
```

is an ultrafilter on $`\mathcal P(\mathbb N)`$, and contains every
cofinite set. For clarity, its complement decision follows by meeting
the product complement of $`(0,S)`$ with $`(0,\mathbb N)`$; this gives
$`(0,\mathbb N\setminus S)`$. Properness excludes both alternatives.

Admission of U supplies a finite partition $`\mathcal P`$ whose
stabilizer fixes its current table. Formula (16) then shows that
$`\mathcal V`$ is invariant under every element of
$`G_{(\mathcal P)}`$.

The ultrafilter $`\mathcal V`$ contains exactly one cell C of the finite
partition. If C is finite, its cofinite complement also belongs to
$`\mathcal V`$, a contradiction. Thus C is infinite. Enumerate C in
increasing order and let $`C_0,C_1`$ consist of its alternating even and
odd positions. Define g to swap each successive pair of this enumeration
and to fix every point outside C. It swaps the two disjoint infinite
subsets and fixes every original support cell setwise.

Invariance gives

```math
C_0\in\mathcal V\quad\Longleftrightarrow\quad C_1\in\mathcal V.
\tag{17}
```

But their disjoint union C belongs to the ultrafilter, so exactly one
belongs to it. This contradicts (17). No admitted ultrafilter extends
$`F_*`$, and $`\mathrm{UFE}_t`$ fails at the root.

Only the current truth table of U was used. Its leaf profile may be
arbitrary; the argument therefore rules out even the material ultrafilter
qualification in (3), rather than only a stronger operation-preservation
qualification.

## 7. Interpretation of the separation

The model has enough admitted Boolean tests to distinguish each pair of
propositions, using a different leaf when necessary. Every finite list of
cofinite-profile requirements is accepted by some one of those leaf tests:
the intersection of finitely many cofinite sets is nonempty. Yet no admitted
Boolean test accepts all the requirements simultaneously.

Thus the result isolates the gap between pair separation and filter
extension. Section 5.1 shows that even necessary full logical separation does not close this gap.

We do not claim here a classification of the additional principles that
restore extension, or any unproved choice, infinity, or modal verdict for
this model.

## 8. Sources and status

The typed construction is a discrete-profile adaptation of
[Ternary Cantor symmetry](../../classicism-results-2026-10-24-v2/proofs/h-observer-space/ternary-cantor-observer-model.md),
§§2–4, replacing its clopen profiles by all subsets of $`\mathbb N`$ and
its homeomorphism supports by finite partitions under all permutations.
The complete domain and C-soundness verification is repeated above because
the typed admission conditions are essential to the result.

The distinction between point separation and extension, and the established
direction from admitted filter extension to separation, are discussed in
[Zorn supplies admitted lattice and Boolean characters](../../classicism-results-2026-10-24-v2/proofs/h-observer-space/zorn-lattice-character-extension.md),
§§2–5. That note proves extension from its explicit Zorn premise; no such
premise is used here.

The ordinary finite logical qualifications and full typed separation used
in §5.1 are stated in
[Typed separation and the recovery of Classicism over H](../../classicism-results-2026-10-24-v2/proofs/h-observer-space/typed-separation-and-classicism.md),
§§1 and 3–4. Their satisfaction here is checked directly, rather than
inferred by adding a stronger choice or modal premise.

The fixed H/C framework is Bacon and Dorr, *Classicism*, draft of 16 May
2023, §§1.1–1.3, as recorded in
[the topic framework](../../classicism-results-2026-10-24-v2/source/topics/classicism/background.md).
The discrete model, cofinite-filter witness, and nonextension proof in this
note are original ordinary proof arguments for this research session,
direct source `misc`. No human verification or Lean certificate is claimed.

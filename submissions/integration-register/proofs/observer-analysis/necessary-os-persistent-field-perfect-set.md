# Necessary observers and the perfect-set property of a persistent real field

Ordinary mathematical argument by OpenAI Codex, 26 October 2026 (`misc`); numbered sections, unpaginated.

**Result.** Fix a persistent real-field tuple, including its natural-number predicate, which satisfies Real necessarily. Under C5 + □OS, the perfect-set property for admitted subproperties of this field is noncontingent. The same coding argument makes real countable choice and real dependent choice noncontingent, without asserting that either choice principle is true. In particular, current PSP implies necessary CH for this field, and possible failure of CH implies necessary failure of PSP.

The fixed persistent tuple and its necessary completeness are explicit extra premises. This is not a theorem for arbitrary moving real fields, an inaccessible lower bound, or a Con(ZFC)-only contingent-CH model.

## 1. Exact setting and the endpoint theorem used

Fix an admitted carrier type σ and a tuple

```math
\mathfrak R=(X,0,1,+,\times,<,N)
\tag{1}
```

of the project's relational real-field data. All its predicates and relation graphs are persistent, including X and N, and assume

```math
\Box\mathrm{Real}_\sigma(\mathfrak R)
\tag{2}
```

Completeness has the authorized **nonempty bounded** meaning. Under C5, persistence makes every application of the fixed predicates endpoint-valued. Arithmetic relations, rational coding, and predicates defined from this tuple by ordinary quantification are likewise persistent. Object identity is endpoint-valued.

Use [the existential-relation endpoint theorem](necessary-os-ch-semantic-continuation.md), §3: under C5 + □OS, an assertion

```math
p=\exists A_1\cdots A_k\;\theta(\vec A;\vec P)
\tag{3}
```

is an endpoint when the P's are persistent predicates, the matrix uses only ordinary object quantifiers and Boolean operations, and the variable relation witnesses A_i occur only as predicate heads. In particular they may occur negatively and under ordinary quantifiers, but not as opaque arguments to an independently quantified higher predicate. The proof applies a qualified observer to the whole expression and replaces each A_i by its admitted pointwise image, obtaining E(p)≤p. Necessary observer separation then makes p equal to bottom or top.

Only finitely many types occur in the expanded formulas below. One may use any finite qualification list covering their exposed binders, or the established C5 reduction to qualification at t. No infinitary qualification conjunction or object-language quantification over types is required.

The obstacle to using (3) directly for PSP is that countability and existence of a perfect subproperty quantify over relation witnesses inside the matrix. The following coding removes those inner relation quantifiers.

## 2. One real codes every admitted sequence of reals

All constructions in this section are internal to the displayed field. Ordinary arithmetic on N defines pairing, finite binary strings, rational numbers and their enumeration, and the elementary finite-sequence recursions. Their graphs are relations in the fixed grammar; no function-returning-individual type is introduced.

First, every admitted predicate B⊆N has a real Cantor code. Form its finite base-4 sums

```math
s_n=\sum_{i<n}(1+1_B(i))4^{-(i+1)}
```

and take their supremum. The finite-prefix relation and its set of partial sums are admitted by comprehension and arithmetic induction. The sums form a nonempty bounded subproperty. Completeness supplies a real c. Its tail after n terms lies between (1/3)4^{-n} and (2/3)4^{-n}, so the decoding intervals for distinct finite 1/2 strings of equal length are disjoint and decoding has no endpoint ambiguity. Digit 2 means membership in B. This gives a persistent arithmetic digit predicate Digit(c,n), restricted by a persistent predicate Cantor(c), such that

```math
\forall B^{\sigma t}\,[B\subseteq N\to
 \exists c\in X\;(\mathrm{Cantor}(c)\land
        \forall n\in N\,[\mathrm{Digit}(c,n)\leftrightarrow Bn])]
\tag{4}
```

Conversely a code gives its admitted bit predicate by lambda abstraction. Pairing puts any admitted subset of N×N into the form (4). The construction uses no selection from nonempty sets: each finite prefix is unique, and one supremum supplies the code.

Let q_k be the fixed arithmetic enumeration of the field's rationals, expressed by a persistent relational graph. Define Entry(c,n,x) by saying that the bits in column n of c are exactly the rational lower cut of x:

```math
\mathrm{Entry}(c,n,x)
\quad\Longleftrightarrow\quad
x\in X\ \land\ \forall k\in N\,
 [\mathrm{Digit}(c,\langle n,k\rangle)
                                      \leftrightarrow q_k<x]
\tag{5}
```

The notation q_k is eliminable using its graph. Rational density makes an entry unique. Put

```math
\mathrm{Seq}(c):=
c\in X\land\mathrm{Cantor}(c)\land
\forall n\in N\;\exists x\in X\;\mathrm{Entry}(c,n,x)
\tag{6}
```

These definitions contain only ordinary quantifiers and fixed field predicates. Given any admitted total sequence graph F:N→X, comprehension forms its paired rational-cut bits; (4) supplies one c whose entries are exactly F. Conversely (5)–(6) supply a total functional sequence graph by comprehension and uniqueness. This is the exact admitted-sequence coding equivalence, not an assumption that every external sequence is admitted.

Consequently, for any admitted A⊆X,

```math
\mathrm{Countable}(A)
\quad\Longleftrightarrow\quad
\exists c\in X\,[\mathrm{Seq}(c)\land
 \forall x\in X\,(Ax\to
          \exists n\in N\;\mathrm{Entry}(c,n,x))]
\tag{7}
```

Here countable means that an admitted relational injection A→N exists. Given such an injection, its inverse is a partial sequence with at most one real at each index; fill unoccupied indices with 0 and code the resulting uniquely defined sequence. This handles empty and finite A too. Conversely a code covering A yields an injection by assigning to each member its least occurrence index. The least-index relation is admitted and functional. Neither implication uses Choice.

All the arguments use the field's N and its induction, not an assumption that its natural numbers are externally standard. In a nonstandard Henkin interpretation, (4)–(7) concern its own finite strings, digit predicates, and admitted relations.

## 3. One real codes a perfect subset

Define a nonempty perfect admitted subproperty P⊆X in the ordinary order topology: it is closed and has no isolated point. Both conditions are expressed by real quantifiers over neighborhoods; they do not require quantification over arbitrary topologies.

A rational Cantor scheme assigns a nondegenerate closed rational interval I_s to every finite binary string s. Require that the two child intervals lie inside the interior of their parent, are disjoint, and have length at most 2^{-|s|-1}. The endpoints constitute one admitted countable sequence of field elements. By §2 it has a real code c. Valid(c) states the rational-endpoint, nesting, disjointness, and length conditions using the persistent decoding relations. Define

```math
\mathrm{Body}(c,x):=
x\in X\land\forall n\in N\;\exists s\in N\,
 [s\text{ codes a binary string of length }n
                          \land x\in I_s(c)]
\tag{8}
```

Both Valid and Body are defined using only the fixed field data, arithmetic coding, and ordinary object quantifiers. In particular they are persistent predicates of their displayed arguments.

If Valid(c), its body is a nonempty perfect admitted subproperty. Following the all-zero branch and taking the supremum of its left endpoints gives a point in every interval of that branch. The body is closed because it is the intersection of the finite unions of the closed intervals at each level; equivalently, a point outside the body misses one such finite union and has an open neighborhood missing it. To see absence of isolated points, take a sufficiently small interval containing a given body point, follow the other child at a later split, and then the all-zero continuation. Completeness gives a different body point arbitrarily close to the original one. Each step uses a uniquely specified branch or one supremum, not countable Choice.

Conversely, let P be a nonempty perfect admitted subproperty. Choose the least code of a rational interval whose interior meets P as root. At each node choose the least code of a pair of rational child intervals satisfying the stated size and separation requirements and whose interiors meet P. Such a pair exists because P has no isolated points and the rationals are dense. The least-code rule gives one uniquely defined arithmetic recursion, so its full graph is admitted without selecting an arbitrary member from each of a countable family. Code its endpoints by §2.

The resulting body's points belong to P: at any level their containing interval meets P, and its length becomes arbitrarily small. Every neighborhood therefore meets P, so closedness puts the point in P. This argument makes only one existential use of a point of P for a given neighborhood; it does not choose a sequence of such points.

We have proved the exact equivalence

```math
\begin{aligned}
&\exists P^{\sigma t}\,[P\subseteq A\land P\text{ is nonempty perfect}]\\
&\hspace{12mm}\Longleftrightarrow\quad
\exists c\in X\,[\mathrm{Valid}(c)\land
       \forall x\in X\,(\mathrm{Body}(c,x)\to Ax)]
\end{aligned}
\tag{9}
```

The reverse direction simply takes the lambda-defined body. Every quantifier on the right is an ordinary object quantifier; A appears only as a predicate head.

For completeness, each valid scheme also gives an admitted injection X→Body(c). Encode x by its rational-cut bits, follow the corresponding branch, and use completeness to take its unique limit. Different cuts split at a node whose children are disjoint, so their limits differ. The graph is defined by that unique-limit property. Thus a perfect subproperty of A, together with the inclusion A⊆X, gives A≈X by the ordinary relational Cantor–Bernstein argument. This also proves internally that PSP implies the project's subset-cardinality form of CH without Choice.

## 4. PSP is an endpoint

Write $`\mathrm{PSP}(\mathfrak R)`$ for the assertion that every admitted A⊆X is countable or contains a nonempty perfect admitted subproperty. By (7) and (9), its failure is equivalent to

```math
\begin{aligned}
\exists A^{\sigma t}\;[A\subseteq X
&\land\neg\exists c\in X\;(\mathrm{Seq}(c)\land
             \forall x\in X\,[Ax\to\exists n\in N\;\mathrm{Entry}(c,n,x)])\\
&\land\neg\exists d\in X\;(\mathrm{Valid}(d)\land
             \forall x\in X\,[\mathrm{Body}(d,x)\to Ax])]
\end{aligned}
\tag{10}
```

Apart from the initial relation witness A, (10) has only ordinary object quantifiers. Its other predicate heads are persistent, and A occurs only as a predicate head. Therefore (3) makes (10) an endpoint under C5 + □OS.

The equivalence with failure of PSP was proved from Real. Necessitating that closed conditional and using the explicit premise (2) gives the equivalence necessarily; no optional assumption is silently necessitated. Complements of endpoints are endpoints. Hence

```math
\boxed{\mathrm{PSP}(\mathfrak R)
 \leftrightarrow\Box\mathrm{PSP}(\mathfrak R)
 \leftrightarrow\Diamond\mathrm{PSP}(\mathfrak R)}
\tag{11}
```

The same is true of its negation. Combining (11) with the necessary form of the ordinary PSP→CH theorem from §3 gives

```math
\mathrm{PSP}(\mathfrak R)\to
               \Box\mathrm{CH}(\mathfrak R),
\qquad
\Diamond\neg\mathrm{CH}(\mathfrak R)\to
               \Box\neg\mathrm{PSP}(\mathfrak R)
\tag{12}
```

Thus a CH-contingency construction with this same persistent necessarily real tuple must fail PSP everywhere. This agrees with the earlier repair constructions, whose CH-true side was required to have CH without PSP.

## 5. Short choice corollaries

The coding already proved also applies to real countable choice. Its failure can be written

```math
\exists H\,[\mathrm{Serial}_{N,X}(H)
       \land\forall c\in X\;
          \neg\mathrm{SelectorCode}(H,c)],
\tag{13}
```

where SelectorCode says Seq(c) and that its nth entry lies in H's nth row. H occurs only as a predicate head. Equivalence with ordinary relational selection follows from §2. Therefore CC_{N,X} is an endpoint.

For dependent choice, define the principle with an arbitrary prescribed initial point x₀∈X. Its failure is

```math
\exists H\;\exists x_0\in X\,
[\mathrm{Serial}_{X,X}(H)\land
       \forall c\in X\;\neg\mathrm{PathCode}(H,x_0,c)]
\tag{14}
```

PathCode says Seq(c), its zeroth entry is x₀, and consecutive entries are related by H. Again H occurs only as a predicate head and the remaining quantifiers are ordinary. Thus DC_X is an endpoint under the same assumptions.

These are modal constancy assertions, not proofs of Choice. The [finite-cylinder countermodel](necessary-os-real-countable-choice-separation.md) satisfies the persistent-field assumptions, necessary CH, and necessary failure of CC(R). There is no claim here about unrestricted higher-type Relational Choice.

## 6. The Feferman–Levy/Truss proposal and its remaining scope

Miller's [*Remark 3.4: A Dedekind Finite Borel Set*](https://people.math.wisc.edu/~miller/res/remark.pdf), Proposition 3 and its proof, pp. 1–3, supplies an uncountable real subset B in the Feferman–Levy model N with no injection of the reals into B. Thus B has no perfect subset. The correction footnote on p. 1 redirects an earlier weak-CH claim to the inner model N₀=HOD((Ord^ω)^N). Since every real is a sequence of ordinals, this inner model contains N's real numbers; they have the same real line.

**Conditional application.** If the particular N₀ is additionally verified to have PSP, then N₀ and N cannot be represented as the two evaluated real-relation structures of a C5 + □OS model on one persistent necessarily complete real-field tuple, with their real-subset facts interpreted exactly. Their opposite PSP verdicts would contradict (11). This obstruction is native and does not require that either side be an internally full ordinary forcing extension of a common ground.

The source bridge is explicit: Miller's footnote itself redirects the weak-CH statement; it does not state PSP for this N₀. The separate published Truss-model account used in the finite-cylinder note reports PSP, but identifying its model with this exact N₀ must be justified before applying the conditional conclusion. No such identification is silently supplied here.

Even with that identification, (11) does not exclude a construction using moving real-name labels and a nonpersistent real-field tuple. Equality of the actual sets of real numbers in two set-theoretic models is not already an admitted persistent native field. A successful varying-field interpretation still owes the complete finite-type Henkin closure, the C5 equality argument, and proper qualified cross-observers. A Boolean identity swap with an admitted qualified inverse would instead give reversible transport and cannot supply opposite CH. None of these interpretation obligations follows from the set-theoretic inclusion N₀⊂N alone.

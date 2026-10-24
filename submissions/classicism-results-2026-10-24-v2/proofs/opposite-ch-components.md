# Opposite CH components from consistency of ZFC

Assuming the syntactic consistency of ordinary first-order ZFC, there are two
one-world Henkin models of the project's fixed Classicism C. Each contains a
real number structure at type `e`; the first satisfies the project's structural
CH formula and the second falsifies it. No transitive model or externally
standard natural numbers are required. The two components can therefore be
used in the existing coalescence construction.

This is a mathematical construction by OpenAI Codex, prompted by Daniel Kodsi,
23 October 2026. Its direct attribution is `misc`; the relative-consistency
inputs are the classical results cited below.

## The exact claim and metatheory

Write `Real(R)` for the existing seven-parameter real-structure predicate:
a domain X, order, addition and multiplication graphs, zero, one, and the
least inductive subproperty N. Completeness means that every **nonempty**
admitted subproperty of X bounded above has a least upper bound. Write

$$
 CH(R)\;:\!\iff\;
 \forall Y\subseteq X\,
   \bigl(\exists G\;\mathrm{Injection}(Y,N,G)
       \;\lor\;
       \exists G\;\mathrm{Bijection}(Y,X,G)\bigr).
$$

Both subproperty and graph quantifiers range over the component's admitted
relational domains. They do not range over all external subsets or functions.
The definitions are those of `CoalescedCHVocabulary.lean` and the canonical
23 October database's Background, Analysis, and `non-contingency-of-ch`.

In a classical metatheory supporting first-order completeness and the usual
relative-consistency theorems, the assertion is

$$
 \mathrm{Con}(\mathrm{ZFC})\Longrightarrow
 \exists H_+,H_-\;
 \left\{
 \begin{array}{l}
 H_+,H_-\models C,\quad\text{each over one world},\\
 H_+\models\exists R\,(\mathrm{Real}(R)\land CH(R)),\\
 H_-\models\exists R\,(\mathrm{Real}(R)\land\neg CH(R)).
 \end{array}\right.
$$

The displayed assertion is a relative model-existence conclusion, not a proof
of `Con(ZFC)`. In particular it does not assert that ZFC proves its own
consistency or possesses an internally available set model of all of ZFC.

## Obtaining the two ordinary set models

The relative consistency of CH and its negation gives
`Con(ZFC + CH)` and `Con(ZFC + not CH)` from `Con(ZFC)`.
Apply ordinary first-order completeness separately to these theories. Obtain
set-sized structures

$$
 M_+\models\mathrm{ZFC}+CH,\qquad
 M_-\models\mathrm{ZFC}+\neg CH.
$$

One may choose countable models, but countability is unnecessary below. Their
membership relations may be externally ill founded; their natural numbers
may be nonstandard. The construction uses their actual first-order
satisfaction relation, never an identification of their membership with
external membership.

The consistency inputs are Gödel's theorem, *The Consistency of the Axiom of
Choice and of the Generalized Continuum-Hypothesis*, PNAS 24 (1938), pp. 556–557,
and Cohen's *The Independence of the Continuum Hypothesis*, PNAS 50 (1963),
pp. 1143–1148, and part II, PNAS 51 (1964), pp. 105–110.
[Gödel](https://pmc.ncbi.nlm.nih.gov/articles/PMC1077160/),
[Cohen I](https://pmc.ncbi.nlm.nih.gov/articles/PMC221287/),
[Cohen II](https://pmc.ncbi.nlm.nih.gov/articles/PMC300611/).
The relative-consistency theorem is the input here: this argument does not
infer a countable **transitive** model from consistency or carry out an
external generic-extension construction over an arbitrary ill-founded model.

## The internal finite type hierarchy

Fix either structure `M`. For an element a of M, let
`a* = {x in |M| : M satisfies x in a}` denote its external extension.
An internally named set and its external extension remain distinct objects.
Choose in M its usual real field, with underlying set r. Standard ZFC proves
the existence of this set and of its operation graphs, so these are actual
elements of M. Set the individuals domain to `D_e = r*`.

Use the project's relational types: an argument may have any type, but every
nonindividual type ends in t. Define internal set codes by external recursion
on these **standard finite** types. If rho is a finite argument list ending
in t, put

$$
 T_t=\{u\}^{M},\qquad
 T_{\sigma\to\rho}=D^{\rm code}_\sigma\times^{M}T_\rho,
 \qquad
 D^{\rm code}_e=r,\qquad
 D^{\rm code}_{\mathrm{rel}(\rho)}=\mathcal P^{M}(T_\rho).
$$

Here u is a fixed element of M, for example its empty set; products use an
internal injective ordered-pair coding. The external typed domains are
`D_sigma = (Dcode_sigma)*`. An argument tuple is encoded recursively by u
for the empty tuple and the chosen pair of its head and encoded tail.
Product membership gives a bijection between external typed tuples and
`T_rho*`. Pair injectivity proves injectivity by finite induction; product
membership and the induction hypothesis prove surjectivity.

An admitted relation is an element `A in M` that M regards as a subset of
`T_rho`. Its profile on an external tuple a is

$$
 \mathrm{profile}(A)(a)\iff M\models\mathrm{encode}(a)\in A.
$$

If two admitted relations have the same profile, they have the same M-members
by the tuple bijection; all their members lie in `T_rho`. Extensionality in M
then makes them equal as elements of M. Thus profiles are injective at every
relational type. At t, the only profiles are false and true: an internal
subset of a singleton is empty or that singleton, also externally, by
extensionality.

All domains are nonempty. The real set contains zero. Every relational
domain contains the empty set of tuples. This argument also covers types
with relational arguments and the nullary truth type; no external full
powerset assumption enters it.

## Comprehension and the one-world C model

Translate a finite formula of the nonmodal typed relational language to a
first-order set formula. A variable of type sigma is restricted to the
internal set `Dcode_sigma`; relation application is membership of the encoded
tuple. Equality is equality of the corresponding elements of M. Translate
Boolean connectives directly, and a typed quantifier as a first-order
quantifier restricted to its domain code. All codes and the finitely many
assigned values are ordinary first-order parameters.

Induction on the finite formula proves the satisfaction lemma. In the
quantifier step the external quantifier over `D_sigma` ranges over exactly
those M-elements satisfying membership in the domain code. In the application
step the assertion follows from the definition of profile. Thus the induction
does not require the formula to range over external powersets or M to have
an externally correct satisfaction predicate for nonstandard formula codes.

For a formula phi with free argument tuple of type rho, Separation in M
forms the subset of `T_rho` whose decoded tuple satisfies the translated
formula. Tuple decoding can be expressed with finitely many existentially
bound components and equality to the nested pair code. This supplies an
admitted relation for every such comprehension instance, with parameters.
Only standard finite instances of Separation are used.

Consequently the hierarchy is an extensional Henkin structure for the
project's relational language. A mutual induction on terms and formulas
proves term admission together with the satisfaction lemma. Application of
a relational object A to an argument x is represented by the internal slice
`{b in T_tail : pair(x,b) in A}`. Abstraction is the Separation construction
above, after interpreting its finitely many subterms. Logical operations
are their corresponding finite comprehension instances.
Give the structure one reflexive world. Necessity there is identity on truth,
so modal subformulas translate by erasing the singleton box; substitution
and binding are handled by the same finite translation.

This validates H and Logical Equivalence: an H-provable equivalence holds
under every assignment; the two abstracted relations consequently have the
same profile, and injectivity makes them identical. It therefore validates C.
Equivalently, this is the existing `ChoiceFirstOrder` construction: the
translation gives `SmallComprehension`, from which the existing modelhood
theorem follows. `CoalescedFirstOrder` transports its unique world to the
unique-world category required by the coalescence implementation.

## Representing the real structure

For concreteness, construct integers in M from pairs of omega elements,
rationals from integer fractions, and reals as the set of nonempty proper
downward-closed subsets of those rationals with no greatest element. These
Dedekind cuts form a subset of M's power set of its rationals. Order is cut
inclusion; the usual cut definitions of addition, additive inverse and
multiplication give internal set graphs by Separation and Replacement.
The standard ordered-field verification is a ZFC theorem. A nonempty family
of cuts bounded above has their union as its least upper bound: the bound
makes that union proper, and nonemptiness, downward closure and the absence
of a greatest rational are preserved. This proves internal completeness
without assuming a complete field as additional model data.

Let `R_M` be this real field constructed **inside M**. Its whole
underlying domain, order relation, addition and multiplication graphs, and
the image `N_M` of the internally constructed omega are sets in M. Recode
these relations into the nested tuple convention just defined. For example,
an internal unary subset A of r is represented by

$$
 \{\langle x,u\rangle:x\in A\}^{M}.
$$

Replacement gives this code. Conversely, Separation on r decodes any
admitted unary relation. The same two operations work for each finite arity.
The graph code for a binary relation is nested as
`pair(x, pair(y, u))`; it is not silently identified with a set-theoretic
binary-pair code `pair(x,y)`. This recoding is an internal bijection of the
two tuple sets and preserves application.

The first-order ordered-field axioms transfer by the satisfaction lemma.
For completeness, every admitted nonempty unary subproperty bounded above
decodes to an M-subset of r with those properties. M's theorem that its real
field is Dedekind complete supplies a least upper bound in r; translating
back gives the required object-language witness.

The set `N_M` is inductive. If an admitted subproperty of r contains zero and
is closed under addition by one, its decoded M-subset has those same
properties. Induction on omega **inside M**, applied to the embedding of
omega into its real field, shows that it contains `N_M`. Thus `N_M` is the
least admitted inductive subproperty, exactly as required by `Analytic.Real`.
No claim is made that this subset is the external standard natural-number
part of the ordered field. In a nonstandard model it need not be.

We have therefore constructed actual seven-parameter witnesses to
`Real_e(R_M)` in the associated one-world C model.

## The CH truth correspondence

By the recoding bijections, unary relations supported on r correspond to
all M-internal subsets of r. Binary relations supported on two subdomains
correspond to all M-internal graphs between them. Support, totality,
functionality, injectivity and surjectivity are first-order assertions about
these sets. The satisfaction lemma consequently gives

$$
 H(M)\models CH(R_M)\quad\Longleftrightarrow\quad
 M\models\forall Y\subseteq\mathbb R\,
   (Y\hookrightarrow\mathbb N\ \lor\ Y\cong\mathbb R).
$$

The right-hand assertion is equivalent in ZFC to ordinary CH. Here is the
cardinal argument, carried out **inside ZFC**, so it applies inside every M.
The internally defined natural subset of the real field is in bijection
with omega, and the real set is in bijection with the power set of omega.
If CH holds, an internal subset Y of the reals either has cardinal at most
aleph-zero or, by Choice and cardinal comparison, has cardinal at least
aleph-one and at most the continuum. In the latter case CH makes its
cardinal equal to the continuum. Choose the required injection or bijection
as an internal set graph; its recoding is an admitted relational witness.

Conversely, the continuum is uncountable by Cantor's theorem. Choice
therefore supplies a subset Y of the real set of cardinal aleph-one.
This Y does not inject into the naturals. The displayed structural assertion
forces Y to be in bijection with the real set, giving CH. Equivalently, if
CH fails, that same Y has cardinal strictly between aleph-zero and the
continuum and witnesses the failure of the structural assertion.

The ordinal formulation used by Flypitch says that every ordinal is at most
countable or at least as large as the power set of omega. In ZFC it has the
same truth value by well ordering and the preceding comparison. Its
`at_most_f` encodes a partial surjection from the larger set onto the smaller
one. Choice selects one preimage per value to obtain an injection in the
reverse direction; conversely an injection's inverse graph on its image is
the required partial surjection. These operations are internal set
constructions. An external function selected outside M is insufficient.

Apply the correspondence to `M_+` and `M_-`. It gives the two actual
opposite-CH component witnesses in the theorem, without any standardness or
transitivity requirement.

## Use in the broader project

The two components meet the existence premises of
`CoalescedCHModel.coalesced_countermodel` in its actual namespace
`Classicism.Meta.Research.CoalescedCH`. Coalescing them yields a root accessing
both leaves. At that root, the CH-positive leaf falsifies the boxed assertion
that all real structures falsify CH; the CH-negative leaf falsifies the boxed
assertion that all real structures satisfy CH. Thus the exact database
non-contingency sentence fails, at its `e` instance.

In particular, failure at this one type refutes the all-type principle.
This does not require that every type contain a real structure, or that all
real structures at either leaf be classified. The two existential witnesses
alone suffice. The general coalescence and soundness lemmas also turn the
components into the two C-consistency witnesses used by the conditional
Maximalism argument. Optional rigidity and choice verdicts for the coalesced
root require their own proofs and are not inferred here.

## A smaller positive-component construction

The Lean implementation can avoid formalizing the general theorem that every
internal set has an ordinal of the same cardinality. It is enough to retain
one particular ordinal witness in the same first-order sentence as the real
field. In the collapse Boolean model, take the checked ground-model first
uncountable ordinal A. The pinned source proves that A remains an ordinal,
every member a of A injects into internal omega, and internal P(omega) is at
most as large as A. The final comparison is initially expressed as a partial
surjection from A; internal Choice converts it to an injection into A.

These assertions, the field, its least inductive subset N, and the actual
cardinal maps are preserved together when extracting the ordinary model.
The real-field coding supplies injections both ways between R and P(omega),
and a bijection between N and omega. Hence R injects into A, and every proper
initial segment of A injects into N. All orders, subsets, and maps in this
paragraph are internally coded sets.

Here is the exact argument for structural CH from those data. Fix an
internal Y contained in R. Form the internal set of partial injections from
A to Y whose domains are downward closed in A. This is a set of graphs in
P(A × Y), selected by one finite formula. It contains the empty graph.
The union of any internally coded chain is again a partial injection with
downward-closed domain, so the internal Zorn axiom supplies a maximal graph G.

If G has all of A as its domain, compose R → A with G to obtain R → Y.
Inclusion supplies Y → R, and internal Schroeder–Bernstein gives Y ≅ R.
Otherwise the internally coded complement of its domain has a least element a.
Downward closure and linearity show that its domain is exactly the proper
initial segment below a. If G failed to cover Y, adjoining the pair (a, y)
for any omitted y would give a larger allowed graph, contradicting maximality.
Thus its inverse injects Y into that initial segment and then into N.
This establishes the two alternatives of structural CH for every admitted Y.

The argument uses only the selected ordinal, its countable initial segments,
finite Separation, products, the source Zorn axiom, and internally coded
cardinal maps. It neither replaces internal subsets by arbitrary external
subsets nor assumes an external well-order has an internal graph. For the
negative component, the failed ordinal CH sentence already supplies its
particular offending ordinal; no arbitrary-set ordinal representation is
needed in that direction either.

The source inputs are the pinned `bSet.check_Ord`,
`bSet.injects_into_omega_of_mem_aleph_one_check` in `Flypitch4/AlephOne.lean`,
and `collapse_algebra.aleph_one_not_lt_powerset_omega` in
`Flypitch4/ForcingCH.lean` (unpaginated Lean sources). The new internal Zorn
argument is this project's construction; those source lemmas are not being
credited with the whole structural-CH proof.

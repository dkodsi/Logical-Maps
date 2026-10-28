# Pure Maximalism and Forcing Possibilism

25 October 2026. Ordinary mathematical proof developed in this research task.
Direct source of the connecting results: `misc`. Metatheory: external ZFC.
This note is not a Lean certificate, a human review, or a literature-priority
claim. No database record is changed.

**Result.** There is a model of C + pure Maximalism + the database's strict,
unboxed Forcing Possibilism, simultaneously at every admitted carrier type,
including e. The existing one-individual definable-profile root is such a
model. Conversely, the pinned-substitutions root satisfies pure Maximalism
and refutes FP. Thus FP is relatively independent of pure Maximalist C.
Pure Maximalism nevertheless entails the failure of **boxed FP**, already
at carrier type t.

## 1. Exact scope

C is the fixed relational theory in `topics/classicism/topic.yaml`: base
types e,t, with σ→τ admitted only when τ≠e. Logical Equivalence retains
its H-theoremhood condition. Pure Maximalism has the fixed C side condition:


$$
\Diamond P\qquad(P\text{ closed and pure},\ C+P\text{ consistent})
$$


Its equivalence with the official distinctness form is the equivalence in
`distinctness-schema-r`. No signature Maximalism or Strong Possibility is
assumed.

The target is the upstream `forcing-possibilism` record at commit
`a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb`:


$$
\forall X^{\sigma t}\,\forall R^{\sigma\sigma t}.
\bigl(\mathrm{CBA}(X,R)\land
 (\mathrm{Fin}(X)\lor X\prec D_t)\bigr)
\to\exists p^t\ne\top\; (X,R)\cong([0,p],\le)
\tag{FP}
$$


Here D_t abbreviates the universal property of propositions. Fin is
Dedekind finiteness using admitted injection graphs; strict smallness
requires an admitted injection forward and none backward. CBA tests every
admitted subproperty. Isomorphisms are admitted binary relations. All
quantifiers are unboxed. The order on propositions is the Boolean order
defined by whole-entity equality, not current material implication. The
one-element Boolean algebra is permitted.

## 2. A general criterion at extensionally full evaluation points

Call an evaluation point *extensionally full* here if every external subset
of every finite product of its admitted carriers is the current extension
of an admitted relation. This is a semantic hypothesis, not Functional
Choice or an assertion that coextensive relations are identical.

**Externalization lemma.** At such a point, a represented CBA is an
externally complete Boolean algebra on its current carrier. Admitted
injections and order isomorphisms exist exactly when the corresponding
external graphs exist. In ZFC, internal Dedekind finiteness is therefore
ordinary finiteness.

Indeed, the unboxed first-order order and Boolean-algebra clauses use
literal carrier equality and the current extension of R. Every external
subset of the carrier occurs among the properties in the completeness
clause. Every required function graph is a current binary relation,
including mixed-type graphs. Multiple intensional representatives of one
extension do not change these graph predicates, which test their arguments
by application. For proposition intervals the order is still the actual
Boolean-algebra order on proposition entities.

**Cardinal lemma.** Every infinite externally complete Boolean algebra has
at least continuum many elements in ZFC.

To prove it, choose disjoint nonzero elements b_0,b_1,…. If there are
infinitely many atoms, take distinct atoms. Otherwise the complement of
the join of all the finitely many atoms is nonzero: if it were zero, the
algebra would be finite. That complement is atomless; repeatedly split
the remaining nonzero part, retaining one part as b_n. Completeness gives
s_U = sup{b_n : n∈U} for every U⊆ℕ. If k∈U, b_k≤s_U; if k∉U, every
summand is below ¬b_k, so s_U≤¬b_k. Thus U↦s_U is injective.

**Criterion.** Suppose the evaluation point is extensionally full and its
proposition Boolean algebra B is infinite with |B|≤2^ℵ₀. Then strict FP
holds there if and only if B has infinitely many atoms.

For sufficiency, the externalization and cardinal lemmas show that every
qualifying CBA is finite. If it has n atoms, choose distinct B-atoms
a_1,…,a_n and set p=a_1∨…∨a_n. A further atom witnesses p≠top. Every
q≤p is the join of exactly those a_i below q, since finite distributivity
gives q=∨_i(q∧a_i). Hence [0,p] is the Boolean algebra of all subsets of an
n-element set. The finite CBA is isomorphic to it, and the mixed-type graph
is admitted. When n=0 use p=bottom.

For necessity, for each external natural number n choose 2^n distinct
members of B and represent the finite Boolean algebra with n atoms on
them. The relations are admitted, and this is a finite CBA at carrier t.
FP gives an interval with n atoms. An atom of [0,p] is an atom of B:
anything below it is already below p. Thus B has arbitrarily many atoms.

For **countably infinite** B, the strict-smallness part of the sufficient
direction is even simpler and needs no completeness cardinal bound. If X
injects into B and is infinite, X is countably infinite; a reverse
injection exists and is admitted. Thus X≺B already implies X finite.
The CBA cardinal lemma remains useful for continuum-sized roots and the
non-strict variant in §5.

## 3. The definable-profile root

Use the construction already proved in
`research/2026-10-22/sp-structural-proof-package/profile-root-construction-20261022.md`,
§§1–5. Its pure reduct is exactly the upstream
`coalesced-definable-root` construction. The following details make the
present use self-contained.

Take a set of pure action models complete for C, with disjoint component
categories. Add a fresh root o with one individual *. For every component
object V and a∈D_e(V), include an arrow h_(V,a):o→V carrying * to a.
Composition is k h_(V,a)=h_(V',k·a). No nonidentity arrow returns to o.

For every relational type τ, let B_τ be the families of denotations of
pure terms T(z):τ, with at most one free variable z:e, over all (V,a).
Two terms determine the same profile exactly when these families agree.
For τ=σ_1…σ_k t put, recursively,


$$
D_\tau(o)=\mathcal P\bigl(D_{\sigma_1}(o)\times\cdots
 \times D_{\sigma_k}(o)\bigr)\times B_\tau
\tag{1}
$$


For t the first coordinate is a truth bit. Transport of (S,[T]) along
h_(V,a) is T^V(a). Application slices S and applies the component term
profiles; the individual * has profile z.

**Closure and C.** A term with finitely many root parameters obtains a
profile by capture-avoiding substitution of their pure profiles into it.
At each outgoing arrow it denotes the corresponding component entity.
Abstraction has its arbitrary actual root extension and this term
profile, hence belongs to (1). Bound variables at a component range over
that component's entire domain, not just the image of a root transport.
Beta and eta follow from slicing and component beta/eta. The current
truth, quantifier and literal-equality clauses validate H. H-provably
equivalent abstractions have identical root extensions and identical
profiles, since every component validates C. This verifies Logical
Equivalence with the required theoremhood restriction. It does not
restrict an old model to its term-denotations or assume a surjective
transport.

**Pure Maximalism.** If C+P is consistent, a component object V makes P
true. Any a∈D_e(V) gives an outgoing arrow at which P is true. Its root
denotation therefore differs from bottom. Every original pure Maximalism
instance holds at o, with its side condition still relative to C.

**Countability and extensional fullness.** There are countably many finite
pure terms T(z), so B_t and D_t(o)=2×B_t are at most countable. There are
infinitely many profiles, as the sentences “exactly n individuals” are
separated by finite extensional C models. The proposition carrier is
therefore countably infinite. Every current relation is admitted: pair
its chosen extension with a bottom profile of the appropriate relational
type. This includes every carrier type, e included, and every mixed-type
graph. Higher carriers need not themselves be countable.

## 4. Infinitely many atoms in that root

Let F be the Fregean Axiom and E_n say that exactly n individuals exist,
for each external n≥1. Put A_n=F∧E_n, a closed pure proposition.

At any component object satisfying A_n, F makes the proposition domain
two-element and entails Extensionality at every admitted relational type.
Inductively all type domains are finite and full: every subset of a finite
product is definable with parameters by a finite disjunction of equality
tests. Extensionality makes the resulting extension map injective. Hence
the local typed logical structure is the full extensional hierarchy on n
individuals, uniquely up to isomorphism. Its individual permutations act
transitively. Therefore any pure proposition term T(z) has one fixed truth
value over all pointed A_n-objects (V,a), independent of V and a.

This uniformity gives a statement about **whole profiles**, not merely
current coextension. At every component object, A_n∧T(a) has either always
the same truth as A_n, or always the same truth as bottom, with the choice
fixed for T and n. The same is true after every component arrow, because
the target with its transported individual is again one of the pointed
objects in the family. Equality of these truth profiles is equality of
propositions in the action model. Thus [A_n∧T] is [A_n] or [bottom].

F is false at o because its proposition domain is infinite. Consequently
A_n has false root truth bit. For any root p=(b,[T]), the meet p∧A_n has
false truth bit and profile either [bottom] or [A_n]. It is therefore
literally bottom or A_n. The latter is nonzero: C+A_n has the full finite
extensional model, so a component realizes A_n. This proves Atom_t(A_n).

The A_n are pairwise disjoint, since E_n and E_m are incompatible for
n≠m. We have infinitely many distinct global Boolean atoms. Applying §2
proves FP at o for **all** admitted carrier types simultaneously.

An explicit witness for a finite CBA with n atoms is
p=A_1∨…∨A_n. It is proper, since A_(n+1) is a disjoint nonzero atom.
Choose an enumeration x_1,…,x_n of the given finite CBA's atoms and map
x to the join of A_i for which x_i≤_R x. The graph is an admitted
σt t relation by (1). This supplies precisely the isomorphism requested
by FP, including when σ=e. For the degenerate CBA use the unique map to
bottom.

## 5. Further conclusions, with scope kept explicit

**The non-strict version is also compatible with pure Max.** In this same
countable root, even a CBA whose carrier merely injects into D_t must be
finite: an infinite complete Boolean algebra cannot be countable by §2.
Thus replacing strict smallness by the non-strict bound also holds here.
This is an ancillary strengthening, not a replacement of the target
definition. It does not assert compatibility with the source's additional
boxed Rigid Comprehension, Intensional Choice, and CH conditions.

**FP is not necessary under pure Max.** Consider the closed pure instance
FP_t. A full one-world extensional C model has precisely two propositions.
Its whole proposition carrier with Boolean order is a finite complete
Boolean algebra. The only p≠top is bottom, and its interval has one
element. Thus this model falsifies FP_t. Therefore C+¬FP_t is consistent.
Pure Max supplies ◇¬FP_t, equivalently ¬□FP_t. This proves the
incompatibility of pure Max with boxed FP, without strengthening the
reference theory in Max's side condition.

**Strict FP and ordinary current analysis can coexist with Max.** There
is also a continuum-sized variant. Enumerate all C-consistent pure
sentences φ_i and choose countable-domain BBK C models M_i satisfying
them, using countable completeness. Form the free-current root with any
nonempty individual set E and


$$
D_\tau(o)=\mathcal P\bigl(\textstyle\prod_jD_{\sigma_j}(o)\bigr)
             \times\prod_i D_\tau(M_i)
\tag{2}
$$


Choose arbitrary individual maps E→D_e(M_i). The profile-free closure
proof is the same coordinatewise proof as §3: lambda and quantifiers use
the entire domain within each coordinate. Every φ_i has a true component,
so the root satisfies pure Max. The proposition algebra is
2×∏_i D_t(M_i), of cardinal continuum, since each factor is countable
and nontrivial. For infinitely many distinct i, φ_i is F∧E_n, forcing
D_t(M_i) to be two-element. The element supported only on each such
factor is a global atom. Formula (2) is extensionally full, so §2 proves
strict FP here as well.

Taking E=ℕ gives the very construction in
`research/2026-10-25/max-analysis-review/current-analysis.md`. As proved
there, it admits the full current real field on its continuum-sized
proposition carrier using relational operation graphs and all external
finite-arity relations. The present argument adds strict FP to that same
construction. No operation representative, necessary analysis, or
non-strict FP claim for this continuum-sized variant is being asserted.

## 6. Negative models and the six requested families

**Pinned interpretation root.** This root has exactly one Boolean atom,
δ, the proposition true only at its identity arrow. To see that there are
no others, let p have a nonzero component part and finite support S.
Choose a component arrow (V,I) at which p is true and a propositional
constant c outside S. Vary I(c) between top and bottom, fixing S. Both
arrows remain in p. The admitted entity ĉ splits p into two nonzero
parts; it lands in each component by construction and is pinned by {c}.
Any p without a component part is bottom or δ. A four-element finite BA
is representable on four distinct root individuals using equality-defined
finite relations. FP would require an interval with two atoms, hence two
global atoms. Thus `coalesced-pinned-interpretations-root` refutes FP.

**Pinned substitution root.** If a nonzero p has a component witness, the
preceding fresh-constant argument splits it. Otherwise it has a root
self-map witness f. Let S support p and choose two distinct fresh
individual constants c,d outside S. Extend f|S once with c,d mapped to
the same individual constant and once with different images. Both maps
remain in p, and the equality proposition c=d distinguishes them. That
proposition is admitted by C and supported on {c,d}. Thus every nonzero
p splits: the proposition algebra is atomless. A two-element BA on two
distinct root individuals is a finite represented CBA. FP would make it
an interval below an atom, which is impossible. Therefore
`coalesced-pinned-substitutions-root` refutes FP. Its already established
pure Maximalism proves the negative half of the independence claim.

For the six records requested in the assignment:

| Model ID | Conclusion justified here |
| --- | --- |
| `coalesced-definable-root` | FP holds; §3–4 applies to its pure reduct. |
| `coalesced-pinned-interpretations-root` | FP fails; exactly one propositional atom. |
| `coalesced-pinned-substitutions-root` | FP fails; no propositional atoms. |
| `coalesced-maximalist-root` | The countable-component specialization (2) satisfies FP. The unbounded family receives no uniform verdict here. |
| `coalesced-single-individual-root` | The same specialization with E a singleton satisfies FP. The unbounded family receives no uniform verdict here. |
| `coalesced-constant-indexed-root` | With countable signature and a countable complete family of countable-domain components, the same product criterion proves FP. Preserve that size qualification. |

For the last row, enumerate consistent signature sentences instead of
pure ones; the finite Fregean pure sentences remain among them and supply
the two-element factors. Countability of a possibly larger signature is
an additional explicit condition, not something inferred from the presence
of countably many individual constants. In the three product families,
do not infer a verdict for arbitrary component sizes from this choice of
components.

## Sources

Connecting results: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026, §§2–6 (unpaginated), `misc`. The definable and pinned root constructions retain their existing database attribution. The earlier profile construction and its verification are retained in the previous submission:

- [Profile-root construction, §§1–5](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/sp-structural-proof-package/profile-root-construction-20261022.md).
- [Construction audit](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/sp-structural-proof-package/reflection-universal-core-20261022.md).
- Bacon and Dorr, *Classicism*, database draft of 16 May 2023, §1.4 p. 16 n. 18, §2.4 pp. 35–36 and Appendix E pp. 80–83. The author-hosted 1 July 2022 draft has different pagination; its Theorems 3.2 and 3.23 provide the countable/action completeness inputs.

The correction of the definable-root completeness explanation is in [the separate correction note](definable-root-completeness-correction.html).

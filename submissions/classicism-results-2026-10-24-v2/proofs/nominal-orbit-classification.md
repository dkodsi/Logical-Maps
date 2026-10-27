# Nominal orbit classification and Intensional Choice

Original research by OpenAI Codex, prompted by Daniel Kodsi, 23 October 2026; direct source `misc`, cited unpaginated sections. No claim of human verification or literature priority.

## 1. Exact construction and two targets

Let A be **any set**, let G be its full permutation group, and let W be a
G-set in which every world has a finite support. Individuals are the fixed
trivial-action set N. Propositions are all finitely supported subsets of W;
each admitted relational arrow contains all finitely supported functions
under conjugation. Truth is membership at a designated world. The ambient
metatheory is ZFC. An actual semantic verdict supplies a world, so the
unpointed empty-world case is not presented as a pointed model.

The first target is the exact equivalence

```math
\mathrm{DedInf}_t\quad\Longleftrightarrow\quad
\text{the external set }W/G\text{ is infinite}
\tag{1}
```

Here DedInf_t is the existing **operational** sentence: an admitted operation
on the whole proposition domain is injective and misses a proposition. It is
not the map's quantified Frege Axiom of Infinity. Both truth and falsity in
(1) hold at every world, hence also in their respective boxed forms.

The second target specializes W to A with its natural permutation action:

```math
\Box\mathrm{IC}_\sigma\quad\text{for every admitted type }\sigma,
\qquad\Box\neg\mathrm{DedInf}_t
\tag{2}
```

For a pointed atom model A must be nonempty. The result includes infinite A,
so all-type Intensional Choice can coexist with failure of operational
Dedekind infinity in an infinite-world model. The old certificate already
proved the negative Dedekind assertion and IC for individual witnesses;
all-type IC is the new part of this corner. The full IC/FC/RC classification
for arbitrary W is outside this continuation.

The arbitrary-atom extension concerns these two targets specifically. If A is
finite, its whole set supports every external function: Fix(A) contains only
the identity. The hierarchy is then full and ambient ZFC supplies Functional
Choice even when the chosen group action is nontrivial. Thus the original
nontrivial-action FC failure must retain its infinite-atom hypothesis.

## 2. Finite global orbits split into finitely many support-fixer orbits

Fix a finite set S of atoms. First consider one global orbit with representative
w and any finite support K of w. Least supports are unnecessary. For g∈G,
record the finite pattern

```math
\pi_g:K\longrightarrow S\sqcup\{*\},\qquad
\pi_g(a)=\begin{cases}g(a),&g(a)\in S,\\ *,&g(a)\notin S\end{cases}
```

There are at most $`(|S|+1)^{|K|}`$ patterns. If g and h have the same pattern,
the finite partial bijection g(a)↦h(a), a∈K, fixes every point it mentions
inside S and maps the mentioned points outside S bijectively to points
outside S. Extend the latter partial bijection to a permutation of the
finite union $`(gK\cup hK)\setminus S`$: the unassigned domain and range
have equal finite cardinalities, so choose a bijection between them. Extend
by the identity elsewhere. The resulting p∈G fixes S pointwise and obeys
p(g(a))=h(a) for every a∈K.

Consequently h⁻¹pg fixes K, hence fixes w. Thus p(gw)=hw. Equal patterns
therefore give the same orbit under Fix(S). Choosing one representative for
each realized pattern gives finitely many Fix(S)-orbits inside Gw. This uses
neither infinite A nor a classification of G-orbits by least-support symmetries.

If W has finitely many global orbit representatives w1,…,wm with chosen
finite supports K1,…,Km, take the union of those finite sets of local
representatives. In particular,

```math
|W/\mathrm{Fix}(S)|\le
\sum_{j=1}^{m}(|S|+1)^{|K_j|}
\tag{3}
```

The same proof covers finite and empty atom sets. This strengthens the
countably-infinite-atom hypothesis of the existing Dedekind argument. It does
not extend (3) to an arbitrary subgroup of Sym(A), or to infinite supports.

## 3. Proof of the exact Dedekind equivalence

If W/G is infinite, choose pairwise distinct global orbits O0,O1,….
Each characteristic proposition qn=On is fixed by every permutation. Define
an operation on **every** admitted proposition by

```math
f(q_n)=q_{n+1},\qquad f(p)=p\text{ when }p\notin\{q_n:n<\omega\}
```

It is equivariant, hence empty-supported and admitted at type tt. Its action
on the chosen sequence is injective, and no off-sequence value can enter the
sequence, so f is injective on the whole domain and misses q0. The new orbit
quotient module removes the previously explicit assumption that a separating
sequence of world representatives has already been supplied.

Conversely suppose W/G is finite. For any finite S, §2 makes W/Fix(S)
finite. An S-supported proposition is constant on each of these orbits, so
there are only finitely many such propositions. In fact they are precisely
the unions of these orbits; every such union is S-supported and admitted.

Suppose an admitted injective f misses r. Choose finite supports S for f and
T for r. Equivariance relative to Fix(S) shows inductively that every fⁿ(r)
is supported by S∪T. These iterates are pairwise distinct: an equality
fⁿ(r)=fᵐ(r), n<m, cancels by injectivity to put r in the range of f.
This contradicts the finite S∪T-supported stratum. Thus no such f exists.

The argument has no dependence on the designated evaluation world. In the
already verified nominal semantics, the same conclusion consequently holds
under the actual defined modal box. No object-language quantification over
the external set of orbits is introduced.

## 4. All-type Intensional Choice on atom worlds

This argument works for every finitely supported G-set X as a witness domain,
and therefore for every domain in the typed hierarchy. Let F be an admitted
family with a witness at every world, and let finite S support F.

If A=S, enlarge the support to A. Its pointwise fixer is trivial, so every
witness is fixed by the relevant stabilizer and the checked selector criterion
applies. Assume otherwise and choose a0∉S. Choose an F-witness x0 at a0 and
a finite support K for x0. For every a∈S choose an F-witness xa at a and a
finite support Ka for xa. The set
$`T=S\cup\{a_0\}\cup K\cup\bigcup_{a\in S}K_a`$
is finite and supports F. At w∈S use xw. At w∉S use
x=(a0 w)·x0, where (a0 w) is the swap, interpreted as the identity when
w=a0. This swap fixes S, so covariance of F makes x an F-witness at w.
Its translated support lies inside K∪{a0,w}⊆T∪{w}.

Every permutation fixing T and w therefore fixes the selected witness.
For w∈S the same follows because its chosen witness support is contained
in T. This is exactly the verified stabilizer criterion, including the
essential requirement that the evaluation world be fixed. The criterion
constructs an admitted unique-witness graph, proving IC(W,X).

Apply this to X=Dσ for every admitted type σ. The existing quotation theorem
identifies that semantic selector assertion with the actual ICσ sentence.
It holds at every atom world, hence yields the boxed instance. Together with
the previously checked atom-world Dedekind obstruction, this establishes (2).
No countable reservoir, least-support theorem or full orbit decomposition
is needed.

Still outside this work: the complete all-type IC criterion for general
finite-supported W, nontrivial-action FC/RC failures, larger support ideals,
the full mathematical-core/Frege-infinity interpretation and any database
integration. None is silently included in the new certification scope.

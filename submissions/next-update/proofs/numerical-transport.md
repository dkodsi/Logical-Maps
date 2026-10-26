# Canonical numerical transport already follows from unboxed ND

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi.

## 1. Framework, premises, and recorded inputs

Work in the original finitary pure language of Classicism C, with its fixed
relational types. Put

    nu_sigma := (sigma t)t,
    nu_rho   := (rho t)t.

Write 0_sigma, S_sigma, and N_sigma for Frege zero, successor and natural
numberhood. As in `topics/classicism/background.md`,

    I*_sigma := zero is not a successor on N_sigma,
                and S_sigma is injective on N_sigma;
    I_sigma  := diamond I*_sigma.

Goodsell's recorded argument proves in C that I_sigma implies I*_sigma;
the converse follows by T. It also proves N_sigma n -> box N_sigma n.
Neither assertion uses Countable Boolean Completeness. See
`topics/classicism/writeups/countable-boolean-completeness-implies-necessity-of-arithmetic.md`,
Lemmas 2–6, transcribing Goodsell, *Arithmetic is Necessary*, draft of
5 June 2024. The input's noncollapse is not an assumption that its underlying
counting type is actually infinite, and no external standardness is assumed.

The research note
`research/2026-10-22/notes/relational-coding-recursion-20261022.md`,
Sections 34.1–34.2, defines

    PairInd(Z) := Z(0_sigma,0_rho)
                  and forall u v (Z(u,v) -> Z(S_sigma u,S_rho v));

    J_(sigma,rho)(x,y) := forall Z (PairInd(Z) -> Z(x,y)).

Here Z and J have admitted type nu_sigma nu_rho t. We abbreviate this J
below. Its C-theorems are:

1. J(0_sigma,0_rho), and successor closure of J.
2. J(x,y) implies N_sigma x and N_rho y.
3. J(x,y) iff x=0_sigma and y=0_rho, or there are u,v with
   J(u,v), x=S_sigma u and y=S_rho v.
4. I_sigma implies that every N_sigma-member has exactly one J-mate.
   Every N_rho-member has a J-preimage.
5. Under I_sigma and I_rho, J is a numerical graph bijection preserving
   zero, successor, Sum and Prod. Its current numerical graph is the unique
   zero/successor-preserving functional graph.

For clarity about item 4, existence is immediate by N_sigma-induction.
For uniqueness at zero, the unfolding's successor case contradicts the
source's zero-not-successor theorem. At a successor S_sigma n, unfolding
gives J(u,v) with S_sigma u=S_sigma n. Its source-numberhood clause and
I*_sigma give u=n; induction gives uniqueness of v. This is internal
induction over all admitted numbers. Target injectivity is not used.
The range predicate exists by lambda abstraction, contains target zero
and is successor-closed, so N_rho-induction gives surjectivity.

We use C's Intensionality: necessarily universally coextensive relations
are identical. Optional assumptions are never fed into Logical Equivalence.
All necessitated implications below are first proved as theorems of C.

## 2. Persistence of the canonical graph is a theorem of C

**Lemma 1.** C proves

    forall x y (J(x,y) -> box J(x,y)).

**Proof.** Define the admitted relation

    K := lambda x y . box J(x,y).

J's zero-pair theorem can be necessitated, so K(0_sigma,0_rho).
Necessitate the universally closed C-theorem expressing successor closure
of J. Repeated converse Barcan, or equivalently its pointwise boxed
universal instantiation, gives

    forall u v . box(J(u,v) -> J(S_sigma u,S_rho v)).

K therefore has successor closure by normal modal K. We have proved
PairInd(K) in C. Instantiate J's defining universal quantifier with K:
J(x,y) implies K(x,y), which is the desired box J(x,y). All substitution
steps use lambda beta conversion. No graph identity, BF, ND, Infinity,
or optional noncollapse premise was used. QED.

This is the two-sorted analogue of the recorded persistence proof for N.
In particular it does not rely on enumerating the externally standard
successor pairs.

## 3. Stable source noncollapse gives one explicit transport operation

Define the following pure term, whether or not either noncollapse holds:

    F_(sigma,rho) :=
      lambda n^(nu_sigma) X^(rho t) .
        exists m^(nu_rho) (J_(sigma,rho)(n,m) and m(X)).

Its type is nu_sigma -> nu_rho. Both number types are relational, so no
forbidden individual-output arrow occurs.

**Theorem 2.** C proves

    box I_sigma ->
      forall n (N_sigma n -> J_(sigma,rho)(n,F_(sigma,rho)(n))).

In fact C proves the stronger conclusion for this same term:

    box I_sigma ->
      box forall n (N_sigma n -> J_(sigma,rho)(n,F_(sigma,rho)(n))).

The target's I_rho is unnecessary for this forward transport theorem.

**Proof.** Assume box I_sigma and fix an actual n with N_sigma n. By T,
I_sigma holds, so choose the unique actual m with J(n,m). Lemma 1 gives
box J(n,m). Recorded numberhood persistence gives box N_sigma n.

Necessitate the C-theorem

    I_sigma -> forall x (N_sigma x -> exists! y J(x,y)).

Its pointwise boxed consequence, combined with box I_sigma and
box N_sigma n, gives box exists! y J(n,y). Together with box J(n,m),
this yields

    box [J(n,m) and forall z (J(n,z) -> z=m)].             (1)

The ordinary logical implication

    [J(n,m) and forall z(J(n,z)->z=m)]
      -> forall X [exists z(J(n,z) and z(X)) iff m(X)]

is a theorem with the parameters universally closed. Necessitate it and
instantiate pointwise. Using (1) and the definition of F gives

    box forall X^(rho t) (F_(sigma,rho)(n)(X) iff m(X)).  (2)

Intensionality applied to (2) gives the identity F_(sigma,rho)(n)=m.
Substitute into J(n,m). Generalize over the current n. QED.

The inference to (2) does not exchange forall X and box by BF. The whole
forall-X consequence lies inside the consequent of a necessitated logical
theorem. Likewise the final forall-n is unboxed. The chosen m is local
existential elimination in a proof; no simultaneous choice of witnesses
is made. The operation F was already defined by one pure lambda term.

To obtain the stronger boxed conclusion, abbreviate the displayed unboxed
correctness formula by T_(sigma,rho). The proved C-theorem
box I_sigma -> T_(sigma,rho) can be necessitated, giving
box(box I_sigma -> T_(sigma,rho)). Axiom 4 supplies
box I_sigma -> box box I_sigma, and normal modal K yields
box I_sigma -> box T_(sigma,rho). This boxes the entire universal
correctness assertion for the same already fixed pure F. It neither
necessitates an optional premise nor exchanges a quantifier and box by BF.

The same argument gives, under box I_sigma,

    forall n m [N_sigma n and J(n,m) -> F_(sigma,rho)(n)=m].

Consequently its value identities are individually necessary by NI. The
same necessitation-and-4 argument also gives the boxed universal version
of this conclusion. Neither assertion controls F's arbitrary values away
from the numerical field.

## 4. Unboxed ND is sufficient; C5 is stronger than required

The proved record
`topics/classicism/results/distinctness-necessary-t-implies-modal-five.yaml`
gives propositional ND -> 5, where

    5 := forall p (diamond p -> box diamond p).

At p=I*_sigma, this is exactly I_sigma -> box I_sigma. Therefore:

**Corollary 3.** Over C + ND_t, for every sigma,rho,

    I_sigma ->
      box forall n (N_sigma n -> J_(sigma,rho)(n,F_(sigma,rho)(n))).

By T, this includes the unboxed assertion. In particular ND_t, and hence
all-type ND or C5, implies the proposed
schema

    AT_(sigma,rho) :=
      (I_sigma and I_rho) ->
        exists f^(nu_sigma nu_rho)
          forall n (N_sigma n -> J_(sigma,rho)(n,f(n))).

The proof is stronger than an existential assertion: the same displayed
pure F realizes every instance under the relevant noncollapse. ND was
not necessitated. No Atomicity, Actuality, BC, Plenitude, Functional Choice,
Rigid Comprehension, BF, or external standardness premise enters this proof.

The genuinely local sufficient hypothesis is just I_sigma -> box I_sigma,
or box I_sigma for the conditional theorem. This upper bound does not
establish that AT entails ND, and the argument supplies no separating model
between these principles.

## 5. Canonical inverses, arithmetic preservation, and coherence

Work under ND_t and I_sigma and I_rho. Let F=F_(sigma,rho) and
G=F_(rho,sigma). The two synchronized-successor definitions are converse
relations: interchanging the two arguments sends PairInd relations to
PairInd relations, so C proves J_(sigma,rho)(n,m) iff
J_(rho,sigma)(m,n).

By Corollary 3, J(n,F(n)) for every source number. Since J's values are
target numbers, reverse transport applies, giving
J_(rho,sigma)(F(n),G(F(n))). The converse-relation fact and source
single-valuedness in the reverse direction give

    forall n in N_sigma . G(F(n))=n;
    forall m in N_rho   . F(G(m))=m.

These are pointwise numerical identities. They are not identities of F,G
on their entire ambient number types. In particular arbitrary nonnumbers
have not been quotiented away or assigned canonical values.

Every F preserves zero and successor on source numbers, and Sum and Prod
on numerical tuples, because its current numerical graph is J. Hence the
existing ordinary first-order arithmetic transport by J is now implemented
by admitted operations under ND.

For three noncollapsed bases sigma,rho,tau, under ND_t the operation
F_(rho,tau) composed with F_(sigma,rho) is zero/successor-preserving on
N_sigma, and its values lie in N_tau. Uniqueness of the synchronized
graph therefore yields

    forall n in N_sigma .
      F_(rho,tau)(F_(sigma,rho)(n)) = F_(sigma,tau)(n).

Similarly F_(sigma,sigma)(n)=n for every source number. Thus canonical
transport satisfies identity and composition coherence on the numerical
fields. The proof is internal induction/graph uniqueness, not external
categoricity of standard arithmetic.

More generally suppose an admitted f:nu_sigma -> nu_rho sends zero to
zero and satisfies f(S_sigma n)=S_rho(f(n)) on source numbers. Number
induction makes its numerical values target numbers. The graph

    K(n,m) := N_sigma n and N_rho m and f(n)=m

is PairInd, so J is contained in K. Under I_sigma, totality of J therefore
makes f agree with F_(sigma,rho) on every source number. Accordingly G is
a pointwise numerical inverse for **every structure-preserving f** when
both bases are noncollapsed. No Functionality is used to identify f and F
as entire operation entities.

## 6. Limits and next exact question

Canonical arithmetic transport is not an established new strengthening
above ND: this note proves it follows already from ND_t. Its converse and
strictness below ND remain unclassified here. This is relevant to a proposed
presentation-independence programme: merely realizing the canonical
zero/successor comparison cannot force a stronger principle than ND.

An **arbitrary** admitted permutation of N_sigma need not preserve zero or
successor. The uniqueness argument of Section 5 therefore does not apply.
Its current bijectivity supplies unique preimages now, but not the stable
unique-preimage premise (1): new future numbers might enter its fibres.
Applying pooling to its inverse graph without addressing that issue would
illicitly promote current coextension to intensional identity.

Thus the canonical-graph argument alone does not prove that ND suffices
for inverses of arbitrary numerical permutations. A suitable stable
inverse-fibre premise gives the same pooling proof. One sufficient package
is ND together with BF at the two number types, hence in particular C5:
N-membership is persistent in C and its negation is persistent under 5;
identity and disequality are settled under NI and ND. Boolean combinations
of these atoms are settled, and BF at the two number types extends this
to the quantifiers in the guarded bijection assertion. That assertion is
therefore necessary, so every current target number has a stable unique
preimage; pooling supplies an inverse. No stronger lower-bound conclusion
is claimed. A potentially sharper argument using least preimages and
bounded arithmetic requires its own proof and is not an input here.

The principal new theorem in this note concerns canonical arithmetic maps
and maps preserving their arithmetic structure.

Nor does the pointwise coherent transport above establish transport of
arbitrary predicates, properties of arbitrary higher type, or an actual
inverse on all entities of a number type. Those are separate formulations
which can have different strengths.

**Stopping point.** The explicit positive theorem under box I_sigma,
including uniform boxed correctness of the same term, its ND_t corollary,
canonical numerical inverses, and pointwise composition
coherence are proved above. No ND-converse, separating model, arbitrary
permutation inverse theorem, database entry, or Lean claim is supplied.

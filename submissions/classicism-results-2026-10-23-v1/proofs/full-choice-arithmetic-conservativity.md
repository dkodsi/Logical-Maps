# Full Choice preserves ordinary arithmetic over boxed Plenitude

Ordinary proof using an external interpretation theorem; no full Lean certificate. This is the existing Frege-note §36 argument, with its application to the two infinity packages made explicit. The argument and its separate AI review do not establish historical novelty or human verification.

The mathematical sections below are retained from the 23 October 2026 detailed audit by OpenAI Codex, prompted by Daniel Kodsi. [Provenance and exact review scope](../evidence/full-choice-arithmetic-review.json) records the original source hashes. Process history has been omitted; the original proof is also retained in [Frege infinity, §§35–36](../source/research/2026-10-22/notes/frege-infinity-20261022-1726.md), and its quotient construction is in [relational coding, §§29, 32.1, 33](../source/research/2026-10-22/notes/relational-coding-recursion-20261022.md).

Here I_e is the Frege notes’ weak arithmetic noncollapse condition: possibly, zero is not a successor and successor is injective on the Frege numbers counted at e. This is distinct from the quantified Infinity axiom on the individual domain.

## 1. Exact statement

Fix finitary relational Classicism C: types e,t, and alpha -> beta only when
beta is not e. All type indices in schemata are external. Let

  T  = C + full boxed Plenitude + quantified Infinity_e + quantified Infinity_t,
  CC = C + full boxed Functional Choice + the same two infinity axioms.

Let A be an ordinary first-order arithmetic sentence and A^sigma its fixed
Frege interpretation at counting type sigma. Let I_sigma be the established
numerical noncollapse assertion in the Frege notes. Then

  CC proves A^e  iff  T proves A^e  iff  C + I_e proves A^e.                 (1)

More generally, for any fixed admitted sigma and rho, the common arithmetic
theory is also the arithmetic theory of

  C + boxed Functional Choice + {boxed Infinity_tau : tau admitted},

read at rho, and of C+I_sigma read at sigma. Each proof uses only finitely many
instances of these external schemata. We do not assert conservation for
higher-order, modal, parameterized, or world-dependent sentences.

The previously reviewed numerical-output selection lemma is not being used
as a surrogate for (1). Here arbitrary relational output types are covered.

## 2. Exact source dependency

Colin McLarty, Interpreting set theory in higher order arithmetic,
arXiv:1207.6357v5, 15 February 2013:
[McLarty, primary manuscript, version 5](https://arxiv.org/pdf/1207.6357v5)

Section 2 (p.2) specifies Z_m using full finite-order comprehension and
extensionality, with second-order induction. Sections 3--5 (pp.3--6), especially
Theorems 3.2, 3.4, 4.3 and 5.3, give an interpretation of ZFG[n+] plus V=L
in Z_(n+2). Its set theory has Replacement and global well-ordering and
supplies the requisite finite iterates of powerset. Section 3.1 and Theorem
5.2 identify the interpreted natural numbers through descending-sequence
trees; this fixes the number domain rather than merely equating consistency
strength. The constructible restriction retains these numbers.

This audit read the primary manuscript's definitions and arguments. It uses
its interpretation theorem as an external mathematical theorem; it is not
a complete independent reproof of the underlying Simpson constructibility
results. No Sochor theorem, unseen Yakubovich proof, or mere equiconsistency
claim is substituted for this dependency. The theorem is source-based, not
a source-free consequence of the numerical selection lemma.

## 3. Recover the arithmetic input without Choice

The existing current quotient construction (relational-coding-recursion-
20261022.md, sections 29, 32.1, 33.1) applies over C+I_sigma. At the current
point its individual base B is N_sigma, with inherited Peano operations
represented by graphs. It supplies an extensional, two-valued relational
Henkin hierarchy E with full comprehension at every fixed finite type.
Induction holds for every admitted predicate, including predicates defined
with parameters from higher types. Neither ambient full function spaces nor
Choice is assumed in this construction.

For each external m, take the unary powerset chain over B in E. Its sorts
are B, admitted extensional properties of B, properties of those properties,
and so on for m orders. Comprehension in this many-sorted language is a
special case of comprehension in E. Quotient equality gives extensionality.
Induction on B with arbitrary fixed higher-type parameters gives the stated
induction axiom and its comprehension-derived instances. Hence E interprets
the exact Z_m used in section 2 of the external source. Its arithmetic is
the original Frege arithmetic, not the external standard natural numbers.

For any required external finite n, compose with the source interpretation
to obtain a set-theoretic interpretation S satisfying ZFG[n+] and V=L.
The number-preservation point needs more than the word 'interpretation':
the canonical tree for omega consists of descending finite sequences of
elements of B. Its immediate subtrees are indexed by b in B, each coding
the initial segment below b. Thus its elements, modulo tree equality, are
precisely those initial-segment codes. Internal induction and initial-segment
comparison give equality of two such codes exactly when their indices are
equal, and membership exactly when the first index is less than the second.
Empty segment and adjoining the endpoint give zero and successor. Recursion
and induction give addition and multiplication. These operations, and all
their arguments, survive the constructible restriction. Consequently S's
omega is definably isomorphic to B for first-order arithmetic.

This reasoning includes internally finite but externally nonstandard
segments. It never appeals to external categoricity, standardness, or an
external well-order of a Henkin domain. A model with a false arithmetic
sentence remains a counterinterpretation after this step.

## 4. Build only the fragment required by a finite proof

Let pi be a proposed proof of A^rho in C + boxed Functional Choice + all-type
boxed Infinity. Expand its defined terms and include the finite H proofs
certifying the Logical Equivalence instances used by pi. Include the finite
auxiliary type list needed for the arithmetic bridge below. This produces
a finite set of types closed under subtypes. The source interpretation can
be chosen high enough for this particular list; there is no demand for one
set containing all finite types.

For clarity, finite powerset bounds suffice. Put B_0=omega and B_(k+1)=P(B_k).
Code individuals in B_0 and propositions in B_1. If two carriers inject into
B_m, then Kuratowski pairs of their codes belong to B_(m+2), and function
graphs belong to B_(m+3). The entire function carrier is a definable subset
of B_(m+3); Separation forms it. Singleton lifting aligns lower bounds.
Thus the recurrence

  b(e)=0, b(t)=1, b(alpha -> beta)=max(b(alpha),b(beta))+3

is a sufficient bound on the codes of carrier elements. Take n larger than
the finitely many bounds, with additional finite room for arithmetic graphs,
logical operations and auxiliary interpretations. Products, images and
decoding use Pairing, Union, Separation and Replacement. No claim of an
optimal bound, uniform finite order, or internally infinite type iteration
is needed.

Inside S use D_e=omega, world domain W=omega, D_t=P(W), and full INTERNAL
function sets D_(alpha -> beta) for the required types. 'Full internal'
means the sets S supplies, not all functions in the external metatheory.
At w, p is true exactly when w belongs to p. Connectives and quantifiers
act pointwise, and identity is set identity, represented by W or empty set.
The defined box (identity with the true proposition) is universal necessity
over W. All admitted domains are constant and nonempty.

Term interpretation is closed under lambda abstraction because Separation
and Replacement form its graph and the corresponding internal full function
carrier contains it. H is valid at each world. If an H proof certifies two
formula bodies as equivalent, their interpretations agree at every world
and every assignment, so their lambda denotations agree as functions into
P(W). This checks Logical Equivalence at its actual side condition. A proof
from optional premises is never treated as an H theorem. The finite list of
H certificates prevents a hidden appeal to additional unbounded types.

At a fixed w, a serial U gives for each x a nonempty SET of candidates y.
The global order of S supplies a least candidate; Replacement gives the
selecting function. That function belongs to D_(alpha -> beta), so it is
an operation at the original admitted type. Its values are full objects y,
not only their extensions at w. Since this works at every w, it validates
the boxed Functional Choice instance. No uniform choice of a selector over
all worlds is being assumed. The output restriction beta!=e is respected.

## 5. Frege arithmetic and quantified infinity in the new interpretation

For each required counting type tau define an injection j_tau from omega
into D_tau. At e use identity as a relation; at t use n |-> {n}; at an
arrow use constant functions with the recursively given output. Domain
nonemptiness makes the latter injection injective. These graphs are present
in the appropriate internal full relation domains.

For n in omega define q_tau(n) to be the intension whose value at X,w says
that {x in D_tau : X(x) is true at w} is in bijection with [0,n). Quantify
over represented bijection graphs. At each required finite rank this is a
definable set and belongs to D_(nu_tau), where nu_tau=(tau t)t. The graph of
n |-> q_tau(n) is represented by an admitted original operation e -> nu_tau;
an individual-valued operation is not needed.

Deleting the element corresponding to the last point of [0,n+1), and the
converse adjunction, give q_tau(0)=0_tau and
q_tau(n+1)=Suc_tau(q_tau(n)). These equalities hold at every X,w, hence are
equalities of complete intensions. Internal induction on n, with the
relevant set-theoretic parameters, proves that q_tau(n) is a Frege number
at every world. Conversely, the represented predicate

  P(z) iff there exists n in D_e with z=q_tau(n)

contains zero and is successor-closed. Frege induction therefore places
every internal Frege number in its image. This is an admitted predicate,
not an external standard cut.

The property j_tau[[0,n)] witnesses that q_tau(n) counts n elements. If
q_tau(n)=q_tau(m), compose the witnessing bijections to obtain a bijection
between the two initial segments. Internal finite pigeonhole yields n=m.
It follows that q_tau is a bijection onto the whole Frege number domain,
including its nonstandard part. It respects zero, successor and, by their
recursive graph characterizations, addition and multiplication. Every
ordinary arithmetic sentence is thus preserved in both directions.

Finally no initial segment [0,n) can biject with the whole D_tau: otherwise
j_tau restricted to the first n+1 numbers gives an injection of n+1 into n.
Since q_tau exhausts the Frege numbers, this proves the quantified Infinity
axiom, not merely the list of standard finite lower bounds. The proof works
at every world, supplying every required boxed Infinity instance as well.

## 6. Closing the proof and its significance

There are two equivalent presentations of the conclusion. For countermodels,
start with a C+I_sigma interpretation falsifying A^sigma, then use sections
3--5 for the finite type list of any alleged strong-theory proof of A^rho.
The resulting internal S5 interpretation validates that proof's axioms but
falsifies its conclusion, a contradiction. The rank may depend on the proof.

Alternatively, avoid any extra appeal to full-semantics completeness:
the current quotient, finite-order source interpretation and finite S5
interpretation are definable interpretations. Verify the finitely many
axioms/rules of the given derivation through their composition. The round
trip identifies its arithmetic conclusion with A^sigma over C+I_sigma.
This syntactic reading also shows why finitary proof conservativity, rather
than only equiconsistency, follows.

The converse inclusion follows from Infinity_rho implying I_rho and the
previously proved independence of the counting base (coding note section
33). In particular CC is intermediate between C+I_e and the strongest
boxed-Choice/all-type-boxed-Infinity theory just treated. Hence CC has the
arithmetic theory of C+I_e. The reviewed section 33 theorem places T at the
same arithmetic theory. This proves (1).

For the abductive paper the consequence is specific: full arbitrary Choice
over T has no additional ordinary first-order arithmetic consequences.
Its further case must concern selection, representation, modal structure,
or other non-arithmetical merits. This is not a proof that Choice follows
from Plenitude, that their higher-order theories coincide, or that one is
abductively superior. The existing model separations remain relevant.

The proof also provides an exact interpretation-theoretic characterization:
the common arithmetic theory is that of Z_<omega, the union of all fixed
finite-order extensional arithmetic theories from the source. One inclusion
is the current quotient. For the other, apply the finite internal S5 model
construction to a C+I proof and interpret its finite set theory in a high
enough Z_m. This corollary is already stated in the Frege note, section 36.7;
it is corroborated here, not claimed as newly discovered.

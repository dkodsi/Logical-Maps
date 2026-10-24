# Strong Possibility and atomic finite extensional worlds

Original mathematical arguments, 22 October 2026. The fixed background is Classicism C in the database's relational type system. The arguments below have been cross-checked by research agents, not by a named human; no Lean verification is claimed. The direct source for the new arguments is `misc`. Literature novelty is not asserted.

The construction and its consequences have passed independent mathematical audits by additional agents. These are ordinary mathematical research notes, separate from the proved database records; no human or proof-assistant certification is claimed.

## 1. Exact targets and conventions

Write M for pure Maximalist Classicism, and S for pure Strong Possibility. Write F for the Fregean Axiom and E_n for the pure sentence saying that there are exactly n individuals, where n is a positive external integer. Put A_n := F ∧ E_n.

The distinctness-preserving necessity is

    □ne p := ∃q [q ∧ □(◇q → p)],
    ◇ne p := ¬□ne¬p.

The database's S has, for each closed pure P with M+P consistent, the axiom ◇ne P. Its reference theory remains the original finitary C. A signature Σ is admitted here only with at least one relational constant, as in the database.

The principal conclusions are:

1. S entails Atom_t(A_n) for every positive n.
2. S is inconsistent with Maximalism for any admitted signature Σ, in every interpretation of its constants.
3. S refutes the Barcan Formula at every admitted type.
4. S refutes Functionality at every admitted pair of input and relational output types.
5. S refutes Strong Leibniz at every relational type.

These conclusions do not assert inconsistency of S itself or of original finitary M.

## 2. The consistency construction

Here is the construction supplying M + Atom_t(A_n), simultaneously for every positive n. Its background is the action-model and coalesced-root semantics of Bacon and Dorr, *Classicism*, draft 16 May 2023, §3.5 and Appendix E, pp. 58–61 and 80–83. The restricted profile domains below are an additional construction, not a theorem attributed to that source.

Take a set of component C-models sufficient to witness every C-consistent closed pure sentence. Include all their objects and arrows. Add a root o with one individual. For every component object V and individual a at V add an arrow h_(V,a):o→V. Define composition by k h_(V,a)=h_(V',ka).

For each type σ, a profile is the family of denotations of one pure σ-term T(z), with z its only possible free variable and of type e, evaluated at every (V,a). Identify terms with the same family. The profile sets B_σ are countable. At a relational type σ=τ₁…τₖt put

    D_σ(o) = P(D_τ₁(o) × … × D_τₖ(o)) × B_σ.

For k=0 this is 2×B_t. The first coordinate is the arbitrary actual extension; the second gives transport along h_(V,a). Application takes fibers in the first coordinate and substitutes profiles in the second. The sole individual's profile is z. Logical constants have their usual pure profiles. Quantifiers range over the root domains at o and over the unchanged component domains at their objects.

Every term with root parameters has a profile: substitute a pure one-variable profile for each of its finitely many parameters. Abstraction has its actual extension as its first coordinate and the substituted abstraction as its profile. Both are admitted. Beta follows from the definitions; eta follows from equality of the actual extensions and componentwise eta. Identity is literal equality at the root. The truth and quantifier clauses validate H. H-equivalent abstractions agree in their root extension and in all component profiles, so Logical Equivalence holds with its original theoremhood restriction. Thus the structure is a model of C.

Every C-consistent pure sentence holds at a component reached from o, so the root satisfies M.

At a component satisfying A_n, the local typed structure is the full extensional structure on n individuals. Fregean extensionality gives two truth values; induction on types gives finite domains, and finite comprehension realizes every extension at each type. Every individual permutation extends to an automorphism. Consequently any pure proposition term T(z) has the same truth value at every such pointed structure (V,a).

For a fixed pure T(z), let its common truth value at pointed A_n-objects be ε. If ε is false, T(a)∧A_n is false at every pointed component object; if ε is true, its symmetric difference with A_n is false at every such object. Apply this observation at every descendant k:V→V′, with the transported individual ka. Proposition entities in the action models are separated by these future truth evaluations, so the first conjunction is literally bottom at each component, or literally A_n, respectively. Thus this is equality of full component entities, not merely agreement of actual truth at A_n-objects. For a root proposition p, therefore, the profile of p∧A_n is either uniformly bottom or the profile of A_n. Its actual coordinate is false: the root has infinitely many propositions, so F fails there. Hence p∧A_n equals either bottom or A_n. The proposition A_n is nonzero, since a full n-individual extensional component realizes it. Thus A_n is an atom at the root.

The model also has a freely chosen actual truth coordinate and an actual-world atom. It is not claimed to satisfy S.

## 3. Universal equality reflection

**Lemma.** If U is a universally quantified formula whose matrix is a finite Boolean combination of typed term identities, C proves

    ◇ne U → U.

To prove the contrapositive, suppose U fails and choose a countertuple. Put its quantifier-free counterexample in disjunctive normal form and take a true finite conjunction of identity or disequality literals witnessing that failure. True identities are □-necessary by NI. A true disequality a≠b is □ne-necessary: use q=(a≠b), and note that NI proves □(◇(a≠b)→a≠b). The normality and finite-conjunction closure of □ne therefore make the counterexample □ne-necessary. It follows that □ne¬U.

Algebraic entailment is an identity of Boolean terms. The standard Boolean-algebra characterization

    Atom(a) ↔ a≠⊥ ∧ ∀p [a≤p ∨ a≤¬p]

therefore belongs to this fragment. Section 2 makes M+Atom(A_n) consistent. S supplies ◇ne Atom(A_n); the lemma gives Atom(A_n).

No Infinity assumption or Barcan Formula is used.

## 4. Obstruction to every signature expansion

Choose any relational constant c:τ in Σ. Both

    A_n ∧ (c=⊤_τ),
    A_n ∧ (c≠⊤_τ)

are C(Σ)-consistent. Use the full extensional structure on n individuals and interpret c respectively as top and bottom. Other constants can be interpreted arbitrarily at their types.

Signature Maximalism makes both propositions possible, hence nonzero. They are disjoint parts of A_n. Thus signature Maximalism entails ¬Atom(A_n).

Section 3 gives the opposite consequence from pure S. Therefore

    C + S + Max(C(Σ)) is inconsistent

for every admitted Σ. In particular, a pure S-model cannot acquire a signature-Maximalist expansion merely by choosing better denotations for the constants.

Since signature Strong Possibility entails signature Maximalism, the two Strong Possibility principles cannot hold together. This is stronger than the elementary observation that a fixed arbitrary interpretation of a fresh constant need not preserve Maximalism. It does not by itself decide whether either Strong Possibility principle is separately consistent.

## 5. Failure of Barcan at every type

**Atom-persistence lemma.** For every relational type τ, C proves

    BF_τ ∧ Atom_τ(a) → □ne Atom_τ(a).

By the atom characterization, for every p the disjunction a≤p ∨ a≤¬p holds. Its disjuncts are positive identities, so NI gives its ordinary necessity. BF_τ yields

    □∀p [a≤p ∨ a≤¬p].

Also a≠⊥ is □ne-necessary by the disequality argument in Section 3. Ordinary necessity implies □ne-necessity, and normality combines the two clauses into □ne Atom(a).

Apply this at τ=t and a=A_1. There is a direct witness for consistency of M+¬Atom(A_1): take the ordinary full coalesced Maximalist root with two separately selectable copies of the finite one-individual extensional component. The proposition selecting one copy cuts A_1 into two nonzero parts. This witness does not require a signature-Maximalist construction. Thus S entails ◇ne¬Atom(A_1). But S already entails Atom(A_1), so BF_t would give its □ne-necessity, a contradiction. Therefore S entails ¬BF_t.

For any relational σ=ρ₁…ρₖt, propositions are a split retract of σ in C. Choose arguments a₁,…,aₖ and put

    c(p) := λx₁…xₖ.p,
    r(X) := X[a₁,…,aₖ].

C proves r(c(p))=p. Given ∀p□Pp, apply BF_σ to Q(X):=P(r(X)); then instantiate the resulting boxed universal formula at c(p). This proves BF_t. The empty tuple is the identity retract. Therefore S refutes BF_σ for every relational σ.

The remaining type is e. The recorded S→E_1 argument uses the consistency of M+E_1 and the □ne-persistence of an actual inequality. Pure Maximalism also implies ◇E_2. Choose the actual sole individual a. NI gives ∀x□(x=a); BF_e would give □∀x(x=a), contradicting ◇E_2. Thus S refutes BF_e as well.

## 6. Failure of Functionality at every type pair

Fix an input type σ and relational output type τ. Suppose Functionality holds at σ→τ. Given ∀x□Px, the operations

    f(x) := ⊤_τ,
    g(x) := λȳ.Px

have identical values at every actual input. Functionality makes f=g. Necessary coextension of identical operations, followed by instantiation of the inhabited output-argument tuple, gives □∀xPx. Thus this single Functionality instance implies BF_σ.

Section 5 therefore refutes every such instance under S. The failure concerns equality of operation values, not merely coextension of predicates.

## 7. Strong Leibniz fails at every relational type

Pure Maximalism rules out every closed pure proposition term W as a strong world. If W≠⊥ is C-consistent, attach two selectable copies of a model witnessing it to an ordinary full coalesced root. The two copies split W, so C+(W≠⊥∧¬Atom(W)) is consistent. Maximalism therefore makes that conjunction possible. A strong W would necessarily decide every proposition and thus be an atom wherever nonzero, contradicting that possibility. If W≠⊥ is C-inconsistent, W is bottom and cannot be strong in the first place.

In particular A_1 cannot be a strong world in M. But S makes A_1 an atom. Strong Leibniz at t would supply a nonzero strong world below A_1; atomhood makes it identical to A_1, contradiction. Hence S refutes SL_t.

For completeness, SL_σ implies SL_t in C for every relational σ. Given a nonzero proposition p, apply SL_σ to the constant relation λx̄.p. If W is the supplied strong world, let q:=∃x̄.W[x̄]. Then q is nonzero and q≤p. For any proposition r, W≤λx̄.r iff q≤r, by the logical quantifier laws under the defining box. The necessary deciding property of W therefore transfers to q. So q is a strong world proposition. This proves the reduction and hence the failure of every relational SL instance under S.

## 8. Provenance and scope

- The definition of S and the recorded monism argument are in `topics/classicism/principles/strong-possibility-r.yaml` and the corresponding incompatibility record with individual Infinity.
- Action-model soundness and coalesced sums are the source background for Section 2. The profile restriction and its closure proof are new arguments here.
- Signature-Maximalist consistency is an existing source-backed construction; no consistency of Strong Possibility is assumed.
- The profile construction and the reflection, signature splitting, Barcan and Functionality consequences have passed independent agent audits. The all-descendants argument in Section 2 states explicitly the identity step highlighted by those audits. They remain ordinary mathematical arguments, not human certification or proof-assistant verification.


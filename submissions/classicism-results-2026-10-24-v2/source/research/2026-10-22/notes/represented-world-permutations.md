# Represented world permutations and internal homogeneity

Research theorem, 22 October 2026. Ordinary mathematics in the fixed relational type system of C; no database edits or formal-verification claim. The finite transposition construction is already recorded in `topics/classicism/writeups/c5-and-atomicity-imply-no-pure-contingency.md`, following the Goodsell–Yli-Vakkuri theorem and Dorr's 23 September 2026 sketch. The present extension to all represented permutations, and its explicit Henkin-domain qualification, are research additions (`misc`).

## 1. Precise statement

Assume C5 + Atomicity_t, equivalently boxed Plenitude. Let W be the rigid property of propositional atoms. A represented permutation of worlds is a rigid binary relation P of type ttt, supported on W times W, which is a total functional bijection there. Its inverse is the converse graph P^op. No function type ending in e is introduced.

Every such P induces, canonically and recursively, bijections Phi_sigma of every original type sigma. They fix individuals, preserve application and identity, fix every pure logical constant, and preserve quantification. At type t they carry an atom w to the unique atom v with P(w,v). The construction respects identity and composition of represented world permutations, and its action is faithful.

For every original pure formula A with parameters a, the exact truth-transport equation is

    w <= A(a)  iff  v <= A(Phi(a)), whenever P(w,v).

Thus the theorem concerns the unpointed logical structure and transports the truth point. It does not say that a nontrivial permutation preserves actual truth. It also does not assert that an arbitrary external permutation preserves a Henkin model's admitted domains: the graph P must be represented.

No Choice principle is used.

## 2. The propositional automorphism

Define the allowed term of type tt

    F_P(p) := exists u v . W(u) and W(v) and P(u,v)
                            and u<=p and v.

The occurrence of v at the end is ordinary propositional evaluation, not an equality test. Let G=F_(P^op). The statement that P is a rigid supported permutation is necessary under the assumptions: rigidity is necessary, support is an identity/order condition, and its first-order functionality/surjectivity conditions are built from bivalent graph values and identity, with BF collecting the quantifiers.

For atoms u,v with P(u,v),

    v <= F_P(p) iff u <= p.                                      (1)

Indeed, at a world at which v is true, it is the unique true atom. The displayed existential can therefore use only v as its output atom, and the unique P-preimage is u. All graph and order facts involved are necessary. The forward and reverse implications lift to entailment by the same rigidity-and-Intensionality argument used in the recorded transposition proof. Equivalently, (1) is the basic atom-world graph correspondence from `rigidity-actualization.md` section 14.

Atomicity now gives G(F_P(p))=p and F_P(G(p))=p: by (1) both sides have the same atoms below them. The same atom test shows that F_P fixes top and bottom and preserves negation and conjunction. Hence it is a Boolean algebra automorphism.

It also commutes with every typed universal quantifier:

    F_P(forall x^sigma . Qx) = forall x^sigma . F_P(Qx).           (2)

For an atom v with P-preimage u, being below the left side means u<=forall x Qx, equivalently forall x(u<=Qx), using BF_sigma and CBF. By (1) this means forall x(v<=F_P(Qx)), equivalently v<=forall x F_P(Qx). Atomicity proves the identity. This is valid for the admitted Henkin quantifier domain; it does not require external fullness.

Every identity proposition is top or bottom under C5, so F_P(x=y)=(x=y). Necessity is definable from equality and top, and is therefore preserved too. Replacing P by P^op proves the same facts for G.

## 3. Conjugation through all original types

Define simultaneous inverse transformations Phi_sigma and Psi_sigma. At e they are metalinguistic identity substitution, not terms of forbidden type ee. At t let Phi_t=F_P and Psi_t=G. For an allowed type sigma tau define

    Phi_(sigma tau)(X) := lambda y . Phi_tau(X(Psi_sigma(y))),
    Psi_(sigma tau)(X) := lambda y . Psi_tau(X(Phi_sigma(y))).

When sigma=e, the identity substitution simply leaves y unchanged. Every displayed lambda term that is actually formed has relational output, hence an allowed type. Induction on types, using the inverse identities at lower types, gives

    Psi_sigma(Phi_sigma(x))=x,
    Phi_sigma(Psi_sigma(x))=x,
    Phi_tau(Xx)=Phi_(sigma tau)(X)(Phi_sigma(x)).                 (3)

Passing these pointwise calculations under lambda is legitimate: the permutation hypothesis is necessary, BF supplies necessary universal closure, and Modalized Functionality/Intensionality supplies identity. No equivalence under an optional unboxed hypothesis is silently used as Logical Equivalence.

Equations (2) and (3), preservation of identity, and bijectivity show that the conjugation fixes each connective, each identity constant, and each typed quantifier constant. Induction on pure terms therefore gives

    Phi_tau(A(a)) = A(Phi(a)).                                  (4)

Together with (1), this proves the truth-transport equation in section 1. It is precisely the arbitrary-permutation extension of the recorded transposition argument.

If P and Q are represented permutations, their relational composition is represented by core comprehension. Equation (1) gives F_(Q o P)=F_Q o F_P; structural induction gives the corresponding composition identity at every type. Identity graphs induce identity transformations. Faithfulness holds already at type t because each atom is sent to its P-image.

The supported hereditary rigid core over e and the Boolean endpoints is fixed pointwise. Individuals and top/bottom are fixed. Inductively a core relation has fixed core arguments and endpoint values there; its support is false off those arguments. Bijection and the induction hypothesis preserve core membership, so conjugation fixes the whole relation by Intensionality. This is the original mathematical core, not the expanded core whose base sorts include arbitrary worlds or propositions.

## 4. Agreement with the Gallin-style representation

Use the inverse j_sigma,k_sigma maps of `rigidity-actualization.md` section 14. On the explicit-world target, act identically on e and Boolean truth, by P on the world sort, and by conjugation at each admitted relation type. The target core's comprehension makes every such transformed relation available. The target action L satisfies

    j_sigma(Phi_sigma(x)) = L_(T(sigma))(j_sigma(x)),
    Phi_sigma = k_sigma o L_(T(sigma)) o j_sigma.

At propositions this is (1): a world predicate is precomposed with the inverse world permutation. The higher-type identities follow from application preservation and supported extensionality. Thus the direct conjugation and the explicit-world construction agree; neither presupposes externally full function spaces.

## 5. Internal finite homogeneity and the parameter obstruction

For distinct atoms a,b the transposition graph

    P(u,v) := W(u) and W(v) and
      ((u=a and v=b) or (u=b and v=a)
       or (u!=a and u!=b and v=u))

is rigid, supported, and a represented permutation. It uses comprehension only. Every finite permutation of named atoms is similarly represented; every finite partial bijection between distinct atom tuples extends to one, by closing the finitely many paths in its finite directed graph. Consequently the atom-world structure is internally finitely homogeneous over the original hereditary mathematical core.

For finitely many propositional parameters p_1,...,p_n, a transposition of atoms with the same truth values on those parameters fixes all the p_i. It fixes every original hereditary-core parameter as well. Equation (4) therefore proves that a pure formula with precisely these permitted parameters cannot split a Boolean cell of the p_i. This is the theorem already proved in `rigidity-actualization.md` section 20, and it applies to EVERY C+boxed-Plenitude Henkin model, not merely full Gallin models.

In particular, a pure term defining an atom selector from these parameters exists exactly when all their nonzero Boolean cells are atoms. Under world Infinity no finite tuple of propositions plus original-core parameters can define such a selector, even though boxed Functional Choice supplies an atom selector as a higher-type entity.

The conclusion is term definability, not definable closure relative to the designated actual truth predicate. The actual atom is uniquely described by W(w) and w without parameters, but that pointed description is transported to a different world by a transposition. There is no contradiction.

For comparison, a pure-structure automorphism fixes every closed pure proposition term. Therefore it cannot interchange two distinct atoms that happen to be denoted by distinct closed pure terms, such as the finite-extensional propositions A_n in the restricted-profile Maximalist construction or under the researched Strong Possibility consequence. This comparison must be stated conditionally: pure Maximalism alone is not asserted here to make every A_n an atom. Under C5+Atomicity, closed pure propositions are top or bottom, so a contingent atom can never be closed-pure-term denotable.

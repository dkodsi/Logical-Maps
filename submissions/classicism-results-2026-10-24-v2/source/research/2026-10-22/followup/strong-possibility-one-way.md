# Strong Possibility: the one-way arithmetic frontier

22 October 2026. Ordinary mathematical deductions by OpenAI Codex; direct source: misc, this note. Self-checked, not independently checked or formalized. The original finitary C, its relational types, and pure Max remain fixed. No database or Lean changes.

## Target and status

The target remains Con(Max+G#+D(not G#)), equivalently Con(Max+U_G+D(not G#)), with the true Pi^0_2 sentence G independent of Max constructed in [the previous follow-up](strong-possibility.md). Write H=Box_ne and D=Diamond_ne. Separate consistency of the two added axioms is not a joint-consistency proof.

This continuation first identifies a structural obstruction to the previous construction: RETURN MAPS, not just the full root-extension domains, prevent arithmetic variation. A successful replacement must use genuinely one-way embeddings or a different mechanism. The lemmas below do not themselves construct the required embedding.

## 1. Logical homomorphisms preserve the numerical embedding

Use the many-sorted algebraic signature containing every pure term operation, including quantifier-valued operations but not actual truth. Let f:A→B be a homomorphism between the reducts of two genuine C-models whose evaluation points satisfy I=I_e. Max models meet this assumption.

Then f maps actual numbers to actual numbers, is injective on those numbers, fixes each standard numeral, and preserves and reflects their atomic arithmetic facts.

**Numberhood.** C proves N(n)→Box N(n), so actual numberhood is the literal equation N(n)=top. The homomorphism preserves this equation. Consequently f(n) is an actual number in B whenever n is one in A.

**Numerical injection.** If actual numbers n,m of A differ, the recorded numerical distinctness lemma gives the literal Boolean inequality

    I_A ≤ neq_A(n,m).

If f(n)=f(m), its image would give I_B≤bottom. But I_B is actually true and therefore nonzero. Hence f(n) differs from f(m). No injectivity of f on other entities was assumed.

**Atomic arithmetic.** Zero and successor are pure operations. For Sum and Prod, the recorded conditional rigidity lemma says that, on numerical arguments, the true or false atomic value is necessitated conditional on I. Equivalently I lies below that value or its Boolean complement. The homomorphism preserves these inequalities, and I is true at B, so the same truth value holds there. Equality and inequality follow from numerical injectivity. Thus the induced map is an embedding of the ordinary first-order arithmetic reducts, with Sum and Prod interpreted relationally.

Inputs: `topics/classicism/writeups/countable-boolean-completeness-implies-necessity-of-arithmetic.md`, Lemmas 3, 6 and 7. These lemmas use HK, not the later Countable Boolean Completeness step. The previous follow-up records the partial primary-source check and the full-PDF access limitation.

## 2. A retract forces arithmetic isomorphism

Suppose h:A→B and j:B→A are such logical homomorphisms, and jh is the identity on A. Then their restrictions to the actual numerical domains are inverse isomorphisms.

For any number b of B, j(b) is a number of A, and h(j(b)) is a number of B. We have

    j(h(j(b))) = j(b).

Section 1 makes j injective on B's actual numbers, so h(j(b))=b. Therefore h is surjective on B's numerical domain; its injectivity and preservation of all atomic arithmetic were already proved. First-order induction on formulas now gives agreement on EVERY arithmetic sentence, even if both number fields are externally nonstandard.

This applies directly to the return pairs in the previous supported-root construction. All distinguished roots there have the same first-order arithmetic theory as the source. Adding nonstandard roots while retaining genuine return maps cannot produce a root satisfying not G when the source satisfies G.

If the possibility-fixed root indicator is also retained, the construction settles every closed arithmetic sentence under H: all distinguished roots agree, so the root indicator witnesses the true side. Since Max+G and Max+not G are both consistent, SP excludes both H(G#) and H(not G#). Thus NO model with these retract and indicator features can satisfy SP, regardless of whether its arithmetic is standard. This strengthens the earlier standard-root obstruction; it is not an inconsistency proof for SP.

There is a second restriction. Any logical homomorphism from a C+I point to a standard-arithmetic C+I point forces the source number field to be standard: a source number maps to some standard numeral k, and injection identifies it with the source's own k. Thus a nonstandard root cannot have such a standard C+I component exit. A construction intended to admit nonstandard roots must audit its component exits as well as its root-to-root maps.

## 3. One-way embeddings are enough, and give an exact local criterion

Let M be a genuine Max model and P a closed pure sentence. Then

    M satisfies D(P)
      iff there are a genuine Max+P model N
          and an embedding Alg(M)→Alg(N).

The embedding omits actual truth but preserves ALL pure term operations. This is a local version of the common-embedding analysis in `../notes/reflection-universal-core-20261022.md`, §6; it should not be confused with an elementary embedding of the full truth structures.

**Right to left.** If D(P) failed in M, its algebraic characterization would supply r!=0 with r=diamond r and r∧P=0. An embedding preserves these facts. Its image r is nonzero and diamond-fixed, hence actually true in N; P is true there too. This contradicts r∧P=0.

**Left to right.** Name every entity of M and take its complete algebraic diagram. Consider a finite part, split into equations Delta+ and disequalities Delta-, together with a finite conjunction K of pure Max axioms. In M every true equation has value top by NI. Each disequality and each Max axiom is diamond-fixed. Their conjunction q is actually true, hence nonzero and diamond-fixed. D(P) gives q∧P!=0. Since Delta+ has value top, this says the entire finite diagram, K and P are jointly ordinarily possible at M.

It follows that their existential closure is C-consistent: a C-proof of its negation could be necessitated as a whole and would contradict this possibility. Thus every finite subset of Max+P+Diag_alg(M) is consistent. Compactness and Henkin completeness give N and a realization of the complete diagram. The equations give a homomorphism and the disequalities give injectivity. The optional K was never necessitated; its diamond-fixed identity was used instead. QED.

Accordingly the target is exactly the existence of two genuine Max models M,N with M satisfying G#, N satisfying not G#, and a ONE-WAY full-term embedding M→N. No return map should be requested.

## 4. What that embedding must do numerically

For the target G=forall n P(n), with P Sigma^0_1, every source number has a witness to P. The numerical atomic embedding transports that witness, so P remains true at every image number. A numerical counterexample to G in N must therefore lie outside the image of M's numerical domain. The numerical embedding must be proper.

A full-term embedding in fact preserves Sigma^0_2 arithmetic truth on numerical parameters. As checked in the previous follow-up, under I a Sigma^0_1 formula is equivalent to a positive-existential identity expression. Its negation can be expressed using a disequality of that expression with top, since positive-existential identity expressions are persistent. A Sigma^0_2 formula is therefore equivalent, under the necessary numerical guards and I, to an existential finite-Boolean-identity formula. Embeddings preserve this fragment. In particular both Sigma^0_1 formulas and their Pi^0_1 negations are preserved, so the numerical embedding is Sigma^0_1-elementary. This still permits new counterexamples to Pi^0_2 sentences.

There is no obstruction at this arithmetic reduct alone: the standard numbers embed Sigma^0_1-elementarily into the arithmetic reduct of any Max model of not G, because Max decides standard Sigma^0_1/Pi^0_1 arithmetic correctly. The obstruction is extending the map to a genuine source's entire logical algebra without introducing an H(G) witness. The earlier standard supported source cannot be that source, since its H(G) witness would be preserved by any embedding.

## 5. Unconstrained term profiles cannot supply nonstandard numbers

The standardness obstruction survives removal of all standard-arithmetic component exits. It also survives adding arbitrarily many unconstrained parameters to the term profiles. Here is a syntactic canonicity lemma and its precise application to that proposed repair.

**Uniform numeral canonicity.** Let c be any finite tuple of fresh constants of admitted types, with no nonlogical axioms imposed on them. If T(c) has type nu_e and

    C(c) proves N(T(c)),

then, for one external standard integer k,

    C(c) proves T(c)=k.

The converse holds by the ordinary numeral axioms. In particular the conclusion is one uniform numeral; it is not a case distinction whose value depends on c.

**Auxiliary model construction.** The generic-profile root used to prove this lemma is a variant of the earlier restricted profile root, not an assumption of signature Max in the SP problem. Take a finite nonempty root individual domain with a separate labelled individual for each individual constant in c; add one label a if needed. Attach a C(c,a)-complete family of component models, allowing every interpretation of these constants. Root exits send each labelled individual to its interpretation in the selected component. There are no nonidentity arrows between new roots.

At each relational type, an entity consists of an arbitrary current extension on the already constructed argument domains and a term profile in c,a, interpreted at every component exit. Profiles agreeing in all components are identified. Interpret each relational constant by its own constant profile and, for example, the empty current extension. Types are handled in order of their finite construction complexity. A profile may mention higher-type constants: their component interpretations have already been specified independently, so this creates no circular definition of a current argument domain.

Application transports profiles by term substitution. For lambda abstraction, use the actual root truth of its matrix for the current extension and the syntactically substituted abstraction for its component profile. This also covers matrices with quantifiers and identity: at the root their bound variables range over the stipulated root domains, and at a component they range over that component's unchanged domain. Equal parameter profiles produce the same complete component tails. The standard profile-root verification therefore gives H and Logical Equivalence, hence C. Finally, literal root equality of two term values implies equality at every component, and C(c,a)-completeness makes that equality a theorem of C(c,a).

At this root there is an admissible predicate W of cardinalities whose current extension is exactly the set of standard numeral denotations: choose this arbitrary current extension and the constantly false component profile. Its root extension contains zero and is closed under successor. The definition of N therefore makes every actual number a standard numeral; conversely C proves that each numeral is a number. The component family supplies pure Max and hence I, so distinct standard numerals are distinct entities.

Now evaluate the assumed theorem N(T(c)) at the root. Its value T(c) equals a standard numeral k there. By the equality-reflection property, C(c,a) proves T(c)=k. The fresh label a does not occur in this statement and can be eliminated. This proves uniform numeral canonicity. No numberhood hypothesis on an arbitrary c was necessitated or substituted for a C-theorem.

**Term-profile obstruction.** Let F(S) be the algebra of terms in any set S of unconstrained fresh constants, modulo C(S)-provable identity. Suppose a genuine C+I model A has a homomorphism

    pi: Alg(A) -> F(S)

preserving all pure term operations and the pure constants. Then A's arithmetic is standard.

Indeed an actual number n has N(n)=top, so its profile pi(n)=T(c) satisfies N(T(c))=top in F(S), for some finite tuple c from S. Uniform numeral canonicity makes this profile the standard numeral k. If n were different from k in A, numerical rigidity would give I_A<=neq(n,k). Applying pi would give [I]<=0 in F(S), which is impossible because C+I is consistent and adding unconstrained constants is conservative. Hence n=k in A.

This proof does not require a standard-arithmetic component in the chosen family. A family complete for identities in C(S) gives exactly the same term-profile algebra, even if all its I-true components were replaced by nonstandard elementary extensions. Nor does an infinite stock of free profile parameters help: each individual profile term uses only finitely many of them.

There are two distinct obligations for a replacement construction. Its profiles must extend beyond this unconstrained term-algebra regime, and its admissible higher-type extensions must omit the external standard-numeral predicate when nonstandard arithmetic is intended. Meeting the first condition does not meet the second. For example, imposing N(c)=top on a numerical profile generator defeats the canonicity hypothesis, but arbitrary current extensions still admit W and prevent c from becoming a nonstandard actual number. No suitable restricted-domain policy is constructed here.

## 6. A free numerical generator also requires an arithmetic type choice

There is an additional finite obstruction to treating a numerical generator as otherwise unconstrained. Let F_N be the term algebra for C(c) with the identity N(c)=top imposed, where c has type nu_e. It cannot be the faithful full-term algebra of a genuine C+I point.

Let Even(c) be the usual bounded arithmetic parity formula, translated using relational Sum, and put E(c)=I meet Even(c). The bounded conditional-rigidity lemma gives, at any genuine C+I point with c numerical,

    E(c)=I or E(c)=bottom.

This uses ordinary classical bivalence for Even(c): its true case is necessary conditional on I, as is its false case. Nevertheless neither equality is a theorem of C+N(c)=top. A standard C+I model with c=0 refutes the second equality; one with c=1 refutes the first. Thus F_N has E(c) different from both I and bottom. Realizing its complete identity diagram at a genuine I-true point would contradict the displayed disjunction.

This is a failure of the proposed GENERIC numerical profile, not a failed disjunction for pure Max: c is an extra constrained parameter, and a genuine Max model is free to choose its parity. More generally, the bounded arithmetic type of an admitted numerical parameter must be reflected in its conditional identity diagram. Specifying numberhood while leaving all those identities free is already too weak to support the desired actual truth interpretation. This explains one concrete part of the extra profile data required by section 5; choosing such a type still supplies no Henkin completion theorem.

## 7. A quotient that removes exactly the old H(G) witnesses

There is a direct algebraic surgery for the single target, although its output is not yet a genuine model. Let A be the full-term algebra of any genuine Max+G model and B its common pure a-term subalgebra. Define the Boolean ideal

    J_G = { p in A_t : diamond p <= G }.

Diamond preserves finite joins and is idempotent, so J_G is a diamond-closed ideal; it is contained in the principal Boolean ideal below G. As in `../notes/sp-essential-extension-20261022.md`, section 6, the relation

    x ~ y iff neq(x,y) belongs to J_G

is a congruence for every pure term operation. Write Q=A/~.

**The old term algebra survives.** Suppose nonzero b=U(a) in B belonged to J_G. The equality diamond U(a) meet G=diamond U(a), being an equality of old terms true in A, is a C(a)-theorem. Since U(a) is nonzero in B, unary Possibility+ gives Max proves forall a diamond U(a). The equality would therefore give Max proves G, contrary to the choice of G. Hence J_G meets B only in zero and the quotient preserves B at every sort. In particular G meet I remains nonzero in Q.

**No H(G) witness survives or is created algebraically.** Suppose [r]=diamond[r] and [r] meet not[G]=0 in Q. It follows that diamond r meet not G belongs to J_G. But every member of J_G is below G, whereas this particular member is below not G. It must therefore be zero already in A. Thus diamond r<=G, so r belongs to J_G and [r]=0. Consequently Q satisfies the universal algebraic sentence

    forall r [r=diamond r and r meet not G=0 -> r=0],

which is the D(not G) condition. This check handles NEW fixed points in the quotient as well as images of old fixed points.

This is not the required consistency proof. A Boolean ultrafilter can contain the surviving G meet I, but it has not been shown to give correct truth even for all literal identities in Q, much less the Henkin quantifier clauses. An arbitrary diamond-closed quotient need not have the identity-correctness property of a B-essential quotient: nonzero fixed propositions could have zero meet after quotienting. One may further quotient maximally while preserving B to recover the previously established essential-algebra machinery, but its Henkin gap remains unchanged. Nor does an ordinary Henkin completion preserve the displayed universal condition; it can introduce a new H(G) witness.

The useful distinction is therefore between removing the unwanted witnesses in an algebra, which this construction does, and completing that algebra while keeping them absent, which remains open here.

## 8. The exact quotient seen by all Max+not G homomorphisms

The single-ideal construction has a sharper version that incorporates the target's Max axioms. Let K range over finite conjunctions of pure Max axioms, including the empty conjunction, and put

    J* = { p in A_t : for some K, diamond p meet K <= G }.

This is again a diamond-closed Boolean ideal: for two members use the conjunction of their two finite K's, and use preservation of finite joins and idempotence of diamond. The argument in section 7, with K retained, shows J* meets B only in zero. Let Q*=A/~_(J*).

**Exact kernel characterization.** For an element p of A_t,

    p belongs to J*
      iff every full-term homomorphism from A to a genuine Max+not G model
          sends p to zero.

For the forward direction transport diamond p meet K<=G. If the image of p were nonzero, its diamond would be true at the target; K is true there too, forcing G, a contradiction.

For the reverse direction suppose p does not belong to J*. Take the complete POSITIVE operation diagram of A, with a name for every entity, and add Max, not G and p!=0. Every finite part uses finitely many diagram equations and some K. The diagram equations have value top in A, while

    diamond p meet K meet not G != 0

is precisely the failure of the corresponding inequality in the definition of J*. Thus this finite part is ordinarily possible at A and its existential closure is C-consistent. Compactness supplies a genuine Max+not G model realizing the entire positive diagram with p nonzero. Its realization is the required homomorphism. No injectivity of this homomorphism was assumed or obtained.

Consequently every such homomorphism factors through Q*, and these factorizations jointly separate its entities: for two distinct quotient entities apply the characterization to their nonzero disequality value. Choosing one separating target for each pair embeds Q* in a PRODUCT of genuine Max+not G algebras.

**The algebraic D(not G) condition still holds.** If [r]=diamond[r] and [r] meet not[G]=0, then p=diamond r meet not G belongs to J*. Choose K with diamond p meet K<=G. Since p<=diamond p, this gives p meet K=0, hence diamond r meet K<=G. Therefore r belongs to J* and [r]=0.

This identifies exactly the distinctions that every target homomorphism must erase, rather than guessing which extra root coordinates should be removed. It still does not give the single embedding BETWEEN GENUINE MODELS required in section 3. A product of their algebraic reducts need not support a genuine identity-correct Henkin truth; nor is the universal identity U_G automatically preserved by the quotient. The surviving nonzero pure term G meet I is weaker than either assertion. The completion problem has therefore not been bypassed.

## 9. For the earlier supported source, the exact quotient is just B

Apply section 8 to the supported source from the preceding follow-up, with all its distinguished roots satisfying G. It has the full-term profile homomorphism pi:A->B, which is the identity on the old pure a-terms. Then

    J_G = J* = ker(pi) at proposition sort,

and the associated full-term quotient is exactly B.

If pi(p)=0, p has zero component profile. Its diamond also vanishes at every component exit and can be nonzero only at distinguished roots. All those roots satisfy G, so diamond p<=G and p belongs to J_G. Conversely, if p belongs to J*, project the witnessing inequality to B. Were pi(p) nonzero, this would be a C(a)-provable inequality diamond pi(p) meet K<=G. Unary Possibility+ and the Max axioms in K would make G a Max theorem. Thus pi(p)=0. The inclusions J_G subset J* finish the proof; the corresponding identity congruences agree at every sort.

It follows that EVERY full-term homomorphism from this supported source to a genuine Max+not G point discards all its additional root coordinates and factors through B. Its kernel is exactly that of pi, since the remaining B map is injective at every Max target. The Boolean witnesses and other root enrichments constructed earlier cannot be retained by such a map. Quotienting this particular source therefore returns directly to the common term algebra and its unresolved Henkin truth problem; it does not give an intermediate repaired model. This does not assert that B admits no suitable truth interpretation.

## Current boundary

The joint consistency target Con(Max+G+D(not G)) is still unresolved. The completed deductions in this continuation are the retract obstruction, the exact one-way embedding criterion, the obstruction to unconstrained term profiles, the finite obstruction to a free numerical profile, and the exact target-kernel quotient, which reduces the earlier supported source back to B. None is being recorded as an independently checked theorem or as a completed SP model.

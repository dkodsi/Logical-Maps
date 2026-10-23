# Strong Possibility: the minimal Henkin-algebra route

22 October 2026. Research subagent `/root/henkin_minimal`. Original ordinary mathematical arguments, not independently human checked or formalized. No database or Lean edits. Direct source for the deductions below: misc, this note. Fixed background: Bacon–Dorr, *Classicism*, draft 16 May 2023, §1.3 and §2.6 p. 42, with the topic's relational type grammar. The general profile-root construction used for orientation is the separate note `/tmp/classicism-research/profile-root-construction-20261022.md`; its new results are not attributed to the published paper.

## 1. Scope

Write `Max` for pure Maximalist Classicism, with the reference theory fixed at C. Write `SP` for the pure Strong Possibility schema with its Max-consistency side condition. All terms below are pure unless a single displayed individual parameter is explicitly allowed. Quantifiers inside terms are unrestricted; restrictions concern the outer Boolean combination of identity atoms, not the internal syntax of terms.

The previously established equivalence `SP = UMax` identifies UMax as the set of universal finite-Boolean-identity sentences individually consistent with Max. It reduces SP consistency to the disjunction property for closed existential finite-Boolean-identity sentences. The present note does not assume that disjunction property.

## 2. A positive existential identity sentence is already settled by Max

Call an identity formula positive-existential when it is built from typed identity atoms by finite conjunction, finite disjunction, and existential quantification. Empty conjunctions/disjunctions may be represented by top/bottom. Arbitrary well-typed pure terms, including lambda and quantifier terms, may occur inside each identity atom.

**Lemma 2.1.** For every such formula E(xbar), C proves

    E(xbar) -> box E(xbar).

Here the displayed free parameters are preserved by transport; this is not the assertion that an arbitrary optional hypothesis may be necessitated.

**Proof.** Necessity of identity gives the atomic cases. If A and B each imply their own boxes, normal modal reasoning gives the same implication for their conjunction and disjunction. Suppose the result holds for F(y,xbar). At a witness y of exists y F(y,xbar), the induction hypothesis gives box F(y,xbar). The theorem F(y,xbar) -> exists y F(y,xbar), necessitated as a C-theorem and combined with normal K, gives box F(y,xbar) -> box exists y F(y,xbar). Existential elimination over the original witness yields the desired implication for exists y F. This is the usual persistent-witness argument, requiring no Barcan assumption or surjectivity of transports. Induction proves the lemma. Reflexivity gives the converse box E -> E. QED.

**Theorem 2.2.** For every CLOSED pure positive-existential identity sentence E,

    C proves E       implies Max proves E;
    C does not prove E implies Max proves not E.

Consequently Max decides every sentence in this fragment, and its positive instances are exactly the C-theorems.

**Proof.** The first assertion is immediate. By Lemma 2.1 and reflexivity, C proves E iff box E, with box E defined as E=top. Thus C proves E=top iff C proves E. If C does not prove E, E=top is a closed pure identity not provable in C, so its Max instance is E!=top, namely not box E. The C-theorem E->box E gives not E. QED.

**Corollary 2.3.** Max has the disjunction property for finite disjunctions of closed pure positive-existential identity sentences. In fact it decides every individual branch, so an entailed disjunction must contain an entailed branch, assuming the already established consistency of Max.

This is stronger than merely saying that every branch is consistent or inconsistent with Max. The selection is controlled by C-theoremhood. It does not establish an effective algorithm, since C-theoremhood is undecidable.

**Theorem 2.4 (positive term-witness extraction, with parameters).** Let E(a) be a positive-existential identity formula whose only possible free variable is the individual a. Arbitrary pure a-terms may occur as coefficients. If E(a) is true at any chosen individual in any Max model, there is a finite existential branch of E and a tuple of pure a-terms Ubar(a), including a itself for all individual witnesses, such that C(a) proves every identity in that branch after substituting Ubar(a). Consequently E(a) holds at EVERY individual of EVERY Max model. In the algebraic reading of its outer existential quantifiers, E(a) also holds in the common pointed term algebra B.

**Proof.** The closed positive-existential sentence exists a E(a) is true in a Max model. Theorem 2.2 therefore makes it a C-theorem. Evaluate it at the singleton profile root R. Put its finite positive matrix into disjunctive normal form, choose a true branch and its finitely many witnesses, and collapse every individual witness to R's unique individual. Each relational witness has a pure one-individual profile U_i(a). A true root identity has equal component profiles; thus every selected identity remains true after transporting to every C-component with every interpretation of a. The component family is complete for C(a), so each substituted identity is a C(a)-theorem. This gives the asserted explicit finite branch and pure term witnesses.

The resulting finite conjunction is therefore true in every C-model with an interpretation of a, and in particular every Max model. It also holds in B, whose equality is precisely C(a)-provable identity. Conversely, any such term-witness proof trivially verifies E in every Max model. This establishes the full equivalence between truth in some Max model at some a, truth in all Max models at every a, and existence of a C(a)-provable finite branch with pure a-term witnesses. QED.

The argument applies to the algebraic outer existential quantifiers only; it does not assert the Henkin truth clause for quantified proposition TERMS in B. In particular it does not repair clause 3 of §4. The parameter form uses just one individual parameter; replacing it by several independently interpreted individuals would invalidate the singleton-collapse step.

## 3. Negated identities depending on a single individual can be eliminated

Fix pure terms S(x), T(x) of the same type, with at most the one free individual variable x. Max has the unary Possibility+ consequence: whenever a pure P(x) is C-consistent, Max entails forall x diamond P(x). This is the singleton-root consequence proved in the profile-root note, §6.

**Lemma 3.1.** Exactly one of the following alternatives applies:

1. C proves forall x S(x)=T(x), and Max proves forall x S(x)=T(x).
2. C does not prove forall x S(x)=T(x), and Max proves forall x S(x)!=T(x).

**Proof.** In the second case C+S(x)!=T(x) is consistent for the free individual variable x; otherwise universal generalization would prove the universal identity. Unary Possibility+ gives forall x diamond(S(x)!=T(x)). At each actual x, identity S(x)=T(x) would imply its ordinary necessity by NI, contrary to the displayed possibility. Thus every actual x satisfies the disequality. The first case follows from the C-theorem. QED.

The distinction is a metatheoretic case split; neither alternative follows by necessitating an optional premise. Closed pure identities are the special case in which x does not occur.

Consider now a closed sentence written as a finite disjunction of expressions

    exists x^e exists ybar . [ A(x,ybar) and N_1(x) and ... and N_k(x) ],

where A is a positive finite Boolean combination of typed identities, and each N_j(x) is a disequality between pure terms whose sole possible free variable is x. The tuple ybar may have arbitrary admitted types and may include further individual variables. A disjunct may omit x when all its negative literals are closed.

**Theorem 3.2.** Max decides every sentence of this form. Each disjunct is Max-equivalent either to bottom or to the positive-existential identity sentence exists x exists ybar A(x,ybar).

**Proof.** Lemma 3.1 makes each negative literal uniformly true or uniformly false over all actual x in every Max model. A false negative literal kills the disjunct. If all negative literals are true, delete them. The resulting existential-positive sentence is decided by Theorem 2.2. A finite disjunction of decided sentences is decided. QED.

**Interpretive limit.** This excludes failed-disjunction constructions whose negative literals are confined to one individual parameter in each branch. It does NOT exclude disequalities depending on two or more individual witnesses, nor prove that every possible failure requires a relational witness. For example, exists x,y (x!=y) is a genuine existential identity sentence not decided by Max, since both singleton and larger coalesced roots are available. Any stronger assertion must handle those multiple-individual patterns separately.

## 4. Exact truth-ultrafilter formulation of the pointed term-model attempt

Let a be one new individual symbol. For each type sigma, let B_sigma be the pure a-terms of that type, identified when C(a) proves their identity. Pure term operations act by substitution. The unary Possibility+ lemma ensures that the resulting many-sorted term algebra embeds into the algebraic reduct of every Max model after choosing any actual individual a. Its identity diagram is therefore independent of that model and its chosen individual. In particular it satisfies every member of UMax as an ABSTRACT algebraic structure.

This does not yet give a model of C. To obtain an all-type a-term-generated model with these domains, one needs a subset V of B_t satisfying all of the following:

1. V is a Boolean ultrafilter, so it gives classical truth-functional evaluation.
2. For all typed terms S,T, the proposition [S=T] lies in V iff [S]=[T] in the fixed term algebra.
3. For every formula F(z,abar) and tuple abar of term denotations,

       [exists z F(z,abar)] lies in V
         iff [F(U,abar)] lies in V for some a-term U of z's type.

The universal clause follows by Boolean duality. With these conditions the straightforward induction on formula construction is the truth lemma, yielding a Henkin truth interpretation of the fixed algebra. The all-type term-model condition is stronger than the proposition-only generation criterion that already suffices for SP.

Clause 3 is the genuine obstacle: the term-operation symbol for a quantified formula is already fixed, but quantification in a model ranges over its actual domain. An arbitrary Boolean ultrafilter, or a restriction of an existing model to its term denotations, need not make those two readings agree. The ordinary Henkin construction obtains clause 3 by adjoining new names, which may change the algebraic universal theory. No existence claim for V has been established here.

The distinction between a bare algebra and a Henkin model must also be preserved when using ultraproducts, quotients, or elementary extensions. An elementary extension in the full truth language preserves witnesses already required by existential formulas; deleting their names afterward does not delete their existence.

## 5. A substantially larger fragment has the disjunction property

The singleton-root observation communicated by `/root/failed_disjunction`, combined with §2, yields the following stronger restriction. Unlike Theorem 3.2, the individual negative literals may involve arbitrarily many individual witnesses.

Call E **individual-negative** when it has the form

    exists xbar^e exists ybar . theta(xbar,ybar),

where theta is a finite Boolean combination of identities, and, after putting theta into disjunctive normal form, every negative identity literal contains only xbar as free variables. The positive identity literals may involve all of the witnesses ybar, at arbitrary relational types. Bound variables INSIDE a term do not count as free witnesses. Pure closed terms inside literals are unrestricted.

**Theorem 5.1.** If E_1,...,E_m are closed pure individual-negative existential identity sentences and

    Max proves E_1 or ... or E_m,

then Max proves at least one E_i.

**Proof.** Choose a model M of Max with exactly one actual individual a; the existing singleton coalesced root, or the restricted profile root, supplies one. The proved disjunction is true in M, so some E_i is true. Put its matrix into disjunctive normal form and choose a true disjunct together with its witnesses. Every individual witness is the same a. Substitute a for all xbar, and call the resulting positive part A(a,ybar) and its negative literals N_1(a),...,N_k(a).

Each N_j(a) is a disequality between pure terms whose sole possible free variable is an individual. Since it is true in a Max model, Lemma 3.1 excludes the C-provable-identity case and gives

    Max proves forall z^e N_j(z).

Meanwhile the closed sentence

    P := exists z^e exists ybar A(z,ybar)

is positive-existential in identities and true in M. By Theorem 2.2, if C did not prove P then Max would prove not P, contrary to M. Therefore C proves P. In any Max model choose witnesses z,ybar for P. The universal negative guards just proved hold at z, so these witnesses satisfy the collapsed original disjunct. Assigning z to every original individual variable recovers a witness tuple for E_i. Thus Max proves E_i. QED.

The empty-individual-tuple case can be handled by adding a dummy z; types are nonempty. DNF introduces no problematic quantifiers because the matrix is a finite Boolean combination of identity atoms. Quantifiers occurring inside its terms stay inside those terms throughout.

**Corollary 5.2.** No failed existential-identity disjunction witnessing SP inconsistency can lie entirely in this fragment. In particular:

- Allowing relational witnesses only in positive identity literals does not create a counterexample.
- Multiple individual disequalities, even though Max does not decide their individual existential sentences, cannot by themselves create a failed disjunction.
- A counterexample must escape this restriction through a negative identity literal whose terms depend on a relational witness, or an equivalent algebraic condition that cannot be eliminated into the fragment by the available equations.

The last point is a restriction on the search space, not an assertion that a relational-witness disequality suffices to cause failure. No failed disjunction is constructed here.

**Corollary 5.3 (positive substitutions).** The theorem continues to apply when some negative literals initially mention relational witnesses but positive equations in their own DNF branch identify every such occurrence with a pure term in the individual witnesses. Substitute those terms using the positive equations first. The resulting equivalent branch is individual-negative. This is a literal equational simplification; no arbitrary choice of new definable witnesses is assumed.

## 6. The Boolean propositional fragment has an explicit simultaneous model

This section admits negative literals depending on proposition witnesses, so it goes beyond §5 in a different direction. It does not permit a witness to occur inside a quantifier, identity-valued term, modality, or arbitrary higher-order application. Those operations remain available inside COEFFICIENT terms that do not contain a proposition witness.

Let B be the Boolean algebra of pure proposition terms T(a), with a one-individual parameter, modulo C(a)-provable identity. Let R be the restricted singleton profile root of the separate profile-root construction. Its actual proposition algebra is

    A = 2 x B.

A pure term T(a) denotes the pair (u([T]),[T]), where u:B->2 is its actual truth value in R. Thus j(b)=(u(b),b) embeds B into A as a Boolean algebra. The Boolean ultrafilter selected by u need not obey the Henkin clauses for B itself; this section does not claim it does.

**Lemma 6.1.** The ultrafilter u contains no atom of B. More generally, the truth ultrafilter induced on B by ANY Max model and any actual individual contains no atom of B.

**Proof.** Suppose b=[T(a)] is an atom of B and is actually true in a Max model M. For every pure Max axiom K, both b and [K] have truth value 1. Their meet is therefore nonzero in B, so atomhood gives b and [K]=b. By the definition of B, C(a) proves the identity T(a) and K = T(a). Hence C(a)+T(a) proves K by the algebraic-order implication to material implication.

The theory C(a)+T(a) is consistent, witnessed by M, and recursively enumerable. We have shown it contains every pure Max axiom. This is impossible by the undecidability argument already recorded in the profile-root note §8: dovetail a C-proof of a closed pure identity I against a proof of not I in this r.e. extension; Max guarantees that exactly the appropriate search succeeds, deciding C-provability of pure identities and hence C-theoremhood. Adding the one symbol a to the r.e. extension does not affect that decision argument. QED.

**Boolean-algebra lemma 6.2.** Let B be any Boolean algebra and u a Boolean homomorphism B->2 whose ultrafilter contains no atom. Under the diagonal embedding j(b)=(u(b),b), B is existentially closed for quantifier-free Boolean identity formulas in 2 x B. Explicitly, every finite Boolean combination of equations or disequations between Boolean polynomials, with coefficients from j(B), that has witnesses in 2 x B also has witnesses from j(B).

**Proof.** Fix the finite coefficient list c_1,...,c_l and witnesses (epsilon_i,b_i), i=1,...,k. The coefficients partition 1 into their nonzero Boolean cells c_s, indexed by bit strings s. Exactly one such cell c_* has u(c_*)=1.

The b_i partition each c_s into cells

    d_(s,t) = c_s and conjunction_i b_i^(t_i),

where b_i^1=b_i and b_i^0=not b_i. In 2 x B the corresponding cell has a nonzero first coordinate only when s=* and t=(epsilon_1,...,epsilon_k). Thus all its zero/nonzero statuses agree with those of the d_(s,t), except that this one cell may acquire an extra nonzero first coordinate.

For s!=*, keep the original partition of c_s. For c_*, let m be the number of variable cells required to be nonzero in 2 x B. The element c_* can be partitioned into m nonzero pieces: otherwise it would be a join of finitely many atoms, and u would contain one of them, contrary to the hypothesis. Assign these m pieces to precisely the required nonzero patterns, and assign zero to the others. Define b'_i by taking the union of the new cells whose ith pattern bit is 1.

Every coefficient-and-variable Boolean cell now has in B exactly the zero/nonzero status it had in 2 x B. Every Boolean polynomial equality is equivalent to the vanishing of its symmetric difference, which is a union of these cells. All the original equalities and disequalities therefore hold of b'_1,...,b'_k in B. Applying j gives witnesses in j(B). This proves the full finite Boolean combination, not merely one conjunction of literals. QED.

**Theorem 6.3.** Let E be a closed pure sentence of the form

    exists xbar^e exists pbar^t . theta(xbar,pbar),

where theta is a finite Boolean combination of identities between Boolean polynomials in pbar. The coefficient propositions in those polynomials may be arbitrary pure terms T(xbar), with any internal lambda abstractions or quantifiers, but contain none of the witnesses pbar. If E is true at R, then E is true in every Max model.

**Proof.** At R all individual witnesses equal its unique a. Regard the finitely many coefficient terms T(a,...,a) as elements of B. Lemmas 6.1–6.2 replace the proposition witnesses of E by elements of the diagonal copy j(B), while preserving its complete Boolean identity matrix. Choose a pure a-term representing each replacement element. The resulting Boolean identity diagram holds in B. The common-term-algebra embedding of B into any Max model, based at any actual individual, preserves all those equations and disequations. Using that individual for every x variable and the represented terms for the p witnesses verifies E in that Max model. QED.

**Corollary 6.4.** R simultaneously satisfies EVERY Max-consistent universal sentence in the Boolean fragment dual to Theorem 6.3. Consequently Max has the restricted disjunction property for finite disjunctions of sentences in that existential fragment.

**Proof.** If a universal U of this fragment failed at R, its existential negation E would hold there. Theorem 6.3 would make E hold in every Max model, contrary to the assumed consistency of Max+U. For the disjunction statement, a Max consequence is true at R; one branch is true there, and Theorem 6.3 makes that branch a Max consequence. QED.

This supplies a genuine C+Max model for the ENTIRE restricted universal fragment, not merely an abstract Boolean algebra. It leaves full SP unsettled. In particular the actual extra atom of R is visible using possibility as an operation on a witness: a condition such as r=diamond r falls outside this Boolean fragment. Such terms cannot be treated as coefficients when r is a quantified witness.

## 7. The Boolean absorption extends to every relational type

For a relational type sigma=tau_1...tau_k t let B_sigma be its Boolean algebra of pure one-individual term profiles, with the pointwise Boolean operations. In the profile root R,

    A_sigma = P(X_sigma) x B_sigma,
    X_sigma = D_tau1(R) x ... x D_tauk(R).

For sigma=t the product X_sigma is the one-element empty-tuple set. A pure term T(a) is embedded as

    j_sigma(b) = (h_sigma(b),b),

where h_sigma:B_sigma->P(X_sigma) is its actual extension at R, a Boolean homomorphism.

**Lemma 7.1.** The actual-extension homomorphism h_sigma sends every atom of B_sigma to the empty set. This holds for the analogous actual-extension homomorphism in any Max model based at any actual individual.

**Proof.** Suppose b=[T(a)] is an atom of B_sigma and has an actual instance xbar in a Max model. For each pure Max axiom K, let constant_sigma(K) be the pure lambda abstraction lambda xbar.K. Since K is actually true, the extension of b and constant_sigma(K) still contains xbar. This meet is therefore nonzero in B_sigma: a zero profile would be a C(a)-provable identity with bottom and could have no actual instance. Atomhood yields

    b and constant_sigma(K) = b

in B_sigma. By definition of its quotient, C(a) proves that identity. Hence C(a) proves forall xbar (T(a)[xbar] -> K), and the consistent recursively enumerable theory

    C(a) + exists xbar T(a)[xbar]

proves K. This holds for EVERY pure Max axiom, contradicting the same undecidability argument as Lemma 6.1. Empty tuples recover the propositional proof. QED.

**Boolean-algebra lemma 7.2.** Let h:B->D be a Boolean homomorphism that sends every atom of B to zero. Then the graph embedding j(b)=(h(b),b) makes B existentially quantifier-free reflecting in D x B, in the Boolean-algebra language with all coefficients from j(B).

**Proof.** Repeat the finite-cell proof of Lemma 6.2. This time more than one coefficient cell c may have h(c)!=0, and the D-coordinate may add several nonzero variable-pattern cells within each. For every such c, the interval below c has arbitrarily large finite partitions: a finite join of B-atoms would be killed by h. Partition c into precisely as many nonzero pieces as the complete D x B diagram requires, and assign them to the required variable patterns. If h(c)=0, its diagram is already supplied by the B-coordinate and can be kept unchanged. The resulting B-witnesses reproduce every cell's zero/nonzero status, hence every equation and disequation. QED.

**Theorem 7.3.** The profile root R realizes the minimum possible existential identity theory over Max for the following multisorted Boolean fragment:

    exists xbar^e exists Fbar . theta(xbar,Fbar),

where the F witnesses may have ANY relational types; every identity in theta compares two pointwise Boolean polynomials at a common type sigma; a polynomial may use witnesses of that same type and arbitrary pure coefficient terms T(xbar) of that type; and theta is an arbitrary finite Boolean combination of these identities.

More explicitly, every sentence E of this fragment true at R is true in every Max model. Therefore R simultaneously satisfies all Max-consistent universal sentences dual to this fragment, and Max has the finite disjunction property for the corresponding existential sentences.

**Proof.** Collapse all individual witnesses to the unique root individual a. At each relational type appearing in the finite matrix, apply Lemmas 7.1–7.2 to its finite witness-and-coefficient diagram. Witness sorts interact here only through the outer Boolean combination; no term operation in the fragment sends a witness into another sort. Thus their diagrams can be reproduced independently in the respective B_sigma. Choose pure a-term representatives of the new witnesses. The whole matrix now holds in the common typed term algebra. Its embedding into every Max model based at any actual individual preserves the diagram. Assign that individual to every x variable and the represented terms to Fbar. This proves E there. The universal and disjunction conclusions follow exactly as in Corollary 6.4. QED.

The theorem does not cover application of one witness to another, an equality-valued term containing a witness, a modality applied to a witness, or a quantified term containing a witness. Pointwise Boolean connectives are admitted even though their underlying lambda definitions use application; they are treated here as the specified Boolean operations, whose algebra laws C proves. An arbitrary use of application does not become a Boolean polynomial merely because its output is propositional.

This all-type result is an explicit, full-C fragment-model theorem. It still leaves the genuine Henkin closure issue of §4 unresolved: the term algebra need not inherit R's truth and quantifier clauses, and R's extra actual extensions remain present.

## 8. Guarded modification for extensional term contexts

This extends the simultaneous-model theorem in another direction: it admits application and quantification through extensional contexts, while restricting the existential relation witnesses to types with only individual arguments.

Call a term context S(Fbar,a) of relational output type sigma **extensionally dependent on Fbar** when C proves that replacing Fbar by actually coextensive relations makes the resulting S terms actually coextensive:

    conjunction_i forall ubar_i (F_i[ubar_i] iff G_i[ubar_i])
      -> forall vbar (S(Fbar,a)[vbar] iff S(Gbar,a)[vbar]).

This is a C-theorem requirement, not an inference from an optional extensionality hypothesis. The displayed vbar runs over all argument types of sigma; it may be empty. Ordinary first-order formula constructions in relation variables are examples. Applying box or an identity-valued operation to a witness is not generally an example.

**Guard lemma 8.1.** Let D(a) be a pure term of relational type sigma whose profile is nonzero in B_sigma. Then some pure Max axiom K has the property that

    C(a) + exists vbar D(a)[vbar] + not K

is consistent.

**Proof.** C(a)+exists vbar D(a)[vbar] is consistent. Otherwise C(a) would prove that D has no instances; necessitation and the C characterization of relational Boolean order would make D=bottom a theorem, contrary to its nonzero profile. This is a consistent recursively enumerable extension of C. If it entailed every pure Max axiom, the undecidability argument from §6 would give a contradiction. Choose one axiom K it does not entail. Its negation can consistently be added. QED.

**Theorem 8.2.** Let E be a closed pure existential finite-Boolean-identity sentence. Permit arbitrary individual witnesses, and require each relational witness F_i to have a type e...e t (including t). Suppose every term S or T appearing on either side of an identity atom S=T is extensionally dependent on the whole tuple Fbar in the sense just defined. If E holds at the singleton profile root R, then E holds in every Max model.

**Proof.** Choose witnesses at R. Collapse all individual witnesses to its unique a. Record the complete true/false assignment of the finitely many identity atoms in E's matrix; it is enough to reproduce that assignment. Write U_i(a) for the pure profile term of each actual witness F_i. Because every argument of F_i has type e and R has one actual individual, F_i's actual extension is the constant relation epsilon_i, where epsilon_i is top or bottom. These constants are pure terms. Let epsilonbar be their tuple.

For a true identity S(Fbar,a)=T(Fbar,a), equality of profiles gives the C(a)-provable identity S(Ubar,a)=T(Ubar,a). Extensional dependence also shows that the pure sentence

    chi_(S,T)(a) := forall vbar
          (S(epsilonbar,a)[vbar] iff T(epsilonbar,a)[vbar])

is actually true at R: Fbar and epsilonbar are actually coextensive there.

For a false identity, put

    D_(S,T)(a) := S(Ubar,a) symmetric-difference T(Ubar,a)

at the common relational output type. There are two cases. If D has nonzero profile, choose a Max axiom K_(S,T) by Lemma 8.1. If D has zero profile, the false identity at R must be witnessed by a difference in actual extensions. Extensional dependence then makes the pure sentence

    psi_(S,T)(a) := exists vbar
          (S(epsilonbar,a)[vbar] xor T(epsilonbar,a)[vbar])

actually true at R.

Let G(a) be the finite conjunction of all the chi sentences for true atoms, all the psi sentences for the zero-profile false atoms, and all the selected Max axioms K for the remaining false atoms. This is a pure one-individual sentence, true at R, and therefore C(a)-consistent. Define replacement pure profiles by pointwise Boolean modification:

    V_i(a) := (constant(G(a)) and epsilon_i)
                 or (constant(not G(a)) and U_i(a)).

At a world where G is true, each V_i is actually coextensive with epsilon_i. At a world where G is false, it is actually coextensive with U_i. Extensional dependence propagates this comparison through every S and T context.

For a true identity atom, on the G region the corresponding chi gives coextension of S(Vbar,a) and T(Vbar,a). Outside G, the old profile identity S(Ubar,a)=T(Ubar,a) gives it. Hence C(a) proves the universal pointwise equivalence of the new terms. Necessitating this theorem and using C's equivalence between relational Boolean order and necessary universal pointwise implication yields their identity. No optional hypothesis is necessitated.

For a false identity with nonzero old profile, Lemma 8.1 provides a C(a)-world with an actual D instance and not K_(S,T). There G is false, so the new terms are actually coextensive with the old ones and still differ on that instance. Thus their identity is not a C(a)-theorem. For a false identity with zero old profile, take a C(a)-world satisfying G, which exists by its consistency. The corresponding psi gives a differing instance of the epsilon terms, and hence of the new V terms. Again the new identity is not a C(a)-theorem.

The replacement terms therefore reproduce the entire identity diagram in the common one-individual term algebra. Its embedding into any Max model, or equivalently Lemma 3.1 applied to the new identity atoms, reproduces that diagram there after choosing any actual individual. These are witnesses for E. QED.

**Corollary 8.3.** R simultaneously satisfies every Max-consistent universal identity sentence dual to this fragment, and Max has its restricted disjunction property. This includes ordinary first-order extensional constructions in existentially quantified relations of types e...e t, with application to individual variables and individual quantification inside the term contexts.

The theorem does not require the quantifier-free identity matrix to have only propositional outputs: its compared terms may have arbitrary relational output types, provided the extensional-dependence theorem holds. It does not cover arbitrary higher-type witnesses with arbitrary actual extensions, since such a witness need not be actually coextensive with any pure term. Nor does it cover intensional operations on the witnesses. The small modal candidate r=diamond r lies outside the theorem for precisely this latter reason.

## 9. Independent cross-audit of the mixed two-root construction

I read and checked `/tmp/classicism-research/sp-failed-disjunction-20261022.md`, §§9.1–9.5, including the profile, support, landing and quantifier clauses. This is an independent AI-agent audit, not a named-human check. The construction passes the following checks.

1. Its root category is well-defined under marker substitutions d_i->d_j/top/bottom. There are only two arrows 0->1, determined by z->x or z->y, and one endomorphism of root 0. All assignments of the countably many d_i to Boolean constants define return arrows 1->0, each retracting either 0->1 arrow. Component exits admit arbitrary interpretations of the markers; composing an exit with a root substitution again gives such an assignment.
2. Domains at each relational type are defined simultaneously from already available argument domains. No same-type landing recursion is needed: root 0 has unrestricted root extension coordinates, while finite support at root 1 directly ensures its endomorphism tails remain supported. Root-0 tails into root 1 are supported by {x} or {y}, since all their further root composites depend only on that marker's image.
3. Agreement on the finite support at two arrows with the same codomain gives identical transported parameter ENTITIES. Further root composition preserves support agreement, and further component composition preserves the interpreted support values. This validates the support claim for identity and quantified terms. At each target, quantifiers use that target's full admitted domains; no transport surjectivity is assumed.
4. Fresh d_i split any nonzero root-1 relational entity. Fix an arrow and target tuple witnessing a nonempty extension, then vary only d_i outside the entity's support between top and bottom. The target and the full transported entity remain fixed. The constant lift of D_i therefore yields two nonzero disjoint Boolean parts at every relational type.
5. The root-0 singleton proposition w is a true atom and witnesses Actuality, but its h-tail is not an atom. That tail has empty support: its root truth value depends only on whether the arrow's codomain is 0 or 1. Distinct return arrows can assign a fresh d_i opposite truth values while keeping that tail true, so root-1 atomlessness is compatible with the retraction.
6. Every A_n=Fregean and Exactly_n(e) is false at both root objects. Root-0 profiles remain pure one-individual terms, hence are constant on pointed finite extensional A_n components. Thus the old profile proof gives Atom(A_n) at root 0, even though the transported A_n is atomless at root 1.
7. Root 0 has three root-arrow truth bits and countably many pure component profiles, so its proposition domain is externally countable. Its actual higher-relation extensions remain unrestricted, allowing the standard-numeral property and graph relation used in the earlier internal countability proof. This uses internal countability, not Countable Boolean Completeness.

The return arrows give D(P) at 0 for every pure P true at 1. They therefore certify the advertised consistency package with E_1, Actuality, all Atom(A_n), and distinctness-preserving possibility of E_2 plus all-type atomlessness and not Actuality. The construction still fails full SP: the two-root component-profile obstruction applies to E_3. This failure is explicit rather than an unresolved point in the audit.

## 10. Finite families of retract targets with prescribed finite splitting

The audited construction extends uniformly to finitely many bookkeeping contexts. This is a new construction consequence; it does not assert SP consistency.

Take Gamma_0={z:e}. For i=1,...,r, let Gamma_i contain k_i>=1 individual markers and m_i proposition markers, where k_i is finite and m_i is either finite or countably infinite. Root arrows are all substitutions sending individual markers to individual markers and proposition markers to proposition markers or top/bottom in the target context. Use every interpretation assignment as a component exit, exactly as in §9. At 0 use all root extension coordinates with pure z-profiles. At each i>0 use finite supports containing the profile's free markers.

The type induction, support and landing proofs from §9 carry over verbatim with the following explicit observations. Every 0->i arrow chooses the image of z, so its tails are supported by that one target individual marker. A supported i-entity transported along an i->j substitution has support given by the finitely many target generic markers appearing in the images of its original support; Boolean constants require none. Transport to 0 has a pure z-profile and lands in the unrestricted domain there. Agreement on supports after further composition still gives identical transported entities. Hence quantified and identity terms close, and the structure is a C-model. Complete component exits make every root a pure-Max point.

Every 0->i arrow has return arrows i->0: collapse all individuals to z and send every proposition marker to a Boolean constant. Thus every pure sentence true at any target i is distinctness-preservingly possible at 0.

For finite m_i, put

    N_(i,n) = 2^(m_i) * sum_{s=1}^{min(k_i,n)} Stirling2(k_i,s).

**Claim.** At root i, A_n=Fregean and Exactly_n(e) has exactly N_(i,n) Boolean atoms below it, for every n>=1.

**Proof.** All root objects satisfy Max and are non-Fregean, so A_n has zero actual extension at every root arrow. At an A_n component the finite extensional hierarchy is unique up to permutations of its n individuals. A tuple of k_i individual markers is classified up to that permutation by its equality partition, which has at most n blocks. Each of the m_i proposition markers is either top or bottom. The possible orbits are therefore exactly the N_(i,n) pairs (individual equality partition, proposition truth-bit pattern).

Each orbit is described by a finite pure-marker proposition: conjoin A_n with the relevant individual identities/disequalities and proposition literals. It is nonzero because the corresponding component assignment exists. The orbit propositions are disjoint and exhaust A_n. Every Gamma_i term profile has a fixed value on each such complete pointed finite extensional orbit. Because all A_n root coordinates vanish, an arbitrary root-i proposition meets each orbit proposition in either zero or that whole orbit. Thus every orbit proposition is an atom and there are no others below A_n. QED.

For countably infinite m_i, the fresh-marker argument makes EVERY relational Boolean algebra at root i atomless, not merely the intervals below A_n. Thus the same singleton source can distinctness-preservingly access arbitrarily many finitely specified splitting patterns and an all-type atomless target, while itself retaining Actuality and Atom(A_n) for every n.

The source proposition domain remains externally countable. There are 1+sum_i k_i root arrows out of 0, hence only finitely many root truth bits, and countably many pure z-profiles. Its full actual higher-relation extensions again supply internal countability of propositions. This avoids silently introducing a full P(N) coordinate by taking infinitely many unrestricted root targets at once.

By ordinary compactness, if one prescribes countably many finite-context target properties, every finite collection can be realized by this construction while retaining the source's fixed properties and internal countability. A model of the resulting countable collection of D-instances therefore exists. This compactness statement concerns the specified target properties, not all Max-consistent sentences. In particular it does not remove the full-SP obstruction or establish that arbitrary Max-consistent theories can be represented by these supported contexts.

## 11. Higher-type witnesses with finitely many named observations

The guarded argument does extend to some higher-type witnesses. Its exact proof requirement is weaker than the first-order witness restriction in Theorem 8.2.

**Replacement criterion 11.1.** In Theorem 8.2 allow the existential witnesses F_i to have arbitrary relational types. Keep the C-provable extensional-dependence requirement for all compared term contexts. Suppose, for the chosen witnesses at R, there are pure one-individual terms W_i(a) such that every compared context S(Fbar,a) and S(Wbar,a) has the same actual extension at R. Then the same conclusion holds: the existential identity sentence is true in every Max model.

**Proof.** Repeat the proof of Theorem 8.2 with Wbar in place of epsilonbar. The finite chi and psi guard sentences are actually true at R by the assumed context-wise coextension. Define V_i=(G and W_i) or (not G and U_i), pointwise at the witness's type. At G-worlds the V witnesses are actually coextensive with Wbar, and elsewhere with Ubar. All steps of the old proof, including preservation of the original profile disequalities outside selected Max guards, apply unchanged. There is no requirement that W_i itself be globally coextensive with F_i, only that the finitely many compared contexts have the required actual coextensions. QED.

A useful uniform syntactic fragment satisfies this criterion. For each witness F_i of type tau_i1...tau_iki t, choose finitely many tuples s_ij(a) of PURE a-terms of its argument types. Assume C proves, for each compared context S,

    conjunction_(i,j) [F_i[s_ij(a)] iff G_i[s_ij(a)]]
      -> forall vbar [S(Fbar,a)[vbar] iff S(Gbar,a)[vbar]].

Call this finite-observation dependence. The tuple terms s_ij contain none of the existential witnesses. Their internal syntax is otherwise unrestricted. Finite-observation dependence implies the full extensional dependence used in §8.

**Theorem 11.2.** The profile root R realizes the minimum existential identity theory over Max for all finite-observation-dependent diagrams of this form, with arbitrary relational witness types and arbitrary relational output types. Therefore the corresponding universal Max-consistent laws all hold simultaneously at R, and the restricted disjunction property holds.

**Proof.** Given actual root witnesses, record the truth bit epsilon_ij of each observed F_i[s_ij(a)]. Define the pure finite-table term

    W_i(a) := lambda ubar .
        disjunction_{j : epsilon_ij=true} [ubar=s_ij(a)],

where tuple identity is the finite conjunction of the matching typed identities. If two named argument tuples are identical at R, the original relation has the same truth value on them, so the table is consistent. It therefore matches every recorded observation at R. An empty set of positive observations gives bottom. Nullary witnesses give the corresponding top/bottom proposition.

By finite-observation dependence, all compared contexts have at R the same actual extensions under Fbar and Wbar. Apply Replacement Criterion 11.1. The universal and disjunction conclusions follow by the same argument as Corollary 6.4. QED.

This permits genuinely higher-type applications such as a witness of type tt applied to finitely many pure named propositions. It does not permit unrestricted application to another unnamed relational witness, or a bound variable ranging over its whole type, unless a separate finite-observation theorem is supplied. It also does not make arbitrary identity-valued contexts extensionally dependent.

## 12. A sharp obstruction to adding identity-valued contexts wholesale

The modal counterexample audited in §9 shows that the existential reflection theorem cannot simply be extended by adding even one identity-valued operation on a proposition witness.

Consider the closed existential identity sentence

    E := exists r^t [r!=bottom and r=not(r=bottom) and r and E_1=r].

Here r=not(r=bottom) is exactly r=diamond r. Thus E is H(E_1), equivalently box_ne E_1. Its only non-Boolean operation on the witness inside a term is the single identity-valued operation r |-> (r=bottom); all other witness-dependent term operations are Boolean. The outer matrix is a conjunction of typed identities and one disequality.

At the isolated singleton profile root R, the root-only atom w has w!=bottom, w=diamond w, and w<=E_1. Hence E is true there. In the audited retract Max model, E_1 is true but D(not E_1) is true as well, so H(E_1) is false. Thus E is NOT a consequence of Max.

Consequently the exact minimum-existential-theory conclusion of §§6–8 and 11 fails for the isolated profile root as soon as this elementary identity-valued witness operation is freely admitted. This is a rigorous boundary counterexample to that MODEL-BUILDING METHOD. It is not a failed disjunction for Max and does not refute SP: the retract model also refutes H(not E_1), as already proved in the sibling note.

## 13. A supported root with no actual atom, unchanged pure profiles, and a modal obstruction

This construction isolates a limitation of the pointed-generation/omitting-types approach. It is not a proof that a pointed-generated SP model cannot exist.

### 13.1 The root category and its component exits

Take one root object o with individual domain {a}. Introduce a countable set of BOOKKEEPING markers d_0,d_1,... and two bookkeeping tokens 0_* and 1_*. They are not symbols of the object language. The root endomorphism monoid M consists of all maps

    f : {d_i : i in N} -> {d_i : i in N} union {0_*,1_*},

extended by fixing 0_* and 1_*. Composition is substitution. Each root endomorphism fixes the sole individual a.

Attach a C-complete family of the ordinary component models used in the profile-root construction. For each component object V and each b in D_e(V), add an exit alpha_(V,b):o->V taking a to b. EVERY root endomorphism is annihilated by an exit:

    alpha_(V,b) composed with f = alpha_(V,b).

Component arrows compose with exits in the ordinary way, transporting b. This is an associative category. In particular the bookkeeping markers are never assigned arbitrary component propositions; the component profiles below remain PURE one-individual terms.

### 13.2 Finite-supported domains with pure profiles

Define the root relational domains by induction on type. For sigma=tau_1...tau_k t, an entity consists of:

- a pure one-individual component profile T(a) of type sigma, identified modulo its complete component family;
- a root extension R_f contained in D_tau1(o) x ... x D_tauk(o) for every f in M;
- a finite support S contained in the bookkeeping markers such that R_f=R_g whenever f and g agree on S.

The support is a property, not an additional coordinate of the entity. Its root f-tail has extension family g |-> R_(g composed with f) and the SAME pure profile T(a). It is supported by the finitely many generic markers occurring among f(S); the fixed tokens need no support. Thus every root tail lands in the indicated root domain. A component tail is the value of T at its exit's individual b and therefore lands in the component domain.

If f and g agree on a support S of an entity, their tails are equal ENTITIES: after every further root h, h composed with f and h composed with g still agree on S; after every component exit the profiles coincide because exits annihilate root endomorphisms. This is stronger than equality of actual extensions and supplies the identity-term clause.

A term with finitely many root parameters has the pure profile obtained by substituting their pure profiles into that term. Its root extension family is supported by the union of their finite supports. Indeed f and g agreeing on this union give exactly the same transported parameter entities in the same target root domain. Evaluation of a formula, including quantified formulas, is therefore the same; quantifiers in both evaluations range over the SAME complete root domains. Lambda abstraction gives the required extension equality for every tuple of its target arguments. Component evaluation is ordinary profile substitution. This proves term closure, with no surjectivity of transport assumed.

The H axioms and Logical Equivalence are verified as in the profile-root construction: equality is equality of the complete extension families; extensional lambda operations are evaluated at every arrow; H-theorems agree at every root and component target. Therefore this is a C-model. Complete component exits make its root a pure-Max point.

### 13.3 The root indicator and fresh splitters

Let r have root extension true at EVERY endomorphism and bottom component profile. It has empty support. It is nonzero, and every root tail of r is r. Every component tail is bottom. Consequently

    r = diamond r,       r <= E_1,       r != bottom.

The middle assertion uses the singleton individual domain at every root arrow; r vanishes at every component. Thus H(E_1) holds.

For each marker d_i define D_i with bottom component profile and root truth value

    D_i(f) = 1 iff f(d_i)=1_*.

This has support {d_i}. Under a root substitution f it becomes D_j when f(d_i)=d_j, becomes r when f(d_i)=1_*, and becomes bottom when f(d_i)=0_*. These rules commute with composition and component exits. In particular 1_* encodes r, NOT the logical top proposition: both r and bottom have bottom component profile. Confusing 1_* with logical top would destroy the construction.

Every relational entity X with a nonempty extension at SOME root arrow is non-atomic. Choose an arrow f and tuple witnessing nonemptiness, and choose d_i outside a finite support of X. Change only f(d_i), once to 1_* and once to 0_*. The two resulting arrows have the same target and agree on the support, so X has the same extension at the chosen tuple. The constant lift of D_i has opposite truth values at the two arrows. Hence X intersect constant(D_i) and X intersect not constant(D_i) are disjoint nonzero parts. This works at every relational type.

In particular every actually true proposition has a proper nonzero Boolean part, so there is no true propositional atom. Actuality would supply a true atom: a proposition below every actual truth is below either q or not q for every q, making every subproposition either itself or bottom. Therefore Actuality is false here.

In fact Vicinity is false. Given any actually true v, take a finite marker support S of v and choose d_i outside S. The proposition q:=r and not D_i is actually true at the identity root arrow. Let f fix every marker in S and send d_i to 1_*. Then v's f-tail is the same full entity v, while q's f-tail is r and not r=bottom. Thus v is true at f but diamond q is false there, so v is not below diamond q. No actually true v bounds the possibilities of all actual truths. This uses the existing construction and introduces no new root objects or domain restrictions.

### 13.4 Every pointed-complete closed proposition is still an atom

Let A be any pure closed proposition for which C(a)+A is consistent and complete. Such an A is false at the Max root. Otherwise its complete recursively enumerable pointed theory would decide each pure Max axiom in accordance with the actual Max truth, thereby entailing every Max axiom, contrary to the r.e. impossibility proved in the profile-root note.

Since a closed term has the same root truth at every root endomorphism, A has zero extension at all root arrows. For any root proposition p with pure profile T(a), pointed completeness makes A and T(a) equivalent to either A or bottom in every C-component. Thus p and A has zero root extensions and component profile either A or bottom. It is literally A or bottom as an entity. The profile A is nonzero by consistency and component completeness. Hence A is an atom.

In particular the model satisfies Atom(A_n) for every A_n=Fregean and Exactly_n(e), simultaneously. More strongly it satisfies EVERY atomicity assertion for a pure closed pointed-complete proposition covered by the earlier classification.

### 13.5 What this proves about omitting the unnamed-proposition type

Let T be Max together with not Actuality and all Atom(A) for pure closed pointed-complete A. The construction proves

    T + H(E_1) is consistent.

Work over an additional individual name a. Consider the type

    p != U(a), for every pure one-individual proposition term U(a).

Let phi(p) be the finite formula

    p!=bottom and p=diamond p and p and E_1=p.

The model just built realizes phi with r. On the other hand no pure a-term U(a) can satisfy phi in ANY Max model. If it did, the common pointed term-algebra diagram (Lemma 3.1) would make phi(U(a)) true in every Max model at every individual. H(E_1) would then be a consequence of Max, contradicted by the audited retract model satisfying Max and D(not E_1). Therefore Max proves phi(p)->p!=U(a) for each U, by identity substitution and the uniform pure-term diagram.

Thus a single consistent formula implies every member of the unnamed-proposition type, even over the strengthened theory T. The type is principal in the sense relevant to the usual omitting-types criterion: nonprincipality is unavailable. This blocks that SUFFICIENT proof method. It does not prove the type cannot be omitted in a model of T, since a T-model may omit the whole definable set phi; nor does it settle the existence of an SP model. The result specifically shows that adding not Actuality and all the known pure closed atomicity consequences does not by itself fix the nonprincipality argument.

**Independent audit.** The sibling research agent `/root/failed_disjunction` checked this construction on 22 October 2026 and reported that the exit-annihilation, full-entity support, quantified closure, two special tokens, fresh splitter, preserved component atoms, and unnamed-type argument all pass. This is an independent AI audit, not a named-human check.

## 14. Further cross-audits of external-symmetry constructions

I independently checked `/tmp/classicism-research/sp-failed-disjunction-20261022.md`, §§12–14. The checks establish the following compatibility results, as ordinary mathematics rather than database verdicts.

- The isolated finite-support root of §12 satisfies Max and refutes Relational Choice at (e,e). Its external permutation group acts by actual-truth-preserving automorphisms and permutes component assignments; it is not added as a set of future arrows. Full quantified lambda closure follows because the chosen domains are invariant under bijections. The invariant serial relation of pairs has no finite-supported selector.
- The symmetric retract of §13 satisfies Max, E_1, Actuality, all Atom(A_n), failure of Choice at (t,t), and distinctness-preserving possibility of failure of Choice at (e,e). External conjugation fixes every permutation arrow because the chosen permutation group is abelian. All remaining arrows have finite support. This is what validates transport of the finite-support domains; equivariance alone without finite support of the arrow would not suffice.
- The combined retract of §14 imposes both external permutation support and substitution support at its target. These are separate invariants: transport preserves external support by adjoining an arrow support, and preserves substitution support by taking finite marker images. Source-to-target tails are automatically pinned by the image of the source individual; target-to-source tails have pure one-individual profiles and need only external support. Agreement on substitution support gives equal complete transported entities, so identity and quantifier terms close. The source simultaneously has Max, E_1, Actuality, all Atom(A_n), and failure of Choice at (t,t). At one target every relational Boolean algebra is atomless, Actuality fails, and Choice at (e,e) fails. All these target truths are distinctness-preservingly possible at the source.

The last model refutes both H(RC_(e,e)) and H(not RC_(e,e)) at its source: singleton individuals give actual RC_(e,e), while a return arrow witnesses D(not RC_(e,e)). Hence that natural modal existential-identity disjunction is NOT forced by Max. The constructions do not prove SP, and their remaining finite-root pure-profile obstruction is explicit in the sibling note.
## 15. Exact all-type atomicity classification for one-individual pure terms

This generalizes the closed-proposition pointed-completeness classification. Fix ANY relational type sigma and any pure term T(a) of that type, with at most the single free individual variable a. Let b=[T(a)] in the Boolean algebra B_sigma of pure one-individual profiles.

**Theorem 15.1.** The following are equivalent:

1. b is a Boolean atom of B_sigma.
2. Some Max model, at some individual a, satisfies Atom_sigma(T(a)).
3. Max together with forall a Atom_sigma(T(a)) is consistent.

Moreover, if b is not an atom, Max proves forall a not Atom_sigma(T(a)). If b is an atom, SP proves forall a Atom_sigma(T(a)). Thus, conditional on SP consistency, this gives an exact determination of which such atomicity laws SP proves; no unqualified syntactic biconditional is asserted for an inconsistent theory.

**Proof.** If b=0, C(a) proves T(a)=bottom and atomhood is impossible. If b is nonzero and not an atom, choose c in B_sigma such that both b and c and b and not c are nonzero. Choose a pure representative U(a) of c. Neither of the corresponding meet-with-bottom identities is a C(a)-theorem, so the uniform unary identity diagram makes both meets nonzero in every Max model at every actual individual. They are disjoint Boolean subobjects of T(a), refuting its atomhood. This proves the contrapositive of (2)->(1), including the uniform negative assertion.

Suppose b is an atom. In the singleton profile root R its actual extension is empty by Lemma 7.1. Every root entity X of type sigma has some pure profile c in B_sigma. Thus T(a) and X has empty actual extension and profile b and c, which is either 0 or b. The entity is therefore literally bottom or T(a). Since b is nonzero, T(a) is a Boolean atom of the full root domain. The root has only one individual, so forall a Atom_sigma(T(a)) holds. This proves (1)->(3), and (3)->(2) is immediate.

Finally forall a Atom_sigma(T(a)) is a universal finite-Boolean-identity sentence: expand atomhood as nonzeroness and the universal subobject condition. Its Max-consistency therefore makes it a member of UMax, and the previously proved SP=UMax equivalence yields the positive SP consequence. QED.

The supported model of §13 simultaneously satisfies every law in the positive case, at EVERY relational type. Indeed pure T(a) is fixed by every root endomorphism, since a is fixed and the term has no other parameters. Its root extension is empty by Lemma 7.1 whenever [T(a)] is a B_sigma atom. Every arbitrary supported X still has a pure one-individual profile, so the same meet calculation makes T(a) an atom of the full supported domain. All root coordinates of the meet are zero; the additional root bookkeeping cannot split it.

Consequently the principal unnamed-proposition type in §13.5 remains principal even over the stronger theory obtained by adjoining ALL these positive all-type atomicity laws, together with not Actuality. This is stronger than adjoining only Atom(A_n) or only the pure closed pointed-complete propositional atoms. It remains a limitation of the ordinary omitting-types proof method, not a refutation of SP.
## 16. Identity-correct truth on an essential algebraic quotient

Let A be the full many-sorted term-operation algebra of a genuine Max model, let B be its common pure one-individual subalgebra, and let Q be a quotient of A in which B embeds and is essential. Here essentiality means every nonidentity congruence of Q restricts nontrivially to B. Such a quotient exists algebraically by the Zorn argument in `/tmp/classicism-research/sp-essential-extension-20261022.md`; its full Henkin status remains open.

Every C-provable identity in arbitrary variables survives in Q. In particular its proposition sort is a Boolean algebra, and its identity-valued operations satisfy the equational forms of reflexivity, symmetry, transitivity, and substitution into EVERY term operation. This last proviso includes operations formed using quantification or lambda abstraction.

### 16.1 The equality-gated congruences

For p in Q_t define a sorted relation theta_p by

    x theta_p y iff p <= eq_sigma(x,y), for x,y in Q_sigma.

It is a congruence. Reflexivity uses eq(x,x)=top; symmetry uses eq(x,y)=eq(y,x); transitivity uses eq(x,y) and eq(y,z) <= eq(x,z). For a k-ary term operation F, the C-provable equational substitution inequality is

    conjunction_i eq(x_i,y_i) <= eq(F(xbar),F(ybar)).

Thus p below all input identities is below the output identity. These are Boolean inequalities, hence equations, so no actual-truth interpretation of Q is being assumed.

The congruence theta_top restricts to equality on B, since B embeds into a genuine Max model where eq(b,c)=top implies b=c. Essentiality therefore makes theta_top the identity congruence of Q. In particular Q itself has the implication eq(x,y)=top => x=y at every type, including e.

### 16.2 Finite subdirect irreducibility

B is finitely subdirectly irreducible for this entire term signature. To see this without requiring a Henkin truth interpretation on B itself, restrict actual truth from any Max model into which B embeds. If distinct pairs x_i,y_i are given, the proposition disjunction_i eq(x_i,y_i) is actually false, and therefore is not top. Any joint embedding into a finite product in which each coordinate identifies one of these pairs would instead send that disjunction to top in every coordinate, contradicting injectivity. Equivalently, a finite intersection of nonidentity congruences of B is nonidentity.

Essentiality transfers this property to Q. Every nonidentity congruence of Q restricts to a nonidentity congruence of B; a finite intersection of those restrictions is nonidentity; therefore the corresponding intersection on Q is nonidentity.

### 16.3 Extending any already correct truth ultrafilter

Let D be ANY subalgebra with B contained in D contained in Q. Suppose V is a Boolean ultrafilter on D_t that gives literal identity truth:

    eq_D(x,y) is in V iff x=y, for every same-type x,y in D.

No Henkin quantified-witness clause is assumed for V. Then V extends to a Boolean ultrafilter W on Q_t giving literal identity truth on ALL of Q.

**Proof.** Require W to contain V and the complement of eq_Q(x,y) for every distinct same-type pair x,y in Q. It suffices to prove the finite intersection property. Let d be the conjunction of finitely many elements of V, so d is in V, and consider finitely many distinct pairs x_i,y_i. Put e_i=eq(x_i,y_i).

First theta_d restricts to equality on B. If d<=eq(b,c) for b,c in B, upward closure of V makes eq(b,c) true in V, so identity correctness gives b=c. Essentiality therefore makes theta_d the identity congruence of Q.

Suppose d and conjunction_i not e_i were zero. Then d<=disjunction_i e_i, hence disjunction_i(d and e_i)=d. Each theta_(d and e_i) is nonidentity, because it identifies the distinct pair x_i,y_i. But

    intersection_i theta_(d and e_i)
       = theta_(disjunction_i(d and e_i))
       = theta_d
       = identity,

contrary to finite subdirect irreducibility. Thus the required finite meet is nonzero. The Boolean ultrafilter lemma gives W. Equal pairs have equality value top by reflexivity; distinct pairs have their equality complements in W. Hence W has precisely literal identity truth. Its restriction to D is V because both are ultrafilters. QED.

Taking D=B and restricting truth from any Max model supplies the hypothesis. Thus the maximal essential quotient ALWAYS admits an identity-correct Boolean truth interpretation, and any prescribed identity-correct truth on an intermediate subalgebra can be retained. The still-unproved issue is the Henkin witness clause for quantified terms, not the Boolean or literal-identity clauses.

The equality-gated congruence proof was independently audited by the sibling agent `/root/existential_products` on 22 October 2026. This is an AI-agent audit, not a human verification or a formalization.

### 16.4 Stronger form: every Boolean extension is already identity-correct

The sibling agent `/root/failed_disjunction` supplied the following simpler strengthening, independently checked here. If x!=y in Q, essentiality gives distinct b,c in B in the congruence generated by (x,y). Choose a finite polynomial chain witnessing this generated-congruence membership. Every chain step satisfies the equational substitution inequality

    eq(x,y) <= eq(F(x),F(y)).

The parameters of F may be arbitrary elements of Q. Chaining the inequalities by equality transitivity gives

    eq(x,y) <= eq(b,c).

Thus every false literal identity in Q is bounded by a false literal identity in B. ANY Boolean ultrafilter W on Q extending an identity-correct Boolean ultrafilter on B must omit eq(b,c), and therefore must omit eq(x,y). Equal pairs have equality value top. Consequently every Boolean extension is identity-correct; no additional ultrafilter selection is needed. Ordinary Boolean ultrafilter extension already supplies such extensions, including extensions of any prescribed identity-correct truth on an intermediate D.

This stronger proof does not require the separate finite-subdirect-irreducibility argument, though §§16.1–16.3 remain valid independent deductions. It again supplies no Henkin quantified-witness clause.

## 17. Such a quotient embeds in a genuine Henkin model, but may acquire new witnesses

The identity-correct truth of §16 also gives a useful completion fact. Name every element x of Q by a constant c_x of its sort. Let Gamma contain the full operation diagram, all literal identity/disequality facts of Q, and the actual truth literal c_p or not c_p for every proposition p according to an identity-correct ultrafilter W.

**Claim.** C plus Gamma is consistent. Hence ordinary Henkin completeness gives a genuine C-model containing Q as a term-operation subalgebra and extending W's actual truth. Since B embeds, the resulting C-model satisfies pure Max.

**Proof.** Every finite conjunction gamma from Gamma is true under the direct Q evaluation and W. If C plus gamma were inconsistent, the deduction theorem, followed by replacing its finitely many fresh constants with variables, would give a C-theorem not gamma in those variables. Necessitating a C-theorem identifies its proposition with top; therefore the corresponding Boolean identity gamma=bottom holds in A under every parameter assignment and survives in its quotient Q. But W makes gamma true, contradicting gamma=bottom. Thus every finite subset is C-consistent, and compactness gives the whole theory.

In its Henkin model the named elements are distinct exactly as in Q, and the operation diagram makes their interpretation a homomorphic embedding. All named proposition truth literals preserve W. The common pure one-individual diagram survives inside this embedding, including every pure Max disequality, so the new model is Max. QED.

The conclusion is an EMBEDDING into a Henkin completion, not a Henkin interpretation on Q's existing domains. The completion may add witnesses outside Q. Essentiality of B in Q does not automatically extend to the larger Henkin model. Alternating a Henkin completion with a maximal B-preserving quotient also does not yet solve this: the next quotient can destroy the truth of new witnesses even while retaining the entire old algebra and its old truth. No witness-preservation theorem has been proved. This isolates the remaining obstacle more narrowly than merely saying the algebraic quotient has no available truth valuation.
## 18. Essentiality is equivalent to modal density, and rules out Actuality

Let A be the full term-operation algebra of a genuine Max model N, with common pure one-individual subalgebra B. Write diamond p for not(p=bottom).

**Theorem 18.1.** The following conditions are equivalent:

1. B is essential in the full term algebra A.
2. Every nonzero r satisfying r=diamond r contains a nonzero q in B_t.
3. Every such r contains q in B_t that is ACTUALLY TRUE in N.

**Proof of (1)->(3).** For r!=bottom, the congruence generated by (r,bottom) is nonidentity. Essentiality and the finite polynomial-chain argument give distinct b,c in B with

    eq_t(r,bottom) <= eq_sigma(b,c).

Taking complements yields q:=not eq_sigma(b,c) <= diamond r=r. Since b and c are distinct pure profiles, the common identity diagram makes q actually true in every Max model, hence nonzero. This proves (3), which immediately implies (2).

**Proof of (2)->(1).** Let theta be a nonidentity full-term congruence and choose x!=y in one theta-class. Put r:=not eq(x,y). Since the model has literal identity truth, r is actually true and nonzero. NI and reflexivity give the C-theorem eq(x,y) iff box eq(x,y); necessitation of that theorem converts it into an identity of propositions. By Boolean duality, r=diamond r. Because theta identifies x,y and preserves the identity-former and Boolean operations, it sends eq(x,y) to top and sends r to bottom. Choose nonzero q in B with q<=r by (2). The equation q=q and r forces theta to send q to bottom. Its restriction to B is therefore nonidentity. QED.

Condition (2) is equivalently the statement that every nonzero diamond-closed Boolean ideal meets B nontrivially: the principal ideal below a diamond-fixed element is diamond-closed, and any nonzero diamond-closed ideal contains diamond p for any nonzero member p. Thus, in this setting, essentiality for the FULL logical term signature agrees with essentiality for the Boolean algebra with diamond reduct. This equality of conditions has been proved, not inferred merely from their names.

The proof of (2)->(1) uses literal identity, or equivalently eq(x,y)=top => x=y. For an arbitrary algebraic quotient lacking that property, that direction is not asserted. The essential quotients of §16 do have the property by theta_top, so the same equivalence applies to them algebraically once an identity-correct Boolean truth is supplied.

**Theorem 18.2.** A genuine Max model satisfying these equivalent conditions refutes Actuality. More generally, an essential quotient with an identity-correct truth ultrafilter extending Max truth on B has no actually true Boolean atom.

**Proof.** Suppose w were an actually true Boolean atom. Let K range over the closed pure Max disequality axioms. Every K is actually true. Therefore w and K is actually true and nonzero; atomhood gives w<=K. Such a K is possibility-fixed: it is the negation of a pure identity, and the NI calculation in Theorem 18.1 gives diamond K=K. Hence diamond w<=K for every K.

The proposition diamond w is nonzero and diamond-fixed by C's ordinary S4 identities. The density condition gives a nonzero pure one-individual term q=Q(a) with

    q <= diamond w <= K

for EVERY closed pure Max disequality axiom K. Each inequality q<=K is itself an identity between pure one-individual terms. Since the common B diagram is exactly the C(a)-provable diagram, C(a) proves each such inequality. Nonzeroness of q in B makes C(a)+Q(a) consistent; this follows by the same necessitation argument as Guard Lemma 8.1. The consistent recursively enumerable theory C(a)+Q(a) now proves every pure Max axiom, contradicting the established r.e. impossibility. Thus w cannot exist.

Actuality would supply an actually true atom, so it is false in a genuine Henkin model. The algebraic proof used only the Boolean ultrafilter, literal identity, the fixed B diagram, and essentiality, and therefore also applies to the stated quotient. QED.

Consequently, if the chosen B truth ultrafilter contains the proposition Actuality, NO essential quotient extending it can be Henkin-perfect. Its algebra cannot contain a true atom witnessing that proposition. This strengthens the particular witness-loss example from the original profile root: the incompatibility holds for every essential quotient over that truth assignment. It does not prove SP implies not Actuality, since essentiality is a sufficient SP criterion and has not been shown necessary for SP.
**Stronger corollary 18.3 (parent's refinement).** These same essentiality/modal-density conditions refute Vicinity, not merely Actuality. A Vicinity witness v is true and satisfies v<=diamond p for every actually true p. Apply this to each pure Max axiom K. Since K is diamond-fixed, v<=K, and therefore diamond v<=K, for all K. Density below the nonzero fixed proposition diamond v again gives a nonzero pure q below every K, contradicting the r.e. argument in Theorem 18.2. This is a consequence of the sufficient essentiality criterion; it is not asserted as a consequence of SP itself.

## 19. Finite guards that preserve existential witnesses through quotient stages

This section proves a positive result for the truth-constrained quotient problem. It concerns actual truth of quantified proposition terms, not merely the outer algebraic existential language.

Let Q be a quotient algebra as above, let D be an old term-operation subalgebra of Q, and let V be an identity-correct Boolean ultrafilter on D_t. The statement applies in particular when D is a previous essential stage and a later quotient embeds it. Parameters cbar below are arbitrary elements of D; they need not be pure-term denotations. Assume all displayed dependence claims are C-theorems, uniformly in those parameters.

### 19.1 A singleton guard for first-order relational witnesses

Let the finitely many existential witnesses F_i have types e...e t, including t. Suppose C proves extensional dependence of the proposition context phi:

    conjunction_i forall ubar_i (F_i[ubar_i] iff G_i[ubar_i])
       -> (phi(Fbar,cbar) iff phi(Gbar,cbar)).

For each i let epsilon_i range over the constant top and bottom relations of its type. Put

    E(cbar) := exists Fbar phi(Fbar,cbar),
    L(cbar) := disjunction_epsilonbar phi(epsilonbar,cbar).

Then C proves

    E_1 -> (E(cbar) iff L(cbar)).

**Proof.** At a singleton-individual point, each F_i is actually coextensive with its constant top or bottom relation, according to its truth on the only argument tuple. For nullary F_i this is simply its truth bit. A finite classical case split simultaneously selects one epsilon_i for each i. The stated dependence theorem transfers the truth of phi to this tuple. This proves E->L under E_1. Every disjunct of L supplies witnesses for E, so L->E holds without the guard. This is a finite H/C derivation from the given dependence theorems; it requires no identity of actually coextensive relations. QED.

Equationalizing the resulting C-THEOREM gives the identity

    E_1 and E(cbar) = E_1 and L(cbar).

This identity holds in every quotient Q. One has not necessitated an optional E_1 assumption: the entire guarded implication is first proved in C.

If E_1 and E(cbar) both belong to V, Boolean primeness makes some phi(epsilonbar,cbar) belong to V. These witnesses are already in D. In every later injective term map of D, and every extension of its Boolean truth, the very same tuple remains a true witness. Thus no Henkin completion is needed for this existential instance, and a subsequent quotient cannot erase its witness while preserving D's truth.

The same proof gives finite conjunction elimination for universal quantification over Fbar. In particular false universal instances already have counterexamples in D. Arbitrary quantified or identity-valued subterms may occur inside phi provided the displayed extensional-dependence theorem really holds; merely writing them down does not establish that hypothesis.

### 19.2 Higher-type witnesses observed at finitely many old arguments

Allow F_i to have arbitrary relational types tau_i1...tau_iki t. For each i fix finitely many argument tuples s_ij(cbar) given by terms in the old parameters and containing none of the F witnesses. Suppose C proves

    conjunction_(i,j)
        (F_i[s_ij(cbar)] iff G_i[s_ij(cbar)])
       -> (phi(Fbar,cbar) iff phi(Gbar,cbar)).

Then existential and universal quantification over Fbar reduce UNCONDITIONALLY to finite disjunctions/conjunctions with witnesses already given by old-parameter terms.

For each finite bit assignment eta=(eta_ij), define

    W_(i,eta)(cbar) := lambda ubar .
       disjunction_{j : eta_ij=1} [ubar=s_ij(cbar)].

Tuple identity is a finite conjunction of typed identities. Empty disjunctions give bottom, and nullary observations are treated as a single truth bit. There are finitely many eta. C proves

    exists Fbar phi(Fbar,cbar)
       iff disjunction_eta phi(Wbar_eta(cbar),cbar).

**Proof.** Given Fbar, select eta to be its finite observed truth table. If two named argument tuples are actually identical, identity substitution makes their observed truth bits agree. Thus the selected table Wbar_eta matches every observation, even though unrelated bit assignments in the disjunction might not. The dependence theorem transfers phi's truth to this table. The reverse implication is ordinary existential introduction. All reasoning is a finite classical case split and identity substitution, so it gives a C-theorem uniformly in cbar. QED.

Necessitating this theorem, and using the Boolean identity criterion, identifies the two proposition terms in every quotient. Boolean primeness now gives an old table witness whenever the existential term is true under V. Its truth survives every further injective quotient preserving V. The universal version follows by the same finite dependence, or Boolean duality.

This includes genuinely higher-type applications to finitely many old named propositions or relations. It does not cover an unrestricted quantified argument ranging over a whole higher-type domain, nor a genuinely intensional test of F_i, unless a separate finite-observation theorem is proved. Actuality, Vicinity, and the modal witness r=diamond r do not satisfy the required extensional dependence. Their known witness-loss mechanisms therefore do not contradict this result.

### 19.3 What the theorem contributes to a quotient iteration

At a stage whose old truth contains E_1, EVERY extensional first-order-relation existential request of §19.1 is discharged permanently by old constant witnesses. At all stages, every finite-observation request of §19.2 is discharged permanently by an old finite-table witness. No additional truth choice is needed for these requests beyond preserving the old ultrafilter. The surviving obstacle consists of quantifier requests whose witness dependence cannot be reduced in this way, especially identity/modal tests of unnamed relational witnesses and unbounded higher-type observations. The theorem does not claim that those remaining requests are simultaneously satisfiable or that an iteration is Henkin-complete.
## 20. Exact preservation criterion for a chosen identity-diagram witness

Let D be an old B-essential algebra embedded in a genuine Max Henkin completion R, and let pi:R->Q be any maximal B-preserving algebraic quotient. Its restriction to D is injective, because a nonidentity kernel on D would identify B-elements. Equip Q with any Boolean truth extending D's prescribed identity-correct truth.

### 20.1 Positive and old-negative witnesses survive

Suppose a tuple w in R witnesses a positive-existential identity formula over parameters in D. Choose a true finite conjunction branch. Every asserted literal identity is an equality of entities in R, and a term homomorphism preserves it. Thus pi(w) satisfies the same positive branch in Q, with actual truth supplied by literal identity. This proves witness preservation even when w is NEW and no old term supplies it.

The same statement permits negative identity literals whose terms use ONLY the old parameters: injectivity on D preserves their disequalities. It also permits additional actual truth guards that are propositions of D, since the quotient truth extends D's old truth. No actual-truth predicate on a genuinely new proposition is implicitly preserved.

### 20.2 The exact test for a new negative pair

For a specified distinct pair s,t in R, the following are equivalent:

1. Every maximal B-preserving quotient keeps s and t distinct.
2. The principal full-term congruence generated by (s,t) restricts nontrivially to B.

If (2) holds, any quotient identifying s,t contains this principal congruence and therefore identifies distinct B-elements, which is forbidden. Conversely, if that principal congruence is trivial on B, extend it by Zorn to a maximal congruence trivial on B. The resulting essential quotient identifies s,t. This proves the equivalence.

Condition (2) has a finite certificate: choose distinct b,c in B connected by a finite polynomial chain generated by s,t. Identity substitution and transitivity give the equational inequality

    eq(s,t) <= eq(b,c).

The right-hand side is a pure one-individual identity that is false under every Max interpretation. The inequality therefore protects the new disequality under any B-preserving quotient. The full finite chain, consisting of positive equations over B with finitely many extra parameters, is the explicit certificate when its polynomial parameters are also being transported.

For a fixed finite conjunction of identities and disequalities witnessed by w in R, the witness survives EVERY maximal B-preserving quotient exactly when each of its required negative pairs has this protection. If one pair is unprotected, a maximal quotient can destroy that particular witness by collapsing that pair. This does not imply that the original existential formula loses every possible witness in that quotient.

The criterion pinpoints why the earlier positive extraction theorem is insufficient for full Henkin closure. Positive identities survive quotienting automatically. Genuinely new negative identities survive precisely when their principal congruences are detected already in B. Arbitrary new actual-truth literals require an additional argument, such as the extensional or finite-observation eliminations of §19. No simultaneous preservation of all remaining witnesses has been established.

## 21. A finite proof does not protect an arbitrarily chosen witness

C itself proves exists p (p!=bottom), with the protected pure witness top. Nevertheless, in the original profile root the root-only atom w=(true,bottom) is another witness. Its principal congruence with bottom is contained in the profile-projection kernel, which is trivial on B. That projection is a maximal B-preserving quotient onto B and sends w to bottom. Thus even a C-theorem, needing NO Max axioms, does not protect an arbitrarily selected Henkin witness. Witness replacement is indispensable.

For a closed pure existential finite-Boolean-identity sentence E, the following are equivalent:

1. E has a witness in B.
2. In some genuine Max model, some true conjunction branch of E has a witness for which every negative pair's principal congruence meets B nontrivially.
3. Every genuine Max model has such a protected witness, obtained from the same pure one-individual terms after choosing an individual.

The implication (1)->(3) uses the common embedding of B: a negative pair of B-elements is already a distinct B pair, so it protects itself. Clearly (3)->(2). For (2)->(1), adjoin the finitely many polynomial-chain certificates for all negative pairs to the positive part of the chosen branch. Positive term-witness extraction realizes this expanded finite positive system in B. If one of the negative pairs collapsed there, its certificate would identify the fixed distinct B endpoints. Hence every negative pair survives and the resulting B tuple witnesses E.

This is an exact test for PROTECTED REPLACEMENTS, not merely for one prescribed witness. No argument has yet shown that a finite Max proof of E always supplies them. If every Max-forced existential identity sentence did have such a replacement, Max would have the desired finite disjunction property: apply the replacement theorem to a forced finite disjunction and select its true B branch, which then holds in every Max model. Thus a general replacement theorem would settle the existential DP route to SP consistency. The positive, old-negative, extensional-guard and finite-observation results above establish specific fragments; the unrestricted step is still open.

## 22. H-clopen pure sentences and the missing embedding theorem

The sibling's `sp-failed-disjunction-20261022.md`, §17, proves the following normalization, independently audited here:

1. If E is an existential finite-Boolean-identity sentence, C proves E iff H(E).
2. Every H(P) is such an existential identity sentence, namely

       exists r [r!=bottom and r=diamond r and r and P=r].

3. SP consistency is equivalent to the following relative disjunction property: for closed pure P,Q, if C proves the DISJUNCTION H(P) or H(Q), written C ⊢ (H(P) ∨ H(Q)), then Max proves P or Max proves Q.

For (1), choose a true finite conjunction branch and its witnesses. Each positive identity has proposition value top by identity substitution. The conjunction of its negative identity literals is diamond-fixed, actually true, and therefore nonzero; it lies below the branch and below E. It witnesses H(E). An empty negative conjunction is top. Conversely H is factive. This proof neither commutes a quantifier through H nor assumes Barcan. The finite-Max-guard step needed in (3) is given in the cited sibling section.

Call a closed pure P **C-provably H-clopen** when C proves both P iff H(P) and not P iff H(not P). Such P and its negation are both equivalent in C to existential Boolean-identity sentences. This is a precise two-sided existential definition; it does not itself classify P by closed identities.

### 22.1 Embeddings preserve both truth values

Let M,N be genuine C Henkin models and let j:A(M)->A(N) be an injective homomorphism of their FULL term-operation algebras. No actual-truth preservation is assumed. Every existential finite-Boolean-identity sentence true in M is true in N: use the image of a witnessing tuple, preservation of term values and equality, and injectivity for disequality. The terms inside the identity atoms may themselves contain quantifiers; they are among the operations that j is required to preserve.

If P is C-provably H-clopen, apply this observation to H(P) and H(not P). It follows that

    M satisfies P iff N satisfies P.

The reverse implication here uses preservation of not P: if M failed P, N would fail it as well. Thus actual truth of an H-clopen pure sentence is invariant under algebraic embeddings even when actual truth is NOT part of the algebraic signature.

In particular, the following sufficient condition would make Max decide every C-provably H-clopen pure sentence:

    Any two genuine Max models have full term-operation algebras that
    jointly embed into the term algebra of a genuine C model.

The joint target automatically satisfies pure Max, since its embeddings preserve the closed pure disequalities of either source. If two source models disagreed on P, their embeddings into the target would preserve both opposite truth values, impossible. Completeness then gives Max proves P or Max proves not P.

This joint-embedding condition has NOT been established. It is a statement about genuine C targets with their quantifier truth clauses, not merely the existence of some abstract algebraic coproduct or quotient. Positive equation reflection into B does not supply it.

### 22.2 A conditional finite-identity classification

There is a stronger, still unproved, sufficient hypothesis for the proposed classification. Suppose any two genuine C models with the same complete diagram of CLOSED PURE term identities jointly embed, by full term-operation embeddings, into a genuine C model. The diagram records, for every pair of closed pure terms of the same type, either their equality or their disequality. It need not contain an individual constant; sorts with no closed terms contribute no such pairs.

Under this hypothesis every C-provably H-clopen pure P is C-equivalent to a finite Boolean combination of closed pure identities.

**Proof under the stated hypothesis.** For a genuine C model M let Delta_M be its complete closed pure identity diagram. If M satisfies P, then C+Delta_M entails P. Otherwise there would be a model N of C+Delta_M+not P, and the assumed joint embedding would contradict §22.1. By compactness a finite conjunction delta_M of literals from Delta_M already gives C proves delta_M implies P.

These finite conjunctions cover all C models satisfying P. Another application of compactness gives finitely many of them whose disjunction covers P: the theory consisting of C, P and the negations of all such delta_M has no model. Their finite disjunction is consequently C-equivalent to P and is a finite Boolean combination of closed pure identities. QED.

Conversely finite Boolean combinations of identities are C-provably H-clopen, by NI, diamond-fixity of negative identities and finite Boolean combinations. Thus the proposed classification is exactly available under the stated embedding hypothesis. Neither the hypothesis nor the unconditional classification is proved here. Even deciding all H-clopen P would address only the complementary-branch part of the full relative H-disjunction property in item (3).

## 23. Why positive reflection alone cannot establish that embedding hypothesis

The following elementary example is an ABSTRACT FIRST-ORDER ANALOGY, NOT a model or countermodel of Classicism. Its purpose is to isolate a logically invalid inference from positive reflection to existential disjunction or joint embedding.

Use two nonempty sorts A,D, constants a:A and d:D, equality, and no other operations. Put

    E_A := exists x:A (x!=a),
    E_D := exists y:D (y!=d),
    T := (E_A or E_D) and not(E_A and E_D).

There are T models with sort sizes (2,1) and (1,2). In every T model, the ground-term subalgebra B has exactly one element at each sort. Every finite positive existential equation system over B that is realized in a T model is realized in B: assign every variable its sort's sole B-element. This holds for finite positive disjunctions as well, after choosing a realized branch. All T models have the same complete ground identity diagram.

Nevertheless T proves E_A or E_D and proves neither disjunct. Moreover E_A is equivalent over T to not E_D, so E_A and its negation both have existential identity definitions. It is therefore invariant under embeddings between T models, just as the C-provably H-clopen formulas of §22.1 are in the C setting. The two displayed models have no joint embedding into a T model: any such target would have at least two elements in BOTH sorts, contrary to T.

The algebraic quotient collapsing each sort to its B-element is maximal among B-preserving quotients, and its image B is trivially essential over B. It satisfies simultaneously both separately T-consistent universal identities forall x x=a and forall y y=d. But it is not a T model, precisely because it loses every witness for the T-forced disjunction. Thus positive equation reflection, a common ground algebra, maximal B-preserving quotients and a two-sided existentially definable property do not by themselves force the desired disjunction property or genuine-model closure.

Classicism has much richer logical operations and imposes many further constraints, so this example does not refute any proposed C-specific theorem. It shows why a proof must use an additional C-specific fact to obtain protected replacements, the embedding hypothesis, or Henkin truth closure. No such additional general fact has yet been established in this research.

## 24. Final cross-audits and source boundary

The sibling `/root/failed_disjunction` independently audited §§22–23 on 22 October 2026, including the two compactness steps and the distinction between genuine C targets and abstract algebras. No correction was required. This is an AI-agent audit, not human checking or formal verification.

I independently audited `sp-existential-products-20261022.md`, §§23–25. Section 23 strengthens §19 here to finitely many direct identity tests against old entities, including a finite tuple's mutual identity pattern. Section 24 supplies old entity-valued finite graph interpolants with finitely many old-function exclusions; its necessary and sufficient compatibility guard is eq(a_i,a_j)≤eq(Y_i,Y_j). Distinct false pure perturbations vanish LITERALLY at the prescribed inputs and have preserved nonzero existential supports, so their surviving values supply permanent old witnesses. Section 25 gives arbitrarily large EXTERNALLY finite Functionality multiplicities under SP, with no coded infinite family or internal countability assertion. The stronger graph theorem permits only prescribed old output entities; it does not convert newly observed outputs into old parameters.

The primary-source search inspected the author-hosted [Classicism PDF](https://andrew-bacon.github.io/papers/Classicism.pdf), dated 1 July 2022, rather than the bundle's 16 May 2023 draft. Its §3.6 and Appendix E, Theorem 3.26, provide a common predecessor whose truncations are the chosen models. They do not establish the common-target injective embeddings required in §22. Its printed p.64 separately identifies an injective common-source criterion sufficient for Strong Possibility and leaves that construction open. Text searches in this PDF found no amalgamation or interpolation theorem.

Bacon's book has a potentially relevant §18.5 on disjunction/coherence, printed pp.402–405 in the publisher's contents. Only that contents entry and the local extraction note were obtained in this bounded search; the section's body was NOT inspected. The local `topics/classicism/extraction.md` says the chapter's recorded coherence results concern maximalizations of extensions of C. This remains a source lead, not evidence for the missing embedding theorem. No generic Boolean-algebra or S4 amalgamation theorem has been imported into C.

Final status: the algebraic universal constraints, identity-correct Boolean truth and individual Henkin completions are established in the precise senses above. Simultaneous Henkin truth closure, protected replacement for every Max-forced existential identity diagram, the relative H-disjunction property, and SP consistency remain unproved.

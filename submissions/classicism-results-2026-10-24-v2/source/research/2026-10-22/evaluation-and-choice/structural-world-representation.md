# World-indexed representation over necessary Plenitude

Research note, 22 October 2026. Original arguments in this note have `source_id: misc`; no claim of historical novelty, independent checking, or formal verification is made. No repository records or generated files have been edited. This note is ordinary mathematics, not Lean work.

## 1. Fixed premises and recorded background

Throughout, **T** means the fixed Classicism C plus **boxed Plenitude**. The proved records identify this with C + boxed ND + Atomicity. Unboxed ND + Atomicity is not being substituted. Types are the repository's relational types; a relational type includes t and otherwise has the form tau = sigma_1 ... sigma_n t. Application below is left-nested when several arguments are displayed.

The proved-only `scripts.pmap.load_topic`/`Engine` query, with `necessary-plenitude-r` in the queried premise set and no optional engine background, gives boxed ND, BF, Atomicity, Actuality, Boolean Completeness, Rigid Comprehension and Strong Leibniz, together with Functionality and No Pure Contingency. Relevant recorded arrows include `c5-and-atomicity-imply-necessary-plenitude`, `necessary-plenitude-r-implies-necessary-distinctness-necessary-r`, `necessary-plenitude-r-implies-necessary-atomicity-r`, `necessary-plenitude-r-implies-necessary-actuality`, `necessary-distinctness-necessary-r-implies-necessary-barcan-r`, and the C5-and-Atomicity comprehension/completeness records.

Background sources: Bacon and Dorr, *Classicism*, draft 16 May 2023, §§1.5, 2.1–2.3, pp. 17–33; especially Intensionality pp. 17–18, C5/BF pp. 21–23, Atomicity p. 24, rigidity pp. 28–30, and concluding Plenitude equivalences p. 33. These sources supply the background, not authorship of the new arguments below. The atom-swap argument mentioned in §8 is already recorded from the Dorr/Goodsell–Yli-Vakkuri material; its generalization must not be attributed wholesale as a new discovery.

Write A(w) for Atom_t(w). For tau = sigma_bar t, put

* C_tau(w,X) := lambda x_bar. Box(w -> X[x_bar]);
* Enc_tau(X) := lambda w x_bar. A(w) and Box(w -> X[x_bar]);
* Dec_tau(F) := lambda x_bar. exists w (A(w) and w and F[w,x_bar]);
* A_up := lambda w x_bar. A(w).

All are well-typed lambda terms: Enc_tau has type tau -> t tau and Dec_tau has type t tau -> tau. No operation returning an individual is used. `C_tau` is a slice; the A(w) guard in Enc is essential for its normalization off the world atoms.

Call F of type t tau **admissible** when Rigid(F) and F <= A_up. This is an internal condition on an admitted relation, not quantification over arbitrary external families.

## 2. Small lemmas, with modal scope explicit

Under C5, equality and inequality at every type are noncontingent. BF carries pointwise necessary statements through the object quantifiers. Consequently A(w) is noncontingent: its definition uses only identities/order identities and quantifiers. Its weak-world definition is equivalent to the strong one here.

At every evaluation point exactly one atom is true. Existence is boxed Actuality. If atoms u and v are both true, u meet v is nonbottom. Atomicity of u and v makes their meet equal to each, so u=v. The same proof works throughout the modal range.

For an atom w and any proposition p,

    w -> (p iff Box(w -> p)).                                      (L)

The right-to-left implication uses T. For the other direction, w settles p: either w<=p or w<=not p. The second disjunct is incompatible with w and p. As A(w) is necessary and BF holds, the corresponding laws may be used uniformly with parameters at every world.

Under C5, a rigid relation is pointwise noncontingent, including on its negative instances. Persistence gives truth persistence and S5 gives falsity persistence. Conversely a relation whose instances are necessarily constant is rigid. For inextensibility: if every actual Y-instance necessarily satisfies Z but Y<=Z fails, BF extracts an actual tuple with possibly Y and not Z. Constancy of Y makes it an actual Y-instance, contradicting its necessary Z. This argument is available at every world.

It follows that coextensive rigid relations are identical: their current coextension is necessary pointwise, BF yields necessary universal coextension, and C's Intensionality gives identity. This is also available through the recorded Tame Rigidity consequences.

## 3. Exact representation theorem

**Theorem 1.** In T, Enc_tau and Dec_tau are mutually inverse between the entities of type tau and the admissible relations of type t tau:

    Dec_tau(Enc_tau(X)) = X;
    admissible(F) -> Enc_tau(Dec_tau(F)) = F.

Moreover Enc_tau(X) is always admissible. These are uniform definable maps, not choices of witnesses.

**Proof.** The displayed formula for Enc is pointwise noncontingent: A(w) is noncontingent and its other conjunct is boxed. Hence Enc is rigid by §2 and plainly lies below A_up.

Work at an arbitrary evaluation point and choose its unique true atom w. By (L), Enc(X)[w,x_bar] iff X[x_bar]. The existential in Dec has no other possible true-atom witness. Thus Dec(Enc(X)) and X are coextensive at every evaluation point. Intensionality identifies them.

Conversely let F be admissible. For an atom v, unique true-atomhood gives, necessarily,

    v -> (Dec(F)[x_bar] iff F[v,x_bar]).

Because F is rigid and v is possible,

    Box(v -> Dec(F)[x_bar]) iff F[v,x_bar].

For clarity, right-to-left uses necessity of the F-instance. Left-to-right: if that F-instance were false, its negation would be necessary, and the boxed implication would make v impossible. For nonatom v both F[v,x_bar] and Enc(Dec(F))[v,x_bar] are false by support. The two rigid relations are therefore coextensive and hence identical. QED.

**Consequences.**

1. X=Y iff their slices at every atom are identical. Equivalently, Enc(X)=Enc(Y).
2. Every *admitted rigid* family of extensions indexed by worlds pastes. No Choice axiom is needed beyond the fixed T consequences.
3. Enc preserves meets and joins and sends bottom to bottom and top to A_up. Negation becomes relative negation: Enc(not X)=A_up meet not Enc(X). Thus the Boolean algebra at tau is isomorphic to the Boolean algebra of admissible rigid subrelations of A_up.
4. “Every relation has a rigid world-indexed truth table” is therefore not a strict strengthening of boxed Plenitude. Requiring all *external* world-indexed families would be a different semantic/fullness condition.
5. The slice of an atom-world w is the unique rigid relation Y with Box(w -> coextensive(X,Y)). The uniqueness uses possibility of w and rigidity of both candidate slices.

Do not omit normalization. The unguarded slice C_tau(w,X) is top when w=bottom, so it is not supported on the atoms. Do not confuse a rigid graph of an operation with a rigid operation: in C5 the graph `f(x)=y` is rigid even when the proposition-valued operation f itself is contingent. In Theorem 1 the *uncurried relation* F[w,x_bar] is rigid.

## 4. Atomic normal form and the internal truth lemma

**Theorem 2.** Every atom of type tau=sigma_bar t is uniquely of the form

    h_(w,a_bar) := lambda x_bar. w and (x_bar=a_bar),

with w a proposition atom and a_bar an argument tuple. Conversely every such h is an atom.

**Proof.** If X is nonbottom, Diamond exists x_bar X[x_bar]. BF gives a currently quantified tuple a_bar with Diamond X[a_bar]. Atomicity at t supplies w<=X[a_bar]. The displayed h is nonbottom and lies below X, using necessary identity. For any Y, w settles Y[a_bar], so h<=Y or h<=not Y. Hence h is an atom. If X was an atom, h=X. Equality of two displayed atoms first gives equality of their existential projections, w=v. If the tuples differed, necessary distinctness would make their haecceity factors disjoint, contrary to nonbottomness; hence a_bar=b_bar. The empty tuple recovers exactly the proposition atoms. QED.

This is an explicit factorization of relational atoms as world-times-tuple points. It is not a claim that all external sets of those points are present.

For an atom w define At(w,p):=w<=p, equivalently Box(w->p). It satisfies the expected truth laws:

    At(w,not p) iff not At(w,p);
    At(w,p and q) iff At(w,p) and At(w,q);
    At(w,forall x phi(x)) iff forall x At(w,phi(x));
    At(w,Box p) iff forall v (A(v) -> At(v,p));
    At(w,x=y) iff x=y.

The quantifier law uses BF in one direction and ordinary instantiation in the other. The modal law uses atomic coverage/boxed Actuality and rigidity of Box p. The identity law uses C5. Thus the standard world-relative truth recursion is already internal to T. In particular, E_w(p):=w<=p is a much clearer definition of evaluation at a world than a choice-dependent description of an extension.

## 5. Universal extensions, separating predicates, and pattern cells

For a fixed R^{et}, define its pattern cell, for a rigid X^{et}, by

    c_R(X) := forall x (R x iff X x).

Define EU(R) by `forall rigid X, Diamond c_R(X)`. Define S(R) by: distinct atom-worlds have different slices of R. Equivalently, for atoms u,v, equality C_e(u,R)=C_e(v,R) implies u=v. The existential principles EU_e and S_e quantify R separately; their conjunction initially allows different witnesses.

**Theorem 3.** For rigid X:

* EU(R) says exactly that every pattern cell c_R(X) is nonbottom.
* S(R) says exactly that every pattern cell is either bottom or an atom.
* If S(R), every atom w is c_R(C_e(w,R)).
* Hence EU(R) and S(R) together identify the atoms exactly with the rigid e-properties, by X -> c_R(X), inverse w -> C_e(w,R).

**Proof details.** Different rigid X,Y are not coextensive, so they differ on an argument; this difference is necessary. Hence their pattern cells are disjoint. An atom w lies below c_R(X) iff its slice equals X, by the uniqueness statement after Theorem 1. Thus S says at most one atom lies below each cell. In an atomic Boolean algebra, a nonzero element with exactly one atom below it equals that atom: otherwise subtracting the atom leaves a nonzero element and hence another atom. This proves both directions and the formula for each w. QED.

Under S(R), every proposition p has the normal form

    p = exists X (Rigid(X) and c_R(X)<=p and c_R(X)).

It is the join of the complete literal-pattern cells below p. Thus R may be described as a world-separating family of proposition-generators indexed by individuals. EU adds realization of every complete truth assignment. Together they give an *internal* free-complete-atomic-algebra picture. That phrase must retain the Henkin qualification; it is not an assertion of external powerset fullness.

**Cantorian obstruction.** EU at a domain sigma is impossible if there is an internally represented injection from atom-worlds into sigma. In particular EU_tau fails for every relational argument type tau. The definable injection is j(w)=lambda z_bar.w. Given a proposed universal R^{tau t}, form

    X(y) := exists w (A(w) and y=j(w)
                      and not Box(w -> R(j(w)))).

X is rigid: its ingredients are noncontingent and BF closes the quantifier. At the atom w it disagrees with R at j(w), by (L). Hence it cannot be possibly coextensive with R. Injectivity of j uses only inhabitedness of the finitely many argument types. This is an original diagonal argument, not a recorded Maximalism result.

## 6. One simultaneous EU-and-S witness under Functional Choice

**Theorem 4.** Over T plus Functional Choice (hence over boxed Functional Choice), EU_e and S_e imply that some single R satisfies both.

Here is a fully internal Schroeder–Bernstein proof. Let A be the atom predicate on t and B the rigid predicate on et. An S-witness supplies an injection f:A->B by taking slices. An EU-witness supplies a surjection g:A->B. Functional Choice, at output type t, selects i:B->A with g(i(b))=b. Extend the selecting relation by an arbitrary fixed atom off B to use the total formulation of Choice. Then i is injective.

All relevant graphs are rigid because identities, A and B are noncontingent. Define A0=A minus i[B]. Let D be the intersection of all *rigid* A-subsets containing A0 and closed under i composed with f. This is a legal impredicative lambda definition at tt, with the candidate subsets quantified at tt. It is rigid by C5 and BF. A itself is a candidate, so D is included in A. The usual intersection proof gives A0 included in D and closure of D. More precisely,

    D = A0 union i[f[D]].

For the reverse inclusion in this displayed equality, the right side is itself a candidate: it contains A0, is included in D, and its successor under i composed with f belongs to i[f[D]]. Minimality of D gives the claim.

Define a rigid graph H on A times B by

    H(a,b) iff (D(a) and b=f(a))
                 or (A(a) and not D(a) and a=i(b)).

It is total and single-valued: outside D an a cannot lie in A0, and injectivity of i gives its unique inverse image. Each branch is injective. The branches have disjoint images: if f(a)=b and a'=i(b) with D(a), closure puts a' in D. It is surjective: for b in B, if i(b) is outside D use its inverse branch; otherwise the displayed identity for D and i(b) notin A0 give i(b)=i(f(a)) for some a in D, so b=f(a).

Now put F(a,x):=exists b(H(a,b) and b(x)). F is a rigid atom-supported family. Theorem 1 pastes it to R=Dec(F), whose slice graph is H. Therefore that one R has a bijective slice map and satisfies EU and S together. No external powerset, untyped set collection, or unproved cardinal comparison is used. Choice occurs only in selecting the right inverse of g; the Bernstein construction itself is choice-free.

**Weaker sufficient assumption (parent/algebraic-core refinement).** Full Functional Choice is stronger than this proof needs. It suffices that the world-profile equivalence of the chosen universal R have an admitted transversal. This gives the section i:B->W used above; every later step is choice-free. In particular the propositional complete-subalgebra retraction principle Ret_t suffices, because its dual characterization supplies a transversal for every admitted equivalence on world atoms. Thus over T plus Ret_t, EU_e and S_e imply one exact witness. Ret_t is strictly weaker than full Choice and is not interchangeable with Intensional Choice. The ordered-endpoint model in §20 must fail Ret_t: its surjective profile map has no admitted section, since such a section would inject the larger finite fixed-point set of U into the smaller fixed-point set of W.

## 7. Arity transfer and a strict hierarchy despite the Infinity Schema

Let EU_k say that one k-ary relation on individuals realizes every rigid k-ary extension at some world, for fixed positive finite k.

**Theorem 5 (transfer).** If a rigid relational graph injects B-tuples into A-tuples, then EU_A implies EU_B. Pull the universal A-relation back along the injection. For a rigid B-pattern X, extend X to A by false off the injection's image. The resulting A-pattern is rigid and its realization gives the required B-pattern. This argument uses relational graphs, so it does not postulate the forbidden type e->e.

Consequently EU_k implies EU_j for j<=k by padding tuples with fixed individuals. A represented rigid injection e^k -> e makes EU_1 imply EU_k. Thus an internal pairing assumption collapses the finite-arity hierarchy.

**Theorem 6 (strictness with the recorded Infinity Schema).** For each k>=1, boxed Functional Choice plus `infinity-e` plus EU_k does not imply EU_(k+1), relative to ordinary ZFC metatheory.

For every integer n>=2 take a standard full S5 model with individual set E_n of size n and world set W_n=P(E_n^k). All admitted relational domains are full. Identity is rigid, every relation algebra is atomic, and all forms of Choice hold at every world (the relevant domains are finite at every fixed type). The membership relation R_n(w,a_bar) iff a_bar in w witnesses EU_k. No (k+1)-ary relation can realize all rigid extensions, since it has at most |W_n|=2^(n^k) world extensions but there are 2^(n^(k+1)) rigid patterns.

Expand these finite models by a world sort, evaluation, application and the logical/lambda operations, and take a nonprincipal ultraproduct over n. It is a many-sorted Henkin S5 model. Los's theorem preserves each C axiom/schema instance, each boxed Choice instance, EU_k and failure of EU_(k+1). It satisfies every fixed finite lower bound on the individual domain and hence the entire `infinity-e` schema. Thus the hierarchy remains strict even with the user's preferred boxed Functional Choice.

The *quantified* `axiom-of-infinity-e` is different and is false in these ultraproducts, as it is false in every factor. One must not infer pairing from the Infinity Schema. Section 10 supplies the separate internal well-order argument giving pairing from the stronger quantified Infinity axiom plus boxed Functional Choice.

All finite arities can consistently hold together: for any E use the full S5 model W=P(E^{<omega}), with the coordinate membership relation at each arity. Under ZFC all boxed Choice holds. For infinite countable E, W=P(N) suffices after fixed codings of finite tuples. Neither assertion makes all-type EU consistent; the diagonal of §5 still applies to relational argument types.

## 8. Rigid parameters: a sharp boundary

The recorded proof of No Pure Contingency exchanges two atom-worlds and extends the exchange by conjugation to every type, fixing individuals. Using Theorem 1, the same construction extends an internally represented arbitrary permutation pi of the atom-worlds: at t, send the truth set of p forward along pi; at sigma->tau conjugate application by the already constructed maps at sigma and tau. The inverse uses pi^{-1}. The type recursion is finite and each stage is represented by a lambda term. Identity, application, quantifiers, lambda abstraction and the modal operators are preserved. This is a generalization of the recorded atom-swap proof, not an independent provenance claim for that proof.

Every rigid relation whose arguments are individuals only is fixed by these world permutations. Therefore the same atom-swap argument proves a parameter version of No Pure Contingency: a formula with parameters consisting of individuals and rigid finite-e-ary relations, and no other nonlogical parameters, is necessary if true. One argues by induction on the pure term with these fixed parameters; a contingent truth would have atoms on its positive and negative sides, exchanged by an automorphism fixing the parameters.

The unrestricted all-type version is false in every model with more than one atom-world. Given an atom w, Y:=lambda p(p=w) is a rigid relation of type tt. But the sentence with this rigid parameter

    exists p (Y p and p)

is exactly w, which is contingent when there is another atom. Thus higher-order rigidity does not mean that the parameter carries no world information.

## 9. Definition audit and limits

These are equivalent reformulations under the explicitly fixed T, not silent replacements in the database:

* world evaluation: At(w,p):=w<=p, with A(w) as its domain condition;
* world slice: C_tau(w,X):=lambda x_bar.At(w,X[x_bar]);
* normalized truth table: Enc_tau(X), with the atom guard;
* universal extensions: all rigid-pattern cells c_R(X) are possible;
* world separation: every rigid-pattern cell is bottom or an atom;
* joint EU/S: the complete-pattern cells are exactly the atoms, each once.

No external-fullness conclusion follows. For example, a countable elementary substructure of a countable-language expansion of a full infinite S5 model is a countable Henkin model preserving C, boxed Plenitude, and all internal Choice instances. It still has infinitely many represented worlds, every world singleton, and evaluation separating distinct propositions, by elementarity. Its proposition domain is countable, whereas the external powerset of its countably infinite world domain is uncountable. Its internal Enc/Dec theorem remains exact.

Likewise the ultraproduct in §7 has all internal boxed Choice but is not a full powerset model. Finite factors being full does not make their ultraproduct externally full.

No infinitary syntax has been added here. The quantifier `forall x` in a pattern cell is an ordinary object-language quantifier. Describing it as a complete conjunction of literals is explanatory, not permission to replace C by an infinitary proof system.

## 10. Pairing from quantified Infinity and Choice

This section was added after the initial report. It supplies the previously conditional step in §7; it does not weaken the distinction between the Infinity Schema and the quantified Infinity axiom.

**Theorem 7.** Over boxed Functional Choice and `axiom-of-infinity-e`, there is a rigid relational graph injecting e times e into e. Consequently all positive finite-arity EU_k are equivalent in this stronger theory.

The proved-only Engine gives Well-Ordering (indeed Modal Well-Ordering) from boxed Functional Choice. Rigid Comprehension lets us use a rigid well-order with the same extension. Everything in the following proof is expressed with predicates and relational graphs. Tuples can be coded by their haecceities when a one-sorted presentation is wanted. No forbidden operation type e->e is postulated.

We use four elementary finiteness facts: invariance under bijection; a subset of or injection into a finite set is finite; adjoining one element to a finite set remains finite; and a product of two finite sets is finite. These are internal theorems for the given Fregean `FiniteCardinality`, not assertions that every Henkin-finite set is externally standard-finite. Here are the induction obligations explicitly.

* First prove by induction on FiniteCardinality(Z) that Z is invariant under represented bijections of its instances. The zero case is emptiness. For Suc(Z), remove the successor-witness a from the source and its unique image b from the target, restrict the bijection, apply the induction hypothesis, and restore b. In particular these cardinal predicates are extension-invariant at the evaluation point; no identity of merely coextensive arbitrary intensions is assumed.
* Adjoining a point preserves finiteness: if it was already present use extension-invariance; otherwise use the successor cardinal. For injection-heredity, induct on the target's finite cardinal. Remove its successor-witness a. If the injecting source has a preimage b, remove b and apply induction to the restricted injection, then restore b. If not, the whole source already injects into the smaller target. This proof works across any two fixed types, with finiteness defined at their respective cardinality types.
* Finite unions follow by induction on one finite cardinal, removing its successor-witness, applying induction to the smaller union, then restoring the point.
* For a product, code pairs by haecceities. Induct on one factor, splitting (X union {a}) times Y into X times Y and the fiber {a} times Y. The latter is in represented bijection with Y and is finite by the cross-type result; finite union finishes the successor step.

All these induction predicates are admitted formulas quantifying over represented graphs at fixed types. The least-inductive-property clause of FiniteCardinality supplies the induction. Thus the argument applies even in nonstandard Henkin models. “Infinite” below means the negation of this internal finiteness.

We also use internal Schroeder–Bernstein, proved in §6 without Choice once two injections are supplied, and the following comparison lemma.

**Well-order comparison lemma.** Any two represented well-orders have an initial-segment order-isomorphism whose domain or range is the whole respective field. To prove it, take the union of all order-isomorphisms between initial segments. Any two such isomorphisms agree on their common domain: at the least point of disagreement their two values would have exactly the same predecessors, impossible in a linear order. The union is therefore an order-isomorphism of initial segments. If both sides were proper, the least omitted point on either side could be paired, giving a larger initial-segment isomorphism, contrary to the definition of the union. The union is represented by the lambda formula saying that some represented initial-segment isomorphism contains the pair. This proves the lemma internally; no external ordinal is used.

**Proof of Theorem 7.** Suppose an internally infinite well-ordered E has no represented injection E^2->E. Call a subset *bad* if it is infinite and has no such square injection into itself. Among the bad proper initial segments of E take the one with least endpoint; if none exist take E itself. Call the resulting bad initial segment K. The endpoint condition is a represented predicate, so the choice of its least member uses only the given well-order. Every proper initial segment of K is either finite or admits a square injection.

No proper initial segment L of K is equipotent to K: if it were, it would be infinite and would inherit badness from K by transporting graphs through the bijection, contradicting minimality.

K has no greatest element. Otherwise K=L union {m}, where L is a proper initial segment. L cannot be finite, since adjoining m would make K finite. Hence L has an injection q:L^2->L. Choose a!=b in L. There is an injection K->L^2 taking x in L to (x,a) and m to (a,b). Compose with q to inject K into L. The inclusion L->K and Schroeder–Bernstein make L equipotent to K, contradiction.

Well-order K^2 by the lexicographic triple

    (max(a,b), a, b).

This is a represented well-order: in any nonempty represented set of pairs, first minimize the maximum coordinate, then the first coordinate, then the second. For a pair (a,b), put m=max(a,b) and J={x in K:x<=m}. Since K has no greatest element, J is a proper initial segment. The predecessor set P of (a,b) in this pair-order is included in J^2.

The proper segment J has a least omitted endpoint, so the minimal-bad-initial-segment condition applies to J itself; there is no unmentioned appeal to an external cardinal-minimum principle here.

There is no injection K->P. If J is finite, P is finite and such an injection would make K finite. If J is infinite, minimality gives an injection J^2->J. An injection K->P would therefore inject K into J; inclusion and Schroeder–Bernstein would make K equipotent to its proper initial segment J, again impossible.

Compare the well-orders K and K^2. An initial-segment isomorphism with all of K^2 as its domain would inject K^2 into K, contrary to badness. Thus comparison embeds all of K as an initial segment of K^2. Its range cannot be the whole product, again by badness, so it is the predecessor set of some pair. This injects K into one of the forbidden P's, contradiction. No bad E exists.

Apply this to the individual domain with its represented well-order. The quantified Infinity axiom gives its internal infinitude. The resulting injection graph may be rigidified; C5 preserves its functional and injective character because identities and its rigid membership facts are noncontingent. Iterate the pairing graph to inject each finite e^k into e. Theorem 5 and the converse padding injections make EU_1 equivalent to every EU_k. QED.

This proof proves the relevant ordinary mathematical implication within the admitted comprehension resources; it is not a claim of Lean verification. It also explains why §7's pseudofinite ultraproducts cannot be counterexamples: their individual field is internally finite.

## 11. An expressly infinitary extension: standard finite cardinalities

This section is **beyond fixed C**. It records the parent research lane's proposed countable extension and its consequence, rather than quietly importing infinitary rules into the preceding theorems.

Let C_omega allow countable disjunctions with only finitely many free object variables overall, lambda comprehension for those formulas, countable disjunction introduction/elimination, and the corresponding extension H_omega of the H theoremhood side condition in Logical Equivalence. Treat each displayed type as fixed. The logical rules and comprehension extension are substantive; merely writing an infinitary abbreviation in ordinary C would not suffice.

At the cardinality type used for a fixed domain sigma put

    N_omega(Z) := bigvee_(n<omega) (Z = Suc^n(0)).

This formula has only Z free. It is an admitted inductive property: it contains zero and is successor-closed, by countable disjunction elimination followed by the next disjunct. Consequently the impredicatively defined FiniteCardinality is included in N_omega. Conversely each standard numeral is in FiniteCardinality by ordinary finite induction, and countable disjunction elimination gives the reverse inclusion. Thus

    FiniteCardinality(Z) iff bigvee_(n<omega) Z=Suc^n(0).

With this precise extension, the Infinity Schema at e implies the quantified Axiom of Infinity at e. For each standard n, its n+1-instance refutes the assertion that the universal individual property has cardinality Suc^n(0). Countable disjunction elimination and the displayed equivalence exclude every finite-cardinality witness. The reverse implication was already available in ordinary C.

Combining this with Theorem 7: in C_omega plus boxed Functional Choice and the Infinity Schema, all positive finite-arity EU principles are equivalent. This contrasts with their strict hierarchy over finitary C plus the same Infinity Schema (§7). Full S5 models in ordinary ZFC interpret the countable operations and provide consistency examples for the extension. Ordinary Henkin compactness/ultraproduct preservation must not be reapplied to these countable formulas.

## 12. A much weaker retraction principle: exact equivalence with modal .2

This section concerns **C alone**, before any optional C5 or Plenitude premise. It was developed jointly with the parent research lane. Use `BR` for the existence of a two-valued endpoint retraction:

    exists E^{tt} [E(top)=top and E(bottom)=bottom
                  and forall p (E(p)=top or E(p)=bottom)].

No preservation of conjunction, negation or truth at the evaluation point is required. Calling this a “Boolean homomorphism” would be incorrect. “Two-valued retraction” describes its actual content.

**Theorem 8.** Over C, BR is equivalent to the universally quantified modal convergence axiom .2:

    forall p (Diamond Box p -> Box Diamond p).

**BR implies .2.** Fix a currently quantified proposition p. The contrary to .2 at p is the conjunction Diamond Box p and Diamond Box not p, equivalently Diamond(p=top) and Diamond(p=bottom). If E(p)=top at the base point, NI makes that identity necessary. NI also makes E(bottom)=bottom necessary. The possibility p=bottom would identify E(p) with E(bottom), contradiction. If E(p)=bottom, the analogous argument using the necessary identity E(top)=top blocks the possibility p=top. The range condition excludes both cases of the alleged conjunction. Thus .2 holds for every currently quantified p. No BF, ND or optional necessitation has been used.

**.2 implies BR.** Define E:=lambda p.Diamond Box p. Apply .2 to the proposition Box p. Since C proves 4, Diamond Box p implies Diamond Box Box p, and this instance of .2 gives

    E(p) -> Box E(p).

On the other hand not E(p) is Box not Box p, and 4 directly gives

    not E(p) -> Box not E(p).

Classical excluded middle therefore makes E(p) either top or bottom, using the C-identifications Box q iff q=top and Box not q iff q=bottom. The endpoint equations follow from the modal theorems for top and bottom. This constructs the required retraction without Choice. QED.

ND at type t already implies BR: take E:=lambda p.Diamond p. If p differs from bottom, ND makes that difference necessary; if p equals bottom, NI and substitution give E(p)=bottom. This observation is not needed for the equivalence, but makes the weakness relative to C5 transparent.

**Strictness model.** Use the full action model on the two-object chain 0->1, with one fixed individual. At object 0 the propositions are subsets of {0,1}; at terminal object 1 they are the two truth values. Let E evaluate a proposition at the terminal world and return the corresponding constant proposition. More explicitly its truth at either stage is the terminal truth of its input; at stage 1 it is the identity on the two truth values. This is an admitted full-model intension and is a two-valued endpoint retraction. But the proposition {0} is distinct from bottom at 0 and becomes bottom at 1, so ND fails. Thus BR/.2 is strictly weaker than ND, hence also strictly weaker than ND plus Actuality or boxed Plenitude. This model is C-sound by the full action construction (Classicism §3.5, pp. 58–61).

**Pure Maximalism excludes BR/.2.** Let P be the closed pure sentence “there are at least two individuals.” A one-world full Henkin model with two individuals satisfies Box P; one with one individual satisfies Box not P. Hence each of those closed pure sentences is consistent with the fixed C. The possibility form of pure Maximalism gives both Diamond Box P and Diamond Box not P. This is exactly the failure of .2 at P, and Theorem 8 excludes BR.

This is a precise incompatibility with a simple natural modal principle. It does not establish an absolute ordering of theories as “top” and “bottom,” nor does consistency of the alternatives prove their truth. It provides an independently checkable mathematical basis for comparing the structures the two theories permit.

**Theorem 9 (a simpler retraction definition and Maximalism's bivalence obstruction).** Over C, BR is equivalent to the existence of any bivalent operation E^{tt} with two different currently attained values. If E(a)=top and E(b)=bottom, define

    F(p) := E((p and a) or (not p and b)).

F remains bivalent at every current argument, and its endpoint values are top and bottom. Hence it witnesses BR. The converse is immediate. No meet/complement preservation by E is assumed; the interpolation is performed on its input.

More generally, a bivalent predicate E^{tau t} with two different current values gives BR whenever tau is relational. Choose A,B with E(A)=top and E(B)=bottom, and interpolate pointwise:

    J(p) := lambda x_bar[(p and A[x_bar]) or
                         (not p and B[x_bar])].

Then J(top)=A and J(bottom)=B by the Boolean identities of C, so p↦E(J(p)) witnesses BR.

Conversely BR yields a nonconstant bivalent predicate on each relational tau: fix one argument tuple a_bar and put F(X):=E(X[a_bar]). It separates top_tau and bottom_tau. For the empty tuple this is E itself. Thus .2/BR is equivalent, at **any fixed relational type**, to the existence of even one nontrivial bivalent classification of its current objects. Its failure means that every admitted bivalent test at that type is pointwise constant on the current domain.

Consequently pure Maximalism proves, at every relational tau,

    forall E^{tau t}[(forall x(E x=top or E x=bottom))
                     -> forall x y(E x=E y)].

The same statement holds at tau=e under Maximalism: if E(a)=top and E(b)=bottom, NI makes both identities necessary. Maximalism supplies the possibility of the closed pure singleton-domain sentence forall x y^e(x=y), because a one-world singleton model satisfies it. At that world a=b, contradicting the necessary unequal endpoint values.

**Essential limitation:** the conclusion is constancy on the *currently quantified domain*. It does not say E equals the constant-top or constant-bottom relation as an object. Such an inference would use Functionality/BF, unavailable in bare C or pure Maximalism; a relation can have additional future arguments. The proof excludes a nontrivial current bivalent classification, and nothing stronger is asserted.

**Gallin-rigidity definition audit (over C, not just T).** For a finite-arity relation F, Gallin rigidity, meaning Persistent(F) and Persistent(not F), is equivalent to

    Box forall x_bar (F[x_bar]=top or F[x_bar]=bottom).

At every accessible point, excluded middle plus persistence of the positive and negative instances gives the displayed bivalence; conversely an endpoint-valued instance is necessary when true and necessarily false when false. The quantifier is already inside Box, so no Barcan inference is being used. This is the Gallin convention, not an unqualified redefinition of the repository's different `Rigid` predicate.

Under pure Maximalism, every Gallin-rigid relation therefore has either empty or universal current extension. For several argument places, vary one coordinate at a time: each partially applied unary predicate is bivalent and hence current-pointwise constant by Theorem 9. A finite chain of coordinate replacements makes any two tuples have the same value. The same Functionality guardrail applies: empty/universal current extension is not identity with the bottom/top relation object.

**Related exact definition of ND.** At any fixed type sigma, ND_sigma is equivalent in C to separation of every pair of distinct current objects by a bivalent predicate. Under ND, the haecceity F(z):=(z=x) is bivalent by NI and ND and separates x from each distinct y. Conversely endpoint separation alone suffices: NI makes F(x)=top and F(y)=bottom necessary, so x and y cannot become identical. The global bivalence clause is therefore not needed in the reverse direction.

There is a type-e guardrail. Maximalism can hold with only one current individual: `coalesced-single-individual-root` is a proved source model (Classicism §2.6, pp. 41–42 and n. 61; Appendix E, p. 83). ND_e is vacuous there. The bivalence obstruction therefore does not imply failure of ND_e without two current individuals. Relational types always have their distinct top and bottom, so this exception does not apply to them.

## 13. Gallin model transfer and a simpler Infinity definition

This section audits the forward model translation; the separate rigidity research lane is treating the general reconstruction in the other direction.

Take an extensional Gallin model with nonempty individual sort e, nonempty world sort w, and Boolean sort o. Interpret the C type t as w->o and recursively interpret each admitted C arrow sigma->tau by the ordinary Gallin function type between the translated types. Translate C truth pointwise at a world, C equality as genuine equality of the translated objects (a constant world proposition), and C quantifiers pointwise over their constant typed domains. Then

    Box p = forall v^w p(v),

because C defines Box p as equality of p with the constantly true proposition.

This interpretation gives C5. It gives Atomicity at every C relational type: a nonzero relation has a true world/argument point, and Gallin lambda comprehension supplies its singleton-point relation. The world singletons themselves are lambda v(v=a). Hence it gives T=boxed Plenitude. This argument works in extensional **Henkin** Gallin models as well as full ones; it uses lambda closure and genuine extensional equality, not all external powersets. If the Gallin model satisfies its extensional functional-choice schema, the translated C satisfies boxed Functional Choice: at each world a, select outputs from the current relation U(x,y)(a). In full ordinary function models this follows from metatheoretic AC.

The finite models in §7 can be expanded to full finite Gallin models before taking their ultraproduct. The ultraproduct is therefore also a Henkin Gallin countermodel to the claim that the Infinity Schema plus Choice supplies pairing. Its e-domain is externally infinite, but internally Frege-finite. An assumption merely that the external domain is infinite does not repair that failure in general Henkin semantics. In full Gallin semantics, by contrast, the impredicative finite-cardinality predicate has precisely the standard finite extension, so external infinitude and quantified internal Infinity coincide.

**Definition improvement under the chosen strong base.** Over boxed Functional Choice, `axiom-of-infinity-e` is equivalent to the existence of an injective, nonsurjective self-relation on individuals. Write this as a functional graph I^{eet}, not as a term of forbidden type ee.

The forward direction follows from Theorem 7. If q injects e^2 into e, take distinct a,b and define I(x,y) iff q(x,a,y). This is injective, and the unique q(a,b)-value is outside its range by injectivity of q and a!=b. Conversely an injection of an internally finite set into itself is surjective, by induction on its finite cardinal; hence such an I excludes the quantified finiteness of the individual domain. The graph can be rigidified in T.

Thus a familiar Dedekind-infinity formulation is a simpler equivalent definition **under boxed Functional Choice**. The equivalence is not asserted in bare C or in choiceless settings, and it does not turn the finite-n Infinity Schema into quantified Infinity in finitary C.

**Two different fullness directions.** The mixing-model research lane supplies a useful further distinction. In a supported Gallin/Henkin hierarchy whose symmetry group fixes W, allow supports of size <kappa, with kappa regular and |W|<kappa. Any external W-indexed family of admitted rigid extensions has an admitted pasted relation: choose supports for its rows and take their union, still of size <kappa. Nevertheless object-domain Choice can fail (for example countable supports, countably many worlds, and uncountably many independently swappable individual pairs). Thus even external fullness in the *world-indexing* direction does not imply full powersets or selection in the *argument-object* direction. This is a model-construction observation from the mixing lane, not a new conclusion inferred merely from Theorem 1.

## 14. Independent audit: complete subalgebra retractions are Choice

The algebraic-core lane proves this result in §§16 and 18 of `research/2026-10-22/evaluation-and-choice/structural-algebraic-core.md`. The argument below independently checks the type-sensitive converse against the normal-form theorem here. It is collaborative original research, `source_id: misc`, not a claim of independent human checking or Lean verification.

For any relational type tau, let B_tau denote its internally complete atomic Boolean algebra. A rigid predicate A on B_tau specifies an internally complete Boolean subalgebra when it contains the endpoints and is closed under complements and all admitted joins/meets of its admitted subfamilies. A complete Boolean retraction onto A is an admitted complete unital Boolean homomorphism H:tau->tau with

    forall p A(Hp),
    forall q(Aq -> Hq=q).

Range equality and idempotence follow; they need not be separate axioms.

**Theorem 10.** Over T, the schema saying every such subalgebra at every relational type admits a complete Boolean retraction is equivalent to boxed Functional Choice.

**Audit of the forward construction.** Complete subalgebras of an internally complete atomic Boolean algebra correspond to admitted equivalence relations on its atoms: two ambient atoms are equivalent when they agree on all subalgebra elements. The subalgebra consists exactly of unions of these equivalence classes. This uses admitted meets of the subalgebra members containing a fixed atom, not an external powerset assumption. A transversal supplies a class-selector c. The complete Boolean homomorphism whose dual atom map is c has class-invariant values and fixes all class-invariant elements, hence is the required retraction. Boxed Functional Choice supplies the transversal.

**Audit of the converse.** If H retracts onto the subalgebra associated with an atom-equivalence E, let f be its dual atom map. Class-invariance of every Hp gives f(a)=f(b) whenever aEb: the atoms f(a),f(b) agree below every p, so evaluating at either atom separates them unless equal. Since H fixes the subalgebra, a and f(a) agree on every subalgebra member; hence aEf(a). Thus f is a class-selector, and the admitted predicate f(a)=a is a transversal.

Now let S be an arbitrary current equivalence on objects of any type sigma, including e. T permits rigidifying its current extension, so assume S rigid. Fix a world atom a. The operation

    j(x) := lambda y^sigma(a and y=x)

injects the sigma-objects into the atoms of B_(sigma t), by Theorem 2. Define an equivalence on those atoms by

    E(U,V) iff U=V or
                 exists x y(U=j(x) and V=j(y) and Sxy).

Its classes on the j-image are exactly the S-classes, and its other classes are singleton atoms. It is admitted and rigid. The assumed subalgebra retraction gives an atom transversal C; its pullback x↦C(j(x)) is a transversal for S. Hence Transversal Choice holds at every type. The recorded equivalence with Relational Choice, together with T's Plenitude, gives Functional Choice. Each closed pure schema instance boxes by T's No Pure Contingency; optional assumptions have not been illicitly necessitated. QED.

Two precise guardrails matter. First, “all complete Boolean inclusions split” here includes inclusions of internally represented subalgebra fields. Restricting the phrase to arrows between entire type algebras B_rho and B_tau has not been shown equivalent: an arbitrary subalgebra field need not itself be an entire type algebra. Second, the direction of the Boolean arrow matters. A complete Boolean SURJECTION has an injective dual atom map. Inverting that map on its image and assigning one fixed default atom off the image supplies a left inverse without Choice; unique-value comprehension and Plenitude suffice. Dually every such surjection between nontrivial internally complete atomic Boolean algebras splits already in T. A complete Boolean INJECTION has a surjective dual atom map; splitting it chooses a point in each fiber. This is the Choice-bearing assertion.

## 15. Canonical reverse representation: what is immediate and what requires coding

The following independently audits the model-theoretic meaning of Theorems 1–2. It starts with a pointed extensional model of T and uses its actual typed domains and application operations. No external fullness is assumed.

Let W be the external set of the model's propositional atoms. For each proposition p put

    p-hat := {a in W : a <= p}.

Atomicity makes p↦p-hat injective: distinct propositions have a nonzero Boolean symmetric difference, below which lies an atom. Boolean operations become ordinary set operations. Admitted joins and meets become their actual unions and intersections because an atom is completely prime for admitted joins. This statement does not quantify over arbitrary external families absent from the model.

There is a unique currently true atom a0, by Actuality. The current truth of p is exactly a0 in p-hat. For any atom a, its truth assignment is p↦(a<=p). It obeys ordinary Boolean truth clauses; BF gives the pointwise quantifier clause

    a <= forall x phi(x)  iff  for every actual x, a <= phi(x).

The box clause is universal quantification over W, since Box p holds at every atom iff p=top. Equality is constant across W, using necessary identity and distinctness.

Retain the individual domain. Recursively turn every higher-type object F into its application function on the already represented lower-type domain. This is well-defined, and Functionality makes it faithful: objects inducing the same function are equal. Application and lambda abstraction therefore receive their ordinary function interpretations. This gives a faithful constant-domain world-indexed Henkin presentation of the original C-reduct, with t interpreted by the represented subsets of W and with the original point interpreted by a0. All original formulas have the same truth by induction. The construction is canonical up to the chosen isomorphisms of typed domains.

There is a distinction between this result and immediately announcing a full Gallin model. Gallin's complete type grammar contains additional arrows involving the world and Boolean sorts, and arrows with individual output that C omits. Those extra domains are not literally present among C's original types. They can be added by a graph-coding construction, but that construction should be stated.

Here is the graph construction in detail. For every Gallin type alpha define a C code type c(alpha) and a rigid field predicate P_alpha. Set

    c(e)=e,        P_e(x)=top;
    c(w)=t,        P_w(x)=Atom(x);
    c(o)=t,        P_o(x)=(x=top or x=bottom);
    c(alpha->beta)=c(alpha)c(beta)t.

The field P_(alpha->beta) consists of rigid relations F which are empty off P_alpha times P_beta and are total and single-valued from P_alpha to P_beta. All these clauses can be boxed; over T the equivalent current formulation is also stable. Thus P_(alpha->beta) is itself rigid. Interpret an arrow object F as its graph function, and interpret application by its unique graph value. Extensional equality follows because coextensive rigid graph relations are identical. Every field is nonempty: choose one individual, one world atom and one Boolean endpoint initially, then use the constant graph at the recursively chosen codomain element. This is a recursive construction of defaults, not an internal Choice principle.

Closure under all Gallin terms and quantifiers is verified by a simultaneous value-relation translation. A term u of type alpha has a C formula Val_u(z), with z:c(alpha), asserting its value. A variable has value relation z=x. Application has value relation

    Val_(f u)(z) iff exists G y
       (Val_f(G) and Val_u(y) and G(y,z)).

By induction the values G,y are unique and belong to their fields, so the graph's unique-value clause gives a unique z. For lambda x.u the graph is supplied directly by C lambda comprehension:

    F(x,z) iff P_alpha(x) and P_beta(z) and Val_u(z).

It is total and functional by the induction hypothesis. It is rigid because the translated atomic clauses are identities or membership in already rigid graphs, and Boolean operations and field-restricted quantification preserve rigidity in T. The latter fact uses BF and fixed domains, not an unmentioned Choice axiom.

The Boolean logical constants have their finite truth-table graphs. Equality at each type has the bivalent graph determined by actual equality of its codes. For the Gallin universal quantifier at alpha, its truth on a coded predicate F:alpha->o is the C formula

    forall x(P_alpha(x) -> F(x,top)).

The quantifier's graph sends F to top when this formula holds and to bottom otherwise. This graph is admitted by lambda comprehension, rigid by BF, and functional by excluded middle. Existential quantification is analogous. Thus quantification over a newly coded function domain is simply a C quantifier restricted to its represented field P_alpha. This is the missing closure check: the graph-coded domains do satisfy the entire Henkin comprehension and quantifier semantics of the Gallin language, including arbitrarily iterated new arrows. A forbidden C operation returning e is never required; it is represented by an allowed C relation whose last type is t.

To verify that this expansion recovers the original C model exactly, construct represented isomorphisms i_sigma by induction on the original C types. At e use the identity graph lambda x y(x=y), not an operation of forbidden type ee. At t, send p to the rigid Boolean graph

    G_p(a,b) iff Atom(a) and
       ((a<=p and b=top) or (not a<=p and b=bottom)).

Conversely a graph G:w->o decodes to the proposition

    exists a(Atom(a) and G(a,top) and a).

Atom evaluation and Theorem 1 show these are inverse. The graphs of these isomorphisms are rigid and admitted. For an original arrow sigma->tau, send F to the coded graph which, on input i_sigma(x), returns i_tau(Fx). Comprehension constructs this graph from the represented isomorphisms. Conversely pull any coded graph back along i_sigma and i_tau. This produces an admitted rigid total single-valued relation U:sigma tau t. Since tau is relational, Plenitude gives an original operation F representing U; Functionality makes it unique. The original arrow domains are therefore neither shrunk nor enlarged. Inductively all applications, lambda terms, logical operations, and original quantifiers agree with their Gallin interpretations.

**Theorem 11 (canonical Henkin Gallin expansion).** Every pointed typed algebraic model of T, with its actual domains quotiented by its equality if necessary, admits the foregoing extensional Gallin Henkin expansion whose world sort is its propositional atoms and whose C-reduct is isomorphic to the original model. Its designated world is the unique currently true atom. The forward translation of §13 and this reverse construction establish the matching model presentations. This is a semantic representation theorem, not a categoricity or external fullness theorem. The construction is canonical up to the coding isomorphisms and harmless choices of default inhabitants.

In neither direction are all external subsets of W, all external maps between domains, or all external world-indexed families forced to exist. The countable elementary-submodel examples remain counterexamples to those claims. For models presented over a larger original frame, this theorem reconstructs the pointed T-model's internally discernible atomic-world presentation; it need not preserve redundant original frame points that agree on every admitted proposition.

**Choice correspondence.** In this canonical graph-coded expansion, boxed C Functional Choice is equivalent to ordinary Gallin/Henkin functional Choice at every type, including the added individual-output arrows. In the forward direction translate a total Gallin relation to a C relation between its rigid code fields. Extend it off its input field using one codomain default. C Relational Choice, which follows from Functional Choice and covers individual outputs as relational graphs, gives a selector graph. Rigidify its current extension and restrict it to the code fields. This is precisely a member of the coded Gallin arrow domain. Thus no extra Choice is required merely because that domain was not an original C operation type.

Conversely, at each Gallin world a, apply Gallin Choice to the extension U(x,y)(a) of a C serial relation. The resulting function between the translated C domains corresponds, by the isomorphisms above, to an original C operation when the output type is relational. It selects at a. Since a was arbitrary, boxed C Functional Choice holds. This is a schema correspondence within the represented Henkin domains, not an assertion of external metatheoretic Choice or full function spaces.

## 16. Finite independence, literal compactness, and exact configurations

Fix R:et. Let X and F range over rigid individual properties. Explicitly, Fin_sigma(F) means exists Z^((sigma t)t) [FiniteCardinality_sigma(Z) and Z(F)], with FiniteCardinality exactly the impredicative Frege predicate in the repository Background. In the present definitions sigma=e. In full S5 this is equivalent to the actual extension of F being externally finite. Write Fin(F) for this internally Frege-finite current extension, and define

    Match_R(F,X) := Diamond forall x(Fx -> (Rx iff Xx)),
    Loc_R(X) := forall F[(Rigid(F) and Fin(F)) -> Match_R(F,X)].

The empty finite condition is harmless. Define finite independence of R and its complete-pattern compactness by

    FI(R) := forall X(Rigid(X) -> Loc_R(X)),
    PC(R) := forall X[Rigid(X) ->
                     (Loc_R(X) -> Diamond forall x(Rx iff Xx))].

These are formulas of the existing language, using the already defined finite-cardinality predicate. They are proposed optional principles, not new logical rules. PC says that an admitted complete assignment of generator literals is realizable whenever every internally finite restriction is realizable.

**Theorem 12.** Over T, EU(R) is equivalent to FI(R) and PC(R). Neither Choice nor separation is needed.

If every rigid X is globally realized, every restriction is realized, giving FI, and the conclusion required by PC always holds. Conversely FI supplies the antecedent of PC for each X, so PC supplies its global realization. The elementary proof is intentional: PC isolates exactly the infinitary compatibility issue omitted by finite independence. Together with S(R), this supplies the exact configuration property.

In full models with individual set E, let V_R be the set of realized profiles {x:Rx} inside 2^E. Finite independence says V_R is dense for the product topology whose basic neighborhoods prescribe finitely many coordinates. PC says V_R is closed: a profile lies in its closure exactly when every finite restriction is realized. Separation says the profile map from worlds is injective. Thus a separating R is exact precisely when its profile set is both dense and closed. This is a semantic interpretation, not an appeal to topological compactness to prove Theorem 12.

The distinction is substantive even with genuine Infinity and all Choice. In the full S5 model with E=N and W=Fin(N), let Rx hold at w iff x is in w. Every finite Boolean pattern is realized, and distinct worlds have different profiles. Thus FI(R) and S(R) hold. But X=top is finitely realizable and has no realizing finite world, so PC(R) fails. More strongly EU_e fails for every candidate relation: countably many worlds cannot realize all 2^N rigid individual profiles. The model satisfies boxed Functional Choice and quantified individual Infinity. A closed proper profile family, such as all subsets omitting one fixed coordinate, gives the opposite boundary: PC and S hold while FI and EU fail.

In a general Henkin model, Fin means internal finiteness and profiles range only over admitted rigid X. The topological interpretation using all external finite coordinate sets and all external profiles need not coincide with this internal formula. In particular an externally infinite pseudofinite field can be internally finite. One must not silently replace the formula FI by the schema asserting realization of every standard finite list: the schema can be weaker. In full models and in the countable-infinitary extension of §11, the relevant standardness issue disappears for Frege finite cardinality.

### Why unrestricted proposition-family compactness is too strong

For an admitted rigid family F of propositions, call F internally centered if every internally finite admitted subfamily G has nonzero meet. Consider the principle

    every internally centered admitted rigid proposition family
    has nonzero total meet.

If the admitted rigid set W of all world atoms is internally infinite, take

    F := {not a : Atom(a)}.

Any internally finite rigid subfamily G of F excludes only internally finitely many atoms: its excluded set is lambda a[Atom(a) and G(not a)], and complement gives a represented bijection with G. Finite cardinality is invariant under such bijections by successor-removal induction. Thus there is an atom outside the exclusions and the meet of G is nonzero. This uses no selection from an infinite family and no Choice axiom. But the meet of all these co-singletons is bottom: every atom is excluded by its own complement, and Atomicity detects zero. Thus unrestricted internal FIP compactness rules out internal infinitude of the worlds.

Conversely, if W is internally finite, unrestricted internal FIP compactness holds. If a family F has zero meet, every atom a has some p in F with a not below p; otherwise that atom would lie below the meet. Induction on the finite cardinal of W gives a finite subfamily collecting such exclusions for all atoms. Its meet is bottom by Atomicity. This contradicts centeredness. Only finite choice, proved by the same successor induction, is used; full Choice is unnecessary. Hence the unrestricted internal compactness principle is exactly internal finiteness of the world-atom field over T.

If “finite” in this semantic compactness condition means externally finite instead, the same co-singleton argument forces external finiteness of W. Internal finiteness need not be external finiteness in a Henkin model, so the two conclusions must be kept separate.

Restricting to generator literals avoids this collapse. In an infinite exact configuration space, the complement of a singleton world generally requires an infinite disjunction of mismatched coordinates; it is not a single generator literal and need not belong to the finite Boolean algebra generated by finitely many coordinates. PC concerns the closure of complete generator profiles, not arbitrary proposition families. Full S5 with E=N and W=P(N) satisfies FI, PC and S while having infinitely many worlds; the co-singleton family refutes unrestricted FIP compactness there. This gives a clean, model-backed boundary for the optional compactness strengthening.

## 17. Arbitrary set-sized conjunctions and the parameter-support boundary

This section is expressly about a language extension beyond fixed finitary C. It does not change the consistency reference in the repository's original Maximalist schema. Any Maximalist principle referring instead to the extended proof system must be separately labeled.

Let a supported Gallin hierarchy admit, at every arrow type, all functions whose support belongs to an ideal closed under finite unions. In the principal examples this means all finitely supported functions. Let a group act on worlds and all typed domains, with application equivariant. Extend formulas by arbitrary SET-SIZED conjunctions and disjunctions of formulas whose free variables are contained in one common finite set. Keep finite quantifier strings and the original finite-arity types. Include the corresponding infinitary classical introduction/elimination rules and lambda comprehension for these formulas. Nonlogical named parameters, if used, must have one common allowed support; a common finite list of parameters suffices.

**Closure lemma.** Every such infinitary formula still has an admitted denotation in the supported hierarchy.

Fix its finite free-variable valuation and let S be the finite union of supports of those values, together with the common support of its named constants. Equivariance of satisfaction is proved by induction on the well-founded syntax tree. At an arbitrary conjunction, a permutation fixing S preserves each conjunct, hence preserves their intersection; disjunction uses unions. No union of the separate supports of the conjuncts is needed: all conjuncts already have the SAME support S. Quantification is equivariant because the group permutes the quantified domain. For lambda abstraction, its semantic function is equivariant under the stabilizer of its remaining free parameters, so it has allowed support and belongs to the arrow domain by construction. The argument works at arbitrary set-sized conjunction cardinalities and syntax ranks.

Consequently the supported models witnessing failure of Relational Choice or external fullness can remain models after this L_(infinity,omega)-style extension. Infinitary logical syntax with finite parameter support does not by itself fill all external powersets or select representatives that symmetry forbids. This conclusion is specific to the supported hierarchy's admission of every function of allowed support; an arbitrary Henkin submodel need not be closed under these enlarged conjunctions. The lemma makes no assertion about infinite free-variable families, infinite-arity lambda types, or infinite quantifier blocks.

There is an exact contrasting boundary. Suppose arbitrary set-sized conjunction/disjunction and comprehension are allowed with UNRESTRICTED SET-SIZED FAMILIES OF OBJECT PARAMETERS, so all of the relevant members can be named simultaneously. Then every external subset A of the world atoms is represented by

    disjunction {a : a in A}.

Every external relation on typed object domains is represented by the disjunction of its point-haecceities. More generally any external world-indexed relation is the disjunction of the terms

    a and x_bar=b_bar

over its external set of true world/tuple pairs. Thus those relational domains become externally full. Likewise the graph of any external function is definable by a disjunction of named input/output pairs; Plenitude realizes it as an operation whenever its output type is relational. In a graph-coded Gallin expansion the same observation fills the omitted individual-output arrows as well.

The distinction is therefore substantive: arbitrary conjunction SIZE is compatible with small supported Henkin domains when each formula retains a common finite parameter support; arbitrary parameter FAMILIES can force external fullness. Merely saying “infinitary logic” does not identify which of these very different resources has been added.

### Positive effect: arithmetic fullness without arbitrary-object fullness

The support lemma does not say that infinitary comprehension adds nothing. At a Frege index type with distinct standard numerals, for example under quantified Infinity of its underlying sort, the countable-infinitary extension of §11 makes natural-numberhood exactly the standard numeral sequence. For EVERY external subset A of N the pure infinitary term

    lambda x disjunction {x=n : n in A}

is admitted. It is a rigid predicate naming exactly those natural-number objects. Thus the rigid powerset field of the standard naturals is externally full in C_omega. A countable elementary Henkin submodel of a full finitary model, whose such field is countable, cannot automatically be extended without enlarging its domains to this language.

With arbitrary set-sized disjunctions, this effect iterates through every finite powerset level over the naturals. Each subset A of N already has its own parameter-free infinitary term chi_A. Any external family B of those subsets is therefore named by

    lambda X disjunction {X=chi_A : A in B}.

Repeating this construction names every member of each successive finite powerset field. Suitable function graphs over these named fields are similarly available, with Plenitude representing the relational-output operations. Countable conjunction alone does not justify the uncountable disjunctions needed at the later powerset stages; the arbitrary set-sized extension does.

This is consistent with the supported countermodels: every numeral is fixed by the symmetry group, every subset of the numeral field has empty support, and the same is true recursively of these higher named arithmetic fields. The still-anonymous individual atoms or world atoms need not become individually named by pure terms. Infinitary logic can therefore yield full arithmetic powersets while leaving general object-domain Choice false and omitting many external subsets of those anonymous fields. The distinction is between which objects the language can individually name, not simply between finite and infinite formulas.

## 18. Further compactness boundaries

### A simple no-Choice obstruction to universal compactness

The parent lane supplied a particularly short strengthening. Over T plus EU_e and quantified individual Infinity, there is already a finitely independent R' with PC(R') false, without Choice or separation. Given universal R, define

    FinExt(R) := exists X[Rigid(X) and Fin_e(X) and
                         forall x(Rx iff Xx)],
    R'(x) := Rx and FinExt(R).

Every current extension of R' is finite or empty. It therefore never realizes the universal individual property. But given a rigid pattern X and a rigid finite test F, the property Y=F intersect X is rigid and finite. At an EU world realizing Y, FinExt(R) holds, so R' realizes Y and agrees with X throughout F. Rigid finiteness is stable in T, by the Frege induction facts used in §10. Thus FI(R') holds while PC(R') fails at the universal pattern. A demand that every finitely independent family be compact is incompatible with EU_e plus genuine Infinity even in the absence of Choice.

### A basis-specific compactness guardrail

Even an exact configuration model need not make every other separating, finitely independent family compact. In the full E=N, W=P(N) model, choose a bijection h:P(N)->P(N) minus {empty}. The relation whose profile at w is h(w) is separating and finitely independent but omits the empty profile. Thus the same model contains both an exact compact basis and a noncompact dense separating basis.

This observation has an internal version, not just an external cardinality argument.

**Theorem 13.** Over T plus boxed Functional Choice and quantified individual Infinity, the existence of an exact profile family implies the existence of a separating finitely independent profile family which fails PC.

By Theorem 7 choose a rigid injection q:e^2->e, expressed by its functional graph, and distinct individuals a,b. Put d=q(a,b). The row map x↦q(x,a) is injective and misses d. For every rigid individual property X define

    h(X) := {d} union {q(x,a) : Xx}.

This is a represented injection from the field B of all rigid individual properties into its subfield B+ of nonempty properties. Inclusion gives the reverse injection. The internal Schroeder–Bernstein construction of §6 supplies a represented rigid bijection H:B->B+. All uses of q and H here are relational graphs or allowed relational-output operations; no operation of type ee is introduced.

If R is exact, compose its bijective slice map from world atoms to B with H. Theorem 1 pastes that admitted rigid family into a relation R'. Its profiles are exactly B+, each once. Hence R' separates worlds and omits the empty profile. It is finitely independent: a nonempty target pattern X is itself a permitted profile; for the empty target and any internally finite coordinate set F, quantified Infinity supplies an individual outside F, and its singleton is a nonempty profile agreeing with the empty pattern throughout F. Therefore every finite restriction is realizable, while the empty full pattern is not. QED.

The intended optional strengthening is accordingly existence of a suitable compact generator family, or compactness of a specified family. A universal demand that EVERY separating finitely independent family be compact contradicts the existence of exact configurations under the strong infinite base above. Compactness here is a property of the chosen coordinates, not just of the unstructured proposition algebra.

### Exact boundary for universal pattern compactness

The parent lane proposed the following sharper result. The internal proof below avoids silently identifying number objects of different Frege types.

**Theorem 14.** Over T plus boxed Functional Choice,

    forall R:et PC(R)
       iff Fin_e(top_e) or Fin_t(Atom_t).

Thus universal pattern compactness degenerates to internal finiteness of either the coordinate field or the world field. In full S5 models these are exactly external finiteness of E or W. The proof only needs admitted rigid well-orders of E and W; full Functional Choice is a sufficient way of supplying them. The algebraic-core lane independently audited the finite-position proof below, including its cross-type finite induction.

If E is internally finite, the local test F=top_e already is the global pattern test, so PC holds for every R. If the atom field W is internally finite, suppose a rigid pattern X is not globally realized. At each world atom w there is a coordinate at which slice(w,R) differs from X. Finite choice over W, proved by successor induction, yields a finite set F of such coordinates. Every world fails the pattern already on F, contradicting local realizability. This direction uses no full Choice.

Conversely suppose E and W are both internally infinite. Boxed Functional Choice gives rigid well-orders on these fields. For either ordered field L let

    I_L := {x in L : the predecessor set of x is internally finite}.

The standard finite-induction lemmas from §10 apply to these represented subfields. They show that I_L contains the least member, has an immediate successor for every member, has no greatest member, and that every internally finite nonempty subset of I_L has a greatest element. The successor exists because the predecessor set together with its endpoint is finite, whereas L is not; the well-order supplies the least omitted member. These statements concern internal finiteness, not externally standard numerals. The relevant predicates and orders are rigid; for a rigid finite field, finiteness and the successor-removal constructions are invariant across the T-worlds.

There is a represented order-isomorphism between I_E and I_W: pair x and w exactly when their predecessor well-orders are isomorphic. Uniqueness follows because distinct finite initial segments cannot be order-isomorphic. Existence follows by finite induction on predecessor segments: pair the two least points, and extend an isomorphism of predecessor segments by their endpoints to obtain the successor pairing. More explicitly, a nonempty finite predecessor well-order has a greatest point; removing that point gives the induction instance, and the least omitted endpoint on the other side extends it uniquely. The finite-cardinality successor-removal and invariance facts justify this induction across the two different underlying types. No equation between type-e and type-t numeral objects is assumed. Since the pairing is a unique-value admitted relation, its representation requires no additional Choice beyond the well-orders already obtained.

Define a rigid world/coordinate profile F as follows. At a world w in I_W, with paired individual x in I_E, let its profile be the predecessor set of x in E. At every other world, let its profile be empty. Theorem 1 pastes F into a relation R. Take the rigid target pattern X=I_E.

No world realizes X. Every assigned predecessor set is internally finite, while I_E is internally infinite because it has no greatest element; all other worlds have empty profile. But every internally finite coordinate test A is realizable. The finite set A intersect I_E, if nonempty, has a greatest member x; take the world paired with x's immediate successor. Its finite prefix contains all of A intersect I_E and excludes all coordinates outside I_E, agreeing with X throughout A. If the intersection is empty, the least world, with empty profile, works. Hence Loc_R(X) holds while the global pattern fails. Therefore PC(R) fails. QED.

The full-model counterexample has a particularly elementary form. Choose distinct individuals e_n and worlds w_n for n in N, give w_n the prefix {e_k:k<n}, and give all other worlds the empty profile. The pattern {e_n:n in N} is locally finitely realizable and globally absent. This proves the external full-S5 boundary directly, without relying on the internal well-order argument.

### The standard-finite schema cannot replace internal finite independence

Take finite full S5 models with E_n of size n and W_n consisting of every proper subset of E_n, with membership as R. A nonprincipal ultraproduct satisfies boxed Functional Choice, the finite-n individual Infinity Schema, S(R), and every standard-finite Boolean-independence instance: any fixed k-coordinate pattern is realized whenever n>k. It refutes EU(R), since the universal individual profile is omitted; in fact it refutes EU_e by finite cardinality in every factor. Yet it satisfies universal PC, because each factor has an internally finite individual field and this assertion transfers. In the ultraproduct the individual domain remains internally Frege-finite.

Thus replacing FI(R) in Theorem 12 by the standard-finite independence schema makes the claimed implication false, even with boxed Functional Choice and the Infinity Schema. The quantified internal Fin(F) condition is essential to that exact formula. The countable-infinitary standardness extension of §11 excludes this particular mismatch by making Frege finiteness standard.

## 19. Choice gives a profile-cardinality dichotomy

**Theorem 15.** Over T plus boxed Functional Choice,

    EU_e or S_e.

Here the existential witnesses in the two alternatives need not be the same; if both alternatives hold, Theorem 4 supplies one exact witness.

Let W be the rigid field of world atoms and B the rigid field of all rigid individual properties. Choice well-orders both represented fields. The internal comparison of well-orders proved in §10 gives a represented injection W->B or a represented injection B->W. In the first case paste the profile assignment into a relation by Theorem 1; injectivity makes it separating. In the second case invert the injection on its image and send worlds outside the image to the empty individual property. This is a represented surjection W->B, with no further selection, and its pasted relation is universal. All maps have relational codomains and all field restrictions are admitted. QED.

This is the internal counterpart of comparing the cardinality of worlds with the cardinality of admitted individual profiles. It does not identify that latter collection with the external powerset of E.

**A countermodel without full Choice, even with all Intensional Choice.** Take E=N with the TRIVIAL action of G=Sym(W), where W is any infinite world set. Use the full finite-support typed hierarchy of the algebraic-core report §2. All individuals have empty support; propositions are FinCof(W); higher domains consist of all finitely supported functions. The same closure and singleton-atom arguments give T. The generic-transport proof in that report §4 gives Intensional Choice at every type: it used only finite support of each possible witness, and does not require the individual domain to be singleton. Hence boxed Intensional Choice holds.

Every subset of N gives an admitted rigid individual property with empty support. The standard Frege numerals are fixed by G; the predicate containing exactly their external standard sequence is invariant and admitted. Thus internal finiteness at e is standard and quantified individual Infinity holds. The analogous argument applies to the infinite world-atom field.

But any admitted R:et has a common finite support S in W. Every world outside S has the SAME R-profile, since its stabilizer fixes each individual and acts transitively on W minus S. Thus R has at most |S|+1 distinct profiles. It cannot separate infinitely many worlds, and it cannot realize all the infinitely many admitted rigid individual profiles. Consequently both EU_e and S_e fail. This separates the Choice-derived dichotomy from T plus boxed Intensional Choice and genuine Infinity. The model also satisfies Ret_t: any admitted world equivalence has a finite support, and the full symmetric stabilizer forces the same finite/cofinite transversal classification proved in algebraic-core §16. Thus even adding Ret_t does not supply this dichotomy; Ret_t only combines EU and S witnesses when they already exist.

There is a further useful audit of Theorem 14. In this same model every R satisfies PC, since its profile image is externally finite: if X is not among those finitely many profiles, choose one differing coordinate for each profile, obtaining an admitted finite test excluding X everywhere. Thus universal PC holds although both E and W are internally infinite. The boxed Functional Choice hypothesis of Theorem 14 cannot be dropped or weakened merely to boxed Intensional Choice.

## 20. Audited failure of exactness without Choice

The algebraic-core lane's ordered-endpoint construction gives a sharper countermodel to deleting Choice from Theorem 4. This paragraph records an independent audit; the originating detailed proof is in that companion report.

Let the underlying support atoms be Q with G=Aut(Q,<). Let U be all finitely supported subsets of Q, let E=Q, and let W=U minus {empty,Q}. Use the full supported typed hierarchy over these nominal base sets. Every world itself has finite support, so its singleton proposition and every world/tuple point atom are admitted. The general closure proof gives T, and the admitted predicate of standard Frege numerals gives quantified individual Infinity.

A subset in U is a union of the cells cut out by a finite ordered set of points. It has a unique minimal set of ESSENTIAL breakpoints: a point is essential when its left-neighborhood truth, point truth, and right-neighborhood truth are not all equal. A nonconstant subset has at least one such breakpoint. Define f:W->U by erasing its least breakpoint, extending its right-neighborhood truth value to that point and the entire left tail. This erases exactly that breakpoint, preserves later ones, and is equivariant. It is surjective: for any B in U, prepend a fresh breakpoint smaller than every breakpoint of B, reverse the left-tail bit there, and then erase it to recover B. The arbitrary fresh point is used only to prove each fiber nonempty, not to define an equivariant section.

Ordinary membership E×W separates worlds, while membership in f(w) realizes every rigid individual profile U. Thus S_e and EU_e both hold. However no exact witness exists. Its profile map would be a finitely supported bijection W->U. If supported by a finite set S of rational points, it and its inverse would be equivariant under G_(S), hence would biject the fixed-point sets. There are exactly 2^(2|S|+1) fixed subsets of Q, one for each union of the stabilizer's 2|S|+1 cells. All are in U, while W omits the two constant subsets. The two finite fixed-point counts differ by two, impossible.

Thus T plus quantified Infinity can satisfy EU_e and S_e with different witnesses while refuting the exact configuration property. The Choice used to combine the witnesses in Theorem 4 is substantive. The same example refutes the corresponding internal Schroeder–Bernstein conclusion from an injection one way and a SURJECTION the other; ordinary Schroeder–Bernstein for two injections remains choice-free.

## 21. Field comparability and a typed Hartogs characterization of Choice

This section answers a further scope question from the parent lane. It distinguishes comparing profiles with the fixed world field from comparing arbitrary admitted fields.

For a rigid coordinate field A: sigma t, let B_A be the rigid field of all rigid properties X:sigma t with X contained in A. Define EU_A and S_A using only the coordinates in A. The canonical slice map is then w↦(A intersect slice(w,R)), a represented map W->B_A. Thus

    S_A gives an injection W->B_A;
    EU_A gives a surjection W->B_A.

The latter does not in T alone give an injection in the opposite direction. Under Ret_t, however, the profile partition has a transversal, so the surjection has an admitted section B_A->W. Consequently, over T plus Ret_t,

    EU_A or S_A

is exactly injection-comparability of W and B_A. This is a bounded comparison principle. For entire relational coordinate types S is already available in T, but proper rigid subfields need not contain the world codes which prove that fact. The subfield formulation is therefore the informative one.

Even the schema over ALL coordinate subfields, with W fixed, does not by itself characterize Choice. If W is internally finite, every field B_A is comparable with W by the usual finite induction and finite choice; the corresponding profile dichotomy follows in T. One may take a finite nonempty world set with trivial group action and an infinite ordered nominal individual field Q, using the full finite-support hierarchy under Aut(Q,<). This satisfies T and genuine Infinity while Relational Choice fails (the relation x<y has no finitely supported selector). Nonetheless every coordinate-subfield profile dichotomy holds. The support proof of selector failure is direct: above every finite support choose an input x, then an automorphism fixing that support and x can move any proposed output y>x. Ret_t and Intensional Choice also hold when the world field is finite. Fixed-world profile comparisons should not be promoted to full Choice on this evidence.

There is, by contrast, an exact unrestricted field formulation. Let CC be the schema that for any two admitted rigid fields A:sigma t and B:tau t, one has an admitted rigid injection A->B or B->A. All maps are functional relational graphs; neither sigma nor tau need be an allowed operation codomain.

**Theorem 16.** Over T, CC is equivalent to boxed Functional Choice.

Choice implies CC by well-ordering each field and using the internal comparison of well-orders. For the converse we give the entire higher-type Hartogs construction, so the proof does not presume arbitrary external quotients, ordinal sets, or full powersets.

Fix a rigid field A:sigma t. Code a well-order on a subfield of A by a rigid reflexive relation r:sigma sigma t: its field is D_r(x):=r(x,x); it is empty off that field, is a linear partial order there, and every nonempty admitted subset of its field has a least member. Restricting the subset quantifier to rigid subsets is equivalent in T by rigidification. Write WO_A(r) for these clauses and D_r contained in A. The empty relation codes the empty well-order. Let rho=sigma sigma t.

Order-isomorphism Iso(r,s) is expressed by an admitted rigid bijection graph between D_r and D_s which preserves and reflects the orders. It is an equivalence on WO_A codes. Its classes have canonical, represented higher-type codes:

    c_r := lambda s^rho [WO_A(s) and Iso(r,s)],
    H_A(C) := exists r(WO_A(r) and C=c_r).

The elements C of H_A have type rho t. Equality of these class predicates is exactly isomorphism of their well-orders: each class contains its own representative, and isomorphism is an equivalence. Thus no representative choice or external quotient formation is being assumed. The class predicates and their field are rigid; all defining graphs and quantifiers are available in C.

Order H_A by proper initial-segment embeddability of representatives. This is independent of the representatives. Internal well-order comparison gives linearity; composition gives transitivity, and a well-order is not isomorphic to a proper initial segment of itself. For clarity, that last fact follows by taking the least point on which a proposed initial-segment isomorphism moves an element and then applying the order condition; equivalently, the standard union-of-partial-initial-isomorphisms proof used in §10 gives uniqueness of every initial-segment comparison.

For each r there is a canonical order-isomorphism

    x in D_r  |->  c_(r restricted to the predecessors of x)

from D_r onto the initial segment of H_A strictly below c_r. The restriction is a represented well-order code. Distinct endpoints have nonisomorphic proper initial segments. Conversely any class below c_r, by its definition, is represented by an initial segment of r; a proper initial segment has a least omitted endpoint, so it is one of these predecessor orders. All these maps have unique-value graph definitions.

This proves that H_A is internally well-ordered. Given a nonempty admitted subset K of H_A, choose one class c_r in it. If no member of K lies below c_r, it is the least. Otherwise pull K intersect the predecessors of c_r back through the displayed canonical isomorphism to a nonempty subset of D_r. Its r-least member determines the least member of K below c_r, which by linearity is least in K altogether. This uses one witness to a nonempty set, not a simultaneous representative-selection principle.

There is no admitted injection H_A->A. If j were one, transport the well-order of H_A along j to its image in A. The result is an admitted rigid WO_A code r. Therefore H_A is order-isomorphic to D_r, which by the canonical isomorphism above is order-isomorphic to the proper initial segment of H_A below c_r. This contradicts the well-order fact just used.

Apply CC to A and H_A. The impossible direction H_A->A is excluded, so A injects into H_A. Pull back H_A's well-order to well-order A. Since A and sigma were arbitrary, every admitted field, and in particular each entire type domain, has an admitted well-order. The recorded equivalence of Well-Ordering with Relational Choice and T's Plenitude gives Functional Choice. Its closed pure instances box by No Pure Contingency. QED.

The proof actually needs only the bounded comparisons A versus its own represented Hartogs field H_A, not the entire two-field schema. This provides another precise definition improvement under T: full Choice may be expressed as the assertion that each object field is comparable with its canonical field of well-order types. The canonical field is built one finite number of higher-type steps above A; no new foundational sort is needed.

The injection formulation is essential. Replacing the second injection by an arbitrary surjection invokes a different weak-choice question unless a section principle is separately available. No equivalence of such weakened inject-or-surject comparability with Choice is claimed here.

**One-carrier simplification (parent refinement).** It is enough to assume comparability of two rigid subfields of the SAME relational carrier, schematically over all such carriers. Given original types sigma,tau, put kappa=(sigma t)(tau t)t and define

    j_sigma(x) := lambda A^(sigma t) B^(tau t). A x,
    j_tau(y)   := lambda A^(sigma t) B^(tau t). B y.

Application is explicitly left-nested: ((j_sigma(x)) A) B = A x, and ((j_tau(y)) A) B = B y. Both maps are injective, using haecceities to distinguish two original inputs. Their images are disjoint: at A=top_(sigma t), B=bottom_(tau t), the first has value top and the second bottom. Thus any two rigid fields embed disjointly as rigid subfields of one relational type kappa. Comparing those images and pulling the resulting injection back through the unique inverse graphs compares the original fields. No representative choice is needed. Consequently same-carrier rigid-subfield comparability already yields Theorem 16's full Choice equivalence.

### A concrete Hartogs field in the ordered nominal model

In the ordered nominal individual model E=Q, the Hartogs field H_E consists exactly of the standard finite order types. Here is the support proof, with an important internal/external guardrail.

Let an admitted well-order code r have finite rational support S. Its field is a union of the stabilizer's finitely many point/open-interval orbits. If it contains an open interval orbit I, the restriction of its linear order to I must be the natural rational order or its reverse: on distinct pairs in I there are only the increasing and decreasing orbits, and linearity/antisymmetry select one orientation. But I itself is an admitted nonempty subset and has no least element under either orientation. This contradicts internal well-ordering. Therefore the field is contained in the finite set S. Conversely every finite linear order on rational points is admitted. Its isomorphism type is determined by its standard finite size, so H_E is an admitted standard omega-field, each of whose members is fixed by every group element.

It follows directly that E and H_E are incomparable by admitted injections. A graph E->H_E with support S is constant on every open interval orbit of G_(S), since its outputs are fixed, so it cannot be injective. A graph H_E->E with support S has every output fixed by G_(S), hence has range contained in S, so it cannot be injective either. Thus cardinal comparability fails already between the anonymous individuals and a standard natural-number field.

One must not replace the orbit proof by the unqualified claim that external automorphisms of an internal well-order are trivial: their graphs need not be admitted, so the usual least-moved-point subset may be unavailable. The argument above uses an explicitly admitted interval subset. Likewise the Hartogs proof uses only represented order-isomorphisms, for which the standard well-order rigidity proof is legitimate.

This model remains available under the arbitrary set-sized, finite-parameter infinitary extension of §17. Its arithmetic powerset hierarchy can be externally full while E still cannot be well-ordered or compared with its Hartogs field. Arithmetic fullness and general object-domain Choice are distinct resources.

## 22. Complete bivalent evaluation and atoms which cannot vanish

This section audits a further parent-lane proposal over bare C. It must not be conflated with T's already constant-domain atomic-world theorem. Let CE assert that there is E:tt such that, for every current proposition p and every current operation F:tt,

    E(top)=top,  E(bottom)=bottom;
    E(p)=top or E(p)=bottom;
    E(not p)=not E(p);
    E(forall p Fp) = forall p E(Fp).

The last line is PROPOSITION IDENTITY, not just a material biconditional. CE is a complete bivalent evaluator. No binary meet law needs to be separately postulated for the proof below.

**Theorem 17.** Bare C proves

    CE -> exists w(Atom(w) and Box Diamond w).

Conversely C plus BF_t proves the reverse implication. Over C plus BF_t, these are also equivalent to exists w Box Atom(w).

For the forward direction fix E and put

    w := forall p(Ep -> p).

For each current p, bivalence gives E(Ep->p)=top. If Ep=top, its input is p and its output is Ep=top; if Ep=bottom, its input is top and the endpoint equation applies. Therefore the universal proposition forall p E(Ep->p) is actually true. Quantifier preservation makes E(w) actually true, and bivalence at the current argument w makes E(w)=top.

NI preserves this identity and E(bottom)=bottom. At any future point, w=bottom would therefore imply top=bottom by substitution, impossible. Hence Box(w!=bottom), equivalently Box Diamond w. This is persistent nonzeroness, stronger than w merely being actually nonzero or possibly true.

The proposition w decides every current q. If E(q)=top, the q-instance of the defining universal, together with NI for E(q)=top, gives Box(w->q), so w<=q. If E(q)=bottom, negation preservation gives E(not q)=top and hence w<=not q. A nonzero Boolean element deciding every element is an atom. All quantified propositions here are current objects; no BF inference has been used. This proves the forward implication in C.

For the converse suppose w is an atom and Box Diamond w, and define

    E_w(p) := Box(w->p).

At the current point atomhood makes w<=p or w<=not p. Positive box truths persist by 4. If the second alternative holds, E_w(p) cannot become true at a future point: together with the persistent E_w(not p) it would make w impossible there, contrary to Box Diamond w. Thus E_w(p) is either necessarily true or necessarily false, i.e. equal to top or bottom. The two alternatives are exclusive because w is possible, so negation preservation follows as an identity between bivalent propositions. Endpoint preservation is immediate; the bottom endpoint uses persistent nonzeroness. This part needs no BF.

BF_t gives the CURRENT equivalence

    Box(w -> forall p Fp) iff forall p Box(w->Fp).

The forward direction is Converse Barcan, available in C; the reverse is BF_t applied to p↦(w->Fp). One must not simply necessitate this equivalence under the BF_t assumption to infer the required identity. Instead the left side is bivalent by the preceding paragraph. The right side Q:=forall p E_w(Fp) is also bivalent. If Q is true, each current E_w(Fp)=top, so each is necessary; BF_t gives Box Q. If Q is false, a current bottom-valued witness remains false necessarily by NI, so Box not Q. Thus both sides are bivalent, and their current equivalence proves their identity. This supplies CE with the exact quantifier clause stated above.

Finally, under BF_t, Atom(w) and Box Diamond w imply Box Atom(w). Current atomhood says every current p is decided by w. Each positive order statement w<=p or w<=not p is an identity assertion and hence necessary by NI. BF_t boxes the universal decision property. Persistent nonzeroness was already given, so atomhood holds necessarily. Conversely Box Atom(w) gives current atomhood and persistent nonzeroness directly. This is a de re claim about one and the same proposition object; it is not the weaker assertion that every future point has some atom.

**Relation to BR and Maximalism.** The converse construction's bivalence and endpoint preservation required no BF. Therefore bare C already proves

    exists w(Atom(w) and Box Diamond w) -> BR.

By the independently audited BR<->.2 equivalence of §12, pure Maximalism refutes this persistent-atom condition. Equivalently it proves

    forall w(Atom(w) -> Diamond(w=bottom)).

Every current atom can become the impossible proposition. This says possible VANISHING AS AN OBJECT, not merely possible ordinary falsity of the atom at a world. NI does not forbid vanishing, because the atom's current inequality with bottom need not be necessary in C.

**Full two-world chain: CE without ND.** In the full action model on 0->1 with one fixed individual, let E evaluate at the terminal point and return the corresponding constant proposition. It preserves endpoints, negation and all current proposition-indexed meets: restricting current propositions to the terminal point is onto its two proposition values, so evaluating a universal proposition there agrees with universally evaluating its current instances. Thus CE holds. The terminal singleton is an atom which cannot vanish. Nevertheless the root-only singleton becomes bottom at the terminal point, so ND fails. CE is substantially weaker than T.

**Full omega-chain: necessary Atomicity, .2 and BF_t without CE.** Use the full action model on 0->1->2->... with one fixed individual. At stage n the propositions are all subsets of the tail {n,n+1,...}; transport to a later stage restricts to its tail. Every proposition atom at n is a singleton {m}, m>=n, and becomes bottom after stage m. Therefore there is no current atom w with Box Diamond w, and CE fails by Theorem 17.

Atomicity holds necessarily at all relational types. At a stage n, a relation of type sigma_bar t is an arbitrary truth assignment to future typed points (m,a_bar), m>=n, with a_bar drawn from the typed domains at m. Its singleton point truth assignments are admitted atoms, and every nonzero relation contains one. This is the concrete full-action relational presentation, not an inference from propositional atomicity alone. Necessity follows by the same description at every stage.

The frame is directed, so .2 holds. BF_t holds because every proposition at a later stage is the restriction of a current proposition. Explicitly, if every current p necessarily has property F, then at a later stage any proposition q has a current lift p; naturality of application makes F(q) true there. Thus necessarily every proposition has F. These verifications give a C-model of necessary Atomicity plus .2 plus BF_t with no complete bivalent evaluator. Atomhood everywhere, a weak convergence law, and proposition-domain surjectivity do not guarantee a single atom which remains possible forever.

### The BF_t hypothesis in the converse is essential

The existing recorded model `full-idempotent-monoid` gives a small counterexample. Its construction is the full action model on M={1,k}, k^2=k; see Classicism §3.5, p.59, and the owning model/write-up. The following NPA/CE verdict is a new calculation (`source_id: misc`), not an alteration of that source's record.

Write 0=empty, 1=M, a={k}, and b={1}. Proposition transport is h^t p={u:u h in p}. Thus k^t p=1 when k is in p and 0 otherwise. The atom a never becomes zero: its transports are a and 1. Therefore Atom(a) and Box Diamond a hold, although a becomes top and loses atomhood along k. The other atom b vanishes along k.

Here is an explicit admitted F:tt. In the full exponential presentation it has two component functions f and g, for arrows 1 and k respectively:

    f(p)=1 for every p;
    g(0)=g(1)=g(a)=1,  g(b)=a.

The naturality equations are

    k^t f(p)=g(k^t p),
    k^t g(p)=g(k^t p).

Both hold by the four-entry table: k^t p is always 0 or 1, where g has value 1, and every g(p) contains k. Hence the full action hierarchy admits this F. Every current Fp is the top proposition. But Q:=forall p Fp is b: at arrow 1 all f-values are true; at arrow k the newly bound p ranges over the ENTIRE target proposition domain, where g(b)=a is false at the identity. This is exactly the successor-quantifier convention in the owning action semantics, not quantification restricted to transported inputs.

Suppose CE had a witness E. Theorem 17 constructs a persistent atom w. Of the two atoms only a is persistent, so w=a. The construction also proves that E(p)=top iff w<=p: one direction was used in the proof, and if E(p)=bottom then w<=not p, contradicting w<=p and w!=bottom. Consequently E(b)=bottom. Applying CE's quantifier equation to the displayed F, however, gives

    E(Q) = forall p E(Fp).

Its left side is bottom, while its right side is actually true because every current Fp=top and E(top)=top. This contradiction refutes CE. The same F witnesses failure of BF_t, since forall p Box Fp is true but Box forall p Fp is false.

Thus C plus a necessarily possible atom, and hence BR/.2, does not imply CE. The BF_t condition in Theorem 17 is mathematically essential. This also exhibits the distinction between persistent nonzeroness of an atom and persistence of its atomhood.

## 23. Exact evaluator criterion in full action models

This section is a semantic theorem for FULL action hierarchies, not an extra theorem of arbitrary Henkin C. Its proof and the new verdicts below have `source_id: misc`. The action and quantifier conventions are those of Classicism Definition 3.19, pp.55–57, and `topics/classicism/writeups/strong-worlds-one-object-action-models.md`: newly bound variables range over the entire target domain. The algebraic/model lane independently audited the criterion and the examples.

Let A be an object of a small category K. Write Out(A) for its arrows with source A, keeping targets as part of the arrow data. In the full action hierarchy D_t(A)=P(Out(A)); along g:A→C,

    g^t(p)={k in Out(C):kg in p}.

A singleton {h}, h:A→B, is necessarily possible exactly when h factors through every outgoing g:A→C. This means that for each g there is k:C→B with kg=h. In addition, h^t is surjective exactly when h is an epimorphism in K: the inverse-image map along k↦kh is onto precisely when that map is injective. Neither condition by itself asserts that factorizations kg=h are unique.

**Theorem 18.** In a full action model, CE holds at A if and only if there is an arrow h:A→B which is epic and factors through every arrow with source A.

**Necessity.** The bare-C direction of Theorem 17 produces a necessarily possible atom w. Fullness makes w={h} for some outgoing h, so h has the displayed factorization property. That proof also gives, for every current proposition p,

    E(p)=top iff h in p.

Define a full admitted F:tt by its extension at each outgoing g:A→C:

    I_g=im(g^t:D_t(A)→D_t(C)).

The full relation-intension description permits these extensions. Equivalently the component F_g(q) is the proposition whose truth at a continuation u:C→D says u^t(q) belongs to I_{ug}; this makes the component naturality equations automatic. For every current p and every g, g^t(p) lies in I_g, so F(p) is literally top. But Q:=forall p Fp is true at g exactly when g^t is onto, since the quantifier there ranges over all D_t(C). CE gives

    E(Q)=forall p E(Fp),

and the right side is currently true. Hence E(Q)=top and h belongs to Q. Thus h^t is onto and h is epic.

**Sufficiency.** Suppose h is epic and factors through every outgoing arrow, and put w={h} and E(p):=Box(w→p). At the root, for every p this is top if h∈p and bottom otherwise: at every successor g there is at least one factorization kg=h, and every such factor tests precisely the same root truth h∈p. Thus endpoints, bivalence and negation hold as proposition identities.

Fix any current F:tt. At a successor g:A→C, the right side of the desired quantifier identity is true exactly when

    for every q in D_t(C) and every k:C→B with kg=h,
        F_h(k^t(q)) is true at B.

For each such k, h=kg epic implies k epic, so k^t is onto D_t(B). There is at least one such k. Therefore this condition is equivalent to

    for every r in D_t(B), F_h(r) is true at B.

The latter is precisely truth at h of forall p Fp. It is also truth at g of E(forall p Fp), again because the factorization set is nonempty. The two propositions agree at every outgoing g, hence are identical in the full action model. This verifies CE's exact quantifier identity. ∎

The criterion is not “there is a terminal object” and is not merely a modal frame condition. Epicness controls whether current propositions cover every target proposition along the selected arrow; CE's quantifier identity can detect failure of that coverage. The necessity argument uses a full image-test intension, so it has not been asserted for arbitrary Henkin submodels.

### A necessarily atomic proposition without CE

Use three objects W,V,X, realized concretely as sets W={a}, V={a,b}, X={a,b1,b2}. Include maps

    w:W→V, w(a)=a;
    r_i:V→X, r_i(a)=a and r_i(b)=bi, for i=1,2;
    v:X→V, v(a)=a and v(bi)=b.

Take the category generated by these maps. Thus v r_i=id_V, r1 w=r2 w=q:W→X, and e_i=r_i v are endomorphisms of X. Its outgoing arrows are

    Out(W)={id_W,w,q};
    Out(V)={id_V,r1,r2};
    Out(X)={id_X,v,e1,e2}.

Composition is ordinary function composition, so associativity and the listed equalities need no separate presentation assumption. For example e_i e_j=e_i and e_i r_j=r_i. The singleton {w} transports along w to {id_V} and along q to {v}. Thus it remains a nonzero atom at every successor: Box Atom({w}). Nevertheless no outgoing arrow satisfies Theorem 18. The identity id_W vanishes along w because there are no arrows back to W. The arrow w is not epic because r1 w=r2 w with r1≠r2. The arrow q is not epic because id_X q=e1 q=e2 q=q. Consequently CE fails. This proves that even C plus exists w Box Atom(w) does not imply CE without BF_t.

### CE without any necessarily atomic proposition

Reverse the retract geometry. Let W={a,b}, C={a,b,c}, and g:W→C be inclusion. Let r1,r2:C→W fix a,b and send c to a,b respectively. Include the category generated by these maps. Then r_i g=id_W, e_i=g r_i, and

    Out(W)={id_W,g};
    Out(C)={id_C,r1,r2,e1,e2}.

Here e_i e_j=e_j and r_i e_j=r_j. The arrow id_W is epic and factors through g via either r_i, so Theorem 18 gives CE. But the two root atoms have transports

    g^t({id_W})={r1,r2};
    g^t({g})={id_C,e1,e2}.

Neither transport is an atom in the full target powerset. There is therefore no proposition w with Box Atom(w) at W. This also refutes BF_t, as follows either from Theorem 17 plus CE or directly from the non-surjectivity of g^t. In particular, CE does not imply persistence of atomhood in bare C; Theorem 17's BF_t hypothesis is needed in both directions of its equivalence with exists w Box Atom(w).

### CE and a necessarily atomic proposition can coexist with failure of BF_t

For a separate small example take objects r,s, End(r)={1,k} with k²=k, and a terminal s with unique h:r→s satisfying hk=h. There are no arrows s→r. The terminal arrow h is epic and factors through every outgoing arrow; its singleton remains an atom. Hence CE and exists w Box Atom(w) hold.

Nevertheless k^t on D_t(r)=P({1,k,h}) has only four values (membership at 1 and k always agrees), so it is not onto. A direct BF witness has extensions I_1=D_t(r), I_k=im(k^t), I_h=D_t(s). Every current Fp is top, while forall p Fp is false at k. Thus BF_t fails. The sufficient BF hypothesis in Theorem 17 is not a necessary condition for CE itself.

### Corollary: the full one-object case detects exactly groups

In the full action model on a one-object category, regarded as a monoid M, CE holds if and only if M is a group. This is a semantic corollary of Theorem 18, not a claim that arbitrary C models are monoid models.

Indeed the criterion supplies an h which is right-cancellable (u h=v h implies u=v) and belongs to every principal left ideal M g. Apply this to g=h²: h=u h², so right cancellation of h yields 1=u h. Then (h u)h=h=1h, and cancellation gives h u=1. Thus h is a unit. For any g, write h=k g and multiply on the left by h^{-1}, showing that g has a left inverse. Since every element has a left inverse, all are invertible: if a g=1 and b a=1, then b=b(a g)=(b a)g=g, so g a=1. Hence M is a group. Conversely in a group any chosen h is epic and factors through every g, using k=h g^{-1}, so CE holds. The proof applies to finite and infinite monoids alike.

**Additional modal-scope check.** In the reverse-retract example CE holds at W but fails at its successor C. At C the arrows r1,r2 are epic but neither factors through the other (the only W-endomorphism is id_W); id_C does not factor through r1; and e1,e2 are not epic since r1 e_i=r2 e_i. More strongly no outgoing arrow factors through both r1 and r2, so C has no persistent atom. Its proposition p={r1,e1} becomes top along r1 and bottom along r2. Thus Diamond Box p and Diamond Box not p both hold at C, refuting .2/BR there. Hence bare C+CE implies neither Box CE nor Box BR. A de re persistent root atom may split at a successor into atoms which are individually nonpersistent; persistent nonzeroness and necessarily existing persistent atoms are distinct claims.

## 24. The exact bare-C condition: an atom-local Barcan law

The full-model criterion above suggests a precise object-language replacement for the sufficient global BF_t assumption. For a proposition w define

    LB_t(w) := forall F:tt [
        (forall p:t Box(w→Fp)) → Box(w→forall p:t Fp)
    ].

This is a relative quantifier law at one proposition, not global BF_t. The converse implication inside this equivalence is already a theorem of C by Converse Barcan. No original definition of Atom or Strong World is being changed. If one wants a short new label, “quantifier-complete atom” can mean Atom(w) and LB_t(w), with the quantified type t displayed when other types are discussed.

**Theorem 19.** Bare C proves

    CE iff exists w [Atom(w) and Box Diamond w and LB_t(w)].

In particular the witness E in CE may always be replaced by the canonical operation E_w(p):=Box(w→p), even though no general Functionality inference E=E_w has been used. The claim is existence of a canonical witness, not identity of every original evaluator object with that witness.

**Forward direction.** Theorem 17 constructs w from a CE witness and proves Atom(w), Box Diamond w, and, for every current p,

    E(p)=top iff w<=p.

Fix F and suppose forall p Box(w→Fp). Thus every current E(Fp)=top, so forall p E(Fp) is currently true. The CE object identity E(forall p Fp)=forall p E(Fp) makes E(forall p Fp) true and hence equal to top. The displayed evaluation equivalence gives Box(w→forall p Fp). This is exactly LB_t(w). This argument only evaluates the quantified right side currently; it does not illegitimately infer its necessity from all its current instances being necessary.

**Reverse direction.** Given the right side, define E_w(p):=Box(w→p). Atomhood and persistent nonzeroness give the endpoint, bivalence and negation identities exactly as in Theorem 17, using no BF. Fix any current F and abbreviate

    L := Box(w→forall p Fp),
    Q := forall p Box(w→Fp).

The implication L→Q is a theorem of C, uniformly in w,F. LB_t(w) gives its converse at the current point. Thus L and Q are currently equivalent. L is already bivalent, because it is E_w applied to a current proposition. It remains to establish that Q is bivalent, rather than silently upgrading actual equivalence to identity.

If Q is true, LB_t(w) gives L. Since L is a box formula, axiom 4 gives Box L. Necessitate the universally closed C-theorem L→Q, and instantiate it at the current w,F; this gives Box(L→Q) without necessitating any optional assumption. Therefore Box Q, so Q=top.

If Q is false, some current p satisfies not E_w(Fp). Bivalence gives E_w(Fp)=bottom. NI preserves that identity, so the same transported witness makes Q false at every successor; equivalently Box not Q, so Q=bottom. This uses ordinary existential introduction under Box, not BF.

Consequently both L and Q are bivalent and currently equivalent, so L=Q. This is CE's quantifier identity for every current F. The canonical E_w witnesses CE. ∎

**Definition and scope audit.** BF_t implies LB_t(w) for every w by applying BF to the property p↦(w→Fp), so Theorem 17 follows immediately. Theorem 19 is sharper because only one atom's relative quantifier law is required. The finite categories in §23 show that neither persistent atomhood alone nor global persistence of atomhood substitutes for LB_t. They also show that LB_t at a suitable atom can hold despite failure of global BF_t, and that a complete evaluator's atom need not remain atomic. In full action models, for a singleton {h}, LB_t({h}) holds exactly when h is epic: the full image-test gives necessity, and onto transport gives sufficiency by the same universal-instance calculation as Theorem 18. Persistent possibility remains a separate condition.

### Quantifying over other types

For any type sigma, write LB_sigma(w) for the same formula with p:sigma and F:sigma t. Given a persistently possible atom, the same proof converts LB_sigma(w) into the object identity

    E_w(forall x:sigma Fx)=forall x:sigma E_w(Fx).

Thus one canonical evaluator commutes with a chosen family of universal quantifiers exactly when its atom satisfies the corresponding family of relative Barcan laws. This is an explicit schema extension of CE_t when more types are included, not a hidden change to its original definition.

In a FULL action hierarchy, epic h makes h^tau onto for every relational type tau, not only t. To lift an arbitrary target relation intension q, prescribe its component at k on the root arrow kh and put false off that image. Epicness makes k↦kh injective, so this prescription is unambiguous; all target argument values at that arrow are present in the full intension description. There are no additional naturality constraints on these truth assignments. Hence the canonical evaluator from Theorem 18 automatically commutes with every relational-type quantifier. For the individual type e it does so exactly when h^e is also onto: necessity uses the analogous full image-test, and sufficiency uses h^e=k^e g^e onto to infer that each factor k^e is onto. This is a semantic statement about full hierarchies and is not asserted for arbitrary Henkin C models.

A two-object chain separates the relational evaluator scheme from its all-type extension. Use root individual domain {a}, terminal domain {a,b}, and transport a↦a. The terminal arrow h is epic and persistent, so CE_t and the evaluator laws for every relational quantified type hold. But h^e is not onto. Take an admitted F:et whose current extension contains a and whose terminal extension contains a but not b. Every current F(a) is top, whereas forall x:e Fx is false at the terminal point. The unique persistent root atom is {h}; its LB_e law fails, so there is no evaluator commuting with both proposition and individual quantification. The example changes the individual functor, not the full relational-domain convention.

## 25. Independent audit of the finite-retraction compactness consequences

The algebraic report §§25–31 proves a separate sequence of theorems; this paragraph records the independent mathematical audit, without duplicating ownership or claiming formal verification. All scopes are admitted rigid fields and their admitted rigid properties.

Uniform Ultrafilter Choice (UFC) is equivalent to all-type finite-operation Boolean retractions. Its new consequence is that every internally infinite field I has an admitted nonprincipal ultrafilter. The coordinate-limit proof passes: if every ultrafilter on I were principal, any nonprincipal U on P(I) would define the admitted profile v(i):=U({X:Xi}). UFC chooses K_X concentrated on X△v for X≠v, with an arbitrary nonempty default fiber at v. Their U-sum V contains no singleton, since the event K_X({i}) is contained in the U-small union {X:i∈X△v}∪{v}. This contradicts the hypothesis. Hence all ultrafilters on P(I) would be principal. Applying UFC to all nonempty admitted subfields of P(I) and extracting each unique principal point gives ordinary choice on that one field, hence an admitted well-order of P(I).

A well-ordered Boolean algebra admits a greedy extension of any proper filter. The report's comprehension construction uses all admitted partial assignments on initial segments satisfying the deterministic positive-if-consistent decision rule. They agree by least disagreement. Their union is admitted; an internally finite set of decision indices has a greatest member and lies in one partial assignment, so its consistency is preserved. A proper union domain can be extended at its least missing element, contradiction. This is an internal proof, not an invocation of external ordinal recursion. Applying it to the cofinite filter on the infinite I gives a nonprincipal ultrafilter and completes the contradiction. The internal Zermelo union used earlier is likewise well-ordered: for a nonempty admitted subset choose one member x and take its least member below x if any, otherwise x. No choice of a whole family of such witnesses is made.

The additional ordered-support transfer in algebraic §31 also passes. The primary source is Andreas Blass, *Partitions and Permutation Groups*, §2 printed p.2 and §3 pp.3–4, available at https://janos.cs.technion.ac.il/RESEARCH/AMS-Book-files/pdfs/11_Blass.pdf. It supplies extreme amenability of Aut(Q,<), and the ordered Mostowski BPI/¬Choice example. In the typed model, a finite stabilizer is a finite product of those extremely amenable groups. It acts continuously on the compact external Stone space of ultrafilters extending an admitted supported filter; every algebra element has an open stabilizer. A fixed ultrafilter is supported and therefore admitted by the full supported hierarchy. External ZFC is used to construct the compact Stone space in this semantic argument, not assumed as internal Choice. Thus the endpoint model really satisfies FE/BPI_int/FineUF while having separate EU and S witnesses and no exact witness. BPI_int cannot replace complete Ret_t in the positive exact-profile theorem.

## 26. Complete evaluators characterize the whole core by separation

For an operation E:tt write CE_t(E) for the exact endpoint, bivalence, negation and proposition-quantifier identities of §22, with E displayed rather than existentially bound. Define **complete-evaluator density** by the single proposition-level higher-order sentence

    CED := forall p:t [p≠bottom → exists E:tt(CE_t(E) and E(p)=top)].

This quantifies only over admitted operations and their admitted proposition-indexed families. “Complete” does not mean preservation of arbitrary external meets.

**Theorem 20.** Over the fixed C framework,

    CED iff Box Plenitude
        iff Box ND_all + Atomicity_all.

Equivalently, the complete bivalent evaluators separate distinct propositions:

    forall p,q:t [p≠q → exists E:tt(CE_t(E) and E(p)≠E(q))].

Thus one natural sentence involving only propositional and proposition-operation types axiomatizes the same extension as the all-type boxed Plenitude schema. This is an equivalent formulation, not a stronger optional preset. No Choice assumption enters this theorem.

**CED gives ND_t.** Let p≠bottom and choose E with CE_t(E) and E(p)=top. NI makes both E(p)=top and E(bottom)=bottom necessary. If p ever became bottom, substitution at that point would make top=bottom. Therefore Box(p≠bottom). For distinct p,q, their symmetric difference is nonzero; its persistent nonzeroness prevents p=q at any successor. Hence ND_t.

**CED gives BF_t.** Suppose forall p Box Fp, and put Q:=forall p Fp. If Box Q failed, Q≠top, so (not Q)≠bottom. Density supplies E with CE_t(E) and E(not Q)=top. Negation preservation gives E(Q)=bottom. On the other hand, every current Fp=top, so every current E(Fp)=top and forall p E(Fp) is currently true. CE's object identity

    E(Q)=forall p E(Fp)

then makes E(Q) true, contradicting E(Q)=bottom. Thus Box Q, proving BF_t. Notice that this argument only infers the current truth of the universal right side from its current instances; no illicit BF inference is hidden in the proof of BF.

**CED gives propositional Atomicity.** If p≠bottom, choose a CE witness E with E(p)=top. Theorem 17 constructs its atom w and proves E(p)=top iff w≤p. Thus every nonzero proposition contains an atom.

**From these three consequences to the full core.** The following proved recorded chain is used, with exact modal scopes:

    ND_t + BF_t ⇒ Box ND_t
               ⇒ Box ND_all
               ⇒ BF_all;
    Atomicity_t + BF_all ⇒ Atomicity_all;
    Box ND_all + Atomicity_all ⇒ Box Plenitude.

The relevant owning records are `nd-t-and-bf-t-imply-necessary-nd-t` (Classicism Proposition 2.4, p.23), `necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r` (Proposition 2.2, p.22), `necessary-nd-implies-bf` (Proposition 2.3, p.22), `atomicity-t-and-bf-imply-atomicity` (Dorr's recorded observation of 23 September 2026 with the written-out tuple-atom proof), and `c5-and-atomicity-imply-necessary-plenitude` (Classicism §2.3, p.33). These existing results supply the all-type lift; the evaluator-density derivation of their premises is new here and has `source_id: misc`.

For transparency, the first step uses the current identity/disequality cases, NI, ND and 4 to get forall p q Box(p≠q→Box(p≠q)), then applies BF_t twice. In the atomicity lift, a nonzero relation has a possible tuple instance; BF at its argument types brings that tuple to current parameters. A propositional atom w below that instance gives the relation atom λy_bar(w and y_bar=x_bar). This explains why the all-type passage is justified and why propositional Atomicity alone would not suffice.

**Conversely T gives CED.** Given p≠bottom, Atomicity supplies an atom w≤p. Box ND makes w persistently nonzero, and BF_t supplies LB_t(w). Theorem 19 gives the canonical complete evaluator E_w(q):=Box(w→q), with E_w(p)=top. This proves density.

**Separation equivalence.** Each CE witness determines its atom w, and E(p)=top iff w≤p. Atomhood therefore makes E preserve finite Boolean operations at current arguments as proposition identities: for example E(p∧q)=E(p)∧E(q), since both bivalent sides are top exactly when w≤p and w≤q. Density applied to p symmetric-difference q gives a CE witness with distinct evaluations of p and q. Conversely a CE witness separating a nonzero p from bottom must send p to top because it fixes bottom and is bivalent. Thus separation and density are equivalent.

The theorem does not assert that evaluator objects with the same current action are identical in bare C. The proof needs only their displayed application identities; canonical replacement uses Theorem 19. Nor does it assert that every external two-valued evaluation is admitted. Proper Henkin models of T remain covered.

### A small definition ladder

Write BR(E) for endpoint preservation and current bivalence alone, without negation or quantifier preservation. Define

    BRD := forall p [p≠bottom → exists E(BR(E) and E(p)=top)].

**Theorem 21.** Bare C proves BRD iff ND_t. In fact, under ND_t one SINGLE operation recognizes all nonzero propositions: E(p):=Diamond p satisfies BR(E) and

    forall p [E(p)=top iff p≠bottom].

The forward proof is the same NI argument used for CED: E(p)=top and E(bottom)=bottom prevent a nonzero p from becoming bottom; symmetric differences give full propositional ND. Conversely ND_t makes every nonzero proposition necessarily nonzero, so Diamond p=top for p≠bottom; for p=bottom, Diamond p=bottom. The canonical E fixes both endpoints and is bivalent. No negation preservation is claimed; a possibility detector usually sends both a contingent p and its negation to top.

Together with §12 and Theorem 20 this gives exact formulations at three levels:

    existence of one BR evaluator             iff modal .2;
    BR evaluators separate zero from nonzero  iff ND_t;
    complete evaluators separate propositions iff T.

The first and second levels should not be conflated: the full terminal two-world chain has a BR (indeed CE) evaluator but a root-only proposition can vanish, so ND_t and BRD fail. The last equivalence supplies the all-type core without a separate Choice principle; □Functional Choice remains the further strength analyzed by the retraction and Gallin-core theorems.

### The endpoint clauses in CE are redundant

Preserve the original expanded definition, but an equivalent and shorter definition of CE_t(E) has only three clauses: current bivalence, negation preservation, and the exact proposition-quantifier identity. In fact negation and quantifier preservation alone force both endpoint identities.

Apply quantifier preservation to the identity family F(p)=p. The C theorem (forall p:t p)=bottom gives

    E(bottom)=forall p E(p).

Necessary universal instantiation at p=top gives E(bottom)≤E(top). Negation preservation at bottom gives E(top)=not E(bottom). Hence E(bottom)≤not E(bottom), which in the propositional Boolean algebra entails E(bottom)=bottom; negation then gives E(top)=top. These are object identities. There is no appeal to Functionality, no use of optional-premise necessitation, and not even a use of the bivalence clause in this sublemma. Thus the reduced definition preserves every theorem above while making explicit that endpoints need not be separately postulated.

## 27. A truth-preservation presentation with the same exact strength

For readability one can weaken the preservation clauses to ordinary current biconditionals while retaining bivalence. Define WCE(E) by

    forall p (E(p)=top or E(p)=bottom);
    forall p (E(not p) iff not E(p));
    forall F:tt (E(forall p Fp) iff forall p E(Fp)).

These are three ordinary object-language clauses. The last two display current biconditionals, not object identities. The original CE definition is preserved; WCE is a simpler existential presentation whose equivalence requires proof.

**Theorem 22.** Bare C proves

    exists E WCE(E) iff exists E CE_t(E).

More precisely, every WCE witness determines a persistently possible atom w satisfying LB_t(w), and its canonical strong evaluator E_w has the same current application VALUES as E:

    forall p E(p)=E_w(p).

It is not asserted that E=E_w in bare C, or that the original E satisfies the strong quantifier identity.

First, bivalence makes the weak negation biconditional an object identity: E(not p) and not E(p) are bivalent and currently agree. Endpoints also follow. If E(top)=bottom, negation gives E(bottom)=top. Apply the weak quantifier clause to F(p)=p and use the C identity forall p p=bottom. Its left side is true; its right side forall p E(p) is false at p=top. Contradiction. Hence E(top)=top and E(bottom)=bottom.

Now put w:=forall p(E(p)→p). If E(p)=top, the proposition E(p)→p equals p and its evaluation is top. If E(p)=bottom, that proposition equals top and its evaluation is again top. Thus every current E(E(p)→p)=top. The weak quantifier biconditional makes E(w) currently true and bivalence makes it top. NI on E(w)=top and E(bottom)=bottom prevents w from ever becoming bottom. The same decision argument as Theorem 17 gives Atom(w) and E(p)=top iff w≤p. Finally, if forall p w≤Fp, all E(Fp) are true; the weak quantifier biconditional makes E(forall pFp) true, hence w≤forall pFp. This is LB_t(w). Theorem 19 supplies the strong canonical E_w. Its root values match E because both are top exactly on the propositions above w. The reverse implication CE⇒WCE is immediate.

The construction preserves the evaluation of any designated p. Consequently Theorem 20 has the following compact, entirely equivalent formulation over C:

    forall p [Diamond p → exists E:tt (WCE(E) and E(p))]
        iff Box Plenitude.

In words: every possible proposition is made true by an admitted bivalent evaluation preserving negation and proposition quantification. This is an exact definition audit, not a stronger axiom or a changed language. The only rigidity requirement explicitly postulated is that each current evaluation value is top or bottom; the theorem derives the full core from the density of such evaluations.

### An actual weak witness need not be a strong witness

The reverse-retract category of §23 makes the guardrail concrete. At W, Out(W)={id_W,g}; at C, Out(C)={id_C,r1,r2,e1,e2}. Put

    q0={r1,r2,e1,e2} in D_t(C).

A proposition in im(g^t) has a common bit A at r1,r2 and a common bit B at id_C,e1,e2. Thus q0 is not in that image. Define E's root component by

    E_W(p)=top_W if id_W∈p, and bottom_W otherwise.

For a target proposition q, define E_C(q) to contain r_i and e_i exactly when r_i∈q. Its id_C bit is the common r_i bit when q∈im(g^t), and is zero otherwise. These components form an admitted full action object. The g-naturality equation holds by the image rule. For returns r_i it holds because both required output bits equal q(r_i). For endomorphisms e_i, the proposition e_i^t(q) is a g^t-image with bits A=q(r_i), B=q(e_i), so both sides of the naturality equation are the corresponding constant proposition. In particular E_C(q0)=q0.

Every root E(p) is the constant truth value of p at W. Therefore WCE(E) holds: the actual truth of negation and universal quantification is evaluated correctly. Now define an admitted F:tt by F_W(p)=top_W for every root p, and F_C(q0)=q0 while F_C(q)=top_C for q≠q0. This is natural because q0 is not in the image of g^t, every nonidentity restriction of q0 is top, and every e_i^t(q) lies in that image.

The proposition Q:=forall p Fp is {id_W}: all root instances are true, but the target q0-instance is false at id_C. Hence E(Q)=top_W. By contrast, forall p E(Fp) is also {id_W}, since its q0-instance at C is E_C(q0)=q0 and is false there. Thus

    E(forall p Fp) ≠ forall p E(Fp).

This is a genuine WCE witness failing the strong object-identity clause. The existential equivalence in Theorem 22 works by canonical replacement; it does not silently strengthen the original weak witness.

**Parallel separation form for BR.** BRD is also equivalent to the statement that BR evaluators separate every distinct pair of propositions, hence to ND_t. Under ND_t, if p≠q, one of d=p∧not q or d=q∧not p is nonzero. Set E_d(r):=Diamond(d∧r). Every value is top or bottom by ND_t, E_d(bottom)=bottom, and E_d(top)=top because d is persistently nonzero. Its evaluations of p and q are different. The converse follows by separating p≠bottom from bottom. Thus one may state the definition ladder uniformly as BR-separation iff ND_t, and complete-evaluator separation iff T; a single possibility detector need not separate every pair.

## 28. Full-category calibration of the two separation axioms

These are local-at-A semantic equivalences for a full action hierarchy on a small category K. They concern the designated root A; a property at A need not hold at its successors unless the argument says so. Individuals may be any admissible nonempty base functor.

For g:A→C, let j_g:Out(C)→Out(A) send k to kg. Then g^t is inverse image along j_g. Hence g^t is injective iff j_g is onto, and g^t is onto iff j_g is injective. The first condition is equivalent to g having a left inverse: onto j_g gives k with kg=id_A, and conversely such a k factors every outgoing h as h=(hk)g. The second condition says exactly that g is epic.

It follows that

    ND_t at A (equivalently BR-density or BR-separation)
      iff every outgoing arrow from A is split monic;

    BF_t at A
      iff every outgoing arrow from A is epic.

The BF sufficiency proof lifts each target proposition to a root proposition and uses naturality of application. For necessity, the full intension with extension im(g^t) at each outgoing g makes every current Fp=top, whereas forall p Fp is true at g only if g^t is onto. This is the same image-test used in Theorem 18. The ND equivalence directly expresses preservation of distinct current proposition objects along every arrow.

**Theorem 23.** In a full action hierarchy, the following are equivalent at A:

    CED; WCE-density; T=Box Plenitude; Box ND_t;
    every outgoing arrow from A is an isomorphism.

One proof uses Theorem 20 and the preceding ND/BF tests: CED gives both, so every outgoing g is both split monic and epic. If kg=id_A, then gkg=g and cancellation of the epic g gives gk=id_C, so g is invertible.

For the boxed-ND equivalence, Box ND_t makes every outgoing g split monic, say kg=id_A, and makes k split monic at C, say lk=id_C. Then l=lkg=g, so gk=id_C. Conversely all reachable arrows being invertible makes every proposition transport injective.

There is also a direct evaluator proof. Density applied to each singleton proposition {g} forces its CE atom to be that same singleton. Thus every outgoing g is epic and factors through every outgoing arrow. In particular, the singleton {id_A} is persistently possible, so every outgoing g has a left inverse. Epicness then gives invertibility as above.

Conversely suppose every arrow out of A is invertible. For any outgoing h and any g, h=(h g^{-1})g, and h is epic. Theorem 18 supplies a CE for the singleton {h}. Every nonzero root proposition contains an arrow h, so CE-density follows. Equivalently the successor category generated by A is a groupoid: if g:A→C and u:C→D, both g and ug are invertible by the root hypothesis, so u=(ug)g^{-1} is invertible. Thus the converse covers all relevant successors, not only the root's currently named arrows. Any individual functor sends these arrows to bijections automatically.

The reverse-retract model of §23 calibrates the locality. At W its only outgoing nonidentity arrow g has a left inverse, so ND_t and BR-density hold there; id_W also supplies CE. But g has two left inverses and is not epic, so BF_t, CED and T fail. At C even ND_t fails: for example the singleton {r1} becomes empty along r2. Hence ND_t at a root does not by itself entail Box ND_t in C. The recorded BF_t premise in the boxed-ND lift is substantive. Complete-evaluator density is stronger and, through its equivalence with T, supplies the stable all-type core.

These full-model equivalences are not asserted to characterize arbitrary Henkin C structures by their original presentation category. A proper Henkin hierarchy can omit the image-test intension or external singleton propositions. The general object-language results remain Theorems 19–22.

### Necessary evaluator existence still does not give evaluator density

A category with a zero object 0 supplies CE at every object A: the unique arrow h:A→0 factors through every outgoing g:A→C via the unique C→0, and h is epic because there is only one arrow from 0 to any fixed target. The factorization is unique, so the atom {h} remains an atom. Thus its full action hierarchy satisfies Box CE and Box exists w Box Atom(w) at every point. These conclusions do not imply that every possible proposition contains such an atom.

For a finite concrete example take two objects 0,C and arrows g:0→C, k:C→0 with kg=id_0 but e=gk≠id_C. The outgoing arrows are

    Out(0)={id_0,g},  Out(C)={id_C,k,e},  e²=e.

This is the category generated by a proper retract; it can be realized by the singleton {a}, the two-element set {a,b}, inclusion g(a)=a, and constant k. The object 0 is both initial and terminal in this generated category. Use a constant singleton individual functor if no individual-domain variation is desired.

At root 0, g is split monic, so ND holds at every type: functoriality gives k^sigma g^sigma=id at each typed domain, hence g^sigma is injective. However id_C g=e g with id_C≠e, so g is not epic, and BF_t fails by the full image-test. Hence T and evaluator density fail. Full action Atomicity holds at every relational type and every successor, as in §22. The verified package is therefore

    C + ND_all + Box CE + Box Atomicity_all
      + Box exists w Box Atom(w) + not BF_t + not T.

At C the atom {id_C} vanishes along k, so ND_t does not hold necessarily. This makes the scope explicit: even necessary existence of complete evaluators, necessary ordinary Atomicity, and current full all-type ND together do not replace the density requirement. The missing root atom {g} is persistently possible but its arrow is not epic, so it has no complete evaluator.

## 29. Further independent algebraic audits

The companion algebraic report §§32–41 received the following checks. These are informal independent audits of the displayed arguments, not formal verification or claims that the underlying published constructions have been reconstructed.

The full-in-M transfer of a ZFA model of uniform Ultrafilter Choice plus failure of BPI is sound: take singleton (or fixed two-element) worlds, individual field a tagged union of the bad Boolean-algebra carrier with omega, and all finite-type function domains as computed inside M. Fixed-term interpretation uses M's Separation and Replacement; functional graph recovery, singleton atoms and internal infinity require no Choice in M. Typed ultrafilter kernels are the canonical extensions of the M-chosen fiber ultrafilters. Any admitted ultrafilter on the coded bad algebra would be an M-ultrafilter, contradiction. The underlying ZFA separation remains an explicit literature-dependent premise of algebraic §32.

The equivalence UFC iff uniform nonprincipal-ultrafilter choice also passes. For the reverse direction, split on whether the ambient output type is internally finite. In the finite case one admitted order of that single finite field supplies fiber choices. In the infinite case inflate each nonempty fiber R_x to R_x times the whole output field. Its infinitude follows from any one witness in R_x, without choosing witnesses uniformly. A free ultrafilter on each inflated fiber pushes forward to the required possibly principal ultrafilter on R_x.

The complete-Boolean categorical characterization is exact: over T, Intensional Choice at all types is equivalent to injectivity of B_t among represented NONTRIVIAL internally complete atomic Boolean algebras with complete homomorphisms. A dual lifting problem is a serial world-indexed relation, and Enc/Dec turns its selector into IC. Conversely a serial relation R⊆Worlds×D_sigma gives the complete embedding B_t→P_int(R) by first-coordinate inverse image; an injective lift supplies a dual section and hence world-indexed choice. The nontrivial qualification matters to blanket projectivity/splitting statements: a surjection from a nontrivial Boolean algebra onto the trivial algebra has no unital section. Nonempty atom fields provide the one default atom used in the valid no-Choice splitting argument.

For finite-operation Boolean maps, BPI_int is equivalent to injectivity of every represented nontrivial complete atomic target. Atom evaluation pulls a proposed map back to ultrafilters; BPI gives extensions pointwise, UFC on the candidate-extension fields gives uniformity by evaluation sums, and admitted joins of selected target atoms give the extension homomorphism. The converse already follows from injectivity of the two-element target. No arbitrary-meet preservation of the resulting map is asserted.

Finally, algebraic §§40–41 prove and correctly distinguish

    BPI_int iff FineUF + ACfin_all,
    FineUF iff indexed Rado selection iff binary Rado selection.

A short independent proof of the first converse uses the represented field J of pairs (x,y) satisfying a serial rigid R. A fine ultrafilter V on Fin(J) makes the event that x has some pair in F large. Each covered finite row {y:(x,y)∈F} is a finite nonempty field; ACfin_all chooses one of its values uniformly in (F,x). Its V-pushforward is an ultrafilter concentrated on R_x. No family of partial choice functions or uniform pointwise witness selection is needed. An alternative proof chooses a cell from the finite partition of each R_x by a finite set of property tests, then takes the fine-ultrafilter limit of cell-containment evaluations.

In the Rado principle the local choices are supplied as an admitted table g(F,i), for i∈F, and the conclusion is h with every finite restriction h|F agreeing with some g(F',-), F'⊇F. Dropping the supplied-table premise changes the principle. FineUF gives the unique ultrafilter-selected value in each finite output field. Conversely binary Rado applied to a tagged union of requirement labels i and Boolean-event labels P reconstructs a fine ultrafilter: a finite approximation makes finitely many h(P)-bits agree with point evaluation at the finite set of requirement labels present. The tags are represented by relational tuple codes, and the argument uses only internally finite fields. No infinitary proof rule is inserted.

## 30. Finite Boolean evaluators are a genuine intermediate requirement

To isolate the role of quantification, let FBE(E) say that E:tt is bivalent at every current input and preserves negation and binary conjunction as proposition identities. The endpoint clauses follow: E(bottom)=E(p∧not p)=E(p)∧not E(p)=bottom, and negation gives E(top)=top. Equivalently, given bivalence, these finite preservation laws may be written as current biconditionals. Define finite-evaluator density by

    FBED := forall p[p≠bottom → exists E(FBE(E) and E(p)=top)].

**Theorem 24.** Over C,

    T ⇒ FBED ⇒ ND_t,
    ND_t + Atomicity_t ⇒ FBED.

The first implication follows from complete evaluators. The second uses the NI endpoint argument: an evaluator sending p to top prevents p from becoming bottom; symmetric difference then gives ND_t. For the final implication choose an atom w≤p. ND_t makes w persistently nonzero. The canonical E_w(q)=Box(w→q) is bivalent, preserves negation by atomhood, and preserves binary conjunction by the modal distribution law. It sends p to top. No relative or global Barcan law is needed for these finite operations.

In full action hierarchies Atomicity_t always holds, so FBED is exactly ND_t there. The reverse-retract and zero-object models therefore satisfy FBED at their distinguished roots while failing T. Quantifier preservation in the density axiom cannot simply be omitted, even in finite full models.

More significantly, FBED is NOT equivalent to ND_t for arbitrary Henkin C models. The following explicit atomless example separates them; its soundness and closure were independently audited by the mixing-model lane. This construction and its verdicts are original here (`source_id: misc`).

### The finite-coordinate Boolean-group model

Work in the ordinary external ZFC metatheory. Let G=2^N under coordinatewise addition modulo two, and let W=G, with G acting on worlds by translations. For finite S⊆N, write G_S={g:g|S=0}. A supported object is one fixed by some G_S. Use a singleton individual domain with trivial action, or the fixed domain N to obtain quantified individual Infinity as below. Let

    D_t={P⊆W : P is fixed by G_S for some finite S}.

These are exactly the finite-coordinate subsets of W: a G_S-invariant set is a union of the finitely many cosets determined by its S-bits. Recursively let D_(sigma tau) be ALL functions D_sigma→D_tau with such a finite-coordinate support under the conjugation action. Necessity is universal quantification over the constant world set W; equality is literal identity of typed objects; application is function application. Evaluate at any designated world, for example the zero sequence.

**Closure and C-soundness.** Boolean operations are equivariant. A formula with a finite tuple of parameters has a common finite coordinate support S, so its truth set is G_S-invariant and hence belongs to D_t. This includes universal quantification: the quantified typed domain is G-invariant, so quantification preserves the same common support. An abstracted term has support contained in the supports of its free parameters; at each argument its value has support bounded by that finite support together with the argument's support. Thus lambda abstraction lands in the indicated full supported function domain. This structural induction verifies the ordinary Henkin closure and the C rules; it does not assume that a world point itself has a support.

The semantics is constant-domain S5 with literal typed identity, so Box ND_all and BF_all hold. The world points are generally not supported: no finite coordinate set fixes one complete infinite bit sequence. That omission is intentional. It does not affect C-soundness; it prevents the singleton-world atom argument used in the T models.

D_t is atomless. Given a nonempty finite-coordinate proposition P supported by S, choose n∉S. Its intersections with {w:w_n=0} and {w:w_n=1} are both nonempty proper admitted parts. Hence Atomicity_t fails.

**No complement-preserving bivalent evaluator exists.** Suppose E:tt were bivalent and negation-preserving, with finite support S. Choose n∉S and put p_n={w:w_n=1}. Let g flip only coordinate n. It fixes E, top and bottom, while sending p_n to not p_n. Equivariance therefore gives

    E(not p_n)=E(g p_n)=g E(p_n)=E(p_n),

where the last equality uses bivalence. Negation preservation instead gives E(not p_n)=not E(p_n), impossible. Thus no such E exists at all, even without requiring binary-conjunction preservation. In particular FBED fails while Box ND_all and BF_all hold.

This proves a strict gap between BR-separation/ND_t and finite Boolean evaluator density. The other strict gap, FBED versus complete-evaluator density/T, is witnessed by the finite full reverse-retract or zero-object examples. The resulting exact implication ladder is

    ND_t  <  FBED  <  CED = T,

where the arrows point from the stronger condition on the right to the weaker condition on the left, and strictness is model-backed. No claim is made that FBED is identical, over bare C, to a conventional abstract Boolean Prime Ideal principle. It is a separation condition by ADMITTED bivalent Boolean evaluations. An ordinary current truth predicate need not be bivalent: the identity operation p↦p always evaluates actual truth but does not supply the required constant truth values. That distinction is essential in the atomless example.


### Intensional Choice and the parameter boundary in the Cantor model

The same example satisfies Intensional Choice at EVERY type. If Box exists x F(x), the admitted truth sets F(x), as x ranges over the output domain, form a cover of the FULL Cantor product W by clopens. External compactness gives a finite subcover F(x_1),...,F(x_n). Finite priority pasting defines

    G(x) iff OR_(j=1,...,n) [x=x_j and F(x_j) and AND_(i<j) not F(x_i)].

This admitted relation has support bounded by the finite union of the supports of F and the x_j. At every world it chooses exactly one eligible object. The only metatheoretic compactness used is ordinary compactness of 2^N; it can also be proved directly by the finitely branching binary tree of cylinders not covered by any finite subfamily. This argument depends on using the full compact product, rather than the dense direct-sum set of finite bit sequences. The mixing-model lane independently checked this strengthening.

**Stronger choice verdict (independently audited with the mixing-model lane).** The Cantor model satisfies every boxed Modalized Relational Choice and Relational Choice instance. If R has finite coordinate support S, the subgroup G_S acts freely on W times the input domain, because its translation action on W is free. For a necessarily serial R, choose externally one eligible output for a representative of each orbit and extend these choices equivariantly along the orbit; freeness makes the resulting selector well-defined. Its graph is admitted: at fixed input x and output y its truth set is invariant under G_(S union supp(x) union supp(y)), hence is a finite-coordinate clopen, while the whole curried relation has support S. This gives a necessarily functional subrelation of R, proving Modalized RC. For merely locally serial R, apply the same construction on the invariant field of eligible world-input pairs and choose arbitrary default outputs on the remaining orbits; at every world where R is serial the selector lies below R. Thus RC holds at every world as well. External orbitwise choices use only the stated ZFC metatheory and do not assert an admitted operation representing the selected outputs. Consequently the lower separation remains valid over C5 plus Box MRC_all, and in particular over C5 plus Box RC_all.

Take E=N with trivial G-action to obtain genuine quantified AxiomInfinity_e. Every rigid individual subset and individual functional graph is admitted with empty support. In particular the successor graph is an injection from E into its proper subfield E\{0}; the ordinary internal induction for Frege-finite fields rules out such an injection on any finite field. Thus the verified separation may be stated as

    C + Box ND_all + BF_all + Box MRC_all + Box RC_all
      + IC_all + AxiomInfinity_e + not exists E FBE(E).

The same closure proof survives arbitrary set-sized conjunctions/disjunctions whose formulas have ONE COMMON FINITE free-parameter/support set: the resulting truth set remains invariant under the same G_S and is still a finite union of its cosets. Such a specified infinitary extension still has the displayed IC proof and no finite Boolean evaluator. Allowing independently named parameters p_n for all coordinates changes the language: their countable conjunction is a singleton world and is not admitted in this D_t. The common-parameter restriction is substantive.

Finally, this is a C Henkin model whose semantic world points are unsupported. It cannot be expanded, retaining D_t, to a full Gallin world sort containing every actual Cantor point together with equality and comprehension: fixing a world parameter w_0 would make the singleton predicate v=w_0 available. This does not contradict the Gallin representation theorem for T, whose Atomicity hypothesis is deliberately absent here.

## 31. Audit of uniform evaluator selectors

The companion algebraic report §42 passes an independent audit. Over T, an admitted selector assigning to every nonzero proposition a complete bivalent evaluator recognizing it is equivalent to an internal well-order of the world-atom field. The unique generating atom of each chosen evaluator selects a member from every admitted nonempty world subfield; the internal Zermelo argument supplies the well-order. Conversely take the least atom below each nonzero proposition. This is strictly stronger than propositional complete-subalgebra retraction and independent of all-type Intensional Choice, as witnessed by the two supported models in that report.

At B_(sigma t), uniform complete evaluator selection is equivalently a well-order of both the world field and D_sigma, because its atoms form the represented product of those fields. At every sigma these principles recover Box Functional Choice. All products and selections are represented internal constructions; external fullness is unnecessary.

Two useful refinements are correct. First, EU_e plus a well-order of world atoms already well-orders E: assign to each individual the least world realizing its singleton profile. Thus this combination gives individual-output Relational Choice without IC_e. Second, uniform complete retractions for all complete propositional subalgebras are equivalent to the same evaluator-selection principle; it suffices to assign them uniformly to {bottom,p,not p,top}. The forward implication evaluates the retraction at its relative atom p. Conversely a uniformly chosen atom c(b) in each subalgebra block defines H_A(q) as the join of those blocks b with c(b)≤q. The analogous finite-operation version chooses ultrafilters on the blocks, not actual world atoms, and is correspondingly weaker. Relational-argument EU remains inconsistent by the earlier diagonal, so the nonvacuous original-type instance of the profile corollary is the individual one.


## 32. Ordered cuts give finite-evaluator density without atoms

This is a second direct supported Henkin model, proposed by the parent lane and independently audited here and by the mixing-model lane. Work externally in ZFC. Let G=Aut(Q,<), use finite rational supports, and take W to be the nonprincipal Dedekind cuts of Q, equivalently the irrational cuts. Use a fixed singleton or a fixed N as the individual domain. D_t consists of all supported subsets of W; recursively take every supported function at each allowed arrow type.

For a finite rational support S, the orbits of its pointwise stabilizer on W are exactly the |S|+1 open interval cells cut out by S. Thus the admitted propositions are finite unions of rational-ended interval cells. The same finite-parameter equivariance induction as in §30 proves all ordinary C lambda and quantifier closure. Literal typed identity and universal constant-domain accessibility give Box ND_all and BF_all. D_t is atomless, since every nonempty interval cell can be split at a further rational point.

For q∈Q define the right-germ evaluator E_q^+(P) to be top precisely when P contains all irrational cuts in some interval (q,r), where r>q is rational. Every finite interval algebra has a definite truth value immediately right of q. Consequently E_q^+ is bivalent and preserves complements and finite intersections. It has support {q}, because every increasing automorphism fixing q preserves the right-germ condition. Every nonempty admitted P contains an interval and therefore a rational q with a sufficiently small right neighborhood inside P. Hence this model satisfies FBED but not Atomicity_t or T. Taking fixed E=N adds quantified individual Infinity by the admitted successor graph.

The failure of Intensional Choice is explicit. Fix q and let

    F(p) := E_q^+(p) and not p.

At every irrational cut c there is an admitted p with a positive right germ at q that misses c: choose a sufficiently short rational-ended interval immediately right of q. Thus Box exists p F(p). Suppose an admitted selector G(p) had finite rational support T, enlarged to contain q. Choose an irrational c in the T-cell immediately right of q. The unique selected p at c must be fixed by every automorphism fixing T and c. The finite set of rational boundary points of p is canonical. Every rational outside T has an infinite orbit under that subgroup, even with the additional constraint of fixing c; therefore those boundary points must all lie in T. A proposition with boundaries in T and a positive right germ at q contains the entire T-cell immediately right of q, including c. This contradicts the required not p at c. Hence IC_t fails.

There is also a useful obstruction to repairing this example by simply making its world space compact. In any compact topological world model whose admitted propositions are clopen, the positive clopens of an admitted finite Boolean evaluator have the finite-intersection property. Compactness gives a world in their intersection. Comprehension already admits

    w_E := forall p(E(p)→p),

so this intersection is a nonempty admitted proposition. The evaluator's complement decisions show that w_E is an atom. Finite-evaluator density therefore forces Atomicity in such a compact clopen model. With the C5/Barcan assumptions above it forces T. This is a statement about that semantic presentation, not a theorem that IC alone forces Atomicity.

## 33. Audit of the generic Boolean Henkin construction

The stronger boundary C5+IC_all+FBED versus T is resolved by the generic-ultrafilter construction in `research/2026-10-22/evaluation-and-choice/structural-mixing-models.md`, to which this section supplies an independent audit rather than a duplicate full development. The construction is in ordinary external ZFC; no countable transitive model or consistency-of-ZFC assumption is needed.

Choose an atomless complete Boolean algebra B, form the full finite type hierarchy with base t=B and e=N, and choose a sufficiently large regular H_theta containing these domains, their full function spaces, and all relevant witnesses. Take a countable elementary substructure M containing the typed hierarchy parameters. The Henkin domains are the M-parts of these full domains. An M-function maps M-arguments to M-values, and restriction is faithful: if two such full functions differ, elementarity finds an argument in M where they differ.

Worlds are ultrafilters on the countable Boolean algebra B∩M meeting the traces of every M-coded dense subset of B^+. Every nonzero b∈B∩M belongs to such a generic ultrafilter, by an external enumeration of the countably many dense requirements. Thus necessity of b is exactly b=1. Boolean inequality and every typed object inequality remain literal and necessary, and the frame is constant-domain S5.

The critical quantifier check passes. For f∈M of Boolean-valued output, let q be its full-domain join in B. Then q∈M. The dense set of nonzero a satisfying either a≤not q or a≤f(x) for some full-domain x belongs to M. A generic world containing q therefore contains such an a from M below f(x); elementarity supplies x in the restricted Henkin domain. Conversely each f(x) lies below q. Hence q is true exactly when some admitted x satisfies f(x). Duality proves the universal-quantifier clause. This is the precise point where arbitrary ultrafilters would fail and genericity is essential.

Lambda closure follows because the full typed function defined by a fixed formula and M-parameters exists in H_theta and is returned to M by elementarity. The modal truth operation b↦1 iff b=1 is definable there. Full function restrictions are faithful, and distinct Boolean values are separated by generic worlds. These facts verify the H/Logical-Equivalence requirements as well as the ordinary term and formula clauses; no mere agreement at one designated generic is promoted to identity.

Internal ultrafilters on B in M give admitted bivalent finite Boolean evaluators. Elementarity returns a uniform assignment of such an ultrafilter containing each nonzero b, so the model has even UNIFORM finite-evaluator selection, not merely FBED. It remains atomless: every nonzero b∈M has a proper nonzero part in M by elementarity. Maximal-antichain refinements in M give Intensional Choice at every type, and rowwise refinements give the stronger modalized relational-choice schema described in the companion report. The witnesses are Boolean-valued relations; this does not represent every current functional relation by an operation object.

The distinction is visible in the necessarily functional truth-choice relation. This relation and its Boolean atom calculation are already written out in `topics/classicism/writeups/full-boolean-valued-atom-and-atomless.md` §6; the underlying model there is sourced to Bacon, *Could the truths of mathematics have been different?*, online appendix §B.2, pp. 7–9 (PDF pp. 41–43). No novelty is claimed for this witness. Here it is applied to the generic Henkin model:

    U(p,q) := [p and (q=top)] or [not p and (q=bottom)].

Representing its actual graph at a generic world by an admitted X:tt would code that generic ultrafilter as the trace of an M-ultrafilter on B. The complement of any M-ultrafilter is dense in an atomless B and belongs to M, contradicting genericity. Thus Plenitude and Functional Choice fail, despite all the stated relational/intensional choices. In particular this gives a model-backed strictness of finite versus complete evaluator density even after adjoining IC_all, genuine Infinity, and the verified modalized relational-choice instances. The parent's and mixing lane's independent checks agree with this audit.

This separation is for the fixed finitary C. It must not be advertised as surviving every external countable conjunction allowed in C_omega: with fixed E=N and countable M, the formulas OR_(n∈A)(x=n) for arbitrary external A⊆N would add rigid subsets absent from M. M-coded families are covered by the proof, whereas arbitrary externally indexed infinitary syntax changes the closure requirements.


## 34. Existing Boolean-valued construction and optional infinitary scope

The generic model sharpens the semantic form of the separation, but is not needed merely to separate C5+IC_all+FBED from T. The existing write-up `topics/classicism/writeups/full-boolean-valued-atom-and-atomless.md` uses B=2 times A, with A complete atomless, full typed function domains, and designated truth given by the first coordinate. Its atom projection preserves every meet and join, so it gives the required ordinary truth clauses at its designated evaluation. Its source is identified in §33 above; its previously recorded verdicts include C5, boxed BF, current Functional Choice/Plenitude, and failure of Atomicity_t.

Two further verdicts follow by direct arguments, without changing any record. First, metatheoretic AC chooses an ultrafilter containing each nonzero Boolean value, and full function domains admit the entire evaluator assignment. Thus uniform finite-evaluator density has Boolean value 1. Second, a maximal-antichain refinement of each necessarily serial Boolean row gives a functional Boolean-valued subrelation, exactly as in generic-model §31.4 of the companion mixing report. All rows can be refined uniformly by metatheoretic AC, and the resulting relation is admitted by fullness. Hence every modalized relational-choice and Intensional Choice instance has Boolean value 1, as do their boxes. Taking individual domain N adds quantified Infinity. This is already a model of

    C5 + Box BF_all + Box MRC_all + uniform FBED + AxiomInfinity_e + not T.

The distinction between current and necessary Functional Choice is essential: the designated atom supports current FC, while the atomless component prevents boxed FC. The generic model instead supplies ordinary constant-domain Kripke worlds with no propositional atoms anywhere and boxed failure of Plenitude/FC. These are different strengths of semantic realization, not conflicting verdicts.

The full Boolean-valued construction also handles arbitrary SET-SIZED conjunctions and disjunctions with a common finite free-variable set, ordinary finite quantifier formation, and the corresponding lambda comprehension and Logical-Equivalence rules. Completeness of B interprets the connectives, full function domains interpret their abstractions, and the designated atom projection preserves all the relevant meets and joins. The exact proof rules meant here are local set-sized conjunction/disjunction introduction and elimination, the ordinary finite quantifier rules, and Logical Equivalence restricted to theorems of that extended H. No unrestricted infinitary distributivity scheme or completeness for every semantic L_infinity,omega validity is silently added: an atomless complete Boolean algebra need not satisfy arbitrary complete distributivity. Under those explicit local rules the Boolean soundness induction applies. Thus this specified infinitary strengthening does not repair the finite-evaluator/IC versus T gap. This does not assert that full function domains or a complete atom projection are present in the generic Henkin construction.

For completeness, an optional relative forcing construction preserves the ordinary generic-world presentation for countable syntax. In a ground universe take P to be the countable partial functions omega_1→2, ordered by extension, and B=RO(P). Choose p_b∈P below each nonzero b∈B. Force with the full-support product of the cones P below p_b. This product is countably closed: coordinatewise unions of a descending countable chain remain countable partial functions extending p_b. Its extension adds no countable sequences of ground objects. The coordinate generic ultrafilters G_b give a world containing every nonzero ground b. Keep the ground full finite B-type hierarchy as the Henkin domains.

Every countable well-founded formula and parameter code over those ground domains is still ground, so the Boolean denotation and the generic truth lemma provide countable conjunction/disjunction closure. Ground antichain refinements and ground ultrafilter choices preserve all the stated IC/MRC and uniform finite-evaluator properties; atomlessness and the truth-choice obstruction to Plenitude persist. This optional statement is a relative forcing-extension construction, independently audited by the mixing lane. It does not assert an internal generic over the same ground universe, does not allow arbitrary set-sized new syntax, and does not introduce infinite quantifier blocks. The simpler full Boolean-valued construction already suffices for the underlying logical nonimplication.

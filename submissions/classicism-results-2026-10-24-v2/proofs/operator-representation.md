# Atomic observers and finite stabilizers

Original mathematical argument, direct source misc; unpaginated.

1. SCOPE

Bool*(O) requires the composite operation identities for top, bottom,
negation, conjunction and disjunction. For a finite set Delta of types,
Q*_Delta(O) requires, at each sigma in Delta,

  (lambda F:sigma t. O(forall x:sigma Fx))
    = (lambda F:sigma t. forall x:sigma O(Fx)),

and the analogous existential identity. Write S*_Delta for

  forall p,q [p=q IFF forall O
    ((Bool*(O) AND Q*_Delta(O))->O(p IFF q))].

The empty list gives full Boolean separation. Every type list is finite;
claims for all lists are schemata. The base of sections 2-3 is C in the
fixed relational type system. External bijections in sections 4-6 are
arrows of a semantic construction, not object-language functions of type ee.

2. ATOMS GIVE FULL COMPOSITE OBSERVERS UNDER BARCAN ASSUMPTIONS

For each finite Delta, over C,

  Atomicity_t + BF_t + {BOX BF_sigma : sigma in Delta}
    implies S*_Delta.                                         (A)

Proof. For a current atom a let c=DIAMOND a and use the admitted term

  O_a(p)=(c AND BOX(a->p)) OR (NOT c AND p).

The proof in boolean-observers-and-atoms.txt section 1 establishes its
pointwise literal Boolean laws without a stability assumption on a. BF_t
upgrades these to the composite identities: NI makes each output equality
necessary; BF_t collects these necessities under its one or two universal
proposition arguments; Intensionality identifies the composite operations.
This is an application of BF_t to necessary identities, not an application
of Equivalence to a conditional material biconditional.

For universal commutation, C proves the closed conditional

  BF_sigma -> forall a,F
    [O_a(forall x Fx) IFF forall x O_a(Fx)].                    (2)

To verify it, if c is true the two sides reduce in truth to the principal
test P_a(p)=BOX(a->p); BF_sigma and CBF give its commutation. If c is false,
a=bottom and O_a is the identity operation. This proof does not need a to
be an atom. Necessitate the unconditional theorem (2). Under BOX BF_sigma,
normality and CBF therefore give, for the chosen a,

  BOX forall F [O_a(forall x Fx) IFF forall x O_a(Fx)].

Intensionality at (sigma t)t gives the required composite identity directly;
no extra BF_(sigma t) assumption is used. The full Boolean identities and
the C quantifier duality identities give the existential composite law.

If p!=q, choose an atom a below their nonzero Boolean symmetric difference.
At the current point O_a(r) is true iff a<=r. It therefore distinguishes
p and q. The forward separation direction uses the qualified top law.
This proves (A). The same formula for O_a works for every listed type.

Consequently Atomicity_t plus BOX BF at every type supplies every S*_Delta;
the type-t boxed BF instance includes the extra BF_t premise of (A).
The sufficient premise here includes BOX BF.

3. C5 COROLLARIES AND AN EXACT ATOMIC CASE

C5+Atomicity_t gives BOX S*_Delta for every finite Delta. The recorded
C5 consequences give necessary BF at every type and necessary Atomicity_t.
One route to the latter uses Atomicity_t+BF to obtain Atomicity at all
relational types, followed by the recorded C5 atomicity stability theorem.
Apply the necessary form of (A), using axiom 4 on the boxed BF instances.

Thus this positive package gives separation and its persistence with the
user's full composite identities. No Actuality premise is needed for this
sufficient result.

Over C5+Actuality there is also an exact classification:

  Atomicity_t iff S*_{t}
    iff {S*_Delta for every finite Delta}
    iff {BOX S*_Delta for every finite Delta}.                 (B)

For the only remaining implication, apply the quantifier operation identity at t to each predicate. C5+Actuality supplies the correct endpoint
evaluator B(p)=BOX(a->p) from the actual atom a. Composing B with a separating
test and applying its quantifier law to w=forall p(Fp->p) gives an atom below
each nonbottom proposition. That proof is in reverse-entailment-countermodel.txt
section 5 and database-combination-obstruction.txt section 5. The positive
direction and persistence now follow from (A), so (B) covers the full
composite reading for the composite qualification.

4. EXACT REPRESENTATION OF EVALUATION AT AN ARROW

Consider the symmetric ideally-full models with countably infinite
underlying sets, every bijection between every pair as an arrow, finite
pinning ideals, and designated symmetry groups G_V at their objects. This
is the same construction framework as ordered-symmetry-observers.txt.
Assume G_V is closed in the pointwise-convergence topology for the converse
part of the theorem. No closedness is required for the construction.

Fix b:W->V. Evaluation at b means the truth test p |-> [b belongs to p].
Let G_W,(S) denote the subgroup fixing finite S pointwise. The following
are equivalent when G_V is closed:

  (i) Some admitted E:tt realizes this truth test on every current p.
  (ii) For some finite S subset W,
           b G_W,(S) b^-1 is contained in G_V.                 (C)
  (iii) Such an E can be chosen to preserve every Boolean connective and
        both quantifiers at every type, by full composite identities.

The all-type claim in (iii) is about the same semantic witness satisfying
each finite qualification. It is not an object-language infinite conjunction.
Moreover this witness fixes every equality proposition, at every
type: in this groupoid equality propositions are top or bottom, and it
fixes both. This is the precise equality-fixing law, not an injectivity
requirement O(p=q)=(Op=Oq).

5. PROOF OF THE REPRESENTATION THEOREM

(i)->(ii). Let finite S pin E. For g in G_W,(S), pinning fixes E under
transport, and target symmetry preserves actual truth of every output.
Application coherence gives v(E(rho_t(g)p))=v(Ep). If E realizes evaluation
at b, this says bg belongs to p iff b belongs to p for every admitted p.

For any finite F subset W consider the admitted proposition

  p_F={k:W->V : k|F lies in the G_V-orbit of b|F},

with empty components at other targets. It is symmetric and pinned by F.
Since b belongs to p_F, so does bg. Thus some u in G_V agrees with
b g b^-1 on b(F). As F varies, this puts b g b^-1 in the closure of G_V,
hence in G_V by the stated closedness. This holds for every g in G_W,(S).

(ii)->(iii). Define the tt intension E at W by its truth profile at an
arrow h:W->Z with a proposition p at Z. If Z=W and h|S=g|S for some
g in G_W, put

  (p,h) belongs to E iff b g^-1 belongs to p.                  (3)

Otherwise put (p,h) in E iff id_Z belongs to p.

The special-case value is independent of the choice of g. If g'=g u
with u fixing S, then b(g')^-1=(b u^-1 b^-1)(b g^-1). The first factor
belongs to G_V by (C), and p is invariant under its postcomposition.
The profile depends on h only through its target and h|S, so S pins E.

For target symmetry k in G_W, the special case is carried from g to kg;
membership of b(kg)^-1 in rho_t(k)p equals membership of b g^-1 in p.
The special orbit and its complement are invariant under these symmetries.
In the default case id_Z belongs to rho_t(k)p iff k belongs to p iff
id_Z belongs to p. Thus E is symmetric and is an admitted tt entity.
No choice of orbit representatives is needed in definition (3).

At every future application, each output coordinate is evaluation of the
input proposition at a single outgoing arrow. More explicitly, at h:W->Z
and l:Z->Y, first select an arrow a out of Y using (3) for lh (or id_Y in
the default case). The output on p is true at l iff a l belongs to p.
Changing a within its allowed target-symmetry class changes no evaluation.

Coordinate evaluation preserves all Boolean operations. Because every
arrow is invertible, quantified propositions at Z are the intersections
or unions of the current outputs F(x), over D_sigma(Z), at every sigma.
Evaluation at a l commutes with those intersections and unions. This
establishes the Boolean and quantifier identities for every input at every
future h, hence the composite identities themselves. At id_W the chosen
g is the identity and E tests membership of b, as required. Finally
(iii)->(i) is immediate.

6. POSITIVE SEPARATION CRITERIA AND MODEL FAMILIES

It suffices for separation at W that every nonempty admitted proposition
contain an arrow b satisfying (C). The theorem then supplies a full logical
observer accepting that proposition. Here is a convenient condition ensuring
this: for each target V there are a bijection j_V:W->V and finite D_V such that

  j_V G_W,(D_V) j_V^-1 is contained in G_V.                    (D)

Given nonempty p pinned by P and h in p ending at V, extend the finite
partial injection (j_V^-1 h)|P to a finite-support permutation pi of W.
Put b=j_V pi. Then b agrees with h on P, so b belongs to p. Take
S=D_V union support(pi). Every g in G_W,(S) commutes with pi, so
b g b^-1=j_V g j_V^-1 belongs to G_V. The representation theorem applies.

This gives three useful positive families.

* Every ONE-OBJECT model with the full permutation base, finite pinning and
  any designated symmetry subgroup has full Boolean/quantifier separation.
  In (D) take j=id and D empty. Closedness is unnecessary for this sufficient
  result. The atomless permutation example is one member of this family.

* If the designated symmetry groups at different objects are conjugate
  under fixed identifications of their underlying sets, (D) holds at every
  object. Full separation therefore holds necessarily throughout the model.

* If G_W has a finite base, meaning G_W,(D) is trivial for some finite D,
  full separation holds at W regardless of the other designated groups.
  If this condition holds at every object, separation holds necessarily.

These are positive representation statements, not atomicity assumptions.
The observers generally return arbitrary propositions rather than only
top and bottom. No Ramsey-theoretic theorem is required for their construction.

SOURCES AND STATUS

New deductions and representation proof: misc, sections 2-6 of this note,
unpaginated. The patched atom calculation is in boolean-observers-and-atoms.txt
section 1. C5->necessary BF is the recorded
necessary-distinctness-necessary-r-implies-necessary-barcan-r, citing
Classicism, 16 May 2023, Proposition 2.3 p.22 and Figure 5 p.23.
The atomicity stability route uses atomicity-t-and-bf-imply-atomicity
(Cian Dorr's 23 September 2026 observation and its recorded proof), then
c5-and-atomicity-imply-necessary-atomicity (Classicism Proposition 2.6,
pp.25-26; concluding equivalences p.33). A proved-only Engine query with
empty background and explicit premises confirmed those consequences.

The model framework is Dorr, Boolean Completeness does not imply Rigid
Comprehension, draft of 30 July 2026, Definitions 15-18 p.8 and Proposition
20, as recorded in groups/symmetric-ideally-full.yaml and the construction
write-ups. The present operator theorem is not attributed to that source.

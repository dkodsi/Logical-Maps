# Finite S5 clusters for distinctness-preserving necessity

26 October 2026. Ordinary mathematical deductions by OpenAI Codex.
Direct source: `misc`, this note, §§1–6. Self-checked; no independent
audit, human check, formal certificate or literature-priority claim.
Neither unrestricted Strong Possibility question is resolved.

Work independently in the pure language and in exactly Σ={c:e→t},
without original individual names. Write M_L=Max(C_L), H=hat(Box),
D=dual(H), and H₂=hat(H). Every SP side condition below uses M_L.
Let Q_L be M_L plus StrongActuality, ordinary Barcan at every type,
and current Relational and Transversal Choice, as in
[the arithmetic comparison](barcan-arithmetic-conservativity.md).

## 1. The local S5 condition and the known inconsistent strengthening

Put

    Five_H := forall p (Dp -> H Dp),
    Collapse_H := forall p (p -> Hp).

These are unboxed sentences. Five_H is not being identified with the
necessarily NKB definition of an S5 operator in the topic background.
In C,

    Five_H <-> forall p (H₂p -> Hp).                         (1)

For the right-to-left direction, C proves Dp→H₂Dp: use q=Dp in the
definition of H₂ and the necessitated S4 theorem DDp→Dp. The displayed
collapse therefore gives Dp→HDp. Conversely, if H₂p has a true witness q,
then □(Dq→p). Reflexivity gives Dq from q; Five_H gives HDq. Since □≤H,
normality gives Hp. Only C-theorems have been necessitated.

StrongActuality gives Actuality and hence Vicinity. The recorded
Vicinity+BF_t theorem gives H₂p→Hp. Thus Q_L entails Five_H. This invokes
the existing theorem; it does not silently box Q_L's optional premises.

Full SP instead refutes Five_H, already at the one proposition E₁ saying
that all individuals are identical. The licensed DE₁ gives E₁, and the
licensed D(not E₁) gives not HE₁. Since C proves DE₁↔E₁, full SP gives

    DE₁ and not HDE₁.                                      (2)

This reformulates the already recorded incompatibility with H₂≤H. It is
not a new contradiction in SP. The comparison below makes Five_H true
at strongly possible targets while retaining its failure at the root.

## 2. A finite cluster-size sentence

For an external integer n≥1 define the closed finitary sentence C_n^H by

    exists w₁,…,w_n,
      (AND_i Dw_i)
      and (AND_i<j H not(w_i and w_j))
      and H(w₁ or … or w_n)
      and forall p AND_i [H(w_i -> p) or H(w_i -> not p)].    (3)

It says that the local Boolean algebra modulo H-equivalence has an
exhaustive partition into n nonzero atoms. We use it at S5-cluster targets;
we do not assume that (3) by itself entails Five_H in an arbitrary model.

C proves C_1^H↔Collapse_H. A one-part partition yields Hp or H¬p for
each p; if p is true, reflexivity excludes the second alternative. In the
other direction use w₁=top and Collapse_H at p or ¬p. For n≥2, C_n^H
implies not Collapse_H: collapse would make the disjoint D-possible
w₁ and w₂ both actually true.

## 3. Arbitrary finite H-clusters add no arithmetic consequences

Let T be the first-order arithmetic consequence theory of C+I_e, and
TrueΠ₁ the standard-true Π⁰₁ sentences. For every fixed external n≥1,

    Th_arith(Q_L + C_n^H)
       = Th_arith(M_L) = Cn(T + TrueΠ₁).                    (4)

In particular, each Q_L+C_n^H is consistent. Both Γ_L and not Γ_L remain
consistent with it, for the previously fixed arithmetic separator Γ_L.
This proves independence of finite H-cluster size from that arithmetic
choice; it does not construct a map between the opposed arithmetic models.

Use the finite-rank internal set model S and coherent old profiles P_σ
from [barcan-arithmetic-conservativity.md, §§2–5](barcan-arithmetic-conservativity.md#2-inputs-and-their-scope).
Its old category, naturality condition, separation property, and fresh
generator supplies remain unchanged. Replace its one current coordinate
by n current coordinates. Use one common individual carrier, and at every
required relation type σ=τ₁…τ_k t use the common carrier

    (P(D_τ₁×…×D_τ_k))^n × P_σ.                             (5)

The n evaluation points have these same carriers and term operations;
point i evaluates a relation using its ith current extension. The current
truth of an identity at every point is literal equality of the whole
entity. Lambda abstraction and quantification use their genuine truth
clauses at each of the n coordinates, and the old component term values
at profiles. The closure, beta/eta and Logical-Equivalence checks are the
same coordinatewise checks as for the one-coordinate model. In particular
this is not a direct product furnished with an arbitrary truth predicate.

If p=(epsilon₁,…,epsilon_n,alpha) is a proposition, put
w=(1,…,1,bottom-profile). At every current point,

    Hp is true iff every epsilon_i is 1;
    Dp is true iff some epsilon_i is 1.                     (6)

For the forward H implication, a true witness q is nonzero as a whole
entity. Since the carriers and literal equality are shared, diamond q is
true at every current coordinate. Thus □(diamond q→p) forces every
epsilon_i=1. Conversely w=diamond w, and if every epsilon_i=1, w≤p;
its old profile is bottom. Hence w witnesses Hp at every current point.

Every pattern of n truth values is admitted with bottom profile. Taking
w_i to have its only true bit at coordinate i proves C_n^H. Conversely
a nonempty part containing two coordinates is split by an admitted
one-coordinate proposition, so (3) fails for m≠n. This verifies the exact
finite cluster size rather than just a lower cardinal bound.

At point i the true w_i witnesses StrongActuality. For every admitted p,
w_i∧p is w_i or bottom, independently of which current point evaluates
that identity. Therefore Settle(w_i) is true at all n current points;
its old profile is Settle(bottom)=top. Thus □Settle(w_i) holds.

Barcan has two cases. If the existential is true at any current coordinate,
its witness belongs to the common carrier, and makes the source instance
nonzero. If it is nonzero in an old profile, the old-category separation
map first makes that existential actually true. Assign its witness to a
fresh same-typed generator outside the predicate's support. The original
Barcan proof then applies unchanged. Current choices follow from each
coordinate's unrestricted actual extensions and the internal well-ordering.

At each point the actual Frege numbers are exactly the same internal
zero/successor orbit, in bijection with ω^S. Each coordinate admits its
exact orbit predicate and the required arithmetic graphs. The same
induction and separation argument therefore identifies arithmetic with
that of S at every point.

Finally apply the original finite-proof argument. A proposed arithmetic
consequence uses finitely many types and Max instances. A finite-rank S
with arithmetic falsifying that consequence provides the coded old
witnesses and enough powersets for (5). The fixed finite factor n adds
no unbounded rank requirement; (3) uses finitely many further types.
All used Q_L axioms and C_n^H are true, while the proposed conclusion is
false. This proves the upper inclusion in (4); M_L gives the other one.
Both original languages are handled separately, preserving c in every
old profile and giving it any chosen current extensions.

## 4. Exact propositional H-logic of the structural package

For an ordinary propositional modal formula F, let F_H substitute H for
its modality, and let ∀p̄ F_H be its propositionally universal closure.
Then

    Q_L proves forall p̄ F_H iff S5 proves F.                (7)

The forward limitation follows from (5)–(6): every finite universal S5
frame and every valuation of F's variables is realized at a Q_L model.
Every S5 non-theorem has a countermodel on such a finite frame.

For the reverse implication one must not necessitate the optional local
Five_H axiom. Instead take the Boolean algebra of propositions of a Q_L
model, with its H operation. C makes it an S4 modal algebra. Let U be
its actual truth ultrafilter and use the canonical relation

    V R W iff {a : Ha∈V} is a subset of W.

This relation is reflexive and transitive. At U, Five_H implies the local
B condition a→HDa for every algebra element a. If U R V, then V R U:
otherwise choose Ha∈V with a∉U. Since ¬a∈U, the B condition gives
HD¬a∈U, so D¬a∈V, contradicting Ha∈V. Transitivity now makes all points
reachable from U a universal cluster. The canonical truth lemma therefore
makes every S5 theorem true at U, for every valuation from the algebra.
Henkin completeness gives the asserted Q_L consequence. This argument
asserts current propositional laws, not a boxed quantifier schema.

The standard modal input is Stefan Wölfl, *Introduction to Modal Logics*,
draft 22 July 2015, Corollary 3.30, pp.58–59 (universal-frame completeness),
and Lemma 4.10, p.71 (finite universal countermodels). The above local
canonical argument and its application to Q_L are deductions here.
[Primary lecture text](https://gki.informatik.uni-freiburg.de/teaching/ss15/ml/script.pdf).

## 5. Incorporating the clusters into the common SP-fragment model

The finite clusters can also be grafted into the §9 comparison, yielding
a common root with all their D-instances. Fix φ in the full local class
F_L of [triangulation-ladder.md, §9](triangulation-ladder.md#9-many-targets-and-arbitrary-local-finite-order-structures),
choose its infinite full model on E_φ, and choose n≥1. Replace that pair's
special object by n objects S₁,…,S_n. They have matching unrestricted
generator supplies and individual sets of cardinality |E_φ|. Each has
special proposition labels z₁,…,z_n. There is one isomorphism u_ij:S_i→S_j
which preserves all these labels and the unrestricted generators. The
u_ij compose as the unique-arrow groupoid on n objects. Every other arrow
with special source kills all its special labels. Free proposition
generators may map to any target special label. Old exits kill them all.

Interpret z_j at S_i as true precisely at the isomorphism u_ij and false
at every other coordinate. It has finite support: a special label
distinguishes the isomorphism from every annihilating arrow to that target.
Old profiles erase the special labels. The finite-support construction
remains closed under substitution and composition, including cross-arrows
to all the other target pairs. In each cluster use the same chosen local
structure and c-extension, so each S_i satisfies φ°.

Let W be its accompanying atomless object. Matching maps p_i:S_i→W and
j_i:W→S_i give e_i=j_ip_i, fixing the unrestricted generators and killing
all specials. For every annihilating arrow h from S_i, h e_i=h. The
finite-support Barcan proof extends as follows. An isomorphism target
arrow has an actual inverse-image witness. Otherwise rename the finitely
many unrestricted parameters of a target witness y at S_i into fresh
source generators. This gives x₀ with f'(x₀)=e_i(y), while f'(F)=f(F).
Send a fresh source proposition generator d to z_i at S_i.

The lifted witness uses x₀ except at coordinates k:X→S_j for this cluster
with k(d)=z_i at S_j. At such a coordinate use the actual extension of
u_ij(y). Its old profile is x₀'s. This is a finitely supported entity.
After f', an isomorphism u_ij keeps the mask active and gives exactly
u_ij(y). After any annihilating arrow h the mask is inactive, and
h e_i(y)=h(y). Thus the whole f'-transport is y. Individual witnesses
need no mask because e_i fixes individuals. Targets W, R and old objects
have the original fresh-renaming, return, and fresh-assignment proofs.
Consequently every S_i still satisfies all ordinary Barcan instances.

At S_i, z_i is a true strong atom: at every isomorphic target it is a
one-coordinate atom, and along every other arrow it is bottom. Thus
StrongActuality survives. The finite join z₁∨…∨z_n is possibility-fixed
and supported exactly on the cluster isomorphisms. It gives the forward
part of the analogue of (6); the reverse uses the return isomorphisms.
Every cluster truth pattern is admitted, so C_n^H holds. Choice and the
local full interpretation still follow from arbitrary actual extensions.

There are default returns to R, and each composite R→S_i→R is id_R.
Therefore the same root R satisfies

    D(φ° and C_n^H and Q)                                 (8)

for every φ∈F_L, every external n≥1 and every finite conjunction Q of
StrongActuality, ordinary Barcan instances, current choices and not E₁.
All targets are M_L-models, verifying the exact eligibility conditions.
The atomless targets and all §9 requirements remain in place. Root K,
E₁ and A_L have unchanged proofs. One set-indexed graft realizes every
instance (8) simultaneously, with original c fixed throughout.

Call the enlarged theory T_cluster,L. Full SP entails it, and it is
consistent. It strictly strengthens T_loc,L. Indeed it proves
D(StrongActuality and not Collapse_H), using n=2 and φ=top. The §9
model refutes this instance: every S target has Collapse_H, every W is
atomless and so refutes StrongActuality, and R also refutes StrongActuality.
For the last assertion, its unique actually true Boolean atom is its
root-coordinate atom. Transport to an atomless W leaves this atom nonzero
by the return, so it ceases to settle every proposition; hence it is not
a strong world. No other true strong world is possible at R.

The new-object indicator is therefore below the negation of the displayed
target sentence throughout that earlier model and is possibility-fixed;
it witnesses its H-negation at R. Conversely the enlarged model still has
standard arithmetic at every new object, so its new-object indicator gives
HΓ_L. It refutes the licensed D(not Γ_L), just as before. Thus

    T_loc,L < T_cluster,L < SP_L,

with the first two theories consistent, independently for the two L.

## 6. Resulting comparison and source boundary

The local structural package Q_L enforces the current S5 condition for H,
but not its collapse to truth. Every finite nontrivial H-cluster is
compatible with Q_L, with either arithmetic choice Γ_L/not Γ_L, and with
the prescribed recursively saturated arithmetic models by the earlier
lifting theorem. The added C_n^H sentence is recursive, as that theorem
requires. The common SP-fragment root can strongly access all finite
cluster sizes together with the local full structures.

Full SP cannot itself satisfy Five_H, by (2). This separates a consistent
family of required targets from an inconsistent strengthening at the source.
It does not supply the missing embedding from a Γ_L source to a not-Γ_L
target, or verify the unrestricted finite disjunction property.

Inputs other than the modal source named in §4: the coherent-profile and
finite-rank arguments in barcan-arithmetic-conservativity.md, §§2–6; the
construction and source references in triangulation-ladder.md, §§7–9; the
record `vicinity-and-barcan-t-imply-two-hat-implies-nd` (the recorded
application of *The Bounds of Possibility*, Proposition D18, p.408);
and the existing SP/two-hat incompatibility. Formula (1), the finite
cluster modifications, arithmetic comparison (4), and the joint
extension (8) are the deductions supplied here.

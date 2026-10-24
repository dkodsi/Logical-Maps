# A Boolean-valued proof of the finite Choice separations

Original research by OpenAI Codex, prompted by Daniel Kodsi, 23 October 2026; direct source `misc`, §§1–10 (unpaginated).

## 1. Exact theorem and proof route

Keep the original relational grammar: types are e, t, and σ→ρ when ρ is
relational. Write F for C together with every boxed Functional Choice
instance. For each finite collection Ω of relational output types there
is a general one-world C-model which satisfies every boxed FC_(σ,ρ) with
ρ∈Ω, for every admitted input σ, but fails a further boxed selector
assertion. Moreover, with

    ρ₀=e,  ρ_(n+1)=ρ_n t,  A_n=ρ_(n+1),

there is, for each n, such a model satisfying □Sel_(A_n) and
□¬Sel_(A_(n+1)). These supply the negative steps for the previously
established strict selector hierarchy and nonfinite-basis theorem.

The construction is an actual Boolean-valued model of the countable
first-order Henkin theory E₂. Boolean first-order soundness makes the
required ordinary first-order theory consistent; ordinary completeness
then gives an ordinary model, and the E₂ interpretation gives a C-model.
There is no generic filter, transitive symmetric ZF model, or assumption
of the existence of a separating model. In particular, we do not take an
arbitrary Boolean ultrafilter quotient and assume it preserves quantifiers.

The Boolean-valued construction uses an action which moves both the
entities and their Boolean truth values. It is not the ordinary nominal
function hierarchy ruled out in the last subsection of
negative-choice-formalization-followup.md.

## 2. The Boolean algebra and its small-table lemma

Fix an infinite regular cardinal κ. Let P consist of partial functions
`p:κ×κ⇀2` with domain of cardinality less than κ, ordered by extension.
For the present proof it is convenient to construct its Boolean algebra
directly. Let X be the set `2^(κ×κ)`. For p∈P put

    N_p = {x∈X : p⊆x}.

Give X the topology with these cones as a basis. This is the topology of
conditions with fewer than κ specified coordinates; it is not, when κ
is uncountable, the ordinary finite-coordinate product topology. Two
compatible conditions have intersection cone N_(p∪q); incompatible ones
have disjoint cones. Each cone is nonempty, by extending p with zeroes,
and is clopen: its complement is the union of cones specifying an
opposite bit at one of its coordinates.

Let B be the complete Boolean algebra of regular open subsets of X.
Its zero and one are ∅ and X; arbitrary joins are regularizations of
unions, and Boolean complement is interior of the set complement.
Every N_p is an element of B. Every nonzero b∈B contains some N_p, and

    N_p ∧ N_q ≠ 0  iff  p and q are compatible.

Write `c_(i,α)` for the clopen set of assignments having bit 1 at (i,α).
Let Γ=Sym(κ), acting by permutations of the first coordinate. This action
sends N_p to N_(πp), so it acts on B by complete Boolean-algebra
automorphisms. In particular it preserves arbitrary joins and meets,
and `π(c_(i,α))=c_(πi,α)`.

**Small-table lemma.** If I is a ground set of cardinality less than κ
and `(b_a:a∈I)` is any family in B, then

    ⋁_(η∈2^I) ⋀_(a∈I) b_a^[η(a)] = 1,

where `b^[1]=b` and `b^[0]=¬b`.

To prove this, start below any nonzero r∈B with a cone N_p⊆r. Enumerate I
in order type λ<κ. At a successor stage refine the current cone into
either b_a or ¬b_a. Such a nonempty refinement exists because their
Boolean join is 1, and a further cone can be chosen by the basis
property. At a limit stage, take the union of the earlier conditions.
Regularity of κ ensures that its domain still has size less than κ.
The final union, also taken at stage λ when necessary, is a condition q.
It has a nonempty cone below r and below all the chosen bit values.
The choices form an actual η∈2^I in the ZFC metatheory. Thus every
nonzero r meets the displayed join, which must be 1. Empty I causes no
problem. This is exactly the binary distributivity consequence needed
below, proved without passing to a forcing extension.

## 3. The coherent supported hierarchy

For finite S⊆κ let H_S be the subgroup fixing S pointwise. A profile is
supported by S when it is fixed by H_S under the action specified below.
Finite unions combine supports; conjugation carries a support S to πS.

Take `D_e=E=ω`, with trivial Γ-action and crisp Boolean equality
`ε_e(a,b)=1` if a=b and 0 otherwise. Every relational type has a unique
flattening `ρ=σ₁…σ_r t`, including r=0 for t. Its argument product is

    D_Args(ρ)=D_σ₁×…×D_σ_r.

An empty product is a singleton. Each argument type is a proper syntactic
subtype of ρ, so the following recursion is well founded. For argument
tuples put

    ε_Args(a,b)=⋀_(j=1)^r ε_σj(a_j,b_j).

Before imposing support, a profile at ρ is a function
`f:D_Args(ρ)→B` satisfying coherence:

    ε_Args(a,b) ∧ f(a) ≤ f(b).

Since ε_Args is symmetric, this is equivalent to
`ε_Args(a,b)≤(f(a)↔f(b))`. Here and below ↔ is Boolean equivalence.
The group action on profiles is semilinear:

    (π·f)(a)=π_B(f(π⁻¹·a)).

Let D_ρ consist of all coherent profiles with some finite support, and
define their Boolean equality by

    ε_ρ(f,g)=⋀_(a∈D_Args(ρ)) (f(a)↔g(a)).

In particular D_t is the set of finitely supported elements of B, and
`ε_t(p,q)=p↔q`. It is not literally the two-element set. The constants
0 and 1 are empty-supported members of D_t. Constant-zero profiles make
every relational domain nonempty.

The recursive construction simultaneously verifies the following facts.
Each ε_σ is reflexive with value 1, symmetric, and Boolean-transitive:

    ε_σ(x,y) ∧ ε_σ(y,z) ≤ ε_σ(x,z).

The action preserves the domains and is semilinear on equality:

    ε_σ(πx,πy)=π_B(ε_σ(x,y)).

For profiles these facts follow pointwise from Boolean equivalence and
then by taking meets. In the action identity, reindex the argument meet
by the bijection a↦πa and use preservation of arbitrary meets. Coherence
of πf follows from the earlier equality identity. Its support is πS if
S supports f. Equality value 1 also implies literal equality of the
profiles, since it implies equality of their values at each tuple.

Application at σρ is slicing: `(fx)(a)=f(x,a)`. Coherence of f makes this
a coherent ρ-profile, and the union of supports of f and x supports the
slice. Consequently application is an actual operation on the domains.
It satisfies the Boolean congruence inequality

    ε_(σρ)(f,g) ∧ ε_σ(x,x′) ≤ ε_ρ(fx,gx′).

Indeed coherence changes x to x′ in f, pointwise equality changes f to g,
and taking the meet over the remaining arguments gives the inequality.
Slicing is equivariant. The definition also gives exact extensionality:

    ε_(σρ)(f,g)=⋀_(x∈D_σ) ε_ρ(fx,gx).

These are Boolean-valued equalities and congruences. No actual-equality
interpretation of the group action is substituted for them.

## 4. Boolean-valued E₂, including full definable comprehension

Use the countable many-sorted first-order theory E₂ defined in
finite-choice-forcing-extraction-review.md,
§2. Its sorts are the original types; it has typed application, constants
0 and 1 at t, two-valuedness and function-extensionality axioms, and every
first-order definable-comprehension instance with finitely many parameters.
Formulas may quantify over any admitted sorts. The schemata themselves
introduce no object-language quantification over types.

Interpret first-order equality in sort σ by ε_σ, application by slicing,
and the external first-order connectives and quantifiers by Boolean
operations and arbitrary meets and joins in B. The preceding congruence
facts make this a Boolean-valued first-order structure. In a guarded
single-sorted presentation, use the tagged disjoint union of the domains,
crisp sort predicates, and Boolean equality zero across different sorts.

Its proposition-sort axiom has value 1, since for each p∈D_t,

    ε_t(p,0) ∨ ε_t(p,1)=¬p∨p=1.

Also `ε_t(0,1)=0`. Extensionality has value 1 by the exact slicing identity.

For completeness, definable comprehension needs both coherence and
support, not support alone. Induction on first-order formulas proves:

1. **Substitution.** The meet of the Boolean equalities of two assignments
   is below the Boolean equivalence of their formula truth values.
2. **Equivariance.** Applying π to the assigned entities applies π_B to
   the formula truth value.

The atomic cases use the application congruence and Boolean equality
laws. Boolean connectives preserve local equivalence. For quantifiers,
substitution follows by applying the induction hypothesis at every value
of the quantified variable and then taking its meet or join. Equivariance
uses the bijection of that quantified domain induced by π. These proofs
permit parameters and quantifiers at arbitrarily high types.

Given a formula φ(x₁,…,x_r,z̄) and assigned parameters z̄, define the
literal profile

    P(a₁,…,a_r)=‖φ(a₁,…,a_r,z̄)‖_B.

Substitution proves its coherence. The finite union of supports of z̄
supports it, by equivariance. Therefore P belongs to D_(σ₁…σ_r t).
For every ā, the truth value of `P[ā]=1` is exactly P(ā), because
`ε_t(p,1)=p`. Thus this P witnesses the comprehension instance with value
1. The empty argument list is included. Quantification over the parameter
tuple preserves that value. This proves every E₂ axiom, rather than
assuming Henkin closure as a hypothesis about the proposed hierarchy.

## 5. Canonical ground checks and their exact scope

Let G be the ordinary full ground hierarchy with `G_e=E`, `G_t=2`, and
all functions at each admitted arrow. Identify a ground relational entity
g∈G_ρ with its flattened Boolean table on G_Args(ρ). Define checks
recursively by `check_e(a)=a` and

    check_ρ(g)(x)=
      ⋁_(a∈G_Args(ρ)) [ε_Args(x,check(a)) ∧ g(a)],

where a ground bit is interpreted as 0 or 1 in B. Checks of tuples are
componentwise. This formula also gives the two checks at t.

At every type, without a preservation hypothesis, these checks have the
following properties:

    check_ρ(g) is coherent and fixed by Γ;
    check_ρ(g)(check(a))=g(a);
    ε_σ(check(g),check(h)) is 1 if g=h and 0 otherwise.

Coherence follows by Boolean transitivity of the tuple equality and
distribution of a fixed meet over the defining join. Fixity follows
because earlier checks are fixed and π_B preserves the join. For the
ground evaluation equation, earlier isometry makes every summand except
the matching ground tuple zero. If two ground profiles differ, one
ground tuple witnesses different bits, forcing their Boolean equality
to be zero; equal profiles have equality 1. This proves the claims
simultaneously by induction. Application on checked ground inputs also
commutes with check: its first-coordinate equality eliminates all ground
input indices except the given one in the displayed join.

These statements do **not** make check a logical embedding at arbitrary
types. For example, the check of the ground universal predicate at σt is
`x↦⋁_(a∈G_σ) ε_σ(x,check(a))`, which need not be the actual universal
predicate unless the ground checks cover D_σ.

Call a finite subtype-closed collection of types protected when, at every
relational ρ in it, `|G_Args(ρ)|<κ`. Include e and t. Then induction
proves the **coverage identity** at every protected σ:

    ⋁_(g∈G_σ) ε_σ(x,check(g))=1   for each x∈D_σ.

At e it is immediate. At a relational ρ, apply the small-table lemma to
the fewer than κ bits `f(check(a))`, indexed by ground argument tuples.
For a ground Boolean table g, put

    b_g=⋀_(a∈G_Args(ρ)) (f(check(a))↔g(a)).

All such tables are present in the full ground domain G_ρ, and
`⋁_g b_g=1`. Earlier component coverage gives tuple coverage, by finite
distribution. Coherence of f and check(g) then gives

    b_g ∧ ε_Args(x,check(a)) ≤ (f(x)↔check(g)(x))

for each ground a. Joining over a shows the same inequality without its
tuple-equality conjunct. Meeting over x proves
`b_g≤ε_ρ(f,check(g))`, and hence coverage. Conversely evaluation at ground
tuples gives `ε_ρ(f,check(g))≤b_g`, though only the first inequality is
needed.

Coverage also gives the expected **protected** semantic correspondence.
For a coherent predicate ψ on D_σ with covered σ,

    ⋁_(x∈D_σ) ψ(x)=⋁_(a∈G_σ) ψ(check(a)),
    ⋀_(x∈D_σ) ψ(x)=⋀_(a∈G_σ) ψ(check(a)).

The first follows by inserting coverage and using coherence; the second
follows by applying the first to ¬ψ. Thus induction on first-order
formulas all of whose types are protected, at checked ground assignments,
identifies their Boolean truth values with their ordinary ground truth
values 0 or 1. Atomic application and equality use the preceding check
identities. No global logical-elementarity claim is made. In particular,
the later selector counterexample deliberately lies beyond protected
coverage.

## 6. Covered outputs give supported selecting operations

Let τ be a relational type satisfying coverage, and let σ be any admitted
input type; σ need not be protected. Fix R∈D_(στt), supported by S. Its
seriality truth value is

    s=⋀_(x∈D_σ) ⋁_(y∈D_τ) R(x,y).

Well-order the ground set G_τ in the ZFC metatheory as `(a_ξ:ξ<λ)` and
choose a fixed ground default a_*. Ground indices are not moved by Γ.
For each x define

    r_ξ(x)=R(x,check(a_ξ)),
    u(x)=⋁_(ξ<λ) r_ξ(x),
    w_ξ(x)=r_ξ(x) ∧ ¬⋁_(η<ξ) r_η(x),
    v(x)=¬u(x).

Output coverage and coherence of R give
`u(x)=⋁_(y∈D_τ)R(x,y)`. The weights w_ξ(x) are pairwise disjoint and
have join u(x). The latter assertion follows by transfinite induction
on the initial segments of the well-order: at a successor remove the
part already covered, and at a limit take the union of the earlier
joins. Thus these weights together with v(x) form a partition of 1.
No distributivity assumption on the possibly very large λ is needed.

Define a profile at στ, flattening the remaining arguments of τ, by

    F(x,z̄)= [v(x) ∧ check(a_*)(z̄)]
             ∨ ⋁_(ξ<λ) [w_ξ(x) ∧ check(a_ξ)(z̄)].

This is an admitted operation. Coherence of R gives local equivalence of
all r_ξ under ε_σ(x,x′), hence of their joins, complements and weights.
Coherence of each checked output gives coherence in z̄. Combining these
facts proves joint coherence of F. Each check is Γ-fixed, so the same
expression is equivariant under H_S; thus S supports the entire F.
This common support is essential: the construction does not appeal to
an arbitrary mixing operation on independently supported witnesses.

For every ξ and x, pointwise calculation under the weight w_ξ(x) gives

    w_ξ(x) ≤ ε_τ(Fx,check(a_ξ)).

Indeed all other weights vanish under it and its own output table
remains. Since `w_ξ(x)≤R(x,check(a_ξ))`, coherence in the output variable
gives `w_ξ(x)≤R(x,Fx)`. Joining proves `u(x)≤R(x,Fx)`. The reverse
inequality follows from the definition of the existential row value,
so in fact `R(x,Fx)=u(x)`. Consequently

    s ≤ ⋀_x R(x,Fx).

This handles arbitrary s, not just s=1. For every R its Functional Choice
implication therefore has Boolean value 1, and the universally quantified
FC_(σ,τ) has value 1.

The same construction, with input P∈D_(τt) and row R(P,y)=P(y), gives
`P(FP)=⋁_y P(y)`. Thus Sel_τ itself has value 1 whenever τ is covered.
The ground enumeration need not be an entity of the original language:
the constructed profile F is admitted because the explicit formula has
the required coherence and common finite support. Every operation output
used here is relational, including τ=t with an empty remaining tuple.

## 7. Choosing the cutoff and constructing the higher family

Write `beth₀=ℵ₀`, `beth_(r+1)=2^(beth_r)`. The ground tower ρ_r has
cardinality beth_r. Every fixed ground type has cardinality bounded by
some finite beth number: at an arrow, a common infinite bound μ on its
input and output gives the bound `μ^μ=2^μ` on its full function set.

For the finite output collection Ω choose m so that μ=beth_m bounds the
ground domains of all their subtypes, together with E and 2. Set

    κ=μ⁺,  ν=ρ_(m+1),  τ=νt.

In ZFC κ is regular. Protect all the selected output subtypes, as well
as ν and its subtypes. Their ground argument products have size at most
μ, strictly below κ. This includes ν because its argument domain is
G_(ρ_m), of size μ, although `|G_ν|=2^μ≥κ`. Section 5 gives coverage
at each selected output and at ν. Section 6 therefore gives all required
output-Choice assertions and Sel_ν with Boolean value 1.

Choose an external ground injection `b:κ→G_ν`. It is used only to define
profiles and is not an additional object-language operation. For i<κ put

    X_i(z)=⋁_(α<κ) [ε_ν(z,check(b(α))) ∧ c_(i,α)].

This is coherent by Boolean transitivity. The checks are fixed, and the
column action gives `πX_i=X_(πi)`. In particular {i} supports X_i, so
`X_i∈D_τ`. Crisp equality of ground checks and injectivity of b give

    X_i(check(b(α)))=c_(i,α).

For distinct i,j, the Boolean equality of these two entities is zero.
It is bounded above by

    ⋀_(α<κ) (c_(i,α)↔c_(j,α)).

If this meet were positive, choose a cone below it. There is an α whose
coordinates in columns i and j are both unspecified by its condition,
since that condition has fewer than κ coordinates. Extend it by opposite
bits there. The resulting nonempty cone is below the original meet and
below its negation at α, a contradiction. Hence `ε_τ(X_i,X_j)=0`.

## 8. The higher selector assertion has value zero

Take any candidate ε∈D_((τt)τ), and let finite S support it. Define the
available family predicate

    P_S(z)=⋁_(i∈κ\S) ε_τ(z,X_i).

Boolean transitivity makes it coherent. Permutations fixing S reindex
the displayed join, so S supports P_S. It is a member of D_(τt), and
its existential nonemptiness truth value is 1: choose any i∉S and
evaluate at X_i.

Let `y=ε(P_S)`. Equivariant slicing shows that S supports y. Fix i∉S.
We claim `r_i=ε_τ(y,X_i)=0`. Otherwise choose a cone N_p below r_i.
Let col(p) be the first-coordinate projection of dom(p), which has size
less than κ. Choose

    j∉S ∪ {i} ∪ col(p),

and transpose i and j by π. This fixes y and carries X_i to X_j. By
semilinearity it carries r_i to `r_j=ε_τ(y,X_j)`, and carries N_p to
N_(πp). The conditions p and πp are compatible: column j was absent
from p, entries in column i move to the previously unused column j,
and every other column is unchanged. Their union still has size less
than κ, so its cone is nonempty. That cone lies below

    r_i ∧ r_j ≤ ε_τ(X_i,X_j)=0,

a contradiction. Thus each r_i is zero, and `P_S(y)=⋁_(i∉S)r_i=0`.

The selector clause for this particular P_S has truth value 0: its
nonemptiness antecedent is 1 and its selected-membership consequent is
0. Consequently the universal selector clause for this ε has value 0.
This holds for every ε, so the existential selector assertion Sel_τ has
value 0 and its negation has value 1. This is stronger than merely
showing that no candidate has selector value 1.

No membership witness is extracted from a join of value 1. We only use
that a specified positive equality value contains a cone, followed by
compatibility of two explicit conditions. This is why neither a generic
filter nor a maximum principle is needed.

## 9. Extraction of an ordinary general C-model

Let T be E₂ together with the desired FC sentences, Sel_ν and ¬Sel_τ.
One may retain the whole countable input schema at every output in Ω.
All these sentences have Boolean value 1 in the structure constructed
above, over the nontrivial complete Boolean algebra B.

Boolean first-order soundness implies that T is syntactically consistent.
For clarity, this soundness result permits Boolean equality satisfying
the reflexivity, symmetry, transitivity and congruence laws proved in
§3. It does not require literal equality on the Boolean structure's
carrier. An induction on a first-order derivation shows that a conclusion
has value 1 whenever its assumptions do. The propositional steps are
Boolean identities, the quantifier steps use the defining meets and
joins, and equality substitution uses congruence. A finite derivation of
contradiction from T would therefore give `1≤0` in B, which is impossible.

Ordinary many-sorted first-order completeness now gives an ordinary
model M of T. Equivalently, one can use the usual guarded single-sorted
encoding and recover the sorts. This is an ordinary set-coded model in
the ZFC metatheory, not an asserted generic quotient of the Boolean
structure. Its equality is ordinary equality and its proposition sort
has exactly two elements.

There is also a direct alternative to the soundness/completeness step:
`boolean-valued-model-extraction.md`,
§§1–7, constructs countably many names and a descending sequence of
nonzero Boolean conditions, scheduling formula decisions and positive
existential witnesses. Its resulting proper filter and equality quotient
satisfy a truth lemma and retain every value-1 sentence. To use its
relational-language theorem here, replace typed application by the graph
relation with value `ε_ρ(fx,y)`, and constants 0 and 1 by the unary
relations `ε_t(p,0)` and `ε_t(p,1)`, then use the crisp-tag encoding.
These relations are coherent; their required totality, uniqueness and
constant-existence sentences have value 1. Relationalization preserves
Boolean truth: for any coherent formula value ψ(y),

    ⋁_(y∈D_ρ) [ε_ρ(a,y) ∧ ψ(y)] = ψ(a),

by substitution for the upper bound and y=a for the reverse bound.
Induction therefore handles nested terms and their graph witnesses.
After direct extraction, the ordinary total functional graphs and unique
constant predicates recover an ordinary E₂ model. This route requires
neither a proof calculus nor a generic-filter or arbitrary-ultrafilter
truth claim; the standard extraction argument above remains sufficient.

The E₂ interpretation proved in the review's §2 turns M into a genuine
general one-world C-model. Briefly, extensionality identifies its arrow
entities with their represented functions. Definable comprehension,
flattening relational outputs and currying give all lambda abstractions,
including those with parameters and quantifiers of high types. Equality,
Boolean operations and quantifiers have their standard interpretations.
H is sound, and its theorem-level logical equivalences have equal
abstractions, verifying C's actual Logical Equivalence rule. No
equivalence derived only under an optional Choice premise is used there.

In this ordinary model `□p` is `p=⊤`, so it agrees with truth. Therefore
the retained unboxed sentences give the required boxed FC and selector
sentences, including □¬Sel_τ. The standard C equivalence
`Sel_τ ↔ FC_(τt,τ)` identifies a failed FC instance: for the nontrivial
direction use the serial relation

    R(P,y) := (∃z Pz) → Py.

If P has a member choose one; otherwise every y works. Conversely a
selector applied to each row of a serial relation gives a selecting
operation. All these outputs are relational.

Extraction retains the selected sentences. It does not assert literal
preservation of the Boolean construction's carriers, external cardinal
sizes, ground checks, or standard arithmetic in M.

## 10. Adjacent strictness and nonfinite axiomatizability

For a fixed n take μ=beth_n and κ=μ⁺. Then `ν=ρ_(n+1)=A_n` is covered
because its ground argument domain has size μ. Its next predicate type
`νt=A_(n+1)` has the failed selector family from §§7–8. Extraction gives

    □Sel_(A_n) ∧ □¬Sel_(A_(n+1)).

Together with the independently established C selector-transfer
implications, this proves the adjacent strictness of the sequence T_n.
The positive retraction, inclusion and cofinality arguments remain those
in finite-functional-choice.md,
§5; the present note supplies a different direct construction for their
negative witnesses.

For any finite set Δ of boxed FC instances, take Ω to be its finite set
of output types. The model above satisfies Δ and fails a further boxed
FC instance. If a finite set of closed original sentences Γ were an
equivalent axiomatization of F over C, finite derivations of its members
from F would together use only finitely many FC instances Δ. Our model
would satisfy C+Δ and hence Γ, but fail an axiom of F, a contradiction.
Thus F has no finite equivalent basis over C.

These conclusions concern fixed-type sentences in the original
language. They do not treat a type schema as a single axiom, and do not
rule out finite stronger packages which impose additional restrictions
and thereby imply F. The construction here makes no additional claim
about the versions requiring both quantified Infinity axioms.

## Both boxed and unboxed Functional Choice

The same finite-basis argument applies to unboxed Functional Choice. The recovered models have one world, so the boxed and unboxed Choice instances agree there. If a finite list of arbitrary pure fixed-type sentences were equivalent to Functional Choice over C, proofs of those sentences would use a common finite fragment of Choice. The constructed model satisfies that fragment and hence the proposed basis, but fails a further Choice instance, contradicting equivalence. The argument concerns equivalent bases, not finite strictly stronger theories.

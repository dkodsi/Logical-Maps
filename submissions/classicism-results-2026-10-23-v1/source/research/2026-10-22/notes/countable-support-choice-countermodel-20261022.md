# Countable-support Gallin countermodel: Intensional Choice and Dedekind Infinity without Functional Choice

22 October 2026. Original mathematical construction and independent audit by the Gallin-audit agent. Source status: original argument (`misc` if later recorded); no literature-novelty, human-check, or Lean claim. The ambient metatheory in this note is **ZFC**. No main database record is edited.

## Verdict

**PASS.** There is an extensional general Gallin model whose original C reduct satisfies C5, all-type Atomicity, both boxed quantified Frege Infinity axioms, all-type boxed Intensional Choice, and Dedekind Infinity at the proposition type, but refutes Functional Choice and Relational Choice already at input/output type `(t,t)`, at every world. All Frege number domains are externally standard. The ordinary hereditary core over individuals and Boolean values is the full standard finite-type hierarchy over N.

Consequently the implication `IC ∧ DedInf_t → FC`, valid for the infinite-world finite-support family classified in `nominal-choice-classification-20261022.md`, does **not** hold in C, nor over that positive package with both boxed Infinity axioms and the full ordinary core. This does not dispute the finite-support classification: the support ideal is different.

## 1. Domains and exact framework

Let A be an uncountable set, for example omega_1, put W=A, and let G=Sym(A). Let E=N be a separately tagged set with trivial G-action. A subset S of A supports an object x when every permutation fixing S pointwise fixes x. Here supports are allowed to be **countable**, including finite.

Set D_e=E and let D_t consist of all countably supported subsets of A, with direct-image action. Precisely,

    D_t = {p⊆A : p is countable or A\p is countable}.

Indeed, if S is a countable support, membership must be constant outside S, since any two points there can be interchanged while fixing S. Conversely p or its complement itself is a support when countable. Every singleton is admitted, and truth at w means membership of w.

For every admitted original arrow sigma→tau (tau≠e), take **all** countably supported functions D_sigma→D_tau under conjugation:

    (g f)(x) = g(f(g^(-1)x)).

The full auxiliary Gallin expansion has base sorts E,W,o={0,1}, trivial action on E,o, and all countably supported functions at every simple arrow. Its original reduct via `e*=E`, `t*=W→o`, `(sigma→tau)*=sigma*→tau*` has exactly the displayed original domains. This is a general/Henkin hierarchy, not a full hierarchy: W→o omits subsets whose size and complement are both uncountable.

Every object has a chosen countable support. We neither assert nor need a least support. In particular no finite-support intersection theorem is silently imported into this construction.

## 2. Closure, C soundness, and the positive package

Transporting a support S by g gives a support g[S] for gx. All domains are G-sets. Constant functions show all domains are nonempty. If a multivariable function has support S, its section at x has support S∪supp(x); currying preserves support S. Thus the usual relational notation denotes admitted curried functions.

The original quantifier operation is

    All_sigma(F) = intersection {F(x) : x∈D_sigma}.

If S supports F, simultaneous permutation of the quantified domain proves this intersection is fixed by Fix(S), hence belongs to D_t. The operation F↦All_sigma(F) is equivariant. This does not assume closure of countable/cocountable sets under arbitrary external intersections: only intersections arising from an admitted F are used. Existential quantification and the auxiliary Boolean-valued quantifiers are treated similarly.

Application and logical constants are equivariant. Induction on terms gives equivariance under valuation transport. A lambda denotation is supported by the union of the supports of its finitely many free parameters, a countable set. This supplies full parameterized lambda closure and H soundness. If two matrices are H-provably equivalent, they agree at every world under every assignment; their propositions and abstractions are therefore equal genuine functions. This verifies C's Logical Equivalence rule with its exact H-theoremhood restriction.

Equality at every type is W-valued or empty-valued genuine identity. Thus C5 holds everywhere. At a nonzero relational object F of type sigma_1...sigma_n t, choose a tuple a and a world w in F[a]. The singleton point relation, with value {w} at tuple a and empty elsewhere, has support `{w}∪union_i supp(a_i)`, which is countable. It is an atom below F. This proves all-type Atomicity everywhere, including the n=0 propositional case.

For completeness, all actual functional relations have admitted functions: if U is total and single-valued at world w, its unique output function is supported by supp(U)∪{w}; uniqueness gives conjugation equivariance. Hence all-type Plenitude holds everywhere. The model therefore belongs to the positive package denoted B/BP in the companion notes. Rigid comprehension follows independently by freezing an admitted relation's actual extension at w, with support enlarged by {w}.

## 3. Standard Frege arithmetic and both boxed Infinity axioms

For any admitted counting type sigma let nu_sigma=(sigma t)t and let z_n be its standard pure numeral objects. They have empty support, because zero and successor are equivariant pure operations. The rigid characteristic predicate of the external set `{z_n:n∈N}` is therefore admitted with empty support. It is inductive, while every actually inductive admitted predicate contains every z_n by external finite induction. Thus the actual Frege number extension is exactly the standard numeral set at every world.

The source's successor-removal definition gives by induction

    w∈z_n(X) iff the actual extension of X at w has exactly n elements.

Every finite set of objects has an admitted rigid characteristic predicate, because the finite union of their countable supports is countable. Every original domain is infinite: e and t are infinite, and constant functions inject the infinite codomain into each arrow domain. Consequently the standard numerals are distinct and none counts the universal property. This proves the original **quantified** Frege Infinity axiom at every counting type and world, including both boxed AI_e and AI_t. It is stronger than merely checking the external finite-n Infinity schemata.

The auxiliary E/o subhierarchy without W is externally full: trivial actions at its bases make every function at every subsequent E/o type equivariant. Equivalently, the original hereditary core with bases E and {bottom,top}, and supported rigid extensions of arbitrary core functions, is the full ordinary finite-type hierarchy over N. Its quantifiers must be relativized to the core. No assertion that the unrestricted original hierarchy is full is intended.

## 4. All-type boxed Intensional Choice

The exact instance at type sigma is

    forall F:sigma t [Box exists x Fx -> exists G:sigma t
      (G≤F and Box exists x(Gx and forall y(Gy -> y=x)))].

Fix F whose fibers are nonempty at every world, and choose a countable support S for F. Choose a∉S and a witness x with a∈F(x). Choose a countable support T for x and put

    B=(S∪T)\{a}.

Then S⊆B, a∉B, and B∪{a} supports x. For w∉B choose any g fixing B pointwise and sending a to w, and define h(w)=gx. Such g exists, even as a transposition when w≠a. This value is independent of the choice of g: two such permutations differ by a permutation fixing B∪{a}. Moreover w∈F(h(w)), since g fixes S and transports a∈F(x).

For each b∈B choose a witness x_b with b∈F(x_b), choose a countable support T_b for x_b, and set h(b)=x_b. These are countably many choices, permitted by ZFC. The set

    K=B ∪ union_{b∈B} T_b

is countable. Any permutation fixing K fixes each exceptional input b and its output x_b. On A\B the preceding generic definition is Fix(B)-equivariant. Hence the entire external map h:A→D_sigma has support K.

Define its original graph by

    G(y)={w∈A:h(w)=y}.

For each y this proposition has support K∪supp(y), and the curried function y↦G(y) has support K. It is admitted at sigma t. Its fibers are singleton choices contained in F's fibers, so it witnesses the exact IC formula. No forbidden function-returning-individual type is used, even at sigma=e; h is an external proof device and G is the original-language witness.

The proof applies to arbitrary F and is independent of the evaluation world. Therefore all-type Box IC holds. No reservoir, least support, or external well-order of a higher-type domain is needed beyond the explicitly stated ZFC choices.

## 5. Proposition Dedekind Infinity

Choose distinct atoms a_n∈A for n∈N and put q_n={a_n}. Define f:D_t→D_t by

    f(q_n)=q_(n+1),
    f(p)=p when p is not one of the q_n.

The countable set S={a_n:n∈N} supports f. Permutations fixing S fix every q_n and preserve the complement of that family, where f is the identity. Hence f∈D_tt. Its two displayed pieces have disjoint ranges, and the first piece is a shift, so f is injective and omits q_0. This verifies

    DedInf_t := exists f:tt [forall p q(fp=fq -> p=q)
                             and exists r forall p(fp≠r)].

Equality is rigid, so this assertion holds at every world. The argument also shows exactly why the finite-support proof of Dedekind finiteness is unavailable: Fix(S) now fixes infinitely many propositions when S is countably infinite.

## 6. Functional and Relational Choice still fail

At proposition type the atoms are exactly the singleton worlds. Let U(p,q) be the rigid relation which, when p is the union of two distinct atoms, says q is an atom below p, and otherwise says q=bottom. All ingredients are pure/equivariant, so U is admitted with empty support. It is serial.

Suppose f∈D_tt selected a U-output for every input. Choose a countable support S for f and choose distinct a,b∈A\S. At p={a,b}, the only permissible outputs are {a} and {b}. The transposition (a b) fixes S and p, so equivariance of f requires it to fix f(p), while it interchanges both permissible outputs. Contradiction. Thus FC_(t,t) fails at every world.

Suppose instead an admitted relational R≤U were actually total and single-valued at a world w. Enlarge its countable support by {w}. Choose a,b outside that enlarged support and repeat the transposition argument on the unique actual R-output for p={a,b}. The transposition fixes the evaluation world as well as R and p, so preserves actual truth and uniqueness, again a contradiction. Thus RC_(t,t) fails at every world.

This failure is confined neither to a defect in ordinary arithmetic nor to absent ordinary core selectors: in ZFC every serial relation on trivial-action hereditary core input/output fields has an external selector with an empty-supported default extension, even if the given relation has arbitrary world intensions. The unsupported pair choice here ranges over world-dependent objects.

## 7. Scope and optional generalization

The countermodel establishes the concrete non-entailment

    C + C5 + Atomicity + Box AI_e + Box AI_t + Box IC + DedInf_t
      does not entail FC_(t,t) or RC_(t,t),

with all-type versions of the positive assertions and a full standard ordinary core. These are semantic independence claims about the displayed construction, not automatically new database results.

More generally let kappa be an infinite regular cardinal, |A|≥kappa, and permit supports of size <kappa. The same generic IC proof works: fewer than kappa exceptional witnesses each have support of size <kappa, so regularity bounds their union below kappa. The finite-support case is kappa=omega. For every uncountable regular kappa, the countable shift of §5 is admitted and yields DedInf_t, while the fresh-pair obstruction of §6 remains. No corresponding singular-cardinal claim is made: closure of the exceptional-support union is the exact place regularity is used.

## 8. Full actual countable choice survives

There is a sharper contrast with the finite-support model: in this countable-support model the original countability predicate agrees with external countability of the actual extension, and every serial relation on such an extension has an admitted selector.

Fix an evaluation world w and a relational input type tau. Suppose Ctbl_(rho,tau)(X) holds, with its exact source witness R:tau nu_rho t. For each x in the actual extension B of X, the reflexive case of the definition gives at least one standard numerical label n with R(x,z_n) true. Choose the least such n. The off-diagonal clause says distinct x cannot share a label. This gives an external injection B→N, so B is externally countable. No claim that the relation gives a unique label was used.

Conversely, if B is externally countable, choose an injection i:B→N and a countable support for each member of B. The union of those supports is countable in ZFC. The rigid graph

    R(x,z)=W iff x∈B and z=z_(i(x)),

with empty value otherwise, has that countable support, since every standard numeral has empty support. It is admitted and witnesses the exact Ctbl formula. Thus Ctbl_(rho,tau)(X) at w is equivalent to external countability of B for every counting type rho.

Now let U:alpha beta t be actually serial on an externally countable B⊆D_alpha, with beta a relational output type. Choose one permitted y_x for each x∈B and put

    f(x)=y_x for x∈B,
    f(x)=bottom_beta otherwise.

Choose supports for the countably many x and y_x. Their union K is countable. Every permutation fixing K fixes each member of B and each selected output, and preserves the complement of B. Hence f has support K and is admitted at alpha beta. It selects an actual U-output at every x∈B. The argument works independently at every world.

In particular **every original FC instance with input type e=N holds necessarily**, as do all FC instances restricted to a current internally countable input property, including the standard numerical domain. Yet unrestricted FC_(t,t) fails by §6. The use of ZFC here is explicit: countable witness/support choices and the countable-union theorem are part of the metatheory, not inferred object-language Choice principles.

### 8.1 Any trivial-action input field permits choice, with unrestricted outputs

For countable supports the preceding conclusion extends to arbitrary external cardinalities of the input field, provided every input in that field is fixed by all permutations. Let B⊆D_alpha consist entirely of globally fixed objects, let U be actually serial on B at w, and let S be a countable support for U enlarged by {w}. Choose a countably infinite reservoir R⊆A\S.

For each x∈B choose an eligible output y_x and a countable support T_x. A bijection between T_x\S and a suitable subset of R extends to a permutation g_x of A fixing S: the domains and ranges removed are countable, so their complements both have cardinality |A|. Put z_x=g_x y_x. Since g_x fixes x,U,w, z_x remains an eligible output for x. Its support is contained in S∪R.

Define f(x)=z_x on B and bottom elsewhere. The input field B is invariant and pointwise fixed, while every chosen z_x is fixed by Fix(S∪R); hence f has the common countable support S∪R. Thus the selector is admitted. In particular choice holds from every full ordinary hereditary core input field into any relational original output type, even when outputs depend on worlds. ZFC is used to choose and transport the arbitrarily many witnesses. This strengthens the earlier statement requiring core outputs.

## 9. Regularity is exact for Intensional Choice on natural atom worlds

Let kappa be any infinite cardinal, let |A|≥kappa, set W=A and E=N with trivial action, and permit precisely supports of size <kappa at every domain. All of the closure, C5, all-type Atomicity, standard Frege arithmetic and full ordinary core arguments above remain valid for **singular** kappa as well: they use only finite unions of supports, never a union indexed by an arbitrary set of size <kappa. At proposition type the domain is exactly the subsets of A of size <kappa together with their complements.

The exact classification for this family is

    all-type Box IC holds iff IC_t holds iff kappa is regular.

The regular direction is §7's generic-world construction. Here is an independent proof of failure for singular kappa, without least supports.

Let mu=cf(kappa)<kappa, choose a strictly increasing cofinal sequence of infinite cardinals `(kappa_i : i<mu)` below kappa, and choose distinct worlds s_i∈A. Put S={s_i:i<mu}, an admitted support of size mu. Define the property F of propositions by

    F(p)={s_i:|p|=kappa_i}                       when p≠empty,
    F(empty)=A\S.

Every F(p) is admitted: for nonempty p it is a subset of S, while F(empty) is cosmall. The function F itself is supported by S. Permutations fixing S preserve cardinalities of subsets, fix every s_i, and preserve A\S, so they satisfy the conjugation equation for F. Its fibers are nonempty at every world: at s_i use any subset p of cardinality kappa_i, and outside S use empty. Hence Box exists p F(p) holds.

Suppose G were an admitted IC_t selector graph with support T of size <kappa. At s_i let q_i be its unique selected proposition. Since G≤F, necessarily |q_i|=kappa_i. Every permutation fixing T∪{s_i} preserves G, the world s_i and actual truth there, hence uniqueness forces it to fix q_i. Thus T∪{s_i} supports q_i.

Outside T∪{s_i}, all atoms can be interchanged. Therefore either q_i⊆T∪{s_i}, or q_i contains A\(T∪{s_i}). The second case would give |q_i|=|A|≥kappa, impossible because kappa_i<kappa. Hence

    kappa_i=|q_i|≤|T∪{s_i}|.

Choose i with kappa_i>|T∪{s_i}|, possible by cofinality (uniformly one may first bound |T| and 1). This is a contradiction. Thus IC_t fails at every world; F's seriality and the impossibility of a global singleton subgraph are evaluation-independent.

For singular kappa, the support of the counterexample F is itself legitimate. What fails is the attempt to union one output support of cofinally increasing size at each of the mu exceptional worlds: that union can have size kappa. This identifies the exact use of regularity in the positive proof rather than leaving it as an unexplained sufficient assumption. For every uncountable kappa, regular or singular, the countable shift in §5 still yields DedInf_t, and the fresh-pair argument still refutes FC_(t,t).

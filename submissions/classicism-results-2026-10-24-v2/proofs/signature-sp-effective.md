# The effective boundary of the signature SP construction

Original mathematical argument, direct source misc; unpaginated.

## 1. Fixed framework and statement

Keep exactly the original finitary relational language with

$$
\Sigma=\{c:e\to t\},\qquad M=\operatorname{Max}(C(\Sigma)).
$$

There are no individual names in this original signature. Every Strong
Possibility side condition remains consistency with this same M. The
auxiliary marker a:e describes the proposed singleton root; it does not
enlarge the signature of the target schema.

The report defines the countable many-sorted term algebra B, modulo
C(Σ,a)-provable identity, and a nonempty compact space K of Boolean truth
assignments with the correct typed identity diagram and one individual.
For each predicate term F of type σ→t, its witness requirement is

$$
W_F=\widehat{\neg\exists_\sigma F}
       \cup\bigcup_{b\in B_\sigma}\widehat{F(b)},
\qquad
\mathcal H=\bigcap_F W_F.
\tag{1}
$$

A point of H is exactly a genuine Henkin truth assignment on the fixed
domains B. It yields a model of the requested SP_Σ by REPORT §5. Define

$$
K_0=K,\qquad
K_{\alpha+1}=\bigcap_F\overline{K_\alpha\cap W_F},
\qquad K_\lambda=\bigcap_{\alpha<\lambda}K_\alpha.
\tag{2}
$$

Closures may be taken in K or in the ambient Cantor space; K_α is closed.
REPORT §6 proves stabilization at a countable ordinal γ and
K_γ=cl(H). Let γ denote the least stabilization ordinal.

**Theorem.** In the syntactic coding specified in §2:

1. Every V∈H is nonhyperarithmetic. More strongly, V is not hyperarithmetic
   relative to any numerical set admitted by the model it determines.
2. If H is nonempty, K_γ is perfect, H contains a perfect subset, and there
   are continuum many pairwise elementarily inequivalent original-Σ
   rooted models obtained by this construction.
3. No nonempty closed L⊆K with a hyperarithmetic closed-set presentation
   can have every W_F dense in L. The least stabilization ordinal always
   satisfies γ≤ω₁^CK, and

$$
\boxed{\mathcal H\ne\varnothing
       \quad\Longleftrightarrow\quad
       \gamma=\omega_1^{\mathrm{CK}}.}
\tag{3}
$$

Here ω₁^CK is the supremum of the order types of recursive well-orders.
It is countable externally. If H is empty, the sequence becomes empty
at some computable ordinal, so γ<ω₁^CK. This sharpens the previously
proved countable stabilization but does not decide which alternative
holds or establish consistency of the target theory.

## 2. Effective coding without an oracle for quotient representatives

Fix an effective Gödel coding of the finite typed syntax over Σ∪{a}.
Code V by its truth bits on **all closed proposition terms**, rather than
by a chosen transversal for C-provable equality. Extend the code by zero
on numbers that do not code a closed proposition term. This gives a real
V⊆N in a fixed recursive presentation.

The conditions defining K are uniformly arithmetical: the Boolean truth
laws, invariance under C-provable identity, the singleton sentence, and

$$
V(\ulcorner S=T\urcorner)=1
\quad\Longleftrightarrow\quad
C(\Sigma,a)\vdash S=T.
\tag{4}
$$

C-provability is computably enumerable. Its characteristic predicate is
decidable in 0′, so all the forbidden finite truth patterns defining K
are enumerable in 0′. Thus K has a 0′-effective closed presentation,
equivalently the paths through a 0′-recursive binary tree. This coding is
homeomorphic to the Stone-space presentation in the report; no new
truth assignments or quotient choices are introduced.

Enumerate all well-typed predicate terms F_i, allowing repetitions of
their B-denotations. In the ambient syntax-bit Cantor space, W_i is the
union of the cylinder making ¬∃F_i true and the cylinders making F_i(T)
true, over all closed terms T of the argument type. These open sets have
a uniform computable enumeration. Their intersections with K are the
opens in (1).

Consequently H is a lightface arithmetical set of reals: all its
conditions quantify only over natural-number codes, with V as the real
parameter. In particular H is lightface analytic. Its points need not
themselves be arithmetical or hyperarithmetic.

## 3. Standard numerical traces and full comprehension

Fix V∈H and its genuine rooted model on B. Let ν=(et)t, let N be the
established numerical predicate, and write n̄ for the numeral terms.
REPORT §7 proves that every element of B_ν satisfying N is one of the
standard numerals. Distinct numerals are distinct, and the interpreted
arithmetic operations have their standard values. Hence the actual
numerical domain is externally the standard natural numbers.

For R∈B_{νt}, put

$$
X_R=\{n\in\mathbb N:V(\ulcorner R(\bar n)\urcorner)=1\},
\qquad \mathcal S_V=\{X_R:R\in B_{\nu t}\}.
\tag{5}
$$

**Lemma.** (N,S_V) is an omega-model of full second-order arithmetic Z₂.

Translate numerical quantifiers with the guard N, membership n∈X_R by
the actual truth of R(n), and set quantifiers by quantifiers of type
ν→t. Translate set equality **extensionally**, as
∀n(N(n)→(R(n)↔S(n))). Distinct higher-order entities having the same
numerical trace represent the same second-order set. Induction on
second-order formulas shows that their translations depend only on
these traces. Set quantification therefore agrees with quantification
over S_V, even when several entities have the same trace.

For any second-order formula φ(n,X₁,…,X_k), including formulas with
set quantifiers, choose term representatives R₁,…,R_k. Lambda
abstraction of its translated formula gives a term of type ν→t whose
trace is exactly {n:φ(n,X₁,…,X_k)}. Thus every full comprehension
instance, with parameters, holds. Arithmetic is standard and induction
holds for every subset of the actual standard natural numbers. This
proves the lemma. It does not use Functional Choice, Plenitude, or a
map taking actual truth values to the proposition entities top/bottom.

We use the usual effective-recursion fact: an omega-model of Z₂
contains every hyperarithmetic real, and, for each of its sets X, every
real hyperarithmetic in X. The requisite omega-model closure has the
following direct proof.

Let ≺ be an actually well-founded relation on a set D, with both coded
in S_V, and fix an arithmetical recursion rule
Y_b={n:Φ(n,b,Y restricted below b)} with parameters in S_V. A partial
solution is a coded pair (E,Y) whose domain E⊆D is downward closed and
whose rows obey the rule. This condition is arithmetical. External
well-founded induction shows that any two partial solutions agree
where both are defined. Full comprehension forms both the union P of
their domains and the union J of their rows, quantifying over admitted
partial solutions. These are admitted sets, and agreement makes J
unambiguous. If every predecessor of b lies in P, then the restriction
of J below b is a partial solution. Arithmetic comprehension supplies
its b-row; adjoining that row produces a partial solution through b.
External well-founded induction therefore gives P=D and makes J the
full, correct hierarchy. No countable choice or correctness about
arbitrary ill-founded orderings is used.

Apply this to an actual X-recursive well-order, or to the
well-founded notation-dependency relation below a fixed genuine
notation b∈O^X. In the latter description the domain and dependency
relation are arithmetical in X; the base, jump and effective-join rules
are arithmetical. Thus every genuine hierarchy H_b^X belongs to S_V.
Arithmetic comprehension supplies its columns and all Turing-reducible
sets. The hyperarithmetic characterization by these hierarchies now
gives HYP(X)⊆S_V. See Jananthan–Simpson, *Turing degrees of hyperjumps*,
29 June 2020 draft, [Lemma 2.5, p.5](https://sgslogic.net/t20/papers/hyperjump.pdf).

## 4. The truth code cannot be an admitted numerical trace

**Lemma.** V∉S_V.

Otherwise choose a **closed term** R:ν→t whose trace is V, under the
syntax coding of §2. Apply the arithmetic diagonal construction to the
formula ¬R(x), using the standard arithmetical relation for syntactic
substitution. This supplies a closed Σ(a)-sentence L for which the
following material biconditional is true in the model:

$$
L\ \leftrightarrow\
\neg R(\overline{\ulcorner L\urcorner}).
\tag{6}
$$

For completeness, let Sub(u,u,z) represent the computable operation
that substitutes the numeral for u in the one free numerical variable
of the formula with code u. Form
A(x):=∃z(N(z)∧Sub(x,x,z)∧¬R(z)) and take L=A(k̄), where k is the code
of A. Standard arithmetic gives the unique substitution output
z=⌜L⌝, proving the displayed biconditional at the root. Auxiliary
abbreviations are expanded before taking the codes.

Because X_R=V and V is the actual truth code of the same syntax,
R(⌜L⌝) is true exactly when L is true. This contradicts (6).

The predicate is its existing term representative, not a freshly
adjoined truth constant. Equation (6) is a material biconditional; it
is not promoted to identity of proposition entities, nor boxed under
an optional assumption. The SP side-condition signature never changes.

By §3, every hyperarithmetic real is in S_V. The lemma therefore proves
that V is nonhyperarithmetic. Relativizing the same argument gives

$$
X\in\mathcal S_V\quad\Longrightarrow\quad
V\notin\operatorname{HYP}(X).
\tag{7}
$$

Each such X is nevertheless Turing reducible to V: fix a term R
representing it and query the truth bits for R(n̄). This is a restriction
on the external truth code, not a contradiction within the model.
No single admitted predicate is required to capture the truth of the
entire finite-type language.

## 5. A successful kernel has no isolated points

Suppose K_γ is nonempty and has an isolated point V. Since H is dense
in K_γ, V∈H. Some finite syntax-bit cylinder [s] isolates it, so
H∩[s]={V}. The defining property of H∩[s] is lightface arithmetical.
For each natural number n, the two assertions

$$
\exists Y\in\mathcal H\cap[s]\ (n\in Y),
\qquad
\exists Y\in\mathcal H\cap[s]\ (n\notin Y)
$$

are lightface analytic and define complementary predicates on n.
Thus V is Δ¹₁, equivalently hyperarithmetic, contrary to §4. For the
standard equivalence, see Moschovakis, *Hyperanalytic predicates*,
[p.250](https://www.researchgate.net/publication/243076265_Hyperanalytic_predicates).
Hence
K_γ has no isolated points and is a perfect compactum.

H=K_γ∩⋂_iW_i is dense G_delta in it. A binary nested-neighborhood
construction gives a perfect subset of H: at stage n, split each
nonempty relative neighborhood into two disjoint smaller ones, with
closures in W₀∩…∩W_n and diameters tending to zero. Density and the
absence of isolated points permit every split. Compactness supplies a
distinct limiting point for each binary branch; every limit meets all
the witness requirements. Hence H has cardinality continuum.

Different V,W∈H differ on some closed proposition term P(c,a).
Their singleton individual domains imply that the original-Σ sentence
∃x^e P(c,x), with capture-avoiding replacement of a, has the respective
truth values of P(c,a). Thus the rooted models disagree already on an
original-Σ sentence. They are pairwise elementarily inequivalent, not
merely different choices of an auxiliary marker.

## 6. No hyperarithmetic closed certificate, and the lower bound

**Effective Baire lemma.** Let L⊆K be nonempty and closed, with a
hyperarithmetic closed-set presentation. If every W_i is dense in L,
then H has a hyperarithmetic point.

Choose a hyperarithmetic oracle Z making a binary tree for L recursive.
For a finite string s, nonemptiness of L∩[s] is decidable in Z′:
an infinite finitely branching subtree exists exactly when it has
nodes at every finite level. Starting from a cylinder meeting L,
enumerate cylinders in W_i and use this test to choose a compatible
extension s_i whose cylinder still meets L, is contained in W_i, and
has length at least i. Relative density guarantees that this search
terminates. Preserve all earlier cylinder inclusions. The increasing
strings define a point V≤_T Z′ lying in every W_i; closedness puts it
in L. It is hyperarithmetic, proving the lemma.

Section 4 now shows that no such L can exist. In particular a
nonempty stable kernel cannot have a hyperarithmetic closed code.

It remains to relate this fact to the stages in (2). If a closed set
F has a Z-recursive binary-tree presentation, then

$$
F\cap[s]\cap W_i\ne\varnothing
$$

is Σ⁰₂ relative to Z: choose an enumerated cylinder inside W_i and
test whether its compatible intersection with [s] has an infinite
subtree. Consequently Z″ decides which cylinders miss F∩W_i. The
union of those cylinders is the complement of cl(F∩W_i). Taking the
union also over i produces a Z″-effective open complement of
D(F)=⋂_i cl(F∩W_i), hence a Z″-recursive closed-set tree for D(F).
This construction is uniform in the presentation.

At an effective limit stage, a joined sequence of previous closed
codes presents their intersection by enumerating the union of the
open complements. Effective arithmetical transfinite recursion along
any recursive well-order therefore produces hyperarithmetic closed
codes for all its stages, starting with the 0′ code for K₀ from §2.
Equivalently, one may recursively define the code at each element
from the sequence of all earlier codes; intersections handle limits
and the uniform successor operation handles successors. Thus K_α has
a hyperarithmetic closed presentation for every α<ω₁^CK.

If H≠∅ and stabilization occurred at such an α, K_α would be a
nonempty closed set with that presentation and all W_i dense, which
the effective Baire lemma and §4 exclude. This proves the lower-bound
half of (3).

This argument alone does not prove survival to ω₁^CK. The next section
supplies the matching upper bound and the extinction alternative.

## 7. Matching upper bound and exact dichotomy

Represent each stage by its **saturated** open-complement code

$$
S_\alpha=\{s:[s]\cap K_\alpha=\varnothing\}.
\tag{8}
$$

These are sets of finite binary strings, coded by natural numbers.
The seed S₀ is arithmetical: disjointness of a cylinder from the
0′-recursive compact tree for K₀ is Σ⁰₁ relative to 0′.

For an arbitrary set A of cylinder codes, let Cover(u,A) say that [u]
has a finite cover by cylinders with codes in A, and put
Sat(A)={u:Cover(u,A)}. Cover is an arithmetical formula positive in A:
existentially choose finitely many codes, require each to belong to A,
and check the finite clopen coverage. Permit u to code the empty
clopen set when taking intersections of incompatible cylinders.

Let E_i enumerate the cylinder codes whose union is W_i. Define

$$
\begin{aligned}
R(A)&=\{s:\exists i\ \forall t\in E_i\,
                \operatorname{Cover}([s]\cap[t],A)\},\\
\Gamma(A)&=\operatorname{Sat}\bigl(S_0\cup A\cup R(A)\bigr).
\end{aligned}
\tag{9}
$$

The notation Cover([s]∩[t],A) uses the longer string when compatible,
and the empty clopen set otherwise. Enumeration membership in E_i is
arithmetical and independent of A. Consequently Γ is an ordinary
arithmetical, globally monotone, inflationary operator on subsets of
the natural numbers. This assertion holds even for unsaturated A;
the seed is an arithmetically definable predicate, not a new real
parameter of unknown complexity.

For A=S_α, membership of s in R(A) means that some K_α∩W_i misses
[s]. It is equivalently the condition that [s] misses
cl(K_α∩W_i), because [s] is clopen. The complement of K_{α+1} is
the union of these removed cylinders and the old complement. Taking
Sat accounts for all cylinders lying inside that open union. Hence

$$
S_{\alpha+1}=\Gamma(S_\alpha).
\tag{10}
$$

At every nonzero limit λ, compactness gives
S_λ=⋃_{α<λ}S_α. Indeed a cylinder disjoint from ⋂_{α<λ}K_α is covered
by the increasing open complements, so a finite subcover already
lies inside one earlier complement. This is the step that makes the
closed-set derivative an ordinary monotone inductive definition on
natural numbers.

The standard closure-ordinal theorem for monotone arithmetical
operators says that iteration from the empty set stabilizes by
ω₁^CK. See Cenzer–Remmel, *On the Complexity of Inductive Definitions*,
author-hosted manuscript, [Theorem 2.1(d), p.3](https://people.clas.ufl.edu/cenzer/files/n63.pdf).
This cited general theorem is distinct from the coding application
proved here.

To account explicitly for the seed, let T_α be the iterates of Γ from
the empty set. Transfinite induction gives
T_α⊆S_α⊆T_{α+1}: at zero Γ(∅) contains S₀, successors use
monotonicity, and limits use the union identities. The two chains
agree at every nonzero limit, in particular at ω₁^CK. Since the
T-chain is stable there, (10) makes the S-chain stable there as well.
The saturated complement code determines the closed set uniquely,
so γ≤ω₁^CK.

If H≠∅, §6 gives the reverse inequality, hence γ=ω₁^CK. If H=∅,
the stable kernel identity gives K_{ω₁^CK}=∅. Compactness of the
decreasing closed family implies K_α=∅ for some α<ω₁^CK: otherwise
that family would have the finite intersection property. Thus in
this case γ<ω₁^CK. We obtain the exact alternatives

$$
\begin{array}{ll}
\mathcal H=\varnothing:
  &\text{extinction at a computable ordinal};\\
\mathcal H\ne\varnothing:
  &\text{first stabilization, nonempty, at }\omega_1^{\mathrm{CK}}.
\end{array}
\tag{11}
$$

No algorithm for deciding these alternatives is supplied.

## 9. Sources and verification

The local mathematical inputs and their source boundaries are in
[REPORT.md](signature-sp-derivative.md), especially §§3, 5–8. The formulation of
Strong Possibility is Bacon–Dorr, *Classicism*, draft of 16 May 2023,
§2.6, p.42; that source is not credited with the new results here.

The effective-recursion background used in §§3, 5–7 consists of
the equivalence of hyperarithmetic and Δ¹₁ sets, the transfinite-jump
characterization, arithmetic transfinite recursion, and the
closure-ordinal bound for monotone arithmetical operators. The primary
sources linked at the relevant steps were read during this continuation:
Jananthan–Simpson, *Turing degrees of hyperjumps*, 29 June 2020 draft,
Lemma 2.5, p.5; Moschovakis, *Hyperanalytic predicates*, *Transactions
of the AMS* 129 (1967), pp.249–282, specifically p.250. The specific
applications to the unary-signature term algebra, the omega-model
closure proof, the material diagonal argument, and the derivative
are supplied in this note. The general upper bound is stated in
Cenzer–Remmel, *On the Complexity of Inductive Definitions*,
Theorem 2.1(d), p.3; no publication date beyond the manuscript's own
metadata is inferred. Its arithmetical-seed variant is also explicitly
used in Shafer–Terwijn, *Ordinal analysis of partial combinatory
algebras*, 16 September 2021 author-hosted draft,
[proof of Theorem 5.4, p.7](https://peshafer.github.io/ShaferTerwijnPCAOrd.pdf).

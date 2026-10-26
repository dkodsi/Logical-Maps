# Canonical-chain lemmas for propositional completeness

OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026. Source: `misc`, this proof, unpaginated. These are the two chain constructions used in [Zorn and propositional completeness imply Actuality](c5-zorn-and-propositional-completeness-imply-actuality.md).

## 1 Represented progressive graphs


**Lemma.** Let $`P^{\rho t}`$ carry a represented antisymmetric partial order, have a least element 0, and have a LUB in P for every represented chain, including the empty chain. Let f be a represented total single-valued graph from P to P with x≤f(x) for every x∈P. Then f has a fixed point.

The proof uses only predicate comprehension and ordinary quantification admitted in C. In particular it does not assume an external set of ordinals, standard finiteness, an operation representing f, or extensionality of property entities.

Call a predicate $`C^{\rho t}`$ an **f-chain** when:

1. C⊆P and the inherited order well-orders C: every admitted nonempty subproperty of C has a least member.
2. For each x∈C, x is the LUB in P of the graph image


```math
\{f(y):Cy\text{ and }y<x\}.\tag{6}
```


Condition 2 is a formula about being a LUB; it does not presume this image has a LUB before the condition is asserted. The singleton {0} is an f-chain. If x<y lie in an f-chain, then f(x)≤y by (6).

**Comparison.** Any two f-chains C,D are comparable by initial segment. Define I to consist of those common members x for which the C- and D-predecessor properties below x are coextensive. I is an initial segment of both C and D: if x∈I and y<x lies in either chain, then y lies in both, and the predecessor properties below y are equal in extension as subsets of their common predecessor property below x.

If both C\I and D\I were nonempty, let c,d be their respective least members. Their predecessor properties are each coextensive with I. The graph images in (6) are therefore coextensive. Since an antisymmetric poset has at most one LUB for a given actual family, c=d. This equality and equality of their predecessor extensions place c in I, contradiction. Hence C≡I or D≡I (actual coextension), proving comparison by initial segment. Notice that equality of predicate codes was never inferred from coextension; only uniqueness of their order-theoretic LUB was used.

**Union.** Define the admitted property


```math
A(x):=\exists C^{\rho t}.\,(C\text{ is an }f\text{-chain}\land Cx).
```


Comparison makes A a chain. It is internally well-ordered: given any nonempty represented X⊆A, choose x∈X and an f-chain C containing x. Let m be the least member of X∩C. For any z∈X, choose an f-chain D containing z. If D is an initial segment of C, then z∈C and m≤z. If C is an initial segment of D, then either z∈C, giving the same conclusion, or z lies strictly above every member of C, including m. Thus m is least in X.

For x∈A choose an f-chain C containing x. Comparison shows that A and C have the same predecessor extension below x. Condition (6) for C therefore gives it for A, again using only actual coextension of the represented images. Hence A is itself an f-chain, and it contains every f-chain by definition.

**The supremum is a fixed point.** Let u be the LUB of A in P. If u∉A, then A has no largest member. For every x∈A choose y∈A with x<y; (6) gives f(x)≤y≤u. Conversely x≤f(x) for each x, so any upper bound of f[A] bounds A. Therefore u is the LUB of f[A]. Adjoining u at the end of A gives another f-chain: its new predecessor property is A, and the defining LUB condition is the one just proved. This contradicts the definition of A, which would then contain u. Thus u∈A.

If u<f(u), adjoining f(u) at the end of A again gives an f-chain. Its new LUB condition holds because f(u) is the greatest member of f[A]: for x<u in A, (6) gives f(x)≤u≤f(u), and f(u) itself is in that image. Again the definition of A would put f(u) into A, contradicting u being an upper bound. Progressivity leaves f(u)=u. This proves the lemma.

## 2 Descending current graph chains

Here is the order-dual form on the Boolean interval [0,h]. Suppose F is a current total functional relation there, with F(p)≤p. Function notation abbreviates its unique **current** graph value. A predicate C is an F-chain when:

1. its current members form a chain in [0,h], internally wellordered by the reverse Boolean order (every admitted nonempty subproperty has a Boolean-greatest member);
2. each member p is the actual Boolean infimum, within [0,h], of

```math
\{F(q):Cq\text{ and }p<q\}.
\tag{3}
```


The infimum of the empty family in the interval is h. The singleton {h} is an F-chain. Any two F-chains compare by initial segment: form their common part on which strict predecessor extensions agree; if both have a first disagreement, (3) gives the same actual infimum to both first new elements. Only uniqueness of an actual infimum is used, not equality of coextensive family codes.

Their admitted union


```math
M(p):=\exists C\,[C\text{ is an F-chain}\land Cp]
\tag{4}
```


is itself an F-chain and contains every F-chain. BC_t supplies its actual infimum m. Appending that infimum, and then F(m) if necessary, proves m∈M and F(m)=m. These are exactly the comparison, union, and endpoint arguments of §1, with order reversed.

We will also use two immediate consequences. If p∈M, its initial segment through p is an F-chain; adjoining F(p) shows F(p)∈M. If F(p)<p, this is the immediate next member. Moreover, for q<p in M, conformity at q gives q≤F(p). A fixed point in M must be terminal: otherwise the first member after it has, by (3), that same fixed point as its defining infimum.

All families here are admitted predicates of propositions. BC_t is used for their **current extensions**, not identified with a material quantifier.

## 3 Strong crisp chains for operations

**Lemma.** Under C5, let g:tt be an admitted operation such that, throughout [0,h], g(p)≤p, and let these interval and progress conditions be necessary. There is an admitted crisp g-chain D, with full current reverse wellordering and conformity (3), whose terminal member is a fixed point of g. In fact D necessarily has those chain properties. No BC premise is needed for this lemma.

Here crisp means that each membership coefficient is 0 or 1. C5 makes identity assertions crisp, supplies Barcan, and makes Boolean combinations and quantified formulas of crisp assertions crisp. For any crisp X:tt the term


```math
j_X:=h\land\forall p\,[Xp\to g(p)]
\tag{5}
```


is the actual algebraic infimum, within [0,h], of the current g-values at X-members. Indeed every current member has coefficient 1, and every nonmember coefficient 0. Universal instantiation gives the lower bounds. Conversely, if z≤h bounds all current g-values from below, the endpoint coefficients and Barcan collect those bounds into z≤j_X. This argument is valid at every world under C5.

For a code C:tt define Strong(C) to assert:

* C is crisp;
* **necessarily**, its members are a chain in [0,h], fully wellordered in the reverse order against all admitted subproperties, and every p∈C is the algebraic infimum of the g-values at its strict predecessors.

This is a finite formula at existing types. Crispness is a quantified identity condition, and the necessary clause is endpoint-valued under C5. Thus Strong(C) is crisp. The singleton of h satisfies Strong: its assertions hold uniformly, with the empty predecessor infimum h.

Define


```math
D(p):=\exists C^{tt}\,[\mathrm{Strong}(C)\land Cp].
\tag{6}
```


The coefficients in (6) are crisp, so D is crisp.

We verify its necessary chain assertions **uniformly at an arbitrary world**. Every current Strong-member there is a full g-chain there. The ordinary comparison argument of §2 therefore applies at that world, including to the possibly noncrisp differences of chain properties. It makes their union a chain. For any admitted nonempty current subproperty X of D, choose x∈X and a Strong-chain C containing x. Full wellordering of C gives the first member of X∩C. Comparing C with each Strong-chain containing another X-member shows that this member is first in all of X. Thus the union is fully wellordered, not merely wellordered for crisp X. Finally, all predecessors of a union member already occur in one Strong-chain containing it, so its infimum clause transfers by uniqueness of the actual infimum.

This argument uses only the necessary hypotheses built into Strong and the C5 crisp-family bound calculation (5). It consequently proves the union's chain assertions at every world, hence their necessity. No instance of current BC_t is used or necessitated. Therefore Strong(D).

Let u=h∧∀p(Dp→p), the actual infimum of D at every world by the same crisp-family argument. If u∉D, D has no last member. At every world, for each p∈D there is q∈D with u≤q<p; conformity at q gives q≤g(p). Together with g(p)≤p, this shows that the infima of D and g[D] coincide. Hence appending u preserves conformity. Appending a last element preserves full wellordering at every world: a nonempty subproperty either meets D, when D supplies its first member, or consists only of the appended point. The appended family is crisp. These facts give Strong(D∪{u}), contradicting the defining union (6). Thus u∈D.

If g(u)<u, appending g(u) likewise preserves the necessary full wellordering and conformity: g(u) is the least g-value of D, since conformity at u puts every earlier g-value above u. Again (6) gives a contradiction. Therefore g(u)=u.

The case distinctions used here are identity/order assertions involving admitted terms; under C5 they are stable. The append arguments are uniform proofs from necessary premises, not a boxing of optional current wellordering or completeness assumptions. This proves the lemma.

In particular, if g(0)=0 and 0<g(p)<p for every positive p≤h, the terminal member of D is 0.

## Sources

The first lemma is reproduced from OpenAI Codex, *Relational Choice and Boolean Completeness imply Actuality*, Appendix D, unpaginated. The descending form and strong crisp lemma are reproduced from OpenAI Codex, *Propositional completeness excludes a strict splitter on a true interval*, 25 October 2026, §§2–3, unpaginated. The source hashes are recorded with this update.

# Zorn and propositional completeness imply Actuality

OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026. Source: `misc`, this proof, unpaginated.

**C5, Boolean Completeness at the proposition type, and Zorn at the proposition type imply Actuality.** Both additional principles are current, unboxed assumptions. No Relational Choice, higher-type Zorn, higher-type completeness, or admitted strict splitting operation is assumed.

The main difficulty is that Zorn on propositions cannot simply be applied to partial choice functions. Instead, one proposition records a history of separated Boolean bands. The gaps between successive bands prevent a limit from erasing that history. Zorn therefore produces a wellordered refinement of any admitted chain whose meet is zero. Applied to a chain of truths, this gives a definable functional graph selecting a proper part of each true proposition. A coefficient normalization turns that graph into strict partitions on a true interval. A second proposition records choices from a disjoint family, completing the existing partition-and-reconstruction argument for Actuality.

## 1 Statement and conventions

In the fixed finitary relational language,


```math
\boxed{C5+BC_t+Zorn_t\ \Longrightarrow\ \mathrm{Actuality}}
\tag{1}
```


Write 0 and 1 for Bottom and Top. The Boolean order is the algebraic order
$`p\le q\iff p\land q=p`$; put $`p\setminus q=p\land\neg q`$.
“Positive” means nonzero, and does not mean currently true. A predicate's family is always its **current extension** unless stated otherwise. All predicates, relations, images, and unions used below are admitted lambda-defined expressions. Their quantifiers range over the existing types of the framework.

BC_t supplies actual least upper bounds and greatest lower bounds of admitted predicates of propositions. Zorn_t applies to admitted preorders on the carrier t; its chains are admitted predicates on which the preorder is antisymmetric and total. A code below is a single proposition, even though the definition of its validity quantifies over predicates. No application of Zorn has a predicate or a relation as its carrier.

C5 supplies the required Barcan and Functionality instances and makes identity and Boolean-order assertions endpoint-valued. We call such assertions **crisp**. Boolean combinations and quantified formulas of crisp assertions remain crisp. This does not make arbitrary current predicate membership crisp.

Two elementary bound facts will be used. First, fixed Boolean meet preserves every existing actual join: if u is the actual join of X, then b∧u is the actual join of the admitted image $`\{b\land x:Xx\}`$. This follows directly from the Boolean adjunction
$`b\land x\le v\iff x\le\neg b\lor v`$.
In particular, a positive a below u meets some X-member; otherwise ¬a would bound X and hence u.

Second, under C5 the material existential over an entire admitted range is its actual join. More generally, when P is crisp,


```math
\exists x\,[P(x)\land v(x)]
\tag{2}
```


is the actual join of the v-values at current P-members. Each current upper-bound assertion is an identity; its crispness and Barcan give the necessary universal bound, which yields the bound on (2). The dual calculation applies to material universals. We use this calculation only for entire ranges or crisp indexing, never for an arbitrary current family.

## 2 Failure of Actuality produces a true chain with meet zero

This preliminary reduction uses only C, BC_t, and Zorn_t.

Order the currently true propositions by reverse Boolean inclusion. Extend this to a preorder on all propositions by putting the false propositions below every true proposition and making the false propositions mutually equivalent. One formula for it is


```math
R(p,q):=\neg p\ \lor\ (q\land q\le p)
\tag{3}
```


If p is true and is not an atom, choose $`0<b<p`$. Exactly one of b and $`p\setminus b`$ is true, and either choice is a true proposition strictly below p. Thus, if Actuality fails, this preorder has no maximal element: a true member can be strictly extended in the reverse order, and a false member lies strictly below 1.

Zorn_t therefore supplies an admitted R-chain with no upper bound. Its true part D is nonempty, is a Boolean-order chain, and has no currently true Boolean lower bound. If its true part were empty, 1 would bound the original R-chain.

Let u be the actual infimum of D, supplied by BC_t. It is false. Replace D by the admitted image


```math
D_0(p):=\exists d\,[Dd\land p=(d\land\neg u)]
\tag{4}
```


Every D_0-member is true and positive. It is still a chain and has actual infimum 0. Indeed any lower bound v of D_0 is below every D-member and below ¬u, hence below $`u\land\neg u=0`$.

It remains to rule out an admitted all-true chain of positive propositions with actual meet zero.

## 3 Annuli and one-proposition history codes

Let D be any admitted chain of positive propositions with actual infimum 0. Current truth of its members is not assumed in this section or the next.

A **D-annulus** is a positive proposition of the form


```math
b=d\setminus c,\qquad Dc,\ Dd,\quad c<d
\tag{5}
```


Its endpoints c,d are unique. To see this, suppose $`d\setminus c=d'\setminus c'\ne0`$ and c<c′. If d≤c′, the common band is both below and disjoint from c′. If c′<d, the positive proposition c′\c belongs to the first band and is disjoint from the second. Both are impossible. Thus c=c′, and equality of the upper endpoints follows in the same way. Endpoint notation below abbreviates this admitted unique graph; no endpoint operation is extracted.

For a proposition m, define H_m to be its maximal D-annuli:


```math
\begin{aligned}
H_m(b):={}&\mathrm{Ann}_D(b)\land b\le m\\
&\land\forall b'\bigl(
\mathrm{Ann}_D(b')\land b'\le m\land b\le b'
\ \longrightarrow\ b=b'\bigr)
\end{aligned}
\tag{6}
```


Distinct H_m-bands are disjoint and have a positive gap between them. If two overlap or touch, their union is a D-annulus contained in m and strictly extending at least one, contrary to maximality. Since their endpoints lie in a chain, one band lies outside the other. Order bands **from outside to inside**: if b=d\c and b′=d′\c′, then b precedes b′ when d′<c. The gap is c\d′.

A proposition m is a **valid history code** when:

1. m is the actual least upper bound of H_m;
2. the outside-to-inside order wellorders H_m against every admitted current subpredicate.

Denote this admitted condition by V(m). The empty code 0 is valid: H_0 is empty and has join 0.

For valid p,q, write $`p\preceq q`$ when H_p is a subset of H_q and every new H_q-band follows every H_p-band. This is end-extension of histories. Define a preorder on all propositions by


```math
\mathcal R(p,q):=\neg V(p)\ \lor\
\bigl(V(q)\land p\preceq q\bigr)
\tag{7}
```


In (7), the formula defining $`p\preceq q`$ is used at all inputs; its interpretation as an end-extension is needed only when p is valid. Invalid codes lie below all valid codes, and no valid code lies below an invalid code. End-extension is reflexive and transitive. On valid codes it is antisymmetric: equality of their band families implies equality of their actual joins. Thus $`\mathcal R`$ is a preorder and any maximal element is valid.

The following limit observation is the reason a proposition can retain the history.

**Band preservation lemma.** Suppose Y is an admitted, outside-to-inside wellordered family of D-annuli, distinct members have positive gaps, and u is its actual join. Then every D-annulus below u is contained in one Y-band. Consequently the maximal D-annuli below u are exactly the Y-bands.

For the proof, a positive annulus a≤u meets a Y-band. If a meets two bands, let b be the earlier of two met bands and let s be its immediate Y-successor. Such a successor exists by wellordering, since a later band exists. The positive gap between b and s is contained in a: the endpoints of a must extend across the earlier met band and the later met band. This gap is disjoint from every Y-band, by consecutiveness and the linear order of all endpoints. Its complement therefore bounds Y, so the gap is disjoint from u, contradicting its inclusion in a≤u.

If a meets only one Y-band b but is not contained in b, its positive excess a\b is below u and must meet another Y-band, again a contradiction. Hence a≤b. This also shows that every Y-band is maximal among the annuli below u, and that every maximal annulus below u is a Y-band. The empty-family case is immediate.

## 4 Zorn gives a wellordered coinitial refinement

Let X be an admitted $`\mathcal R`$-chain. Ignore its invalid members and let u be the actual join of its valid members, using BC_t; take u=0 if there are none. Put


```math
Y(b):=\exists m\,[Xm\land V(m)\land H_m(b)]
\tag{8}
```


The H_m form end-extended initial segments of Y. Their bands are pairwise gap-separated, because any two bands belong together to the larger of two comparable histories.

Y is wellordered. Given any admitted nonempty subpredicate Z of Y, choose z∈Z and a constituent H_m containing z. The least member of Z∩H_m is least in all Z: every member of Z outside H_m follows every H_m-member. This uses the full current wellordering in V(m), not just wellordering against crisp predicates.

The proposition u is also the actual join of Y. Every Y-band lies below a constituent code and hence below u. Conversely, any upper bound of Y bounds each H_m, so it bounds each constituent code and therefore u. By the band preservation lemma,


```math
H_u=Y\quad\hbox{as current extensions}
\tag{9}
```


Thus u is valid. Each constituent H_m is an initial segment of H_u, so u is an $`\mathcal R`$-upper bound of X. Equality (9) is only a statement about current extensions; no identity of predicate objects is needed.

Zorn_t now yields a maximal valid code m. It meets every D-member. Otherwise let d∈D satisfy m∧d=0. Because D has meet 0 and d>0, choose c,e∈D with


```math
0<c<e<d
\tag{10}
```


Each old band has lower endpoint at least d: a band whose lower endpoint were below d would meet d. Append the new band e\c. It follows all old bands, with a positive gap, and the old wellorder followed by this last band is still a wellorder, including when the old history has no last member. Its join is m∨(e\c). The band preservation lemma shows that its maximal annuli are exactly the old bands together with the new band. It is a valid strict end-extension of m, a contradiction.

Define L to be the admitted image of the lower endpoints of H_m. These endpoints are distinct and strictly decrease along the band wellorder, so L is wellordered by **reverse** Boolean inclusion. This transports full current wellordering: an admitted subpredicate of L pulls back to an admitted subpredicate of H_m along the unique endpoint graph.

L is coinitial in D. For any d∈D, m∧d>0, so d meets some H_m-band. Its lower endpoint is then strictly below d. It follows that L has actual infimum 0. We have proved:


```math
\boxed{C+BC_t+Zorn_t:\quad
\begin{gathered}
\text{every admitted positive Boolean chain with meet }0\\
\text{has an admitted reverse-wellordered coinitial subchain.}
\end{gathered}}
\tag{11}
```


In particular, if the original chain consists of truths, so does L. This construction has not made either chain predicate crisp.

## 5 A true wellordered chain supplies strict partitions

Suppose L is an admitted, reverse-wellordered chain of true propositions with actual meet 0. For every true p there is an L-member c with p≰c. Reverse wellordering supplies the greatest such c in Boolean order. Define its graph by


```math
\mathrm{First}(p,c):=
Lc\land p\nleq c\land
\forall d\bigl(Ld\land p\nleq d\ \longrightarrow\ d\le c\bigr)
\tag{12}
```


The proposition p∧c is true, hence nonzero, and is strictly below p. Define


```math
\begin{aligned}
F(p,q):={}&(\neg p\land q=0)\\
&\lor\bigl(p\land 0<q<p\land
\exists c[\mathrm{First}(p,c)\land q=(p\land c)]\bigr)
\end{aligned}
\tag{13}
```


This is an admitted current total functional graph. False inputs have unique output 0; true inputs have the unique output just described. No Relational Choice is used, and no operation representing its current graph values is asserted. The explicit strictness guard is essential: it gives the algebraic inequality


```math
p\land F(p,q)\le(0<q<p)
\tag{14}
```


without trying to make the current functional assertion necessary.

Normalize its coefficients:


```math
\begin{aligned}
c_p(q)&:=F(p,q)\land\forall z\,[F(p,z)\to z=q],\\
d_p&:=\exists q\,c_p(q),\qquad
a:=\forall p\,d_p
\end{aligned}
\tag{15}
```


For every current p its selected output has a true coefficient. Hence every d_p, and therefore a, is currently true. Universal instantiation gives a≤d_p for every p. Coefficients at distinct outputs are algebraically disjoint: their conjunction implies equality of the outputs, and a false identity is 0 under C5.

For all p,q define admitted operations


```math
u_0(p,q):=p\land c_p(q)\land q,
\qquad
u_1(p,q):=p\land c_p(q)\land\neg q
\tag{16}
```


For every positive p≤a their positive values partition p into proper parts. This includes currently false p: weighting by p eliminates the false-input branch of F. No separate true atomless interval is assumed. Distinct coefficients give disjoint parts, and the two parts at one coefficient are disjoint. If either part is positive, then p∧c_p(q)>0. By (14), this is below the crisp strictness assertion 0<q<p; that assertion must therefore be 1. Consequently
$`u_0(p,q)\le q<p`$ and $`u_1(p,q)\le p\setminus q<p`$.
It is not necessary that both parts at every coefficient be positive.

Finally,


```math
\exists q\,[u_0(p,q)\lor u_1(p,q)]
=p\land d_p=p
\tag{17}
```


The entire-range calculation from §1 makes this their actual join. Define


```math
\mathrm{Child}(p,r):=
(0<p\le a)\land r>0\land
\exists q\,[r=u_0(p,q)\lor r=u_1(p,q)]
\tag{18}
```


Child is crisp: its definition uses only identities, order assertions, and quantification over them. For every positive p≤a its children are pairwise disjoint proper parts with actual join p. Each such p has a child, and every child has a different sibling; otherwise its join would be a single proper part. Moreover,


```math
p=\exists r\,[\mathrm{Child}(p,r)\land r]
\qquad(0<p\le a)
\tag{19}
```


Thus a true p has exactly one true child. We have obtained precisely the strict partition family needed below, on a true interval, without either a global splitter or RC.

## 6 Zorn chooses simultaneously on disjoint pieces

We record the second replacement for choice in a form that uses only C+BC_t+Zorn_t.

Let D be an admitted family of pairwise disjoint positive propositions. Let T(d,r) be any admitted relation such that every current D-member d has a witness with 0<r≤d and T(d,r). Then there is one proposition b such that


```math
Dd\ \longrightarrow\
\bigl(0<(b\land d)\ \land\ T(d,b\land d)\bigr)
\tag{20}
```


This is simultaneous selection by one Boolean mask; it is not unrestricted Functional Choice.

Let j be the actual join of D. A partial mask p is valid when p≤j and, for each d∈D, either p∧d=0 or T(d,p∧d). Extend a valid p to a valid q when p≤q and every already occupied component is frozen:


```math
Dd\land (p\land d)\ne0
\ \longrightarrow\ q\land d=p\land d
\tag{21}
```


Put invalid masks below all valid masks, as in (7). This is a preorder on t, with 0 valid.

For an admitted chain of valid masks, take its actual join u. If u∧d>0, some chain member p has p∧d>0. Comparability and freezing imply that every chain member's d-component is either 0 or p∧d. Fixed-meet preservation of the join gives u∧d=p∧d. Thus u remains valid and extends every chain member. This argument does not require T to be persistent or crisp.

By Zorn, choose a maximal valid b. If b misses d∈D, adjoin one available witness r≤d. Disjointness leaves every other D-component unchanged, and gives a valid strict extension. Therefore b occupies every D-member, proving (20).

## 7 The two canonical-chain facts used in the final argument

The full proofs of both chain facts are included in [Canonical-chain lemmas](propositional-canonical-chain-lemmas.md).

**Current graph chain.** In [0,a], an admitted current total single-valued deflationary graph has, under BC_t, a current reverse-wellordered canonical chain M ending at a fixed point. Its conformity equation is


```math
x=\inf_{[0,a]}\{f(y):My\text{ and }x<y\}
\tag{22}
```


Function notation here abbreviates the graph's unique current output. The graph need not be represented by an operation. The empty predecessor family has interval-infimum a.

The usual proof compares two canonical chains by their common initial segment; first points beyond it would be bounds of the same predecessor image and hence equal. The represented union of canonical chains is again canonical and fully wellordered. BC_t gives its interval-infimum. Adjoining this bound, and then its graph successor if different, forces a terminal fixed point. These are current bound arguments.

**Strong crisp operation chain.** Under C5, an admitted operation g that is necessarily deflationary on [0,a] has a crisp canonical chain N, necessarily fully reverse-wellordered against all admitted subpredicates, ending at a fixed point. Its conformity has the same form as (22). This fact uses no current BC premise: the construction uses crisp-indexed material bounds, available under C5. The necessity and full wellordering are essential; a chain wellordered only against crisp subpredicates would be insufficient.

These facts do not necessitate BC_t, Zorn_t, or any current graph-selection assertion. Their distinct modal scopes are preserved in the final argument.

## 8 Reconstructing the true descent and obtaining the contradiction

Assume Actuality fails. Section 2 gives an all-true chain with meet 0; §§3–4 give an all-true reverse-wellordered chain with meet 0; §5 gives a true a and a crisp proper-partition relation Child on every positive proposition below a.

On [0,a] define the current functional graph


```math
G(p,r):=(\neg p\land r=p)
\ \lor\ (p\land\mathrm{Child}(p,r)\land r)
\tag{23}
```


A false p is fixed. A true p has exactly one true child, which is strictly below it. Apply the current graph-chain fact to obtain M with terminal fixed point m. The terminal m is false, every earlier M-member is true, and for a true M-member p its graph successor G(p) is its next, true member. If q<p are M-members, conformity gives q≤G(p).

Let Δ be the admitted family of children discarded at the true stages:


```math
\Delta(d):=\exists p,r\,[Mp\land p\land G(p,r)
\land\mathrm{Child}(p,d)\land d\ne r]
\tag{24}
```


These are positive false propositions, pairwise disjoint even across stages. At one stage this is the partition property. At a later stage q<p, every child of q lies below q≤G(p), whereas every child discarded at p is disjoint from G(p). Every true stage has at least one discarded child, because its selected child is proper and the whole partition joins to the parent.

Apply §6 to D=Δ and T(d,r)=Child(d,r). This yields b with


```math
\mathrm{Child}(d,b\land d),
\qquad 0<(b\land d)<d
\qquad(d\in\Delta)
\tag{25}
```


Define crisp tests


```math
\begin{aligned}
\mathrm{Mixed}(x)&:=(x\land b>0)\land(x\land\neg b>0),\\
H(c)&:=\exists e\,[\mathrm{Child}(c,e)\land\mathrm{Mixed}(e)]
\end{aligned}
\tag{26}
```


Every discarded d fails H. Its children are either the chosen child b∧d or disjoint from that child. In the first case they lie below b; in the second they are disjoint from b, since they lie below d. None is mixed.

Every true M-member c satisfies H: it has a discarded child d, and (25) makes that child mixed. Consequently, at a true M-member p, exactly one child satisfies H, namely the true successor G(p). All other children are discarded and fail H.

Define the admitted operation


```math
g(p):=p\land\exists c\,[\mathrm{Child}(p,c)\land H(c)\land c]
\tag{27}
```


It is globally deflationary. These Boolean-order identities give the necessary interval and progress hypotheses under C5. At every true M-member p, crisp indexing in (27) selects exactly the entity G(p), so


```math
g(p)=G(p)
\tag{28}
```


This is an entity identity, not merely agreement in current truth. No global strictness of g is claimed.

Let N be the strong crisp canonical g-chain. Compare M and N by their common initial segment. If the false terminal m of M has not yet been reached, their operations agree at every common predecessor by (28). If both chains had first points outside the common segment, conformity would make those points the infimum of the same current predecessor image, forcing equality. Thus one chain is an initial segment of the other. Full wellordering against arbitrary current subpredicates justifies this comparison even though M need not be crisp.

N cannot be a proper initial segment of M: its fixed endpoint u would then be a true M-member and satisfy g(u)=G(u)<u, contradicting fixedness. Hence M, including m, is an initial segment of N.

The predicate


```math
P_m(p):=Np\land m<p
\tag{29}
```


is crisp. Its current members are exactly the strict predecessors of m in M. All are true, and all their g-values are true by (28). Therefore


```math
a\land\forall p\,[P_m(p)\to g(p)]
\tag{30}
```


is true. By crisp indexing, (30) is the actual interval-infimum of those g-values. Conformity of N at m identifies that infimum with m. This makes m true, contradicting its construction. Actuality follows, proving (1).

## 9 Consequences, exact scope, and sources

The established C5+Actuality implication to full Boolean Completeness gives the useful equivalence


```math
\boxed{\text{over }C5+Zorn_t:\qquad
BC_t\ \longleftrightarrow\ \mathrm{Actuality}
\ \longleftrightarrow\ \text{full Boolean Completeness}}
\tag{31}
```


The reverse implication uses [the recorded completeness theorem](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/results/c5-and-actuality-imply-completeness.yaml), sourced there to Bacon and Dorr, *Classicism*, Proposition 2.5, pp. 25, 29–30. Full Boolean Completeness includes BC_t.

The new proof applies Zorn only to three preorders on propositions: the reverse truth order, annulus histories coded by one proposition, and partial masks on disjoint pieces. It uses current BC_t for their bounds and for the current relational canonical chain. C5 is used for endpoint identity and order tests, crisp range bounds, and the strong crisp canonical-chain theorem. No optional premise is necessitated.

The conclusion is Actuality. The argument does not derive a uniform splitting operation, global LocalSplit, Atomicity_t, or necessary BC_t from the displayed premises. It resolves the joint current-premise question directly.

Sources and proof dependencies:

- `misc`, this proof, §§2–6 and §8, unpaginated: annulus histories, functional-graph normalization, disjoint-family masks and their combination.
- [Canonical-chain lemmas](propositional-canonical-chain-lemmas.md): full proofs of the current relational and strong crisp chain constructions used in §7. The partition-and-reconstruction argument also occurs in OpenAI Codex, *Relational Choice and propositional completeness imply Actuality over C5*, 25 October 2026, §§2–7, unpaginated; §§5–8 here give the argument with both choice applications replaced by Zorn.
- [The Zorn schema](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/principles/zorn-r.yaml), [Boolean Completeness (type t)](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/principles/boolean-completeness-t.yaml), and [Actuality](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/principles/actuality.yaml) fix the premises and conclusion.

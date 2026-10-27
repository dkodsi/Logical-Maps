# Zorn and completeness of proposition properties imply Actuality

OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026. Source: `misc`, this proof, unpaginated.

**Over bare C, Boolean Completeness at the single type tt, together with Zorn at type t, implies Actuality.** Both premises are current and unboxed. Here tt is the type of properties of propositions; it is a stronger completeness assumption than completeness of propositions alone.

Zorn first supplies a wellordered descending chain of truths whose meet would be zero if Actuality failed. Taking the differences at its stages produces an admitted disjoint family of false propositions with join Top. Completeness at tt rules out exactly that configuration: joining the properties that identify those false propositions forces a true member. The proof does not require C5 or a choice operation selecting the stage differences.

## 1 Statement and admission conventions

In the fixed finitary relational language,

```math
\boxed{C+BC_{tt}+Zorn_t\ \Longrightarrow\ \mathrm{Actuality}}
\tag{1}
```

Write 0 and 1 for Bottom and Top, and use the algebraic Boolean order
$`p\le q\iff p\land q=p`$. A positive proposition is a nonzero proposition, whether or not it is currently true. Every family below is the current extension of an admitted predicate. An actual join or meet is defined by its algebraic universal property against all current bounds; it is not identified with a material existential or universal quantifier.

For example, put

```math
\begin{aligned}
\mathrm{GLB}(u,X):={}&
\forall x(Xx\to u\le x)\\
&\land\forall v\bigl(\forall x(Xx\to v\le x)\to v\le u\bigr)
\end{aligned}
\tag{2}
```

This is an admitted formula. BC_t gives a unique current u satisfying it for each X. Whenever several such values are needed, the proof binds them existentially using (2). It never extracts an operation taking X to its actual meet.

Zorn_t applies to admitted preorders on propositions. A chain is an admitted predicate on which the preorder is antisymmetric and total. Definitions of the preorder may quantify over higher types; its carrier remains t.

Two elementary Boolean facts will be used. A fixed meet preserves every existing actual join, by the adjunction
$`a\land x\le b\iff x\le\neg a\lor b`$.
Consequently a positive proposition below an actual join meets one of its members: otherwise its complement would bound the family. Neither fact uses a modal distinctness principle.

## 2 Completeness at tt supplies propositional completeness

For each proposition p let $`\kappa(p):=\lambda z^t.p`$, a constant property. Given X:tt, form the admitted family of properties

```math
\mathcal C_X(Y):=\exists p\,[Xp\land Y=\kappa(p)]
\tag{3}
```

By BC_tt, let J be its actual join and put j:=J(1). If Xp, then $`\kappa(p)\le J`$, so p≤j. If q bounds X, the corresponding constant property κ(q) bounds every member of (3). Thus J≤κ(q), whence j≤q. Here constant abstraction and evaluation preserve Boolean order by the unconditional Boolean identities of C; no collection of merely pointwise equalities is used. This proves that j is the actual join of X. Boolean duality gives actual meets, including the empty meet 1. Therefore

```math
C+BC_{tt}\ \Longrightarrow\ BC_t
\tag{4}
```

The same distinction is important for evaluating a nonconstant join. At a proposition x, evaluation has the admitted right adjoint

```math
r_x(b):=\lambda z\,((z=x)\to b),
\qquad X(x)\le b\ \Longleftrightarrow\ X\le r_x(b)
\tag{5}
```

The adjunction follows from the necessary universal closure of the unconditional H equivalence
$`\forall z[Xz\to((z=x)\to b)]\leftrightarrow(Xx\to b)`$,
using C's Logical Equivalence. Thus evaluation preserves every represented actual join that exists at tt. This is an algebraic adjunction, not an assumption of Functionality or Barcan.

## 3 Failure of Actuality gives a wellordered true chain

We prove the needed refinement using only C+BC_t+Zorn_t.

First order true propositions by reverse Boolean inclusion, with all false propositions in a bottom equivalence class. An admitted formula for this preorder is

```math
R(p,q):=\neg p\lor(q\land q\le p)
\tag{6}
```

If Actuality fails, no true proposition is an atom. Given true p and 0<b<p, one of b and p∧¬b is true and is a proper part of p. Hence (6) has no maximal element. By the contrapositive of Zorn_t, it has an admitted chain with no upper bound. Its true part D is nonempty and is a Boolean chain with no true lower bound.

Let u be the actual infimum of D. It is false. The admitted image of D under $`d\mapsto d\land\neg u`$ is a chain of true positive propositions with infimum 0: a lower bound is below every d and below ¬u, hence below u∧¬u. Replace D by this image.

We next refine D to an admitted chain L that is wellordered from larger to smaller elements and is coinitial in D. This refinement is needed because D itself need not be wellordered.

A D-annulus is a positive proposition $`b=d\land\neg c`$, where c,d∈D and c<d. Its endpoints are unique. Indeed, if $`d\setminus c=d'\setminus c'\ne0`$ and c<c′, then either d≤c′, making the common band both contained in and disjoint from c′, or c<c′<d, making the positive difference c′\c belong to only the first band. Thus c=c′, and then d=d′. Endpoint notation below abbreviates this unique admitted graph, not an endpoint operation.

For each proposition m define H_m to be its maximal D-annuli:

```math
\begin{aligned}
H_m(b):={}&\mathrm{Ann}_D(b)\land b\le m\\
&\land\forall b'\bigl(
\mathrm{Ann}_D(b')\land b'\le m\land b\le b'
\to b=b'\bigr)
\end{aligned}
\tag{7}
```

Distinct H_m-bands are disjoint and have a positive gap: overlapping or touching annuli would have a larger annular union still below m. Order the bands from outside to inside. If b=d\c and b′=d′\c′, b precedes b′ when d′<c; their gap is c\d′.

A proposition m is a valid history when it is the actual join of H_m and this order wellorders H_m against every admitted current subpredicate. The empty history 0 is valid. Order valid histories by end-extension of their band families, and put all invalid propositions in a bottom equivalence class. This defines an admitted preorder on t. End-extension is antisymmetric on valid histories because their band families determine their actual joins.

The following limit fact ensures that a join does not erase the history. Suppose Y is an admitted wellordered family of D-annuli with positive gaps, and v is its actual join. Every D-annulus a≤v lies in one Y-band. To prove this, a meets some band. If it meets two, take the least met band b and its immediate Y-successor s. Both exist by full current wellordering. The endpoints of a span the positive gap between b and s, even if a meets only a later band after s. That gap is disjoint from every Y-band and hence from v, a contradiction. If a meets only b but exceeds b, its positive excess is below v and must meet another band, again a contradiction. It follows that the maximal D-annuli below v are exactly the Y-bands.

Now take an admitted chain X of history codes. Let v be the actual join of its valid members and let

```math
Y(b):=\exists m\,[Xm\land\mathrm{Valid}(m)\land H_m(b)]
\tag{8}
```

The constituent histories are end-extended initial segments. Y is wellordered: for an admitted nonempty subfamily Z, select a Z-member in one constituent H_m and take the least member of Z∩H_m. Every Z-member outside H_m follows it. The proposition v is also the actual join of Y, because bounding all bands is equivalent to bounding all constituent codes. The limit fact gives H_v=Y as current extensions. Thus v is a valid upper bound of X; if X has no valid member, 0 is an upper bound.

Zorn_t therefore gives a maximal valid history m. It meets every d∈D. Otherwise m∧d=0; since D is positive with infimum 0, choose c<e<d in D. Every old band's lower endpoint is at least d, since a band whose lower endpoint lay below d would meet d. Appending e\c therefore leaves a permanent positive gap after all old bands. Its join with m is a valid strict end-extension by the limit fact, contradicting maximality.

Let L be the admitted image of the lower endpoints of H_m. They strictly decrease along the history, so L is wellordered by reverse Boolean inclusion. Full wellordering transfers through the unique endpoint graph: every admitted subpredicate of L pulls back to an admitted subpredicate of H_m. For each d∈D, the positive m∧d meets a band, whose lower endpoint lies strictly below d. Thus L is coinitial in D and has actual infimum 0. Every member is still true. We have proved

```math
\begin{gathered}
C+BC_t+Zorn_t+\neg\mathrm{Actuality}\quad\Longrightarrow\\
\text{an admitted reverse-wellordered all-true chain L with actual infimum 0.}
\end{gathered}
\tag{9}
```

No assertion in this construction makes D or L a rigid predicate.

## 4 Stage differences give a false antichain with join Top

Fix L as in (9). Its strict predecessors of l, in the wellordering, are the L-members e with l<e. Define the admitted relation

```math
U(l,u):=Ll\land
\mathrm{GLB}\bigl(u,\lambda e(Le\land l<e)\bigr)
\tag{10}
```

For each current l∈L, BC_t supplies exactly one current u with U(l,u). Write u_l for this value within the proof. The notation does not name an admitted operation. Since l is a lower bound of its strict predecessors, l≤u_l. Define

```math
\Delta(d):=d\ne0\land
\exists l,u\,[U(l,u)\land d=(u\land\neg l)]
\tag{11}
```

Every member of Δ is false: it is below the complement of a true l. The members are pairwise disjoint. If l>m in L, then l is a predecessor of m, so u_m≤l. Hence the increment at m lies below l, while the increment at l is disjoint from l. Distinct witnesses with the same l give the same increment by uniqueness in (10).

The actual join of Δ is 1. It suffices to show that any upper bound k equals 1. Suppose some l∈L satisfies ¬l≰k. The admitted subpredicate $`Ll\land(\neg l\nleq k)`$ has a first member l. For every predecessor e of l, ¬e≤k, so ¬k≤e. Therefore ¬k≤u_l, or ¬u_l≤k. Also u_l∧¬l≤k: the difference is either zero or a member of Δ. Since l≤u_l,

```math
\neg l=\neg u_l\lor(u_l\land\neg l)\le k,
\tag{12}
```

contradicting the choice of l. Thus ¬l≤k for all l∈L. Then ¬k is a lower bound of L, and its infimum 0 gives ¬k=0. This proves

```math
C+BC_t+Zorn_t+\neg\mathrm{Actuality}
\ \Longrightarrow\
\text{an admitted false antichain with actual join 1.}
\tag{13}
```

This is a least-counterexample argument inside the admitted wellorder. It does not assume a transfinite recursion theorem, a selector for the meets u_l, or identity of coextensive predicates.

## 5 Completeness at tt reflects truth of disjoint joins

We reproduce the bare-C reflection argument to make clear where BC_tt enters beyond (4).

Let Δ be any admitted false antichain with a true actual join j. Put $`H_a:=\lambda z(z=a)`$, and use BC_tt to form the actual join J of the admitted family
$`\lambda Y\exists a(\Delta a\land Y=H_a)`$.
For each current a∈Δ, H_a≤J and J(a)=1. By the evaluation adjunction (5), J(x) is the actual join of the H_a(x) at current Δ-members.

Put $`C(x,y):=(x=y\lor x\land y=0)`$. For current a,b∈Δ, either a=b or a∧b=0. Each true alternative is a positive identity and therefore necessary by C's Necessity of Identity. Necessary substitution yields

```math
H_a(x)\land H_b(y)\le C(x,y)
\tag{14}
```

For fixed a, use Boolean implication adjunction and the join property of J(y) to replace H_b(y) by J(y). Then use the same adjunction and the join property of J(x). The result is

```math
J(x)\land J(y)\le C(x,y)
\tag{15}
```

Define the admitted proposition $`v:=\forall p(Jp\to\neg p)`$.
For every a∈Δ, necessary universal instantiation and J(a)=1 give v≤¬a. Consequently j≤¬v. Since j is true, v is false. Classical quantifier duality supplies a current q such that Jq and q are both true.

For every a∈Δ, q≠a because q is true and a is false. Applying (15) to q,a, with both J-values true, gives q∧a=0. Hence j≤¬q, contradicting the truth of both j and q. Thus an admitted false antichain cannot have a true actual join under C+BC_tt.

Applying this to (13), and using (4), proves (1).

## 6 Exact scope

The new refinement (13) uses only current BC_t and Zorn_t over C. The additional completeness at tt is used to join haecceities and reflect truth of the resulting disjoint join. The proof therefore does not settle whether C+BC_t+Zorn_t alone implies Actuality.

Every invocation of Zorn has carrier t. Higher types occur only in admitted definitions and in the explicitly assumed BC_tt. All bounds are actual bounds; no optional premise is necessitated. In particular, the theorem asserts current Actuality, not necessary Actuality. The C5 result with BC_t alone remains the distinct theorem in [Zorn and propositional completeness imply Actuality](c5-zorn-and-propositional-completeness-imply-actuality.md).

## 7 Sources

- The new stage-difference refinement and theorem (1): OpenAI Codex, 25 October 2026, `misc`, §§1–6 of this note, unpaginated.
- The bare-C chain extraction and annulus-history refinement: [Zorn and propositional completeness imply Actuality](c5-zorn-and-propositional-completeness-imply-actuality.md), §§2–4, OpenAI Codex, 25 October 2026, `misc`, unpaginated; restated with proof in §3 above.
- Evaluation's right adjoint, BC_tt⇒BC_t, and higher-type disjoint-join reflection: [Relational Choice and Boolean Completeness imply Actuality](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/writeups/relational-choice-and-boolean-completeness-imply-actuality.md), §§1–2, OpenAI Codex, original proof 22 October 2026, recorded 23 October 2026, `misc`, unpaginated; restated in §§2 and 5 above. Its RC-based refinement is replaced here by (9)–(13).

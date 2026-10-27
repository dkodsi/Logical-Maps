# Numberhood rigidity characterizes Necessity of Distinctness

OpenAI Codex, 26 October 2026. Direct source: `misc`, numbered proof sections below, unpaginated.

**Over C, negative persistence of numberhood at the single type (et)t is equivalent to current modal 5 and to Necessity of Distinctness at every type.** Equivalently, the finite-cardinality predicate is endpoint-valued. With propositional Barcan, this condition gives C5; its boxed version is itself equivalent to C5.

This identifies a structural boundary for Maximalism. The condition is already incompatible with pure Max(C), without Boolean Completeness, observer separation, or Choice. It does not decide the consistency of Max(C) + BC_t, with or without BF or OS.

## 1 Exact statements and background facts

Work in the fixed relational language of C, and put

```math
\nu=(et)t,\qquad N=\mathrm{FiniteCardinality}_e,
\qquad \mathbf1=\mathrm{Suc}_e\mathbf0.
```

Consider the single closed sentence

```math
\mathrm{NN}:=\forall z^\nu\,(\neg Nz\to\Box\neg Nz),
\tag{1}
```

and endpoint-valuedness of that same predicate:

```math
\mathrm{EndN}:=\forall z^\nu\,(Nz=\top\ \lor\ Nz=\bot).
\tag{2}
```

Current modal 5 is forall p(Diamond p implies Box Diamond p), equivalently its dual forall p(Diamond Box p implies Box p). Current ND at a type sigma is forall x,y(x differs from y implies Box(x differs from y)). All-type ND is this schema; C5 is C plus its separately boxed instances.

The [finite-cardinality lemmas](../../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/pure-possibility-implies-axiom-of-infinity-t.md), §1, are theorems of C. We use:

- N(0) and N(1).
- Positive persistence: Nz implies Box Nz.
- Exclusivity: if Nu and Nv, then either u=v or Box forall X.not(uX and vX). In particular, finite cardinalities with a common current instance are identical.

For the empty property O := lambda x.Bottom and any admitted individual a, let S_a := lambda x.(x=a). Directly from the definitions, C gives the proposition identities

```math
\mathbf0(O)=\top,\quad\mathbf1(O)=\bot,
\qquad\mathbf0(S_a)=\bot,\quad\mathbf1(S_a)=\top.
\tag{3}
```

Existence supplies an individual a. The true equalities in (3) are unconditional C identities; no Extensionality premise is used.

## 2 A mixed cardinal tests whether a proposition is an endpoint

Define one admitted operation from propositions to cardinality objects:

```math
M(p):=\lambda X^{et}.\,
       (p\land\mathbf0(X))\lor(\neg p\land\mathbf1(X)).
\tag{4}
```

**Endpoint test.** C proves

```math
N(M(p))\quad\longleftrightarrow\quad
       (p=\top\ \lor\ p=\bot).
\tag{5}
```

For the forward direction, suppose N(M(p)). If p is currently true, then (3)–(4) give the exact identity M(p)(O)=p, so M(p) and 0 have the common instance O. Exclusivity gives M(p)=0. Applying both sides to O then gives p=Top.

If p is currently false, (3)–(4) give M(p)(S_a)=not p, so M(p) and 1 have the common instance S_a. Exclusivity gives M(p)=1. Applying both sides to O again, and using M(p)(O)=p, gives p=Bottom.

Conversely, p=Top identifies M(p) with 0 by substitution and the Boolean identities under lambda abstraction. Likewise p=Bottom identifies it with 1. Both are finite cardinalities. This proves (5). Current coextension has nowhere been promoted to identity: the forward direction obtains identity from finite-cardinality exclusivity, and the reverse direction uses the assumed endpoint identity.

## 3 The current equivalences

**Theorem.** Over C,

```math
\mathrm{NN}\quad\Longleftrightarrow\quad\mathrm{EndN}
\quad\Longleftrightarrow\quad 5
\quad\Longleftrightarrow\quad\mathrm{ND}_{\rm all}.
\tag{6}
```

Here equivalence with all-type ND means that the single sentence implies each ND instance, while ND at t alone suffices for the converse.

First, NN is equivalent to EndN. Positive persistence already identifies every currently true Nz with Top. Under NN, every currently false Nz satisfies Box not Nz and is therefore identical to Bottom. Conversely an endpoint output which is false is Bottom, and so its negation is necessary.

Next assume NN. Applying it to M(p), and using the necessitated C theorem (5), shows that a currently non-endpoint p remains a non-endpoint necessarily. Suppose now Diamond Box p. If p were currently a non-endpoint, its necessary non-endpointness would contradict the possible assertion Box p, which is p=Top. Hence p is currently an endpoint. It cannot be Bottom, since that identity necessarily excludes Box p. Therefore p=Top, or Box p. We have proved the dual form of current modal 5.

Modal 5 gives all-type ND. For arbitrary x,y of any fixed type, suppose Diamond(x=y). NI and the modal rules give Diamond Box(x=y). The dual form of 5 gives Box(x=y), and T gives x=y. Contraposition is the required ND instance. Only this arbitrary fixed type is quantified in the argument; there is no object-language quantification over types.

Finally assume ND at t and suppose not Nz. Then Nz differs from Top. ND_t makes this distinction necessary, that is, Box not Box Nz. Positive persistence is an unconditional C theorem, so its necessitated contrapositive carries this to Box not Nz. This is NN and completes the cycle.

## 4 Boxed conditions and propositional Barcan

All implications used in §3 are theorems of C. Necessitating them therefore gives

```math
C+\Box\mathrm{NN}\quad\Longleftrightarrow\quad C5.
\tag{7}
```

In the forward direction obtain every boxed ND instance separately. In the reverse direction the boxed type-t ND instance suffices. The same statement holds with EndN in place of NN.

There is also the current implication

```math
C+\mathrm{NN}+\mathrm{BF}_t\quad\Longrightarrow\quad C5.
\tag{8}
```

Indeed §3 gives ND_t. The recorded [ND_t plus BF_t theorem](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/nd-t-and-bf-t-imply-necessary-nd-t.yaml) gives boxed ND_t, and the recorded [boxed type-t to all-type theorem](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r.yaml) gives C5. Thus full logical observer separation, which supplies BF_t, also upgrades unboxed numberhood rigidity to C5. Without BF_t, §3 asserts current ND and 5; it does not silently box their universal closures.

## 5 Maximalism and the remaining consistency question

Pure Max(C) is [incompatible with ND](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/maximalist-distinctness-incompatible-with-nd.yaml). Equation (6) therefore makes it incompatible with NN and with EndN, already over C alone. In particular pure Max(C) entails

```math
\exists z^\nu\,(\neg Nz\land\Diamond Nz).
\tag{9}
```

This does not replace the stronger [Max plus Barcan theorem](logical-observers-and-numberhood.md), §1, whose new number can occur where Pi still holds. Equation (9) does not include Pi in the possible conjunction.

Consequently numberhood rigidity provides an exact upper boundary in the logical map, rather than a new inconsistency specifically caused by BC_t. The packages C + Max(C) + BC_t, with current BF or OS added, remain outside the verdict of this theorem. The reference theory in Max(C) remains C throughout.

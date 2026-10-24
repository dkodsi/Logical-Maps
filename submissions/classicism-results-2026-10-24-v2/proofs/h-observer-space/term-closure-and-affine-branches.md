# Term closure, implication, and affine observer branches over H

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: misc, this note, §§1–7, unpaginated. The base is H throughout.

## 1. Definitions and the abbreviation proviso

Use the separation formula S[R], endpoint truth conditions A(E):=E(Top) and Z(E):=¬E(Bottom), and whole-operation preservation from [the truth-profile note](truth-profiles-and-connective-reducts.md). All observers and terms are admitted in the fixed relational type system.

The results below are parametric in fixed operations having the indicated H truth tables. For the syntactic composition examples, choose these explicit expansions:

$$
p\mathbin{\to}q:=\neg p\lor q,\qquad
p\mathbin{\leftrightarrow}q:=(p\to q)\land(q\to p),\qquad
p\mathbin{\oplus}q:=\neg(p\leftrightarrow q).
$$

This is an explicit convention for this note, not a claim that the local ordinary-source files have verified these as the canonical abbreviation expansions. If a different expansion is used, the truth-profile algebraic conclusions still apply to that operation, but the syntactic preservation implications must use its actual expansion.

Write I, D and X for full preservation of the chosen implication, biconditional and XOR operations. For example,

$$
I(E):=(\lambda p,q.E(p\to q))=(\lambda p,q.Ep\to Eq).
$$

The symbol D is only a label for biconditional preservation; it is not a modal distinctness principle. FixTop and FixBottom mean the output identities E(Top)=Top and E(Bottom)=Bottom. The fixed Top and Bottom retain their original H definitions from the truth-profile note.

## 2. Strong preservation is closed under actual term composition

**Term-closure theorem.** Let a finite collection of actual propositional operations f be given. Suppose E satisfies each whole-operation identity

$$
(\lambda\bar p.E(f(\bar p)))
 =(\lambda\bar p.f(Ep_1,\ldots,Ep_n)).
$$

Then E satisfies the corresponding whole-operation identity for every finite term built from these operations and projections. A constant c may also occur if E(c)=c is assumed. Parameters not fixed by E must instead be displayed among the inputs and transformed by E.

The proof is structural. A projection gives the same term on both sides. For f(t₁,…,tₙ), substitute the composite argument maps into the given whole-operation equality for f, then substitute the induction equalities for the whole maps tᵢ into the resulting term. Each substitution is equality congruence in an admitted lambda context. This proves an equality between the complete operations directly; it does not infer function identity from a universally quantified pointwise identity.

Consequently, adding an actually term-defined preservation clause to its generating qualifications does not change the observer class or its separation principle. With the expansions in §1, this gives

$$
N\land V\Longrightarrow I,\qquad
M\land I\Longrightarrow D,\qquad
N\land D\Longrightarrow X.
$$

The same theorem allows variable repetition, permutation and identification. It also explains the parameter rule: I yields full transport of p→r as a binary operation, but its unary specialization at a fixed r commutes with E only when E(r)=r. Without that condition the valid transport is E(p→r)=Ep→Er.

A truth-table definition is insufficient for this theorem. If a new primitive g merely agrees materially with a term t, or if separation proves only ∀p̄(g(p̄)=t(p̄)), no whole-operation bridge g=t has yet been proved over H. The theorem applies when g is the actual displayed term, or a whole-operation identity identifying g with that term is separately available.

## 3. Implication separation gives Boolean upper intervals

Assume S[I]. Its truth profiles are injective and satisfy

$$
J(p\to q)=(K\setminus J(p))\cup J(q).
$$

Choose any proposition a and put

$$
1_*:=a\to a,\qquad
p\vee_*q:=(p\to q)\to q.
$$

Separation makes 1* independent of a and makes ∨* a join-semilattice operation with greatest 1*. More precisely, for the observer order,

$$
p\preceq q\ \leftrightarrow\ p\to q=1_*,
\qquad J(p\vee_*q)=J(p)\cup J(q).
$$

Every I-observer fixes 1* as an object: E(a→a)=Ea→Ea=1*. It preserves ∨* as a whole operation by term closure.

For each r, the admitted interval [r,1*] is a Boolean algebra with its inherited join and with

$$
\neg_r p:=p\to r,
\qquad
p\wedge_r q:=(p\to(q\to r))\to r.
$$

For p,q≥r, their profiles are respectively the complement of J(p) relative to the interval [J(r),K], and J(p)∩J(q). Indeed the latter displayed term has profile (J(p)∩J(q))∪J(r), which reduces to the intersection on this interval. Injectivity supplies all the Boolean equations and their order properties. These are interval operations; no global bottom or global meet is asserted by S[I] alone.

The whole binary operation ∧r transports its parameter to Er. Every I-observer maps [r,1*] into [Er,1*] and preserves the displayed interval operations with that change of parameter. Fixing r yields full preservation of their unary or binary specializations at r.

### Exact top alignment and bottom completion

Over H there are exact equivalences

$$
S[A\land I] \leftrightarrow\ S[\mathrm{FixTop}\land I]
\ \leftrightarrow\ S[I]+(\mathrm{Top}=1_*).
$$

For the forward alignment, every eligible observer accepts both Top and 1*, so separation identifies them. Conversely the alignment, together with the automatic fixing of 1*, makes every I-observer fix Top. Thus in this branch acceptance and fixing are equivalent at the level of separation, without a general H equivalence between those predicates.

There is also the exact truth-level bottom completion

$$
S[Z\land I]
\ \leftrightarrow\ S[I]+\forall p(\mathrm{Bottom}\to p=1_*).
$$

The extra equation says Bottom is least in the derived order. Forward it follows by profiles. Conversely, if an I-observer accepts Bottom, applying it to Bottom→p=1* forces it to accept every p. Such a constant truth profile distinguishes no pair and can be discarded. Therefore the rejecting I-observers still separate.

Under either side, the interval construction at r=Bottom is a Boolean algebra on the whole proposition domain, with bottom Bottom and top 1*. For **full preservation** of its derived negation and meet by the same observers, the direct sufficient qualification is I∧FixBottom. Term closure then gives

$$
\neg_*p:=p\to\mathrm{Bottom},\quad
p\wedge_*q:=(p\to(q\to\mathrm{Bottom}))\to\mathrm{Bottom},\quad
p\vee_*q:=(p\to q)\to q.
$$

All three are preserved as whole operations, and both derived endpoints are fixed. This is a full Boolean observer signature for the displayed derived operations. It does not identify them with the original primitive negation, conjunction and disjunction, and 1* need not be the original Top unless top alignment is included. Mere bottom rejection was enough for the output algebra, but does not itself provide the parameter-fixing step in this full-preservation construction.

## 4. Biconditional and XOR give Boolean groups

Assume S[D] and put 1*:=a↔a. The profile law is

$$
J(p\leftrightarrow q)=K\setminus(J(p)\mathbin{\triangle}J(q)).
$$

It follows that ↔ is a commutative group operation, with identity 1*, and that every element is its own inverse:

$$
p\leftrightarrow1_*=p,\quad
p\leftrightarrow p=1_*,\quad
(p\leftrightarrow q)\leftrightarrow r
 =p\leftrightarrow(q\leftrightarrow r).
$$

This is an elementary abelian 2-group, also called a Boolean group. Here its identity is true. Every D-observer fixes 1*. Exactly as in §3,

$$
S[A\land D]\ \leftrightarrow\ S[\mathrm{FixTop}\land D]
\ \leftrightarrow\ S[D]+(\mathrm{Top}=1_*).
$$

Dually, S[X] gives an elementary abelian 2-group under ⊕ with false identity 0*:=a⊕a. Every X-observer fixes 0*, and

$$
S[Z\land X]\ \leftrightarrow\ S[\mathrm{FixBottom}\land X]
\ \leftrightarrow\ S[X]+(\mathrm{Bottom}=0_*).
$$

These groups need not be supplied with either original lattice operation. Their profile operation alone is not intersection or union. The ternary term (p↔q)↔r, or respectively (p⊕q)⊕r, gives a symmetric ternary group operation with

$$
h(p,q,q)=p,\qquad
h(h(p,q,r),s,t)=h(p,q,h(r,s,t)).
$$

It is strongly preserved by the corresponding observers. The two displayed ternary terms have the same truth table, but no identity between their complete operation objects is inferred merely from that fact.

If negation preservation is added to D, put d:=¬1*. Separation gives

$$
\neg p=p\leftrightarrow d.
$$

Thus original negation is, at the output level, translation by the distinguished nonidentity group element d. Both 1* and d are fixed by the qualified observers. The term λp.(p↔d) is strongly preserved. Its pointwise identity with original negation does not need to be upgraded to a whole-operation identity, since N was already part of the qualification. The XOR version is analogous: d:=¬0* and ¬p=p⊕d.

## 5. A group operation plus meet or join gives a ring branch

These combinations produce substantially more structure while still keeping fixed endpoints and primitive operations distinct.

### Biconditional with one lattice operation

Under S[D∧M], define

$$
p\vee_*q:=((p\land q)\leftrightarrow p)\leftrightarrow q.
$$

Its profile is union. Under S[D∧V], instead define

$$
p\wedge_*q:=((p\lor q)\leftrightarrow p)\leftrightarrow q,
$$

whose profile is intersection. Term closure gives full preservation of the derived operation in each case. Consequently each branch gives a distributive lattice with greatest 1*, and every upper interval is Boolean. A derived implication is

$$
p\to_*q:=(p\wedge_*q)\leftrightarrow p,
$$

where ∧* denotes the original meet in the first branch and the derived meet in the second. Its profile is ordinary implication, so the interval construction of §3 applies. This derived implication is fully preserved; no identity with the chosen original implication operation is claimed.

Equivalently, ↔ is addition and the resulting join is multiplication in a Boolean ring whose additive zero is 1*. The ring identities follow from the profile truth tables: addition is the group operation of §4, multiplication is associative and idempotent, and it distributes over addition. A multiplicative identity, which would be the lattice's least element, is not asserted without a further condition.

Adding Z makes the fixed Bottom that least element at the output level. Adding the stronger FixBottom also gives full preservation of the derived negation

$$
\neg_*p:=p\leftrightarrow\mathrm{Bottom}.
$$

The same observers then preserve a complete derived Boolean signature with endpoints Bottom and 1*. Again, fixing Top or adding A aligns 1* with the original Top.

### XOR with one lattice operation

Under S[X∧M], the derived join is

$$
p\vee_*q:=(p\land q)\oplus(p\oplus q).
$$

Under S[X∧V], the derived meet is

$$
p\wedge_*q:=(p\lor q)\oplus(p\oplus q).
$$

Both identities follow by their intersection/union profile calculations, and their preservation is full by term closure. Now ⊕ is addition and meet is multiplication in a Boolean ring with additive zero 0*. The corresponding distributive lattice has least 0*; a greatest element is not asserted without a further condition. Each lower interval is Boolean.

Adding A makes the fixed Top greatest at the output level. Adding FixTop also gives full preservation of

$$
\neg_*p:=p\oplus\mathrm{Top}.
$$

This completes a derived Boolean observer signature with endpoints 0* and Top. Adding Z or fixing Bottom aligns 0* with the original Bottom. These statements do not identify the derived missing lattice operation or derived negation with an unpreserved primitive.

## 6. What is exact and what remains a representation requirement

For each listed finite signature, the truth-profile argument proves exactly the equations and algebraic universal-Horn implications valid in its corresponding two-element reduct: soundness is coordinatewise evaluation, and the full two-valued H model gives the converse bound. In particular all the displayed group, interval, lattice and ring identities are genuine proposition identities over H.

The term-closure theorem supplies actual implications between strong qualifications whenever the new operation is an actual term in the qualified operations and fixed constants. These implications are stronger evidence than matching truth tables. Conversely, output algebra identities alone do not supply admitted strong characters, and they do not authorize replacing one operation object by another. No characterization of S[D] or S[X] solely by abstract Boolean-group axioms is asserted here.

The endpoint equivalences in §§3–4 are exact H equivalences of separation principles and their stated output alignments. The Boolean completions in §§3 and 5 distinguish the weaker hypothesis sufficient for the output algebra from the parameter-fixing hypothesis used to preserve the derived complement as a whole operation.

## 7. Source and scope

All arguments are new ordinary proofs in this note, attributed to misc, OpenAI Codex, 24 October 2026, §§1–6, unpaginated. They use [the truth-profile representation theorem](truth-profiles-and-connective-reducts.md), not C's Logical Equivalence or a truth-functional clone theorem about abstract Boolean functions. No Lean verification, database implication, choice principle or canonical-abbreviation identification is claimed.

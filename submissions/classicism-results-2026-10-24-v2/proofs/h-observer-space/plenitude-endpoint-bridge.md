# Propositional Plenitude turns logical separation into endpoint separation

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the assembled observer equivalences: `misc`, this note, §§1–4, unpaginated. The Plenitude, modal and completeness ingredients are recorded results of Bacon and Dorr, identified in §5.

Over H, full logical separation together with the single Plenitude instance from propositions to propositions is exactly endpoint-valued logical separation. Thus one familiar admission principle takes ordinary logical separation all the way to C5 + Atomicity_t. Neither separation nor Plenitude needs to be assumed necessary.

## 1. Statements and scope

Write OS and End for the full relational separation schemas using ordinary and endpoint-valued logical observers. Their qualifications are full composite identities at each finite external list of quantifier types, as in [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md). Endpoint-valued means that each admitted input has output identical to Top or Bottom; it does not mean that the observer preserves current truth.

The single admission premise is

$$
\mathrm{Plen}_{t,t}:=
\forall U^{ttt}\left[
\mathrm{Functional}(U)\to
\exists Z^{tt}\,\forall p^t\,U[p,Zp]\right],
\tag{1}
$$
where

$$
\mathrm{Functional}(U):=
\forall p\,\exists q\left[
U[p,q]\land\forall r\,(U[p,r]\to q=r)\right].
$$
Bracketed application is left-nested. Functional relations and representing operations are admitted objects of the language. Formula (1) does not quantify over arbitrary external functions, and it requires no individual-valued operation.

Let Plen_r be the full pre-existing Plenitude schema, BC_r the full Boolean Completeness schema, and Actuality the existence of a true proposition entailing every true proposition. C5 includes C and necessary distinctness at the stated types. The exact theory equivalences over H are

$$
\boxed{
\begin{aligned}
\mathrm{End}
&\longleftrightarrow \mathrm{OS}+\mathrm{Plen}_{t,t}\\
&\longleftrightarrow \mathrm{OS}+\mathrm{Plen}_{r}\\
&\longleftrightarrow \mathrm{C5}+\mathrm{OS}+\mathrm{Actuality}\\
&\longleftrightarrow \mathrm{C5}+\mathrm{OS}+\mathrm{BC}_{r}\\
&\longleftrightarrow \mathrm{C5}+\mathrm{Atomicity}_{t}.
\end{aligned}}
\tag{2}
$$
The full typed OS premise supplies C and BF over H. A single propositional separation formula is not substituted for that premise while leaving C implicit. Once C5 is explicit, the atomicity step itself needs only the propositional separation instance qualified at the list {t}.

## 2. What the single Plenitude instance supplies

Work first over C. The proofs of Propositions 2.13 and 2.15 use only Plen_t,t for the following two conclusions.

**Necessary distinctness at t.** Fix distinct propositions p and q. Apply Plen_t,t to the functional relation that sends p to Top and every other proposition to Bottom:

$$
U[x,y]:=(x=p\land y=\top)\lor(x\ne p\land y=\bot).
\tag{3}
$$
The resulting admitted Z satisfies Zp=Top and Zq=Bottom. NI makes these identities necessary, and the endpoints are necessarily distinct in C. Equality substitution then gives □(p≠q). Universal generalization yields ND_t. The optional premise p≠q was discharged, not necessitated.

**Actuality.** Apply Plen_t,t to the functional relation

$$
V[p,q]:=(p\land p=q)\lor(\neg p\land q=\top).
\tag{4}
$$
Let Z represent it and put a:=∀p Zp. Each Zp is true: if p is true, Zp=p; otherwise Zp=Top. Thus a is true. Universal instantiation as an unconditional C logical identity gives a≤Zp for every p. For true p, the identity Zp=p then gives a≤p. Therefore a witnesses Actuality.

The second disjunct in (4) is **q=Top**. This follows the intended construction and the database's explicit transcription note for Proposition 2.15; the source prose has a conflicting p=Top there.

Add BF_t. The recorded type-t instance of Proposition 2.4 gives

$$
\mathrm{ND}_{t}+\mathrm{BF}_{t}
\quad\Longrightarrow\quad\Box\mathrm{ND}_{t}.
\tag{5}
$$
This is a proved modal argument using NI, 4 and BF_t, not necessitation of the optional ND_t premise. The recorded boxed form of Proposition 2.2 then gives □ND at every required type. Consequently

$$
\mathrm{C}+\mathrm{BF}_{t}+\mathrm{Plen}_{t,t}
\quad\Longrightarrow\quad
\mathrm{C5}+\mathrm{Actuality}.
\tag{6}
$$
Conversely, the pre-existing C5+Actuality result gives BC_r, and C5+BC_r gives Plen_r. C5 also supplies every BF instance. Hence the admission bridge already has the exact strength

$$
\boxed{
\mathrm{C}+\mathrm{BF}_{t}+\mathrm{Plen}_{t,t}
\quad\longleftrightarrow\quad
\mathrm{C5}+\mathrm{Actuality}.}
\tag{7}
$$
The left side may equivalently use all BF instances. In particular, over C+BF_t, the single Plen_t,t instance is equivalent to full Plen_r. The type reduction in the forward direction is a mathematical specialization of the source proofs; the database engine does not instantiate schemas on its own.

## 3. Adding separation

Assume H+OS+Plen_t,t. Full logical separation recovers C and all BF instances. Equation (6) gives C5 and Actuality.

The established local atomic-observer theorem says that C5, Actuality and propositional logical separation qualified at {t} give Atomicity_t. Its construction first uses the true atom supplied by Actuality to obtain a truth-correct endpoint evaluator. Composing that evaluator with an ordinary distinguishing observer gives a distinguishing endpoint observer; the universal diagonal of such an observer produces an atom below each prescribed nonbottom proposition. OS contains the required separation instance. Thus Atomicity_t follows, and the established endpoint theorem gives End from C5+Atomicity_t.

For the reverse implication, End gives C5+Atomicity_t and ordinary OS. BF lifts propositional atomicity to atomicity at every relational type. The recorded C5+Atomicity theorem then gives necessary Plen_r, hence Plen_r and Plen_t,t. This proves the first two equivalences in (2), as well as the last.

Finally, over C5 the recorded equivalence Actuality↔BC_r and the preceding local atomic-observer theorem establish the middle two formulations. Every implication uses a finite collection of schema instances for each particular conclusion. No infinite conjunction of types or implicit boxed OS premise is introduced.

## 4. Position in the map

Plen_t,t already supplies the two-output normalizations in [Plenitude material normalization](plenitude-material-normalization.md), and the partial-signature involutions in [Reversible partial normalization](partial-reversible-normalization.md). Equation (2) identifies what this same admission condition does at the complete logical signature: it forces the endpoint region, not merely a preservation-tier collapse.

The complementary theorem [Necessary separation and one atom](necessary-separation-and-atoms.md) reaches End from C5, necessary ordinary separation and one possibly false atom. Here current Plen_t,t supplies a true atom through Actuality and, with BF_t, supplies C5 itself. That is why current OS suffices in (2).

This does not identify the two-output observers constructed over bare H with endpoint-valued observers. That identification belongs to the stronger complete-logical region reached in (2).

## 5. Sources

The exact observer equivalences and the single-instance synthesis in §§1–4 are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026, direct source `misc`, this note, unpaginated. The substantive source ingredients are:

- Bacon and Dorr, *Classicism*, draft of 16 May 2023, Proposition 2.13, p. 32: [Plenitude implies ND](../../source/topics/classicism/results/plenitude-r-implies-distinctness-necessary-r.yaml). Its type-t proof uses only Plen_t,t.
- The same source, Proposition 2.15, pp. 32–33: [Plenitude implies Actuality](../../source/topics/classicism/results/plenitude-r-implies-actuality.yaml), also using only Plen_t,t, with the relation transcription caveat retained above.
- Proposition 2.4, p. 23: [ND_t and BF_t imply necessary ND_t](../../source/topics/classicism/results/nd-t-and-bf-t-imply-necessary-nd-t.yaml); Proposition 2.2, p. 22: [necessary ND_t implies necessary ND at all types](../../source/topics/classicism/results/necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r.yaml).
- Proposition 2.5, pp. 25, 29–30, via Propositions 2.10 and 2.8: [C5 and Actuality imply completeness](../../source/topics/classicism/results/c5-and-actuality-imply-completeness.yaml). Proposition 2.14, pp. 32–33 and n. 48: [C5 and completeness imply Plenitude](../../source/topics/classicism/results/c5-and-completeness-imply-plenitude.yaml).
- The closing equivalences of §2.3, p. 33: [C5 and Atomicity imply necessary Plenitude](../../source/topics/classicism/results/c5-and-atomicity-imply-necessary-plenitude.yaml), using [Atomicity_t and BF imply Atomicity](../../source/topics/classicism/results/atomicity-t-and-bf-imply-atomicity.yaml).
- The local observer argument is spelled out in [Necessary separation and atoms](necessary-separation-and-atoms.md), §2, with its direct proof source linked there. The full H endpoint characterization is [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md), §§3–6.

The proved-only database engine confirms the all-type chains C5+Actuality⇒BC_r⇒Plen_r and C5+Atomicity_t⇒necessary Plen_r. The specialization to the single Plen_t,t premise and the H observer bridge are established by the arguments above.

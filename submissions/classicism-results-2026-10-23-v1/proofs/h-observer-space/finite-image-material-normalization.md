# Finite-image material observers normalize to two-output pointwise observers

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–6, unpaginated. These are new ordinary arguments, not database records or Lean certificates. The base is H, with no C, NI, BF, Choice or Functionality assumption unless explicitly stated.

This result concerns internal finiteness of an individual observer's image. The proposition domain itself may be infinite, and the truth filter need not have a least member. It extends [Finite semilattice normalization](finite-semilattice-normalization.md).

## 1. Exact comparison

For an admitted E:tt define its admitted image predicate by

$$
\operatorname{Im}(E)(y):=\exists p\,[Ep=y],
$$
$$
\operatorname{FinIm}(E):=
\exists Z\,[\operatorname{FiniteCardinality}_t(Z)\land Z(\operatorname{Im}(E))].
$$
FiniteCardinality is the internal Frege induction predicate from the [background](../../source/topics/classicism/background.md), also displayed in [Finite semilattice normalization](finite-semilattice-normalization.md), §2. No standard finite bound or external enumeration is implicit in FinIm.

Write

$$
\operatorname{Two}(E):=\exists b,c\,\forall p\,[Ep=b\lor Ep=c].
$$
This is an at-most-two-output condition. Its two witnesses need not be the fixed Top and Bottom. Let O be any of no condition, A, Z or A∧Z, where A(E):=ETop and Z(E):=¬EBottom. Then over H,

$$
\boxed{
\operatorname{Sep}_t[O\land\operatorname{FinIm}\land M_{\rm mat}]
\ \leftrightarrow\
\operatorname{Sep}_t[O\land\operatorname{Two}\land M_{\rm pt}].}
\tag{1}
$$
The same result holds with V in place of M. Both equivalences hold at full typed scope, where the pointwise qualification can also be replaced by its whole-operation version.

The proposition domain is not assumed internally finite. In particular (1) is not obtained by first applying the preceding note's global finiteness theorem.

## 2. Folding an internally finite indexed family

Assume conjunction is a meet semilattice. Let U,C,f be admitted predicates or operations of type tt, suppose Fin_t(U), and suppose

$$
\forall x\,[Cx\to fx],\qquad\exists x\,[Ux\land Cx].
\tag{2}
$$
Then there is a true proposition u such that

$$
\forall x\,[(Ux\land Cx)\to u\land fx=u].
\tag{3}
$$
Here U indexes the finite family, C selects its relevant indices, and f supplies its true values. Neither the selected subset nor f's image has to be proved internally finite separately.

To prove this, use Frege induction with the admitted property

$$
W(Z):=\forall V\left[ZV\to
\left((\exists x\,[Vx\land Cx])\to
\exists u\left[u\land
\forall x((Vx\land Cx)\to u\land fx=u)\right]\right)\right].
\tag{4}
$$
Zero is vacuous. At a successor, choose its witness y and use the exact deletion predicate V⁻:=λx.Vx∧x≠y. If V⁻∩C is empty, nonemptiness of V∩C gives Cy, and fy is a true lower bound of all selected values. If V⁻∩C is nonempty, obtain a true lower bound b by the induction hypothesis. Use b when Cy is false, and b∧fy when Cy is true. The semilattice equations verify the bound, and its truth follows from (2). Thus W is successor-closed, and the witness to Fin_t(U) gives (3).

This is the same exact-deletion proof as the finite-closure lemma, now folding an indexed family. Only single existential witnesses are used; no function choosing witnesses or finite enumeration is required. The predicate W is an explicit admitted comprehension term.

Dually, in a join semilattice, if every selected fx is false and there is a selected index, the same induction gives a false v with fx∨v=v for every selected x. Replace b∧fy by b∨fy. This is a finite upper bound in the false ideal.

## 3. Meet normalization of an arbitrary finite-image observer

Assume the conjunction semilattice equations and FinIm(E). First suppose E has both a true and a false output. Apply §2 to U:=Im(E), C(x):=x and f(x):=x. This gives a true u below every true output of E:

$$
Ep\ \Longrightarrow\ u\land Ep=u.
\tag{5}
$$
Apply §2 a second time to the same internally finite U, now with

$$
C(x):=\neg x,\qquad f(x):=\neg(u\land x).
$$
For every selected x, u∧x is false, so f(x) is true. There is a selected index because E has a false output. Obtain a true v satisfying

$$
\neg Ep\ \Longrightarrow\ v\land\neg(u\land Ep)=v.
\tag{6}
$$
Define the admitted terms

$$
d:=v\land\neg u,
\qquad h(p):=v\land\neg(u\land Ep),
$$
$$
F(p):=\neg h(p)\land\neg d.
\tag{7}
$$
Since v,u are true, d is false. If Ep is true, (5) gives h(p)=d, hence F(p)=¬d by idempotence. If Ep is false, (6) gives h(p)=v, hence F(p)=¬v∧¬d. Thus F has exactly E's truth profile, and its output pair is

$$
t:=\neg d\quad\text{(true)},\qquad
b:=\neg v\land\neg d\quad\text{(false)}.
\tag{8}
$$
This pair is a meet chain: b≤t, and their meet table is the ordinary two-valued conjunction table. Consequently, **if E is materially meet-preserving, F is pointwise meet-preserving**. Indeed material preservation determines which of b,t is F(p∧q), and the same two truth values determine Fp∧Fq by that meet table.

If E has only true outputs or only false outputs, use a constant true or constant false observer respectively. Its truth profile is E's, it has at most one output, and semilattice idempotence makes it pointwise meet-preserving. This also handles those cases without selecting a nonempty subfamily in either fold.

The construction proves more than separation: every admitted finite-image observer has a truth-equivalent admitted observer whose two outputs form a meet chain. Material M on the original observer is the only further premise needed for pointwise M on the replacement. A and Z are retained automatically because the entire truth profile is retained. No endpoint-fixing identity is asserted.

## 4. Join normalization

Assume the disjunction semilattice equations and FinIm(E), again first with both true and false outputs. The dual of §2 gives a false v above every false output of E. Apply that dual fold a second time to the true outputs y, with the false values ¬(v∨y). Obtain a false w above all those values. Thus

$$
\neg Ep\ \Longrightarrow\ v\lor Ep=v,
$$
$$
Ep\ \Longrightarrow\ w\lor\neg(v\lor Ep)=w.
$$
Put

$$
t:=w\lor\neg v,
\qquad h(p):=w\lor\neg(v\lor Ep),
\qquad F(p):=\neg h(p)\lor\neg t.
\tag{9}
$$
The proposition t is true. When Ep is false, h(p)=t and F(p)=¬t. When Ep is true, h(p)=w and F(p)=¬w∨¬t. These outputs form the join chain

$$
b:=\neg t\quad\text{(false)},\qquad
u:=\neg w\lor\neg t\quad\text{(true)},\qquad b\le u.
$$
Hence F has E's truth profile, and material V for E gives pointwise V for F. Constant truth profiles are handled by constant observers as in §3. All A/Z orientations survive.

## 5. Proof of the separation equivalences and the tier qualification

For the forward direction of (1), finite-image material M separation implies bare material M separation. The [material characterization](truth-profiles-and-connective-reducts.md), §6, therefore gives the conjunction semilattice equations. Every qualified observer can now be replaced by its two-output pointwise version from §3. If all qualified replacements agree on p,q, every original material observer does too; the assumed separation gives p=q. The V proof uses §4.

For the reverse direction, Two(E) implies FinIm(E) already over H. To see this without an external finiteness argument, choose an actual output a:=E(Top). If every output equals a, the image satisfies Suc(0) by deleting a. Otherwise choose a distinct actual output b. The at-most-two bound implies that every output equals a or b. Deleting a and then b witnesses Suc(Suc(0)) of the image predicate. The definition of FiniteCardinality includes both successor cardinalities by two applications of its induction step. Thus the image is internally finite. This uses actual output witnesses and the exact image predicate, not extensional equality with an external two-element set.

Pointwise preservation implies material preservation by H substitution. Therefore separation by two-output pointwise observers implies separation by finite-image material observers. This proves both directions of (1), and the same proof gives V. In each direction A and Z are preserved exactly as stated.

The argument preserves each observer's truth profile at every input, so it applies at every relational output type. At full typed scope, [Functionality follows from separation](typed-separation-and-classicism.md), §2, and turns the pointwise identities into whole-operation identities. Thus the full typed equivalence has three versions: finite-image material, two-output pointwise, and two-output whole-operation separation.

At propositional scope alone, whole-operation preservation is not inferred from a conditional pointwise identity. The local Functionality instances at t,t and t,tt suffice for that upgrade, exactly as in [Finite semilattice normalization](finite-semilattice-normalization.md), §6.

## 6. What is and is not reduced

The right side of (1) entails unrestricted pointwise M separation. The result does not prove that arbitrary material M observers have internally finite images, or that arbitrary pointwise separators can be replaced by finite-image ones. The unrestricted infinite comparison remains unsettled by this argument.

An immediate sufficient hypothesis is local finiteness of the principal tests: in a meet semilattice, if every admitted map λp.(a∧p=a) has internally finite image, those material tests separate and (1) gives pointwise M separation. The dual statement uses the join cuts λp.¬(p∨a=a). These hypotheses concern the displayed tests' images, not bivalence of all identity judgments.

The two values in (8) or (9) are observer-dependent and need not equal the fixed Top and Bottom. Consequently this is not endpoint-valued logical separation and carries no conclusion of C5, Atomicity or identity bivalence. It is also a result about M and V separately: the constructed pair's meet table does not establish the primitive join or negation table, and conversely for the join construction.

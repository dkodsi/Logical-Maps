# Independent audit: rigid cores, world representation, and bottom cuts

Audit by GPT-6 (OpenAI), 22 October 2026. Ordinary mathematical checking; no human check or Lean verification is claimed. This report leaves the database and the source drafts unchanged. Its direct sources are the research drafts named below, with the local records used only for explicitly identified background lemmas.

## Status at first audit

* **PASS:** `/tmp/rigid-bottom-cut-proof.md`, including its stronger unboxed-premise theorem. The new bottom-containing cut lemma repairs the specific future-world quantifier defect described in the conjecture record.
* **PASS:** `.reproduction/classicism-research/rigidity-actualization.md` §§13–19 under their stated hypotheses. Later sharpening: the Infinity bridge admits a direct C5-only proof with a rigid image predicate and an evaluator-free inverse; see §9 below. Actualization is sufficient in the audited draft, but unnecessary in the stronger proof. Mere external informal cardinal counting would not suffice.
* **PASS, scope important:** §20 is a term-denotability result, not ordinary model-theoretic definable closure at a designated actual point. The distinction already stated in the draft is essential.
* **No database promotion:** the existing published/human-authored proof and its known gap must remain as historical evidence. If this repair is recorded, its source is `misc` and it needs a new proof/writeup rather than attributing the new argument to the book.

## 1. Exact framework and proof obligations

All types are the repository's relational types. Fix a relational type \(\sigma=\sigma_1\cdots\sigma_n t\), with the nullary case allowed, and let \(b=\bot_\sigma\). Algebraic order is an identity-defined condition and therefore persists by NI; it is not current pointwise implication. Inextensibility has its leading box. No use below applies Logical Equivalence to equivalence merely under an optional assumption.

The fixed C background includes the Boolean algebra laws, S4, NI, existential introduction for available terms, and Intensionality from necessary universal coextension. The additional assumptions are precisely the displayed local Strong Leibniz and local Rigid Comprehension instances, followed where stated by local Rigid Power. They are not secretly placed under boxes.

## 2. The bottom-cut lemma in fully scoped form

Put \(D(W):=\forall Y^\sigma(W\leq Y\lor W\leq\neg Y)\) and \(J(A):=\lambda\bar x\,\exists W(AW\land W[\bar x])\). Consider an available \(A^{\sigma t}\) satisfying

\[
\operatorname{Rigid}(A),\qquad \Box Ab,\qquad
\Box\forall W(AW\to D(W)). \tag{B}
\]

**Lemma.** C proves from (B) that
\[
\Box\forall Y^\sigma\;\operatorname{Rigid}(R_Y),\qquad
R_Y:=\lambda W(AW\land W\leq Y).
\]

Here the quantified \(Y\) may first become available at the world where it is quantified. The witness \(R_Y\) is then a lambda term constructed at that world; the argument never requires \(Y\) or \(R_Y\) to be an image of an actual-world entity.

To prove the lemma, work at an arbitrary reachable point with arbitrary current \(Y\). Persistence of \(A\) and of \(\leq\) gives persistence of \(R_Y\). At a further point, suppose \(\forall W(R_YW\to\Box ZW)\). Since \(Ab\) and \(b\leq Y\), this includes \(\Box Zb\). For each current \(A\)-member \(W\), (B) supplies \(W\leq Y\) or \(W\leq\neg Y\).

In the first case \(\Box ZW\), hence \(\Box(R_YW\to ZW)\). In the second case \(W\leq\neg Y\) persists. At every further point where \(R_YW\), we also have \(W\leq Y\), so Boolean antisymmetry gives \(W=b\); \(\Box Zb\) then gives \(ZW\). Again \(\Box(R_YW\to ZW)\).

Weak inextensibility of \(A\), applied at this point to \(W\mapsto(R_YW\to ZW)\), now gives \(A\leq\lambda W(R_YW\to ZW)\). Since \(R_Y\leq A\), this is \(R_Y\leq Z\). It establishes weak inextensibility at every further point, hence inextensibility. Only (B), whose clauses persist, was used inside these arbitrary-point arguments.

**Why bottom matters.** The proof explicitly allows a current nonbottom \(W\leq\neg Y\) to become bottom. The conclusion \(ZW\) at that point follows from the already supplied \(\Box Zb\). Without \(Ab\), that inference fails. No hidden ND is used to prevent this coalescence.

## 3. Construction of one persistent cover

Assume Strong Leibniz at \(\sigma\) and RC at \(\sigma t\). Rigidify the current property
\[
\operatorname{SWorld}_\sigma(W)\lor W=b
\]
to obtain \(A\). Persistence gives \(\Box Ab\). Each current member necessarily satisfies \(D\): for a strong world this is its defining boxed condition; for bottom it is a C theorem. Weak inextensibility of \(A\), tested on \(D\), therefore gives the boxed universal in (B). Its \(\forall Y\) is inside the box, so it constrains newly available future \(Y\)'s.

Each current strong world \(W\) has \(\Box AW\), and consequently \(W\leq J(A)\). The dual Strong Leibniz principle yields \(J(A)=\top_\sigma\). This identity also persists by NI. Thus one initially chosen \(A\) carries all the information used at later points. RC is used once, only at the original point.

## 4. Representation and Barcan

From (B) and \(J(A)=\top\), at every reachable point and for every current \(Y\),
\[
Y=J(R_Y),\qquad R_Y\leq A.
\]
For the nontrivial inequality, at any later tuple satisfying \(Y\), the cover supplies \(W\) with \(AW\land W[\bar x]\). The disjunction \(W\leq Y\lor W\leq\neg Y\) cannot take its second branch, so \(R_YW\). The other inequality is immediate. The argument holds at every later tuple, furnishing necessary coextension and therefore identity. This is the precise point at which the original book gap is avoided.

If RP at \(\sigma t\) also holds, then \(P_A:=\lambda R(\operatorname{Rigid}(R)\land R\leq A)\) is rigid. Suppose \(\forall Y^\sigma\Box XY\) at the original point. Every current \(P_A\)-member \(R\) has a current term \(J(R)\), so \(\Box XJ(R)\). Weak inextensibility of \(P_A\) gives
\[
\Box\forall R(P_AR\to XJ(R)).
\]
The boxed representation of all future \(Y\)'s then yields \(\Box\forall Y\,XY\), namely BF at \(\sigma\). There is no use of BF in proving the representation or in moving the initial pointwise assumption under a box: that movement is exactly what inextensibility of \(P_A\) supplies.

At schema level, Strong Leibniz implies Atomicity; the proved record `atomicity-and-rigid-comprehension-imply-rigid-power` supplies RP. RC supplies Tame Rigidity, and the proved record `tame-rigidity-and-bf-relational-imply-necessary-bf-relational` upgrades relational BF to boxed relational BF. Hence
\[
\boxed{\mathrm{SL}+\mathrm{RC}\ \Longrightarrow\ \Box\mathrm{BF}_{\mathrm{rel}}.}
\]

The conjecture `necessary-strong-leibniz-and-rigid-comprehension-imply-necessary-bf-relational` is a weaker premise case, by T. The individual BF instance is outside this proof.

## 5. Strong Leibniz itself propagates, without RP

The same cover gives a useful typewise strengthening. At a reachable point, let \(Y\ne b\). If no current nonbottom \(A\)-member lies below \(Y\), then every current \(A\)-member lies below \(\neg Y\): its deciding disjunction supplies this unless it lies below \(Y\), in which case it must be bottom and the conclusion still holds. Each such order statement is necessary. Weak inextensibility transfers the assertion to \(\Box\forall W(AW\to W\leq\neg Y)\). Consequently \(J(A)\leq\neg Y\), contradicting \(J(A)=\top\) and \(Y\ne b\).

So some current \(W\ne b\) has \(AW\) and \(W\leq Y\). Persistence of \(A\) together with (B) gives \(\Box D(W)\). Thus \(W\) is currently a strong world below \(Y\). This proves
\[
\mathrm{SL}_\sigma+\mathrm{RC}_{\sigma t}
\quad\Longrightarrow\quad\Box\mathrm{SL}_\sigma,
\]
without RP or any higher-type Atomicity premise. In particular, the low-type statement \(\mathrm{SL}_t+\mathrm{RC}_{tt}\to\Box\mathrm{SL}_t\) is justified separately from the full schema theorem.

Together with the recorded Atomicity + BF_rel ⇒ SL, one obtains, over RC, the exact equivalences
\[
\mathrm{SL}\iff\Box\mathrm{SL}
\iff(\mathrm{Atomicity}\land\mathrm{BF}_{rel})
\iff(\mathrm{Atomicity}\land\Box\mathrm{BF}_{rel}).
\]
These are consequences of the new argument plus recorded theorems, not preexisting Engine output.

## 6. Audit of the internal Gallin representation

Sections 13–14 of `rigidity-actualization.md` avoid the common invalid quotient construction. At each target relation type they take rigid relations supported only on the earlier target argument domains. Application preserves these domains; agreement on the supported arguments then implies agreement everywhere. Without this support clause higher-type extensionality would fail.

Under C5, bivalent matrices are closed under arbitrary admitted quantifiers by BF. Thus intrinsic core formulas define core relations without RC. This is sufficient for a many-sorted extensional Henkin interpretation. When worlds are added as the rigid sort of propositional atoms, the explicit graph
\[
F\mapsto((\bar a,w)\mapsto\operatorname{Atom}(w)\land w\leq F[\bar a])
\]
is rigid. The inverse is the join weighted by the atoms, \(R\mapsto\lambda\bar a\,\exists w(R(\bar a,w)\land w)\). Atomicity plus C5 supplies exactly one true atom at each point and decides every proposition there. These facts prove both inverse equations. Recursive transport of argument sorts is necessary and is supplied by the draft's maps \(j_\sigma,k_\sigma\). Their definitions remain in the relational type system; at e the identity is a substitution, not a term of the forbidden type ee.

The claim proved is Henkin representation. Every available world predicate is represented, but an arbitrary external subset of the world set need not be available. No fullness claim can be inferred from the inverse equations.

## 7. Audit of the quantified Infinity transfers

Section 17's projection \(h(Z)(X)=P(X)\land E(ZX)\) commutes with zero and successor on the supported rigid power domain. The equations use BE's Boolean and quantifier identities, and the fact that rigid \(X\) and \(X-y\) remain rigid under C5.

For the first inclusion, pulling back each available core inductive predicate through h is an admitted ambient predicate. For the reverse inclusion, the draft forms the **actualized image predicate**
\[
B(Y)\land E(\exists Z(NZ\land h(Z)=Y)).
\]
It is an admitted rigid supported predicate, is inductive, and BE converts its truth into a witness. This proves surjectivity onto the core's impredicatively generated naturals; it does not assume they are standard numerals. Applying the equality of actual counting at the universal property proves the precise quantified Infinity equivalence. The same argument works for a rigid subdomain D.

Section 18's finite-powerset step is valid internally in extensional Henkin HOL: adjunction-finiteness agrees with Frege-finiteness, images and subsets of finite sets are finite, and \(P(A\cup\{a\})=P(A)\cup\{B\cup\{a\}:B\in P(A)\}\). Each map or set used is available by comprehension. This is an internal finite-induction argument, not external enumeration of a nonstandard finite set. Hence the world/proposition Infinity equivalence does not require Choice.

Section 19's particular atomic-world lift L supplies the missing injectivity under Atomicity. The predicate \(K(Y):L(h(Y))=Y\) is inductive because both maps commute with zero/successor, so ambient induction proves K on every ambient natural. This does not prove h injective on arbitrary cardinality predicates, and the draft correctly restricts the conclusion. The natural-domain isomorphism is independent of the actual evaluator because its inverse L is. Section 9 records a different lift that removes Atomicity.

## 8. Definability scope and source status

Section 20's atom transposition is an automorphism of the typed algebra preserving logical constants; it need not preserve truth at the designated actual point. It fixes the original supported hereditary core and any given propositional parameters whose Boolean cells contain both swapped atoms. Consequently a *term value* cannot split a Boolean cell. This proves the finite-parameter obstruction to term-denoted world choice.

It does not rule out unique current descriptions, such as the unique actually true atom. A current truth-based description need not denote a closed term; replacing that distinction with a broad claim about definable closure would be false. The draft explicitly retains this distinction.

No literature-originality judgment is made. The bottom-cut argument is a new proof in this research session and should be attributed as such; the underlying gap remains attributed to the source record. The representation and Infinity proofs are similarly session arguments, not claims about what Gallin or Bacon proved.

## 9. Later independent sharpenings

The profile auditor's `.reproduction/classicism-research/audit-bottom-cut-profile-agent-20261022.md` independently verifies the bottom-cut proof and weakens the auxiliary power premise. Section 4 uses only weak inextensibility of the supported rigid power predicate P_A. Steps 1–2 of the recorded Atomicity+RC⇒Rigid Power proof already supply that weak inextensibility from RC at σt and Atomicity at (σt)t. The further comprehension used to make the power predicate fully rigid is unnecessary. Thus the precise local result is

    SL_σ + RC_(σt) + Atomicity_((σt)t) ⇒ □BF_σ.

Here RC_(σt) also supplies the corresponding Tame Rigidity instance needed to box BF. The simpler propagation SL_σ+RC_(σt)⇒□SL_σ remains independent of this higher Atomicity premise.

The same auditor's `.reproduction/classicism-research/audit-infinity-transfer-20261022.md` proves a stronger numerical theorem under C5 alone, for every original counting type σ. Write P(X)=Rigid(X), B(Y)=Rigid(Y)∧Y≤P, and q(Z)(X)=P(X)∧ZX. The evaluator-free inverse is

    ℓ(Y)(X)=∃R [Rigid(R)∧Coext(X,R)∧YR].

The maps commute with zero and successor on their respective natural-cardinality fields. Rigidity of original numberhood, a recorded C5 consequence of its C-persistence, makes B(Y)∧∃Z(NZ∧qZ=Y) an admitted core inductive predicate directly. It gives surjectivity. The equations ℓ0c=0 and ℓScY=SucℓY follow by adjoining or removing a haecceity from a rigid coextension, without RC. Original induction then gives ℓqZ=Z for every original natural Z, including nonstandard and overflow cases; qℓY=Y holds on the core. This is a full zero/successor isomorphism and yields equivalence of the quantified original/core Infinity axioms.

Actuality, BE, Atomicity and Choice are unnecessary for this numerical bridge. The atomic-world/power-set comparison still needs the boxed-Plenitude package. For a proper rigid subdomain D only the finiteness correspondence and natural-cardinality surjection are claimed: the unrestricted original number field can have many values collapsing to the subdomain's overflow value. The independent Frege research lane had also found the C5 e-core bijection by a different argument; no novelty priority is asserted here.

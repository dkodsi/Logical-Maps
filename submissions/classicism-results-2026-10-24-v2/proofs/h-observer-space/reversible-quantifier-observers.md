# Reversible observers: necessary bijectivity and universal preservation

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the observer characterizations: `misc`, this note, §§1–5, unpaginated. The definable inverse uses the existing modalized-Plenitude argument, attributed separately in §5.

Two natural formulations recover reversible logical separation. A logical observer has an admitted qualified inverse exactly when it is necessarily bijective. Moreover, over C an invertible observer preserving the universal quantifier at t already preserves every Boolean connective. Thus Boolean qualification can be omitted on this reversible quantifier branch. Neither result assumes atoms or Choice.

## 1. Statements and exact scope

For an admitted E:tt put

$$
\begin{aligned}\operatorname{Inj}(E)&:=\forall p,q\,[Ep=Eq\to p=q],\\\operatorname{Onto}(E)&:=\forall q\,\exists p\,[Ep=q],\\\operatorname{Bij}(E)&:=\operatorname{Inj}(E)\land\operatorname{Onto}(E),\\\operatorname{Inv}(E)&:=\exists F^{tt}\,[E\circ F=I\land F\circ E=I],\qquad I:=\lambda p.p.\end{aligned}
$$

The two inverse equations are identities of whole operations. Bij(E), by contrast, is a current first-order condition on the proposition domain. The box in □Bij(E) covers the displayed object-variable-closed formula, retaining E as a parameter. In C, □P means P=Top.

For each fixed finite external type list Δ, use the whole-operation qualification Good_Δ from [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md), §1. No schema is placed inside an object-language quantifier.

**Theorem 1, over C.** For any admitted E,

$$
\operatorname{Inv}(E)\leftrightarrow\Box\operatorname{Bij}(E).
$$

If E preserves a finite list of Boolean operations and universal/existential quantifiers, its inverse preserves the same operations. In particular, for a Good_Δ observer, Inv(E) is equivalent to existence of a Good_Δ inverse.

Consequently, **over H**, full logical separation by necessarily bijective Good observers is exactly Rev. The forward direction first recovers C from full logical separation, then applies Theorem 1. The converse uses the established implication Rev⇒C.

**Theorem 2, over C5.** Bij(E) implies □Bij(E). Thus

$$
\mathsf{Rev}\ \leftrightarrow\ \mathrm{C5}+\text{full logical separation by bijective Good observers}.
$$

The C5 premise on the right is explicit. Current bijectivity over C alone is not upgraded by this theorem.

**Theorem 3, over C.** If E satisfies Q_t and Inv(E), then E and its inverse preserve all Boolean operations by whole identities. If Δ contains t, then

$$
\begin{aligned}Q_\Delta(E)\land\operatorname{Inv}(E)&\leftrightarrow\operatorname{Good}_\Delta(E)\land\text{existence of a Good}_\Delta\text{ inverse}\\&\leftrightarrow Q_\Delta(E)\land\Box\operatorname{Bij}(E).\end{aligned}
$$

Here Good's equality clauses are the C-redundant translated logical clauses. The finite Q-list suffices for its matching existential list by C duality. Thus, at full separation scope,

$$
\begin{aligned}\mathsf{Rev}&\leftrightarrow\mathrm C+\text{separation by invertible }Q_\Delta\text{ observers}\\&\leftrightarrow\mathrm C+\text{separation by necessarily bijective }Q_\Delta\text{ observers}.\end{aligned}
$$

where the schemas range over relational output types and finite Δ containing t. Requiring Δ to contain t loses no full-Rev instance: enlarge any requested finite list by t. The explicit C premise is essential to the proof; this note does not claim that quantifier-only separation recovers unpreserved H primitives.

## 2. Necessary bijectivity supplies an admitted inverse

Define the admitted description term

$$
F_E(q):=\forall p\,[(Ep=q)\to p].
$$

It is the proposition-output witness in the recorded [modalized-Plenitude proof](../../source/topics/classicism/results/classicism-implies-modalized-plenitude-r.yaml). We give the premise checks so that the optional bijectivity hypothesis is never necessitated.

Assume □Bij(E). For a current q, T and surjectivity give p with Ep=q. NI gives □(Ep=q). Necessary injectivity, together with that necessary equation, gives

$$
\Box[(Ep=q)\land\forall r\,(Er=q\to r=p)].
$$

This uses the necessitation of the discharged C theorem expressing uniqueness of an injective map's fiber; its parameters are instantiated by CBF. Since q was arbitrary, we have

$$
H_E:=\forall q\,\exists p\,\Box[(Ep=q)\land\forall r\,(Er=q\to r=p)].
$$

The derivation establishes an unconditional, universally closed C theorem □Bij(E)→H_E. Necessitate that theorem, instantiate E by CBF, and use 4 on the given □Bij(E). This yields □H_E. No instance of BF is used.

Apply the recorded description proof with U(q,p):=(Ep=q). It supplies the explicit term F_E above and

$$
\Box\forall q,p\,[(Ep=q)\leftrightarrow p=F_E(q)].
$$

Instantiate p:=F_E(q) for one direction, and q:=Ep for the other. Necessary reflexivity then gives

$$
\begin{aligned}\Box\forall q\,[E(F_E(q))=q],\\\Box\forall p\,[F_E(Ep)=p].\end{aligned}
$$

The corresponding necessary coextensions, followed by C's Intensionality at tt, give E∘F_E=I and F_E∘E=I as whole-operation identities. No arbitrary inverse function is assumed admitted, and no choice operation is selected.

Conversely, assume whole inverse equations for admitted E,F. The universally closed implication from those equations to Bij(E) is an unconditional C theorem. Necessitate it and instantiate E,F by CBF. NI makes the two given operation identities necessary, so □Bij(E) follows. This proves Theorem 1's first assertion.

### Preservation transfers through a whole inverse

For conjunction, write m for the binary operation. E's whole M law is E∘m=m∘(E,E), with the pair notation abbreviating the corresponding curried lambda terms. Substitute F in both inputs and compose F on the output. The inverse identities give

$$
F\circ m=m\circ(F,F).
$$

All these are substitutions of equal operations in admitted term contexts. No conditional pointwise equivalence is turned into an operation identity. The same calculation handles disjunction, negation and a preserved constant.

For a quantifier U_σ:=(λG.∀x:σ Gx), let P_E(G):=λx.E(Gx), an admitted operation on σt. The whole Q_σ law is

$$
E\circ U_\sigma=U_\sigma\circ P_E.
$$

Compose F on the left and P_F on the right. The whole inverse identities yield P_E∘P_F=I by contextual beta/eta conversion, and hence

$$
U_\sigma\circ P_F=F\circ U_\sigma.
$$

This is precisely Q_σ(F). The existential proof is the same. Therefore an inverse of a Good observer is qualified for the same finite list, since over C the remaining translated equality clauses follow from Boolean qualification.

## 3. Current bijectivity under C5

C5 supplies NI, ND_t and BF_t. It also supplies the necessary versions needed by its modal S5 theory, but this proof uses only the displayed current instances.

Assume Onto(E). For each q choose p with Ep=q. NI gives □(Ep=q), and necessary existential introduction gives □∃p(Ep=q). Thus ∀q□∃p(Ep=q); BF_t gives □Onto(E). This part requires C+BF_t, without ND_t.

Now assume Inj(E). Fix p,q. If Ep≠Eq, ND_t makes that inequality necessary, so the implication Ep=Eq→p=q is necessary. If Ep=Eq, injectivity gives p=q, and NI makes the consequent necessary. In either case

$$
\Box(Ep=Eq\to p=q).
$$

Quantify p,q and apply BF_t twice to obtain □Inj(E). Thus Bij(E) implies □Bij(E) under C5. Combining this with §2 and the established Rev⇒C5 proves Theorem 2. The proof does not replace current injectivity with necessary injectivity over a weaker base.

## 4. Reversible universals recover the Boolean operations

First, every Q_t observer is monotone for C's Boolean order. Define the admitted family

$$
B_{p,q}(x):=(x\land p)\lor(\neg x\land q).
$$

Unconditionally in C,

$$
\begin{aligned}\forall x^t\,B_{p,q}(x)&=p\land q,\\B_{p,q}(\top)&=p,\\B_{p,q}(\bot)&=q.\end{aligned}
$$

The first identity follows from an unconditional H equivalence: instantiate x at Top and Bottom for one direction, and use p∧q for the other. Logical Equivalence supplies its full parameterized identity.

Q_t(E) therefore gives

$$
E(p\land q)=\forall x^t\,E(B_{p,q}(x)).
$$

Necessary universal instantiation gives Boolean-order inequalities E(p∧q)≤Ep and E(p∧q)≤Eq. If p≤q, then p∧q=p, so Ep≤Eq. This is a monotonicity proof; it does not conclude that arbitrary Q_t observers preserve meet.

Now assume admitted whole inverse equations for E,F. Section 2 transfers Q_t from E to F, so both are monotone. They are inverse Boolean-order isomorphisms. Such an isomorphism preserves the greatest and least elements, binary greatest lower bounds and least upper bounds, and complements by their unique order characterization. Hence E and F preserve Top, Bottom, conjunction, disjunction and negation pointwise.

To obtain the required whole-operation identities without assuming Functionality, let K be the finite conjunction of Q_t(E) and the two inverse operation identities. NI gives K→□K. The pointwise Boolean preservation argument is an unconditional C theorem once K is discharged and all observer/input variables are universally closed. Necessitate that closed theorem, instantiate observer parameters by CBF, and use □K. This gives the necessary coextensions under all input quantifiers. C's Intensionality identifies the whole composite operations.

If E additionally preserves Q_σ for the other σ in Δ, §2 transfers every listed Q_σ to F. Boolean duality supplies their matching existential identities. This proves Theorem 3. Neither .2 nor BF is added in the individual-observer reduction; the full separation equivalences recover whatever further modal principles follow from Rev.

## 5. Sources and limitations

The inverse-description term and the necessary-unique-fiber lemma come from the existing record [C implies Modalized Plenitude](../../source/topics/classicism/results/classicism-implies-modalized-plenitude-r.yaml): Cian Dorr, 28 September 2026, for the proposition-output term and principle; the record separately attributes its generalization and written proof. Its background modal rules and Intensionality are sourced to Bacon and Dorr, *Classicism*, draft of 16 May 2023, §1.5, pp. 16–18.

The new observer equivalences and reversible quantifier reduction are `misc`, OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026, this note §§1–4, unpaginated. The full-H recovery and Rev⇒C5 implications are in [Logical observer hierarchy](../logical-observer-hierarchy.md), §§4 and 6, and [Typed separation](typed-separation-and-classicism.md), §§3–7.

This note does not assert that current bijectivity alone supplies an admitted inverse over C, that bare quantifier separation recovers C over H, or that arbitrary N+Q/V+Q observers are Boolean. Its exact new conditions are necessary bijectivity, or C5 plus current bijectivity, and invertibility with Q_t in the C-relative reduction.

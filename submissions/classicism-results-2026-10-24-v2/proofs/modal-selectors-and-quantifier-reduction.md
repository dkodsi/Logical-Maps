# Modal selectors and reduction to propositional quantification

Ordinary mathematical arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: misc, this note, §§1–6, unpaginated. This is a result within the C region of the larger H-based research program, not a change of its fixed base.

Use the qualifications and separation notation of [the observer lattice](observer-lattice.md). All commutation is full identity of the displayed composite operations. Bool means preservation of the three original Boolean connectives. Q_t preserves the universal quantifier over propositions. BF_t is the ordinary, unboxed, type-t Barcan formula.

## 1 Endpoint selectors exactly characterize modal .2 over C

Define

```math
\begin{aligned}
\mathrm{BR}&:=\exists B^{tt}\, .\,B\top=\top\land B\bot=\bot\land\forall p\,(Bp=\top\lor Bp=\bot),\\
\mathrm{D2}&:=\forall p\,(\Diamond\Box p\to\Box\Diamond p)
\end{aligned}
```

No logical preservation is imposed on B. Over C,

```math
\mathrm{BR}\ \leftrightarrow\ \mathrm{D2}
```

For BR ⇒ D2, suppose ◇□p. If Bp=Bottom, NI preserves this identity, as well as BTop=Top. Necessary substitution says that at any possibility where p=Top, Bp=Top, contradicting its persistent Bottom value. Hence Bp=Top. Similarly ◇□¬p forces Bp=Bottom, using BBottom=Bottom and C's identification of □¬p with p=Bottom. Therefore ◇□p excludes ◇□¬p, which is exactly □◇p. There is no necessitation of BR or of its universally quantified endpoint condition: only particular true identities are propagated by NI.

Conversely, under D2 put Bp=◇□p. If Bp, axiom 4 first gives ◇□□p; D2 applied to □p then gives □◇□p, namely □Bp. If ¬Bp, rewrite this as □¬□p and apply 4 to obtain □¬Bp. Therefore each Bp equals Top or Bottom. The endpoint-fixing equations follow from unconditional C modal identities. BF and necessary D2 are unnecessary.

The notation .2 for ◇□p→□◇p is standard; see Hamkins and Löwe, [The modal logic of forcing](https://arxiv.org/pdf/math/0509616), arXiv version 1, 27 September 2005, §1, p. 3. That source is cited for the modal axiom's terminology, not for this observer characterization.

## 2 Binary ranges and conjunction

Over C, BR is also equivalent to

```math
\forall p,q\,\exists F^{tt}\, .\,F\top=p\land F\bot=q\land\forall x\,(Fx=p\lor Fx=q)
```

From BR use F(x)=(Bx∧p)∨(¬Bx∧q). Its endpoint cases give the required output identities and both designated values. Conversely specialize the family principle to p=Top, q=Bottom. This is an admitted binary range, not merely a family whose truth values sometimes agree with p and q.

Over C + BF_t, any such family has universal value p∧q. Indeed p∧q≤Fx for each x, where the order is necessary implication. BF_t collects these necessities, giving p∧q≤∀x Fx. Necessary universal instantiation and the two designated values give the reverse inequality.

It follows that

```math
\mathrm C+\mathrm{BF}_t+\mathrm{D2}\ \vdash\ Q_t(E)\to M(E)
```

Apply the binary-range calculation to F and E∘F. Their universal values are p∧q and Ep∧Eq respectively. The Q_t identity at F yields E(p∧q)=Ep∧Eq. NI boxes each such output identity; BF_t, first over q and then over p, collects them into a necessary universal statement. Intensionality identifies the whole binary composite operations. No BF at tt, necessary BF, necessary D2, or Top-acceptance hypothesis on E is used.

The modal assumption is weaker than C5: the full two-object chain satisfies D2 and BF but fails C5. Its unique terminal object verifies D2 directly. D2 is not a theorem of C: the full three-object fork has a proposition becoming Top on one terminal branch and Bottom on the other. These are ordinary applications of the full action construction; no new model records are asserted here.

## 3 Mixed branches under D2

For every finite Δ containing t, over C + D2,

```math
S[A\land N\land Q_\Delta]\ \leftrightarrow\ S[A\land V\land Q_\Delta]\ \leftrightarrow\ S[\mathsf{Bool}\land Q_\Delta]
```

Each left-hand principle supplies BF_t by the universal-separation argument. Section 2 then makes Q_t observers preserve conjunction fully. On the N branch, De Morgan supplies the remaining Boolean law. On the V branch, a distinguishing observer cannot accept Bottom, since p∨Bottom=p would otherwise make it accept every input. Its conjunction and disjunction laws and endpoint truth conditions supply material negation preservation. Apply the finite guard normalization from the earlier lattice note to obtain full Boolean/QΔ witnesses with the same current distinguishing truth values. The reverse implications are inclusion of eligible classes.

The existential dual holds with Bottom rejection: conjunction/existential and negation/existential separation give Boolean/existential separation under D2, for lists containing t. Conjugate observers by negation to transfer the proof.

These are finite-list results. Over C + D2, one fixed type list does not by this argument supply every type law. The corresponding schemas over all finite lists yield full OS, since their BF consequences supply Functionality. Classifying the mixed principles over bare C remains a separate question.

## 4 Over C5, Q_t supplies every quantifier

Over C5, every Boolean Q_t observer E is GoodΔ for every finite Δ. The same observer works; no normalization or new witness is needed.

For F:σt define its range predicate I_F:tt by

```math
I_F(p):=\exists x^\sigma\, .\,Fx=p
```

Every I_F(p) is an endpoint. A witness gives □I_F(p) by NI and necessary existential introduction. If there is no witness, ND_t makes each Fx≠p necessary, and BF_σ makes their universal necessary. Thus ¬I_F(p) gives □¬I_F(p). Boolean observers fix the endpoints, so E(I_F(p))=I_F(p).

The H equivalence between the following universally quantified formulas gives an unconditional C identity:

```math
(\forall x^\sigma\,Fx)=(\forall p^t\, .\,I_F(p)\to p)
```

Applying E, using Q_t and Boolean preservation, and then using the endpoint fact above, gives the material chain

```math
\begin{aligned}
E(\forall x\,Fx)&\leftrightarrow\forall p\,E(I_F(p)\to p)\\
&\leftrightarrow\forall p\,(I_F(p)\to Ep)\\
&\leftrightarrow\forall x\,E(Fx)
\end{aligned}
```

The last equivalence is ordinary equality substitution and quantification over the range. It uses no enumeration, Choice or quantification over types.

For the full Q_σ identity, discharge the derivation as an unconditional C implication from □ND_t, Bool(E), and Q_t(E). The first premise supplies C5 and its BF consequences. Each antecedent persists: use 4 for □ND_t and NI for the full operation identities. Necessitate the discharged implication, instantiate using CBF, and apply Intensionality to the necessary universal equivalence. This gives equality of the λF composite operations. Existential preservation follows from the full Boolean and quantifier duality identities; the translated equality clauses follow from Boolean qualification over C.

Consequently over C5,

```math
\mathrm{C5}\ \vdash\ S[\mathsf{Bool}\land Q_t]\ \leftrightarrow\ \mathrm{OS}
```

For the nontrivial direction, each separating witness qualifies for any requested finite list. C5 supplies Functionality, extending propositional separation to every relational type. This collapses the separation schema over this base; it does not introduce an infinitary object-language qualification.

## 5 Single formulas for C5 + OS over C

Combining §§3–4 with the identity-fixing results gives

```math
\mathrm C\ \vdash\ S[A\land\mathrm{FixEq}_t\land N\land Q_t]\ \leftrightarrow\ S[A\land\mathrm{FixEq}_t\land V\land Q_t]\ \leftrightarrow\ \mathrm{C5}+\mathrm{OS}
```

Identity-fixing and Top-accepting separation gives ND_t; Q_t separation gives BF_t; the recorded ND_t + BF_t theorem gives C5. Dropping FixEq from the qualification then gives one of the mixed separation principles, and §§3–4 give OS. Conversely C5 + OS supplies Good_{t} separating observers. Under C5, identity judgments are endpoints, and the persistent-premise/Intensionality argument makes their fixing a full composite identity. Thus those witnesses satisfy either displayed qualification.

These are exact single-formula characterizations over C. They are not claimed over H. The H program tracks the separate steps needed to recover C rather than using it as an implicit background.

## 6 Boxed BF does not replace .2 in the individual observer reduction

The full three-object fork r→l and r→h, with singleton individuals, supplies a concrete counterexample to dropping .2 from §2. Its construction and all-type joint-surjectivity proof are in [Fork without binary families](h-observer-space/fork-without-binary-families.md), §§1–2. At the root, propositions are triples

```math
p=(p_0,p_l,p_h)\in\{0,1\}^3
```

with root truth p₀, leaf transports the last two coordinates, and coordinatewise Boolean operations. The model satisfies C, all BF instances, and their boxed forms. For every admitted type σ, the pair of leaf transports Dσ(r)→Dσ(l)×Dσ(h) is onto.

Define an admitted root observer E with leaf components identity by

```math
E(p_0,p_l,p_h)=(p_l\lor p_h,p_l,p_h)
```

It is an admitted full action-model operation: its arbitrary root truth function and the two identity leaf functions satisfy the application/transport compatibility equations. It fixes Top and Bottom, preserves disjunction as a whole-operation identity, and is idempotent as a whole operation. These assertions follow coordinatewise at the root and both leaves. Its image is finite, with one output for each pair of leaf bits.

For every σ it also preserves the universal quantifier as a whole-operation identity. Let F:σt have root truth function f and leaf components F_l,F_h, and write α,β for the two transports at σ. The root truth of E(∀x F(x)) is

```math
(\forall x_l\,F_l(x_l))\lor(\forall x_h\,F_h(x_h))
```

The root truth of ∀x E(F(x)) is

```math
\forall x\in D_\sigma(r)\,[F_l(\alpha x)\lor F_h(\beta x)]
```

Joint surjectivity makes this equivalent to the universal statement over every independent pair x_l,x_h. That statement is equivalent in classical logic to the preceding disjunction of universals: if neither universal holds, one counterexample on each side gives a falsifying pair. The leaf components agree because E acts there as identity. This proves equality of outputs for every F at every future object. In the full model the complete λF operation profiles are therefore equal, proving full Qσ(E).

Conjunction fails even materially. Take

```math
p=(0,1,0),\qquad q=(0,0,1)
```

Their meet is Bottom, so E(p∧q) is false at r. Both Ep and Eq are true there. Hence E(p∧q) and Ep∧Eq are distinct propositions.

The dual observer

```math
D(p_0,p_l,p_h)=(p_l\land p_h,p_l,p_h)
```

fixes the endpoints, is idempotent, preserves conjunction and every existential quantifier fully, but fails disjunction. For existential preservation use the equivalence between ∃(x_l,x_h)[F_l(x_l)∧F_h(x_h)] and (∃x_l F_l(x_l))∧(∃x_h F_h(x_h)), again with joint surjectivity. The same p,q witness disjunction failure.

Thus even C + all boxed BF does not imply that every universal-preserving observer preserves conjunction, or the dual existential-to-disjunction assertion. Endpoint fixing, finite image, idempotence and preservation of the opposite binary connective do not repair this example. This establishes the need for an additional hypothesis in that individual-observer upgrade; it does not prove .2 is necessary in every model, or settle the remaining equivalences between separation principles. The fork itself has full logical separation, so it is not a separating model for those latter theories.

For the last assertion, identity and the coordinate readers L(p)=(p_l,p_l,p_h), R(p)=(p_h,p_l,p_h), each with identity leaf components, preserve all Boolean operations and every universal/existential quantifier fully by the individual leaf-transport surjectivities; they separate the three proposition bits, and the model's Functionality supplies full typed separation. The whole-operation equations hold at the root and both leaves, and the translated equality clauses follow from C and Boolean preservation.

The new observer verdicts in this section have direct source `misc`, OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026, §6, unpaginated,  The underlying full action construction retains the source attribution in the linked fork note.

## 7. Separation-theory countermodels without .2

The unrestricted N+Q and V+Q separation reductions are refuted by the [ternary Cantor symmetry model](h-observer-space/ternary-cantor-observer-model.md), §§1–9. It satisfies C, every boxed BF and Functionality instance, and full endpoint-fixing separation for each of the separate M+Q/P, V+Q/P and N+Q/P classes. Every separately boxed instance of each positive separation schema also holds. Nevertheless Boolean observers fail to separate even propositions.

Thus the conjunction of those separate separation theories still does not give a common Boolean separating class. This supplies the theory-level countermodel that the full fork of §6 does not supply. It does not change the positive reductions under .2 in §§1–5: .2 fails in the new model. The construction and proofs are in the linked note, direct source `misc`, OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026, unpaginated.

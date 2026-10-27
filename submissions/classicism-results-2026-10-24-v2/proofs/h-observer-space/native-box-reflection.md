# Native-Box separation reflects universal modal laws

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the reflection theorem, its precise fragments and the separating model: `misc`, this note, §§1–5, unpaginated. The full action-model framework and earlier observer results are attributed in §6.

Native-Box separation gives a reusable reflection theorem: a currently true universal modal law is necessary. The argument extends to universal closures of predicate variables whose bodies are first-order modal formulas, including existential quantification over their object arguments. The placement and use of the variables matter; there is no unrestricted reindexing of existential proposition witnesses through an observer.

## 1. Universal modal laws

Work over C. Write BoxSep(t,Δ) for propositional separation by Good_Δ observers satisfying the whole identity

```math
(\lambda p.\,E(\Box p))=(\lambda p.\,\Box(Ep)),
\qquad \Box p:=(p=\top)
\tag{1}
```

Good_Δ has the full composite Boolean and listed quantifier identities. Every Δ is a finite external list. The full typed theory and its recovery of C over H are defined in [Native-Box logical observers](native-box-logical-observers.md), §§1–2.

A **universal modal sentence** here has the form

```math
A:=\forall p_1^t\cdots\forall p_n^t\,
\theta(p_1,\ldots,p_n),
\tag{2}
```

where n is finite and θ is built from its displayed proposition variables, Top, Bottom, Boolean operations and the native Box. It has no object quantifiers inside θ and no additional parameters. Implication and biconditional may be written using their Boolean expansions. Modal Diamond may be read as ¬Box¬; the framework's equivalent original abbreviation transfers by the unconditional C-equivalence argument below.

**Theorem 1.** For each sentence (2),

```math
\boxed{
\mathrm C+\mathrm{BoxSep}(t,\{t\})
\quad\vdash\quad A\to\Box A}
\tag{3}
```

This is an external schema indexed by finite formulas, not an object-language quantification over formulas.

**Proof.** Fix a qualifying E. Structural induction on θ, using the Boolean operation identities, endpoint fixing over C, and (1), gives

```math
E\bigl(\theta(\bar p)\bigr)
 =\theta(Ep_1,\ldots,Ep_n)
\tag{4}
```

Apply the full Q_t law once for each binder in (2). It follows that

```math
E(A)=\forall p_1^t\cdots\forall p_n^t\,
\theta(Ep_1,\ldots,Ep_n)
\tag{5}
```

Now assume current A. For each current tuple p̄, instantiate A at the admitted tuple Ep₁,…,Epₙ. Thus the right side of (5) is true. Hence E(A) and ETop are both true for every qualifying E. Propositional separation gives A=Top, exactly □A. Discharge A to obtain (3). No optional assumption has been necessitated, and neither injectivity nor surjectivity of E was used. ∎

The number of universal proposition binders does not enlarge the qualification beyond t. For the degenerate case n=0, Q_t is unused; the same statement remains valid. Any larger finite Δ also suffices.

There is an immediate invariance under unconditional C equivalence. If C proves A↔B and (3) has been proved for B, then A implies B and hence □B. Necessitate the unconditional C theorem B→A to obtain □A. Thus A→□A follows as well. In particular, one may use universal first-order modal-algebra sentences with atomic identities s=t or order assertions s≤t between modal terms: replace these atoms by □(s↔t) or □(s→t), respectively. Their C-equivalences and the modal Boolean expansions are unconditional; no observer is assumed to preserve arbitrary equality judgments.

## 2. Predicate-universal first-order reflection

The same argument applies beyond (2). Fix finitely many predicate variables

```math
R_i^{\rho_i},\qquad
\rho_i=\sigma_{i1}\cdots\sigma_{im_i}t
```

Zero arity is permitted, so a predicate variable may itself have type t. Let φ(R̄) be a formula of the following many-sorted first-order modal fragment:

- Its nonconstant atomic formulas are applications R_i[x̄] to tuples of object variables of the indicated input types.
- It uses Boolean operations and native Box, and it may use both universal and existential quantification over object variables.
- No predicate variable R_i is quantified inside φ. No other predicate symbols or atomic equality judgments occur.
- Object variables are used only as arguments of the displayed predicates. In particular, an object variable of type t is not also used as a bare asserted proposition. Zero-arity outer predicate variables supply the proposition atoms when needed.
- All object variables are bound inside φ. Bound names are kept distinct from the outer R_i and from E.

This is an explicit syntactic fragment of the fixed relational language. An object argument can have any admitted type; it remains an argument, rather than a second logical operation. There are no restrictions on the Boolean polarity of the object quantifiers.

Put

```math
A:=\forall R_1^{\rho_1}\cdots\forall R_k^{\rho_k}
\,\varphi(\bar R)
\tag{6}
```

Let Δ contain each outer type ρ_i and each type of an object-variable binder occurring in φ. This is a finite list because A is finite.

**Theorem 2.** For every (6) in this fragment,

```math
\boxed{
\mathrm C+\mathrm{BoxSep}(t,\Delta)
\quad\vdash\quad A\to\Box A}
\tag{7}
```

**Proof.** For a qualifying E define, separately for each predicate variable, the admitted abstraction

```math
R_i^E:=\lambda x_1^{\sigma_{i1}}\cdots
 x_{m_i}^{\sigma_{im_i}}.\,E(R_i[\bar x])
\tag{8}
```

At zero arity this is simply ER_i. Induction on φ gives

```math
E\bigl(\varphi(\bar R)\bigr)=
\varphi(\bar R^E)
\tag{9}
```

The atomic step is contextual beta conversion using (8). The Boolean and Box steps use the whole preservation identities. For an object-variable binder x of type σ, use Q_σ or P_σ and then the induction hypothesis. The variable x remains the same object variable on both sides. There is no transformation x↦Ex and no reindexing of its domain, even when σ happens to be t. The restrictions on atomic formulas ensure exactly this distinction between predicate heads and object arguments.

The outer Q_{ρ_i} identities now give

```math
E(A)=\forall R_1^{\rho_1}\cdots\forall R_k^{\rho_k}
\,\varphi(\bar R^E)
\tag{10}
```

Assume current A. For every tuple of current R_i, each R_i^E is an admitted predicate of the same type, so instantiate A at that tuple. This proves the truth of the right side of (10). All qualifying observers consequently accept A and Top, and separation gives A=Top. Discharge A. ∎

Theorem 1 is the case in which all outer predicates are zero-ary and the body has no object binders. Theorem 2 also contains the earlier Barcan reflection: take one outer F of type σt and

```math
\varphi(F):=
 (\forall x^\sigma\,\Box Fx)
 \to\Box(\forall x^\sigma Fx)
\tag{11}
```

Its finite qualification is precisely {σt,σ}. Current BF_σ therefore implies necessary BF_σ under that single propositional BoxSep instance.

The inner existential clauses in Theorem 2 do not license arbitrary existential predicate or proposition reflection. For example, an outer sentence ∀p∃q θ(p,q), with p and q used as bare proposition atoms, would translate to ∀p∃q θ(Ep,Eq). Its current truth supplies some q, not necessarily one in the image of E. The present proof does not make that inference. Nor does it allow existentially quantified relation heads inside φ.

## 3. Consequences for full native-Box separation

Full typed BoxSep over H recovers C. It then gives every local separation instance needed in (3) and (7). Thus its current universal modal laws and its current predicate-universal first-order modal laws in the stated fragment are necessary.

For familiar modal axioms, write their finite-variable universal closures. Here .2 is ∀p(◇□p→□◇p), 5 is ∀p(◇p→□◇p), and .3 is

```math
\forall p,q\left[
(\Diamond p\land\Diamond q)
\to\Diamond(p\land\Diamond q)\lor\Diamond(q\land\Diamond p)
\right]
```

The theorem gives, for example,

```math
.2\to\Box .2,\qquad
.3\to\Box .3,\qquad
5\to\Box 5
\tag{12}
```

under C+BoxSep(t,{t}). These are conditional reflection statements. They do not assert .3 or 5. Native-Box separation already implies .2 by the smaller Bottom-fixing argument, so its necessary version follows here. The full theory does not imply C5, as the omega-chain model shows.

The .3 consequence here remains conditional. The boundary in §5 establishes that even necessary ordinary separation and necessary BF do not suffice for general reflection.

## 4. Necessary .2 already follows from the lower modal package

The special consequence □.2 is **not** a new strict separation above the previously established C+BF_t+.2 package. In fact,

```math
\mathrm C+\mathrm{BF}_t+.2\quad\vdash\quad\Box .2
\tag{13}
```

Use the exact [endpoint-selector characterization](../modal-selectors-and-quantifier-reduction.md), §1. Over C, .2 is equivalent to

```math
\exists B^{tt}\left[
B\top=\top\land B\bot=\bot\land
\forall p^t\,(Bp=\top\lor Bp=\bot)\right]
\tag{14}
```

Choose a current witness B. For each p, one of the two displayed output identities holds. NI makes that identity necessary, and therefore makes their disjunction necessary. Generalize p and use BF_t to obtain

```math
\Box\forall p^t\,(Bp=\top\lor Bp=\bot)
\tag{15}
```

NI also supplies necessity of BTop=Top and BBottom=Bottom. Combine these necessities and apply necessary existential introduction to B, giving the box of (14). Necessitate the unconditional C implication from (14) to .2, and apply normality to obtain □.2. Only closed C theorems are necessitated; the witness identities are propagated by NI. No BF at tt or necessary BF is required.

Accordingly, the general reflection theorem is the substantive extension. This note does not claim that it is strictly stronger than C+OS+□BF+.2; that comparison is not decided by the model below.

## 5. A finite full-action boundary: ordinary separation does not reflect laws

Take the finite preorder with objects r,s,u,v. The root r reaches every object. The object s is a terminal singleton. The objects u and v form a terminal two-point cluster: each reaches both u and v. Apart from reflexivity, these are all the arrows. Regard the preorder as a thin category, with one arrow for each comparable ordered pair, and take singleton individuals at every object.

Use the full relational action-model domains. At r the proposition domain is the full powerset of {r,s,u,v}; at s it is the powerset of {s}; and at either cluster point its future coordinates are {u,v}. Truth is membership of the current object. Transport restricts a future truth profile to the later accessible coordinates; the mutual cluster arrows reindex the same two-coordinate profiles.

Every arrow in a thin category is epic. For any relational type, an arbitrary profile after an arrow extends to a source profile by arbitrary values on the other coordinates; precomposition with the arrow identifies no distinct later coordinate because the arrow is epic. Singleton individual actions are onto as well. Hence all type transports are onto. The full action construction supplies C, and the full epic-Barcan criterion gives BF at every stage, hence necessary BF and necessary Functionality.

The model also has full OS at every stage. To see this directly, choose any future coordinate w of a source x. Define an entire tt profile which at the identity coordinate x observes the arrow x→w and at every other future coordinate observes the identity there. Fullness admits this profile. Each chosen observation arrow acts onto at every type, so Boolean evaluation and the usual universal/existential argument over transported predicates prove every full Good operation identity, on every future input. The observer reads truth at w at its source. Such readers separate distinct proposition intensions; Functionality lifts separation to every relational output type. The same construction works at every object and every finite qualification list. Thus the model satisfies □OS as well as OS.

Consider the universal modal sentence

```math
A:=\forall p^t\,[\Box\Diamond p\to\Diamond\Box p]
\tag{16}
```

It is read using the standard Boolean/native-Box expansion of Diamond. For any proposition p at r, if □◇p is true at r, then ◇p is true at s. Since s is terminal, p is true at s, so □p is true there. That same s witnesses ◇□p at r. Thus A is currently true at r for every admitted p.

At either cluster point choose the proposition whose extension on the cluster is {u}. Diamond p is true at both u and v, so □◇p is true. Box p is false at both, so ◇□p is false. Hence A is false at that accessible cluster, and □A is false at r. We have proved

```math
r\models\mathrm C+\Box\mathrm{BF}
+\Box\mathrm{Functionality}+\Box\mathrm{OS}
+A+\neg\Box A
\tag{17}
```

This is a failure of the reflection schema, and consequently of BoxSep, despite the necessary ordinary logical package. It is not a current-BF transport failure.

For clarity, the model does not satisfy .2 at r. Take p={s}. Then ◇□p is true at r, witnessed at s, but □◇p is false because no cluster point can reach s. Thus (17) does not separate reflection from the stronger lower bundle containing .2. No such strictness claim is made.

## 6. Sources

The two reflection fragments, their finite qualification lists, the proof of (13), and the finite preorder's new modal-reflection verdict are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–5, unpaginated.

The native modality, C's Intensionality and theoremhood-restricted necessitation are Bacon and Dorr, *Classicism*, draft of 16 May 2023, §§1.3–1.5, pp. 13–18; §2.1, pp. 20–22, with the fixed language and notation in [Background](../../source/topics/classicism/background.md). The Good qualification, full typed recovery and smaller .2 proof are retained in [Native-Box logical observers](native-box-logical-observers.md), §§1–3. The endpoint-selector equivalence used in §4 is the linked ordinary research proof, direct source `misc`, §1, unpaginated.

The full action construction is Bacon and Dorr, *Classicism*, §3.5, pp. 58–61; Appendix D, pp. 73–74, as recorded in [Full action models](../../source/topics/classicism/groups/full-action-models.yaml). Its onto-transport Barcan criterion is Proposition 3.24(ii), recorded in [Full epic Barcan](../../source/topics/classicism/arguments/full-epic-barcan.yaml). Those sources supply the semantic framework; the particular four-object preorder and its observer/reflection analysis are specified above.

# Coherent profiles with a term-closed future image

This construction gives C models whose prescribed lower types have full observer separation while a higher type fails BF and Functionality. The [direct Boolean-algebra argument](observer-no-finite-basis-direct.md) supplies the required future image. Sections 1–7 give the full-leaf construction; §8 extends it to Henkin leaves and identifies the exact condition for OS.

## 1. The future hierarchy and its admitted image

Work in ZFC. Let $`L`$ be the full two-valued relational hierarchy over a nonempty individual domain $`A`$:

```math
L_e=A,\qquad L_t=2,\qquad L_{\sigma\tau}=L_\tau^{L_\sigma}.
```

Only arrows with relational output are admitted. Interpret application, abstraction, the Boolean operations and quantifiers classically in $`L`$. Choose nonempty subsets $`N_\sigma\subseteq L_\sigma`$, with $`N_e=L_e`$ and $`N_t=L_t`$, satisfying this closure condition: every finite typed term with parameters in $`N`$ has its **full-$`L`$ denotation** in $`N`$ at its result type. In particular, logical constants belong to $`N`$, and $`N`$ is closed under application and abstraction.

The bound variables in such abstractions range over the full leaf domains. The collection $`N`$ is not assumed elementary and is not interpreted as a separate structure with quantifiers restricted to $`N`$. Its failure to contain an existential witness will be essential. Taking all term denotations from a prescribed set of parameters provides this closure by substitution of finite terms.

## 2. The root and transport

Use two stages $`0\to1`$, with $`L`$ at stage 1. Define the root domains and transport maps recursively:

```math
D_e=A,\qquad q_e(a)=a,\qquad
D_t=2\times2,\qquad q_t(u,v)=v.
```

At an arrow type, put

```math
\begin{aligned}
D_{\sigma\tau}=\{(f_0,f_1):\;&f_0:D_\sigma\to D_\tau,
\quad f_1\in N_{\sigma\tau},\\
&q_\tau(f_0(a))=f_1(q_\sigma(a))\text{ for all }a\in D_\sigma\},\\
q_{\sigma\tau}(f_0,f_1)&=f_1.
\end{aligned}
```

Root application uses $`f_0`$. A root proposition $`(u,v)`$ is currently true exactly when $`u=1`$.

**Image lemma.** At every type, $`q_\sigma[D_\sigma]=N_\sigma`$.

The base cases are immediate. Given $`f_1\in N_{\sigma\tau}`$, application closure gives $`f_1[N_\sigma]\subseteq N_\tau`$. By induction and ordinary metatheoretic Choice, select a section $`s_\tau:N_\tau\to D_\tau`$ of $`q_\tau`$. Then

```math
f_0(a)=s_\tau(f_1(q_\sigma(a)))
```

is a coherent lift. Conversely every admitted profile has its future component in $`N`$ by definition. This proves the lemma and nonemptiness of all root domains. The section is part of the external construction; it asserts no choice principle inside the resulting model.

## 3. Logical operations and lambda closure

Boolean operations on $`D_t`$ are coordinatewise. Their future components are the ordinary leaf operations and belong to $`N`$, so their coherent curried profiles are admitted. For $`F=(F_0,F_1)\in D_{\sigma t}`$, define

```math
Q_\sigma(F)=
\left(
\bigwedge_{a\in D_\sigma}\pi_0(F_0(a)),
\quad\bigwedge_{b\in L_\sigma}F_1(b)
\right).
```

Here $`\pi_0`$ reads current truth, and the meets are ordinary meets of bits. The existential quantifier uses the corresponding joins. The future component is the full leaf quantifier, which belongs to $`N_{(\sigma t)t}`$. Hence these are admitted coherent operation profiles. The future coordinate quantifies over all of $`L_\sigma`$.

Simultaneous induction on terms proves that every allowed abstraction is admitted and term evaluation commutes with transport. For $`\lambda x^\sigma\, .\,T`$, the two components are the functions obtained by evaluating $`T`$ at the root and at the leaf, respectively. The leaf function lies in $`N_{\sigma\tau}`$ by term closure, since its free parameters are transported root parameters and so belong to $`N`$. The induction hypothesis on $`T`$ proves coherence at $`b=q_\sigma(a)`$. Parameters, application and logical constants satisfy the same assertion directly.

Beta and eta are identities of the resulting profiles. Eta retains the whole future component: two arrow objects may have the same current function while differing on future arguments outside the transport image.

## 4. Equality and the exact C soundness check

Interpret the equality constant at each type by its Leibniz expression:

```math
\delta_\sigma(a,b)=
\forall P^{\sigma t}\, .\,(Pa\leftrightarrow Pb).
```

Its value is

```math
\delta_\sigma(a,b)=
\bigl([a=b],\,[q_\sigma(a)=q_\sigma(b)]\bigr),
```

where brackets denote the appropriate bit. The second coordinate follows from the full classical leaf hierarchy. For the first, distinct root objects $`a,b`$ are distinguished by the admitted predicate with constant-1 future component and root function $`x\mapsto([x=a],1)`$. The constant leaf predicate belongs to $`N`$ and this profile is coherent. Thus equality in current truth is actual identity of root objects.

With $`\top=(1,1)`$, the defined modal operation has value

```math
\Box(u,v)=(u\land v,v).
```

At the root, the first-coordinate clauses validate H's ordinary Boolean and quantifier truth conditions. Actual root identity validates reflexivity and substitution; beta and eta hold by the preceding term induction. At the leaf, the ordinary full classical clauses validate the same axioms and rules. Consequently every H theorem has root value $`(1,1)`$ under every root assignment.

To check C, suppose H proves $`B\leftrightarrow C`$. Their root proposition values agree under every root assignment. Their leaf values agree under **every full leaf assignment**, including assignments outside $`N`$. Thus corresponding abstractions have the same root functions and the same complete future functions. Inductively through an argument tuple, their profiles are identical. Their equality is therefore Top. This verifies the original H-theoremhood restriction on Logical Equivalence, without invoking an optional-premise version of that rule.

## 5. Observers at the preserved types

The identity observer and the terminal reader are admitted:

```math
I_0(u,v)=(u,v),\qquad
E_0(u,v)=(v,v),\qquad I_1=E_1=\mathrm{id}_2.
```

Their leaf identities belong to $`N_{tt}`$, and both profiles are coherent. Both preserve the whole Boolean operations. Identity preserves every quantifier.

If $`N_\sigma=L_\sigma`$, the terminal reader preserves the whole quantifier operation:

```math
E\circ Q_\sigma=Q_\sigma\circ E^*_\sigma,
\qquad E^*_\sigma(F)=\lambda x^\sigma\, .\,E(Fx).
```

For a root predicate $`F`$, the left side has both coordinates equal to $`\bigwedge_{b\in L_\sigma}F_1(b)`$. The right side has current coordinate $`\bigwedge_{a\in D_\sigma}F_1(q_\sigma(a))`$ and the same future coordinate. These agree because $`q_\sigma`$ is onto $`L_\sigma`$. The complete future operation components also agree, since the leaf observer is identity on every leaf predicate, including predicates outside $`N_{\sigma t}`$. Thus this is equality of the operation profiles. Existential preservation follows by the same calculation with joins.

The translated equality clauses hold as well. Reflexivity and substitution are H theorems with value Top, and both observers preserve Top; their Boolean laws give the corresponding observed clauses.

## 6. Finite fragments of relational OS

Take finitely many OS instances. Collect their quantifier qualification types and the argument types in their tested relational outputs. Assume $`N_\alpha=L_\alpha`$ at every collected type. Including every type in the elaborated formulas and its subtypes is a sufficient condition.

The same observers $`I,E`$ satisfy every qualification in each list simultaneously. They separate propositions: identity detects different current bits; otherwise the reader detects different future bits.

For relational separation, suppose an arrow has input type $`\alpha`$ with surjective $`q_\alpha`$. If profiles $`f,g`$ have the same current function, coherence gives equal future outputs on the image of $`q_\alpha`$, hence on all of $`L_\alpha`$. Their future functions are equal, so $`f=g`$. Contrapositively, distinct profiles differ at some root argument. Repeat along the finite argument tuple of the tested relational type. The resulting proposition values differ and are distinguished by $`I`$ or $`E`$. Equal objects cannot be distinguished, proving the full separation biconditional.

## 7. A higher failure of BF and Functionality

Suppose there is a future predicate $`F\in N_{\sigma t}`$ with

```math
\{b\in L_\sigma:Fb=1\}\ne\varnothing,
\qquad
\{b\in N_\sigma:Fb=1\}=\varnothing.
```

Term closure supplies $`H_1=\neg F`$. Pair it with the constantly-Top root function $`H_0`$. The profile $`H=(H_0,H_1)`$ is coherent because every transported root argument lies outside $`F`$. Thus

```math
H(a)=\top\quad(a\in D_\sigma),
\qquad Q_\sigma(H)=(1,0).
```

The first fact makes $`\forall x^\sigma\, .\,\Box Hx`$ currently true. The second makes $`\Box\forall x^\sigma\, .\,Hx`$ currently false. Hence BF fails at $`\sigma`$.

There is also a direct failure of Functionality and relational OS. The predicates $`H`$ and constant Top have different future components, yet each root application of either is exactly Top. No observer can distinguish those outputs, even with an empty qualification list. Merely having $`N_\sigma\subsetneq L_\sigma`$ would not establish this failure: the available nonempty predicate $`F`$ with no available member is essential.

Both the [direct Boolean proof](observer-no-finite-basis-direct.md#5-a-nonempty-family-with-no-term-selected-member) and the [alternative forcing proof](observer-no-finite-basis.md#2-a-high-family-with-no-term-definable-member) construct such an $`F`$ while preserving any prescribed bounded-order fragment. The former uses the Henkin extension below. The latter uses a full forcing extension of ZFC and first-order extraction of ground Henkin countermodels retaining the required sentences; extracted models need not retain full leaf domains or standard individuals.

## 8. Henkin leaves and the exact witness condition

The construction also works when $`L`$ is an extensional two-valued Henkin hierarchy:

```math
L_{\sigma\tau}\subseteq L_\tau^{L_\sigma}.
```

Require ordinary application, all parameterized lambda denotations, the classical Boolean operations, quantifiers over each entire specified $`L_\sigma`$, and Leibniz equality agreeing with actual identity. The closure of $`N`$ is now interpreted in this Henkin hierarchy. Root domains still contain all coherent current functions with future component in $`N`$.

The image lemma uses application closure and external sections only. The abstraction induction uses Henkin lambda closure. Admitted identity predicates distinguish leaf objects, while the root separator with constant-true future component remains admitted. The H and C checks use ordinary Henkin truth and the same beta–eta identities. Equality of whole observer operations compares all specified leaf arguments, and relational separation uses extensionality of leaf functions. Thus §§2–7 remain valid under these assumptions.

There is a precise improvement on the sufficient condition $`N_\sigma=L_\sigma`$. Let $`W_\sigma`$ say that every available nonempty leaf predicate has an available witness:

```math
\text{For every }F\in N_{\sigma t},\quad
\bigl(\exists b\in L_\sigma\, .\,Fb=1\bigr)
\ \Longrightarrow\
\bigl(\exists a\in N_\sigma\, .\,Fa=1\bigr).
```

For this construction, the following are equivalent: BF at $`\sigma`$, $`W_\sigma`$, preservation of the whole $`Q_\sigma`$ operation by the terminal reader, and Functionality for predicates of type $`\sigma t`$.

If every root value of a predicate $`H`$ is Top, its future component $`H_1`$ is true on $`N_\sigma`$. Its complement belongs to $`N`$. The witness condition prevents that complement from being nonempty in $`L`$, so $`Q_\sigma(H)=\top`$. This proves BF. Conversely, a failure of $`W_\sigma`$ supplies precisely the counterexample of §7, also refuting predicate Functionality.

For the reader identity, $`E(Q_\sigma H)`$ tests whether $`H_1`$ is true everywhere on $`L_\sigma`$, whereas $`Q_\sigma(E^*_\sigma H)`$ tests whether it is true everywhere on $`N_\sigma`$. Equivalence for all available $`H_1`$ is $`W_\sigma`$ applied to complements. Every available predicate lifts by the image lemma. The future operation components agree on every leaf predicate because $`E_1`$ is identity. This verifies whole-operation identity.

The same witness condition implies Functionality for any relational output $`\tau`$. If profiles $`f,g`$ have equal current functions but different future functions, the predicate $`\lambda x\, .\,f_1(x)\ne g_1(x)`$ belongs to $`N`$ and is nonempty. A witness in $`N_\sigma`$, lifted to a root argument, contradicts coherence. This proves the remaining equivalence and the stronger output claim.

At all types, therefore,

```math
M(L,N)\models\mathrm{OS}
\quad\Longleftrightarrow\quad
M(L,N)\models\mathrm{BF}
\quad\Longleftrightarrow\quad
(\forall\sigma\, .\,W_\sigma)
\quad\Longleftrightarrow\quad N\prec L.
```

Here the type quantifier and $`N\prec L`$ are metatheoretic. For the forward direction, OS entails BF over C. Conversely, all witness conditions make root functions extensional, as just proved. Repeated application reduces distinct relations to distinct propositions; identity and the terminal reader then separate them, with the same reader preserving every requested quantifier.

For elementarity, present $`L`$ as a many-sorted algebra with application, logical constants, and a function symbol for each parameterized lambda term. These last symbols make $`N`$ a substructure by term closure. Truth is equality with 1, and actual equality agrees with typed Leibniz equality. Each finite first-order formula translates to a typed formula whose characteristic predicate belongs to $`N`$ when its parameters do. The conditions $`W_\sigma`$ are exactly the existential-witness requirement in the Tarski–Vaught criterion. Conversely, elementarity supplies a witness for each nonempty available predicate.

These equivalences concern this model construction, not arbitrary C models. The obstruction is a missing witness for an available predicate; merely omitting some leaf objects does not establish it.

## Sources

New construction and soundness argument: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`). The [source manifest](../evidence/source-manifest.json) identifies the original argument and this presentation. The framework and prior observer semantics are described in [Shift models for C + OS](observer-shift-semantics.md). No published action-model theorem is credited with this new restricted-image construction.

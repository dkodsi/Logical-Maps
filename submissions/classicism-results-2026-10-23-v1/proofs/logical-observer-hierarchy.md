# Logical observer separation and its hierarchy

Separation by endpoint-valued logical observers characterizes **C5 + Atomicity**. Reversible separation and separation by observers with finitely many outputs are incomparable restrictions whose conjunction gives the same characterization. In fact, reversible separation needs only **one** qualified observer with finitely many outputs:

$$
\boxed{\mathrm H+\mathsf S_{\mathrm{rev}}
+\exists E\,(\operatorname{Good}_{\{t\}}(E)\land\operatorname{FinIm}(E))
\ \equiv\ \mathrm{C5}+\operatorname{Atomicity}_t.}
$$

Under C5, atoms correspond exactly to endpoint observers qualified at $t$. Reversible separation is equivalent to involutive separation and to its separately boxed schema; it entails C5 and necessary ordinary separation. Factive separation, or ordinary separation with a unique logical observer, gives Extensionality.

Here C5 includes C and the schema $\Box\mathrm{ND}$. All separation principles use the full typed schema defined below. Under C5, Atomicity at $t$ implies Atomicity at every relational type and necessary Actuality. The finite-image condition uses the database's internal definition of finiteness and imposes no uniform bound.

## 1 Definitions and scope

Use the fixed relational language of [Classicism](../source/topics/classicism/background.md): base types $e,t$, and arrow types with relational codomain. An observer is an admitted $E^{tt}$. For a finite set $\Delta$ of admitted types, use $\operatorname{Good}_{\Delta}(E)$ as defined below. Its Boolean clauses are

$$
\begin{gathered}
(\lambda p\, .\,E(\neg p))=(\lambda p\, .\,\neg Ep),\\
(\lambda p,q\, .\,E(p\land q))=(\lambda p,q\, .\,Ep\land Eq),\\
(\lambda p,q\, .\,E(p\lor q))=(\lambda p,q\, .\,Ep\lor Eq).
\end{gathered}
$$

For each $\sigma\in\Delta$, it includes

$$
\begin{aligned}
(\lambda F^{\sigma t}\, .\,E(\forall x^\sigma Fx))
 &= (\lambda F^{\sigma t}\, .\,\forall x^\sigma E(Fx)),\\
(\lambda F^{\sigma t}\, .\,E(\exists x^\sigma Fx))
 &= (\lambda F^{\sigma t}\, .\,\exists x^\sigma E(Fx)),\\
\forall x^\sigma\,E(x=x),&\\
\forall x,y^\sigma\forall F^{\sigma t}\,
 [E(x=y)\to(E(Fx)\to E(Fy))].&
\end{aligned}
$$

The preservation clauses are identities between the displayed operations. Over C the two equality clauses follow from Boolean preservation; over H they remain part of the definition.

Boolean preservation makes $E\top$ true and $E\bot$ false over H; over C it gives $E\top=\top$ and $E\bot=\bot$. The [reduction proof](logical-observer-endpoint-reduction.md) shows that omitting these endpoint identities preserves the full separation theories over H. Standalone qualification can be broader there; with the endpoint-valued range restriction, the observer classes agree already over H. The existing Lean certificate includes the endpoint identities explicitly.

For a fixed additional condition $R(E)$, write

$$
\begin{aligned}
S_{\tau,\Delta}[R]:\quad
\forall X,Y^{\tau}\;\bigl[X=Y\ \leftrightarrow
\forall E^{tt}\bigl(&\operatorname{Good}_{\Delta}(E)\land R(E)\\
&\to\forall\bar z\,(E(X[\bar z])\leftrightarrow E(Y[\bar z]))\bigr)\bigr],
\end{aligned}
$$

where $\tau=\bar\sigma t$; the empty argument tuple gives $\tau=t$. The three relevant conditions are

$$
\begin{aligned}
R(E)&=\top &&\text{ordinary logical separation},\\
\operatorname{End}(E)&:=\forall p\,(Ep=\top\lor Ep=\bot)
 &&\text{outputs restricted to the two endpoints},\\
\operatorname{Fact}(E)&:=\forall p\,(Ep\to p)
 &&\text{factivity}.
\end{aligned}
$$

OS is the full schema of $S_{\tau,\Delta}[\top]$; endpoint separation and factive separation use the corresponding conditions. Types index the schema externally; every $\Delta$ is finite. A boxed schema means its separately boxed, object-variable-closed instances.

Endpoint-valuedness requires each output to equal $\top$ or $\bot$. Necessary truth-correctness, $\Box\forall p(Ep\leftrightarrow p)$, instead identifies $E$ with the identity observer by C's Intensionality at $tt$; its outputs may remain contingent. For example, “It is true that it rains” necessarily agrees with “It rains.” Under Extensionality, identity also becomes endpoint-valued.

A stronger qualification leaves fewer eligible observers, so its separation principle can be stronger. If $\Delta\subseteq\Delta'$, then $S_{\tau,\Delta'}[R]$ implies $S_{\tau,\Delta}[R]$.

Write $I=\lambda p.p$ and $(E\circ F)(p)=E(Fp)$. The additional restrictions are:

| Restriction | Definition |
|---|---|
| Reversible | $\exists F\,(\operatorname{Good}_\Delta(F)\land E\circ F=I\land F\circ E=I)$ |
| Involutive | $E\circ E=I$ |
| Idempotent | $E\circ E=E$ |
| Identity fixing | $(\lambda p,q.E(p=q))=(\lambda p,q.p=q)$ |
| Finitely many outputs | $\operatorname{FinIm}(E)$, defined next |

Every composition equation in this table is an identity of operations. The reversible inverse is admitted and qualified for the same finite list. Write $\mathsf S_{\mathrm{end}},\mathsf S_{\mathrm{rev}},\mathsf S_{\mathrm{fin}},\mathsf S_{\mathrm{fix}}$ for the corresponding full separation schemas.

Put $\operatorname{Im}_E=\lambda r^t.\exists p^t(Ep=r)$ and use the [background definition of finite cardinality](../source/topics/classicism/background.md):

$$
\operatorname{FinIm}(E):=
\exists Z^{(tt)t}\bigl(\operatorname{FiniteCardinality}_t(Z)\land Z(\operatorname{Im}_E)\bigr).
$$

This is a finitary formula. Each finite output list witnesses it, but internal finiteness is not identified with external finiteness in arbitrary Henkin models. The proofs below use the defining induction, so they also cover internal finite images without a standard enumeration. No common cardinal bound is required across observers.

## 2 Factive separation is Extensionality

**Over H, at each fixed relational type and each fixed finite $\Delta$, factive separation is exactly Extensionality at that type.**

If $E$ is qualified and factive, apply its negation identity and factivity to $\neg p$: $\neg Ep\to E\neg p\to\neg p$. Contraposition gives $p\to Ep$; hence

$$
\forall p\,(Ep\leftrightarrow p).
$$

Consequently coextensive relations agree under every such observer. Conversely, the identity observer satisfies every finite qualification and is factive already in H. Agreement under all qualified factive observers therefore implies ordinary coextension. Substituting this equivalence into separation gives

$$
S_{\tau,\Delta}[\operatorname{Fact}]
\ \leftrightarrow\
\forall X,Y^\tau\bigl[(\forall\bar z\,(X[\bar z]\leftrightarrow Y[\bar z]))\to X=Y\bigr].
$$

At $t$, this is the Fregean Axiom. Over **C**, the Fregean Axiom implies full Extensionality: any true proposition is $\top$, so a true universal coextension statement is necessary; C's Intensionality then identifies the relations. Thus one propositional factive-separation instance, even $\Delta=\varnothing$, suffices over C. This upgrade from propositions to arbitrary relation types uses C; the equivalence over H above is stated type by type.

Adding $\operatorname{End}$ to factive separation adds no strength over C. The forward proof still gives Fregean. Conversely, Fregean makes every proposition $\top$ or $\bot$, so the identity observer satisfies End as well as Good and Fact.

This is **Extensionality**, not the database's **Intensionality**. Intensionality identifies necessarily coextensive relations and is already a theorem of C. [Recorded definitions and implication](../source/topics/classicism/results/fregean-axiom-implies-extensionality-r.yaml).

**Uniqueness gives another exact formulation.** Over H, full OS together with $\exists!E\,\operatorname{Good}_{\Delta_0}(E)$ for any one fixed finite list $\Delta_0$ is equivalent to Extensionality. Identity is qualified, so uniqueness makes the observers in that list just identity; its separation instances are precisely Extensionality. Conversely, Extensionality makes every proposition an endpoint; the endpoint truth facts give endpoint fixing, making every qualified observer pointwise identical to $I$, and the operations identical. With endpoint separation as background, uniqueness of its qualified endpoint observer gives the same result: separation makes the sole observer injective, and its endpoint outputs then force every input to be an endpoint.

### Universal factivity is a different assertion

Put $A_\Delta:=\forall E(\operatorname{Good}_\Delta(E)\to\operatorname{Fact}(E))$. Over H, for each fixed $\Delta$,

$$
S_{t,\Delta}[\operatorname{Fact}]
\ \leftrightarrow\ \mathrm{Fregean}
\ \leftrightarrow\ S_{t,\Delta}[\top]+A_\Delta.
$$

For the last converse, all eligible observers preserve current truth, so separation gives Fregean. In the other direction, Fregean gives $p=\top$ when $p$, and $p=\bot$ otherwise. Since $E\top$ is true and $E\bot$ is false, substitution gives $Ep\leftrightarrow p$, proving $A_\Delta$; identity supplies separation.

For the full typed schemas, **OS plus one $A_{\Delta_0}$** is equivalent over H to full Extensionality. Use the OS instances at the chosen $\Delta_0$ for every relational type. Requiring $A_\Delta$ for all finite lists adds nothing to that package.

Universal factivity alone is much weaker. In the qualitative-contrast model at $W_0$, let $d$ contain all arrows into $W_1$, and $a=\neg d$. The [Boolean-observer obstruction](observer-countermodel.md), §4, proves that every admitted Boolean observer rejects $d$. Its truth map $h_E(p)=v(Ep)$ is Boolean, so $h_E(d)=0$ and $h_E(a)=1$. Target symmetry gives

$$
\neg p\Rightarrow p\le d,\qquad p\Rightarrow a\le p.
$$

Monotonicity yields $h_E(p)=v(p)$. Thus **every Boolean observer is factive**, although $d\ne\bot$ and no such observer distinguishes them. OS and Extensionality fail. This is also why truth-correctness of observers cannot replace the separation requirement.

## 3 Endpoint separation is C5 plus Atomicity

**Over C, the single instance $S_{t,\{t\}}[\operatorname{End}]$ is equivalent to C5 + Atomicity at $t$, to full typed endpoint separation, and to its separately boxed schema.** Any single finite list containing $t$ gives the same equivalence.

**Necessary distinctness.** If $p\ne q$, separation supplies an observer with outputs of different truth values. End makes those outputs opposite endpoints. NI makes their endpoint identities necessary. Necessitate the unconditional C theorem that opposite endpoint outputs entail distinct inputs, and apply normality. This gives $\Box(p\ne q)$. Thus $\mathrm{ND}_t$ holds. No qualification premise or existential witness was necessitated.

**Atomicity.** Given $d\ne\bot$, separate $d$ from $\bot$ by $E$, so $Ed$ is true. Set

$$
w_E:=\forall p^t\,(Ep\to p).
$$

End and the derived endpoint identities give $E(Ep)=Ep$ at every current input. Apply the universal operation identity at $t$ to $\lambda p\, .\,Ep\to p$, then use Boolean preservation:

$$
Ew_E\ \leftrightarrow\ \forall p\,(E(Ep)\to Ep).
$$

The right side is true, so $Ew_E=\top$ and $w_E\ne\bot$. Necessary universal instantiation, an unconditional C theorem, gives

$$
w_E\le(Ep\to p).
$$

If $Ep=\top$, substitution gives $w_E\le p$. Otherwise negation preservation gives $E\neg p=\top$, hence $w_E\le\neg p$. A nonbottom proposition deciding every proposition is an atom. Since $Ed=\top$, it lies below $d$.

**C5.** The same separation instance gives $\mathrm{BF}_t$. If every $Fp=\top$, each eligible observer sends every $Fp$ to $\top$; universal preservation makes its output on $\forall p\,Fp$ true. Separation from $\top$ yields $(\forall p\,Fp)=\top$. Now use the recorded implications

$$
\mathrm{ND}_t+\mathrm{BF}_t
\ \Rightarrow\ \Box\mathrm{ND}_t
\ \Rightarrow\ \Box\mathrm{ND}_{\text{all types}}.
$$

The first uses NI, ND and 4 to obtain each necessary ND instance, then twice uses $\mathrm{BF}_t$ to collect its two proposition arguments. The second is the necessary form of C's type-$t$-to-all-types ND implication. These are [Propositions 2.4](../source/topics/classicism/results/nd-t-and-bf-t-imply-necessary-nd-t.yaml) and [2.2](../source/topics/classicism/results/necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r.yaml) in the recorded form.

**Converse.** Assume C5 and Atomicity at $t$. For unequal $p,q$, choose an atom $a$ below their Boolean symmetric difference. C5 supplies $\Box\mathrm{BF}$, so the [composite atom-observer theorem](operator-representation.md), §§2–3, gives a qualified separating observer for each chosen finite $\Delta$:

$$
O_a(r)=(\Diamond a\land\Box(a\to r))\lor(\neg\Diamond a\land r).
$$

ND makes the atom necessarily nonbottom, so $\Diamond a=\top$; this observer is the principal operation $E_a(r)=\Box(a\to r)$. Atomhood gives $a\le r$ or $a\le\neg r$. In the first case, 4 makes $E_a(r)=\top$. In the second, NI preserves $a\le\neg r$, and necessary nonbottomness of $a$ excludes $a\le r$ necessarily, giving $E_a(r)=\bot$. Thus the already-qualified observer satisfies End. The same observer handles every type in the finite list.

C5 supplies BF and hence Functionality. Propositional separation therefore lifts to full relational separation: identify the values at each argument tuple, then apply Functionality successively. C5 persists by 4, and C5 + Atomicity implies necessary Atomicity. Necessitating each discharged finite implication gives the separately boxed endpoint-separation instances. This proves the claimed equivalences without Actuality.

Finally, over **H**, full typed endpoint separation implies full OS by inclusion of observer classes. The canonical H-to-C argument gives C + BF, after which the preceding proof applies. The converse just proved gives

$$
\boxed{\mathrm H+\text{full typed endpoint separation}
\ \equiv\ \mathrm{C5}+\operatorname{Atomicity}_t.}
$$

The full typed schema is used in the recovery of C from H. The reduction to the single propositional $\{t\}$ instance is asserted over C.

### Atoms and endpoint observers

**Under C5, there is a bijection between propositional atoms and endpoint observers qualified at $\{t\}$:**

$$
a\longmapsto E_a,\qquad E_a(p)=\Box(a\to p);
\qquad
E\longmapsto a_E=\forall p(Ep\to p).
$$

No global Atomicity or Actuality premise is needed. The diagonal proof above shows that $a_E$ is an atom for any such $E$: $Ea_E=\top$, so it is nonbottom, and it decides every proposition. The principal-observer argument supplies $E_a$ from any atom under C5 and qualifies it at every finite type list.

If $Ep=\top$, then $a_E\le p$; if $Ep=\bot$, then $a_E\le\neg p$. Consequently $E_{a_E}p=Ep$ at every input, and Functionality identifies the operations. Conversely, $E_a(a)=\top$, so $a_{E_a}\le a$; both are nonbottom atoms and therefore equal. In particular, endpoint qualification at $t$ already gives qualification at every finite list under C5.

The natural-language interpretation is evaluation at a fixed complete possible scenario: $E_a(p)$ asks whether that scenario entails $p$. In a constant-domain possible-worlds interpretation this is “At that fixed world, $p$.” Endpoint-valuedness does not require the scenario to be actual.

## 4 Identity fixing and reversible separation

### Fixing identity adds exactly C5

Over H with the full typed schema,

$$
\mathsf S_{\mathrm{fix}}\ \equiv\ \mathrm{C5}+\mathrm{OS}.
$$

First recover C + BF by forgetting the restriction. If $p\ne q$, all eligible observers send $(p=q)$ to its false self and send $\bot$ to $\bot$. Separation gives $(p=q)=\bot$, hence $\Box(p\ne q)$. Thus $\mathrm{ND}_t$ holds, and $\mathrm{ND}_t+\mathrm{BF}_t$ yields C5. Conversely, C5 makes every identity proposition an endpoint, so every Boolean observer fixes it. NI, BF and Intensionality give the displayed composite identity. Under C, the equivalent necessity-fixing condition is $(\lambda p.E(\Box p))=(\lambda p.\Box p)$, using $(p=q)=\Box(p\leftrightarrow q)$. This is fixing necessity judgments, rather than the different equation $E(\Box p)=\Box(Ep)$.

### Boolean patching preserves qualification

Suppose $E_1,\ldots,E_k$ are qualified for $\Delta$ and $c_1,\ldots,c_k$ are a finite Boolean partition of $\top$. Then

$$
T(p)=\bigvee_{i=1}^k(c_i\land E_i p)
$$

is qualified for $\Delta$. Boolean identities follow by distribution through the disjoint partition. For each listed quantifier, distributing its fixed guards and using the identities of the $E_i$ gives the quantifier law.

For the composite identity requirement, work over C, where Good is equivalent to its finite conjunction of operation identities and therefore persists by NI. The universally closed guard-distribution theorem is an unconditional C theorem. Necessitate it and use the persistent qualification and partition identities; Intensionality then identifies the composite operations. This does not apply Equivalence to a biconditional proved only under the partition assumptions. In every separation application here, full OS has already supplied C + BF, which also allows NI and BF to collect pointwise operation identities.

### Reversibility gives C5

Let $E$ have qualified inverse $F$. It preserves the truth of identity propositions. For the nontrivial direction, use the translated Leibniz clause at type $t$ with the predicate $P(z)=F(x=z)$. From $E(x=y)$ and $E(Px)=x=x$, obtain $E(Py)=x=y$. The converse follows by substitution and translated reflexivity. With a list containing $t$, reversible separation therefore identifies every false equality proposition with $\bot$, just as above. It follows that

$$
\mathsf S_{\mathrm{rev}}\ \Longrightarrow\ \mathrm{C5}+\mathrm{OS}.
$$

C5 subsequently makes these identity-preservation statements full identities.

### Reversible witnesses can be involutions

Suppose $d\ne\bot$. If $d$ is true, identity already distinguishes it from $\bot$. Otherwise choose a reversible $E$ with $Ed$ true, and let $F=E^{-1}$. Set

$$
c=\neg d\land Ed,\qquad b=Fc,\qquad r=\neg(c\lor b),
\qquad
T(p)=(c\land Ep)\lor(b\land Fp)\lor(r\land p).
$$

Boolean preservation gives $c\land Ec=\bot$ and, after applying $F$, $c\land b=\bot$. Also $Eb=c$. Applying the patching lemma, $T$ is qualified. Expansion on the three pieces proves $T^2p=p$: on $c$, the second application passes through the $b$-piece and uses $EF=I$; on $b$, it passes through $c$ and uses $FE=I$; on $r$, it is identity. Functionality upgrades this to $T\circ T=I$. Currently $c$ is true, so $Td$ is true. Apply the construction to the Boolean symmetric difference to separate any unequal inputs. The converse uses an involution as its own inverse:

$$
\mathsf S_{\mathrm{rev}}\ \equiv\ \text{involutive separation}.
$$

### Endpoint separation supplies reversible witnesses

C5 + Atomicity supplies a true atom $w$ by [Atomicity with BF implies necessary Actuality](../source/topics/classicism/results/atomicity-t-and-bf-imply-necessary-actuality.yaml). Given a false nonbottom $d$, choose an atom $a\le d$; then $a\ne w$. Let $A=E_a$ and $W=E_w$ be the qualified endpoint observers. Define

$$
T(p)=(a\land Wp)\lor(w\land Ap)\lor(\neg(a\lor w)\land p).
$$

The partition lemma qualifies $T$. Endpoint laws give $A(Wp)=Wp$ and $W(Ap)=Ap$. Atomhood gives $a\land Ap=a\land p$ and $w\land Wp=w\land p$. Hence $A(Tp)=Wp$, $W(Tp)=Ap$, and expansion gives $T^2p=p$. Functionality identifies the composite with $I$. Since $w$ and $Ad$ are true, $Td$ is true. For true $d$ use identity. Thus endpoint separation implies involutive, and hence reversible, separation.

### Reversible separation entails its boxed form

Fix a closed separation instance $P=S_{\rho,\Delta}[K]$, where $K$ is either ordinary qualification or reversible qualification. Choose a finite list $\Lambda$ containing $\Delta$, $\rho$, $tt$, and the argument types of $\rho$. For every reversible $\Lambda$-qualified $E$, we have

$$
EP\leftrightarrow P.
$$

To verify this, distribute $E$ through the displayed quantifiers and Boolean connectives. Under C5 it fixes identity propositions. Ordinary qualification is equivalent to a finite conjunction of operation identities, so $E$ fixes its truth. Reversible qualification adds an existential inverse of type $tt$ and identities of compositions; the $tt$ quantifier law fixes its truth too. Postcomposition $B\mapsto E\circ B$ bijects the ordinary $\Delta$-qualified class, and also the reversible class, with inverse $B\mapsto E^{-1}\circ B$. It changes each observed agreement precisely to its $E$-image. Reindexing this quantified class proves the claimed equivalence.

Under full reversible separation, $P$ is true for either class. Every reversible $\Lambda$-observer therefore agrees on $P$ and $\top$. Separation gives $P=\top$, which is $\Box P$. Each instance uses its own finite $\Lambda$:

$$
\mathsf S_{\mathrm{rev}}\ \equiv\ \Box\mathsf S_{\mathrm{rev}},
\qquad
\mathsf S_{\mathrm{rev}}\ \Longrightarrow\ \mathrm{C5}+\Box\mathrm{OS}.
$$

Boxes mean separately boxed instances. No converse from C5 + necessary OS is established here.

## 5 Observers with finitely many outputs

**Under C5, every finite-image observer qualified at $t$ yields an endpoint observer qualified at $t$. A separating finite-image family therefore yields endpoint separation.**

The image of a Boolean observer is a Boolean subalgebra. The internal finite-cardinality induction proves that every nonempty admitted subset of a finite partially ordered set has a minimal element. For completeness, use as induction property of a cardinality $Z$: every $X$ with $ZX$ has that property. The zero case is vacuous. For a successor, delete its distinguished element $y$. If the chosen subset has no remaining member, $y$ is minimal. Otherwise take a minimal remaining $m$ by induction; choose $y$ if it belongs to the subset and $y<m$, and retain $m$ otherwise. Transitivity verifies minimality. Comprehension admits this induction predicate. This uses no choice or assumption that internal finite cardinalities are standard numerals.

Given a nonbottom output $Ed$, apply this lemma to the nonzero image elements below $Ed$. It gives an atom $b$ of the image, with $b\le Ed$. This is a relative image atom, not yet an atom of the whole proposition algebra. It decides every output: $b\le Ep$ or $b\le\neg Ep$. Put

$$
F(p)=\Box(b\to Ep).
$$

C5 keeps $b$ nonbottom necessarily. In the first decision case, 4 makes $Fp=\top$; in the second, NI preserves $b\le\neg Ep$, and stable nonbottomness gives $Fp=\bot$. Thus $F$ has endpoint outputs. The relative atom decisions verify its pointwise Boolean identities. NI, BF and Intensionality upgrade them to composite identities.

For a listed type $\sigma$, qualified universal preservation and BF/CBF give the identity

$$
\Box\bigl(b\to E(\forall x^\sigma Xx)\bigr)
=
\forall x^\sigma\Box(b\to E(Xx)).
$$

More explicitly, substitute the universal law of $E$, distribute the fixed antecedent through the quantifier, and use BF to commute necessity with that quantifier. Necessary BF and persistent Good give the identities between the composite operations on $X$; existential preservation follows by Boolean duality. Consequently $F$ retains each listed qualification. Since $Fd=\top$, it distinguishes $d$ from $\bot$.

This proves, using the endpoint characterization,

$$
\boxed{\mathrm{C5}+\mathsf S_{\mathrm{fin}}
\ \equiv\ \mathrm{C5}+\operatorname{Atomicity}_t
\ \equiv\ \mathsf S_{\mathrm{end}}.}
$$

The converse uses the finite image $\{\top,\bot\}$. The proof works for each fixed finite output list as well as for the internal finiteness formula, and requires no common bound across witnesses.

## 6 One observer suffices alongside reversibility

Reversible separation forces a dichotomy: **the proposition algebra is atomless, or it is atomic and has a true atom.**

If there is an atom $a$, separation from $\bot$ gives an automorphism $E$ with $Ea$ true. A Boolean automorphism preserves atomhood, so $w=Ea$ is a true atom. For any nonbottom $d$, choose a reversible $F$ with $Fd$ true. A true atom lies below every true proposition, hence $w\le Fd$. Therefore $F^{-1}w$ is an atom below $d$. This proves Atomicity. Conversely, a true atom supplies Actuality because it lies below every true proposition.

Combining this argument with the representation and finite-image results gives the following equivalences over H:

$$
\begin{aligned}
\mathsf S_{\mathrm{end}}
&\equiv \mathsf S_{\mathrm{rev}}+\exists a\,\operatorname{Atom}_t(a)\\
&\equiv \mathsf S_{\mathrm{rev}}+\operatorname{Actuality}\\
&\equiv \mathsf S_{\mathrm{rev}}+
 \exists E\,(\operatorname{Good}_{\{t\}}(E)\land\operatorname{End}(E))\\
&\equiv \mathsf S_{\mathrm{rev}}+
 \exists E\,(\operatorname{Good}_{\{t\}}(E)\land\operatorname{FinIm}(E))\\
&\equiv \mathsf S_{\mathrm{rev}}+\mathsf S_{\mathrm{fin}}\\
&\equiv \mathrm{C5}+\operatorname{Atomicity}_t.
\end{aligned}
$$

For the single finite-image witness, apply §5 with $d=\top$ to obtain an endpoint observer, then §3 to obtain its diagonal atom. The reversible class spreads that one atom throughout the algebra. In the reverse direction endpoint separation supplies reversible separation and an endpoint observer. **The single witness need not itself separate propositions.**

There is a corresponding uniqueness result. Under reversible separation, a unique $\{t\}$-qualified endpoint observer means a unique atom. The dichotomy then gives an atomic algebra with one atom, which must be $\top$. Thus

$$
\mathrm H+\mathsf S_{\mathrm{rev}}
+\exists!E\,(\operatorname{Good}_{\{t\}}(E)\land\operatorname{End}(E))
\ \equiv\ \operatorname{Extensionality}.
$$

Without separation, one endpoint observer can correspond to a sole atom alongside an atomless remainder, as at qualitative contrast $W_0$.

## 7 Strict comparisons and their witnesses

The following two chains are strict at every displayed arrow:

$$
\operatorname{Extensionality}
\ \Longrightarrow\ \mathsf S_{\mathrm{end}}
\ \Longrightarrow\ \mathsf S_{\mathrm{rev}}
\ \Longrightarrow\ \mathrm{C5}+\mathrm{OS},
$$

$$
\mathsf S_{\mathrm{end}}
\ \Longrightarrow\ \mathsf S_{\mathrm{fin}}
\ \Longrightarrow\ \mathrm{OS}.
$$

Reversible separation and finite-image separation are incomparable. Their witnesses use the existing constructions, with the following observer calculations.

| Construction and evaluation | Relevant verdicts and reasons |
|---|---|
| [Full action model: two-element group](../source/topics/classicism/models/full-involution-group.yaml), sole object | C5 + Atomicity, hence endpoint separation, while Extensionality fails. |
| [Finite-support action model: permutations of N](../source/topics/classicism/models/finite-support-permutations.yaml), sole object | The [permutation construction](observer-models.md), §3, gives qualified inverse pairs $E_\pi,E_{\pi^{-1}}$ that separate. The algebra is atomless. Thus reversible separation holds and finite-image separation fails by §5. |
| [Qualitative contrast at $W_1$](local-observers.md), §§2–4 | C5 + OS holds. The $W_0$-target proposition $A$ is its unique atom and is false at $W_1$; the complementary $W_1$ component is atomless. Every Boolean automorphism fixes $A$, so reversible separation fails. |
| [Full action model: two-object chain](../source/topics/classicism/models/full-two-object-chain.yaml), at $W_0$ | Atomicity and necessary BF give full OS by the [atomic observer theorem](operator-representation.md), §2. Its propositional domain is finite, so every observer has finite image. ND fails, hence reversible and endpoint separation fail. |

The finite-image and reversible restrictions may be witnessed by different observers. Requiring one observer to satisfy both restrictions is a different condition.

The previously established boxed hierarchy is also strict at every arrow over C:

$$
\underbrace{\mathrm{Extensionality}}_{\text{factive separation}}
\ \Longrightarrow\
\underbrace{\mathrm{C5}+\operatorname{Atomicity}_t}_{\text{endpoint separation}}
\ \Longrightarrow\ \Box\mathrm{OS}
\ \Longrightarrow\ \mathrm{OS}
\ \Longrightarrow\ \mathrm{BF}.
$$

| Converse that fails | Model and evaluation point | Reason |
|---|---|---|
| Endpoint separation implies Extensionality | [Full action model: two-element group](../source/topics/classicism/models/full-involution-group.yaml), sole object | It satisfies C5 and Atomicity. Its four propositions include distinct propositions with the same current truth value. |
| Necessary OS implies endpoint separation | [Finite-support action model: permutations of N](../source/topics/classicism/models/finite-support-permutations.yaml), sole object | Admitted permutation observers satisfy the composite laws and separate at every evaluation; the proposition algebra is atomless. |
| OS implies necessary OS | [Qualitative contrast at $W_1$](local-observers.md), §§2–5 | Full OS holds there, while accessible $W_0$ fails even Boolean separation. |
| BF implies OS | [Qualitative contrast at $W_0$](observer-countermodel.md), §§2–4 | C5, Actuality and necessary BF hold, but every eligible observer rejects the nonbottom $W_1$-target proposition. |

The first implication also follows directly by using the identity observer: Extensionality makes it endpoint-valued. Necessary OS implies necessary BF as well as BF. Whether **OS alone entails necessary BF** remains unsettled in the current synthesis.

## 8 Other useful distinctions

**Boolean versus logical preservation is substantive.** Boolean separation is the propositional $\Delta=\varnothing$ comparison. In the [two-object retract model](observer-models.md), §2, the identity and the admitted observer with components

$$
E_W(b,c)=(c,c),\qquad E_V(a,b,c)=(a,c,c)
$$

satisfy the composite Boolean identities and separate at $W$, while $\mathrm{BF}_t$ fails. Thus Boolean separation does not give logical separation. Conversely, qualitative contrast at $W_0$ satisfies necessary BF but fails Boolean separation. These two lower conditions are incomparable. The [ordered/unrestricted-role construction](ordered-observers.md), §§2–4, using its stated ZFC metatheory, gives the stronger comparison: even C5, necessary BF and necessary Boolean separation do not supply quantifier separation at $e$. These are comparisons, not additional proposed candidate entries.

**Finite quantifier qualification specifies which admitted families an observer must handle.** It does not assert preservation of intersections indexed by arbitrary external subsets. In the endpoint argument, the decisive admitted family is $p\mapsto(Ep\to p)$: preservation at $t$ forces acceptance of its diagonal, hence an atom. An alternative formulation using algebraic meets would have to ensure that the relevant kernel meet exists and is admitted; preservation of whatever meets happen to exist does not ensure that.

**Necessary qualification adds nothing to Good over C.** Remove the redundant equality clauses and call the remaining finite conjunction of operation identities $B_\Delta(E)$. NI and finite modal distribution give $B_\Delta(E)\to\Box B_\Delta(E)$; T gives the converse. The unconditional C equivalence $B_\Delta(E)\leftrightarrow\operatorname{Good}_\Delta(E)$, together with its necessitation, yields

$$
\operatorname{Good}_\Delta(E)\leftrightarrow\Box\operatorname{Good}_\Delta(E).
$$

Thus replacing Good by necessary Good leaves separation unchanged. Boxing the separation instance itself is stronger, as the $W_1/W_0$ example proves. This collapse concerns Good; no unconditional persistence of the additional Fact or End predicates is assumed.

**Existence, correctness and separation have different roles.** A qualified factive observer always exists: the identity. A correct evaluator with outputs in $\{\top,\bot\}$, without imposing Good, satisfies

$$
\operatorname{Correct}(B):=\forall p\,[(p\to Bp=\top)\land(\neg p\to Bp=\bot)].
$$

Over C,

$$
\exists B\,\operatorname{Correct}(B)
\quad\leftrightarrow\quad \mathrm{Actuality}+\mathrm{ND}_t.
$$

For the forward direction, $w_B=\forall p(Bp\to p)$ is true and necessarily entails each true $p$, giving Actuality. If $p\ne q$, correctness gives $B(p=q)=\bot$ and $B\top=\top$. NI preserves these output identities. The unconditional C implication $p=q\to(p=q)=\top$ excludes equality at any accessible point, giving $\mathrm{ND}_t$. Conversely, an Actuality witness is a true atom; ND makes it necessarily nonbottom, and its principal operation $B(p)=\Box(w\to p)$ has the required values. This equivalence does not include composite preservation in Correct.

Even a qualified, correct endpoint evaluator need not belong to a separating class. At qualitative contrast $W_0$, the principal observer of the actual atom is such an evaluator, while every Boolean observer is factive and separation fails. Adding factivity to a **separating** class instead forces Extensionality, as §2 proves.

### Idempotent witnesses are always sufficient

Full OS is equivalent to separation by idempotent observers. For unequal $p,q$, let $d=(p\leftrightarrow q)$ and choose a qualified $E$ with $Ed$ false; such an $E$ exists by separation and Boolean preservation. Put

$$
c=d\land\neg Ed,\qquad
F(r)=(c\land Er)\lor(\neg c\land r).
$$

Patching preserves qualification. Since $Ec=Ed\land\neg E^2d$, we have $c\land Ec=\bot$. Expansion gives $F^2r=Fr$, while $Fd=d\land Ed$ is false. Thus $F$ still distinguishes $p,q$. Under full OS, Functionality upgrades pointwise idempotence to the operation identity. This is a normalization of separating witnesses, so idempotence supplies no additional separation strength.

### Conjunction and universal observers

Separation by observers that accept $\top$ and preserve conjunction gives its meet order; universal observers give indexed greatest lower bounds. Requiring the same observers to preserve both is strictly stronger than the two separate separation principles. A four-proposition model separates them even with BF, CBF and Functionality. Over C, universal separation and joint separation are both equivalent to the corresponding unboxed BF instances for each finite type list. See [Conjunction and quantifier separation](meet-quantifier-separation.md), §§2–5, for the proofs and exact type scope.

### Further observer comparisons

[Relations among observer principles](observer-lattice.md) gives the connective and identity-fixing branches, the sufficient condition C + Atomicity (type t) + BF for OS, and the strict comparisons above C + BF. The [two model constructions](observer-lattice-models.md) show that finite-image separation is incomparable with both C + Atomicity (type t) + BF and ☐OS. Reversible separation is [strictly stronger than C5 + ☐OS even in atomless models](h-observer-space/finite-block-symmetry-reversible-gap.md). [One atom](h-observer-space/necessary-separation-and-atoms.md) gives endpoint separation, while [reversibility implies No Pure Contingency](h-observer-space/reversible-separation-and-pure-truth.md) without atoms. [OS does not imply ☐BF or ☐Functionality](h-observer-space/logical-separation-with-contingent-barcan.md).

## Sources

The observer characterizations and new deductions in this note are ordinary mathematical arguments by Codex, prompted by Daniel Kodsi, 23–24 October 2026; direct source `misc`, this note §§2–8, unpaginated. The canonical OS definition and established observer/model arguments are linked at their uses. Background record implications were checked using `load_topic` and a proved-only `Engine` with empty background and optional assumptions explicit in the premise sets.

Published background locators retained from the records: Bacon–Dorr, *Classicism*, draft of 16 May 2023, §§1.3–1.5, especially Extensionality and Intensionality pp. 15–18; Propositions 2.2–2.4, pp. 22–23; Propositions 2.6–2.7, pp. 25–26; full action models §3.5, pp. 59–61; permutation and qualitative-contrast models Appendix D, pp. 74–79. The new observer claims are not attributed to those sources. The ordered comparison uses the external fixed-point theorem and model construction documented in its linked proof.

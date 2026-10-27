# Reversible separation between propositions

Source: *Pointwise reversible separation and the scope of necessity*, 26 October 2026, §2 (`misc`, unpaginated). The argument is in the fixed relational theory C. The existing [involutive normalization](logical-observer-hierarchy.md#reversible-witnesses-can-be-involutions) supplies the converse direction.

## 1. A single sentence for Rev

Write $`I:=\lambda p^t\, .\,p`$ and $`E\circ F:=\lambda p^t\, .\,E(Fp)`$. Put

```math
J(E):=\bigl((\lambda p,q^t\, .\,E(p\land q))
=(\lambda p,q^t\, .\,Ep\land Eq)\bigr)\land E\circ E=I
```

**Theorem.** Over C, full reversible logical separation is equivalent to

```math
\forall p,q^t\, .\,\Bigl[\forall E^{tt}\, .\,
J(E)\to(Ep\leftrightarrow Eq)\Bigr]\to p=q
```

An observer preserves conjunction and undoes itself when applied twice. These are identities of whole operations. Boolean and quantifier preservation, BF and separation at every relational type follow; none is an extra premise.

## 2. Why the two laws preserve every quantifier

For each admitted type σ, define

```math
c(b):=\lambda x^\sigma\, .\,b,\qquad
L_E(F):=\lambda x^\sigma\, .\,E(Fx),\qquad
Q(F):=\forall x^\sigma\, .\,Fx
```

C proves the adjunction

```math
c(b)\le F\quad\longleftrightarrow\quad b\le Q(F)
```

The order is Boolean entailment at the indicated relational type. The two sides are respectively equivalent to $`\Box\forall x^\sigma\, .\,(b\to Fx)`$ and $`\Box(b\to\forall x^\sigma\, .\,Fx)`$. The intervening equivalence is an unconditional H theorem. This argument does not require Q(F) to be the greatest lower bound of the currently quantified values of F, which would require additional assumptions.

Assume J(E). Substitution into lambda contexts and βη conversion give the same conjunction and involution identities for L_E and the identity $`L_E\circ c=c\circ E`$. Consequently E and L_E are order automorphisms and their own inverses. For all b and F,

```math
\begin{aligned}
b\le Q(L_EF)
&\leftrightarrow c(b)\le L_EF
\leftrightarrow L_E(c(b))\le F\\
&\leftrightarrow c(Eb)\le F
\leftrightarrow Eb\le QF
\leftrightarrow b\le E(QF)
\end{aligned}
```

Antisymmetry gives $`Q(L_EF)=E(QF)`$. Thus universal quantification is preserved pointwise at every type. The order characterizations of Top, Bottom, joins and complements likewise give preservation of the Boolean operations; existential preservation follows by duality.

To obtain identities of the whole preservation operations, discharge J(E), universally close the C theorem and necessitate that theorem. CBF allows E to be instantiated under the box. Since J(E) is a conjunction of identities, Necessity of Identity gives $`J(E)\to\Box J(E)`$. Modal reasoning therefore gives the necessary universal closure of the pointwise identity under J(E). Intensionality identifies the corresponding whole operations. This uses neither BF nor Functionality, and it does not apply Logical Equivalence to a proof with an undischarged optional assumption.

The observed equality laws follow from Boolean preservation over C: apply E to the C identities identifying H-valid reflexivity and substitution formulas with Top. Hence every J-observer qualifies at every finite list of types and has itself as a qualified inverse.

## 3. From proposition separation to full separation

Assume the displayed separation sentence. For any type σ and predicate F, suppose every Fx is Top. Every J-observer fixes Top and preserves the universal quantifier. Its output on $`\forall x^\sigma\, .\,Fx`$ is therefore true, as is its output on Top. Separation forces

```math
(\forall x^\sigma\, .\,Fx)=\top
```

This proves BF at σ. The [established BF-to-Functionality argument](logical-observers.md#4-a-simpler-formulation-over-c) now gives Functionality at every relational output type.

Suppose two relations are indistinguishable, at every argument tuple, by all J-observers. Propositional separation identifies their values at each tuple. Iterating Functionality identifies the relations. Thus J-observers separate at every relational type. Section 2 shows they are qualified reversible observers at every finite list, yielding full Rev.

Conversely, full Rev supplies separating logical observers which are involutions by the existing Boolean patching construction. Each preserves conjunction, hence satisfies J. Its propositional instance gives the displayed sentence.

## 4. Scope

The theorem needs only C and separation between propositions. The conjunction and involution assumptions remain identities of whole operations. Replacing them by their currently quantified pointwise identities gives a different, weaker qualification. Over H, use the full relational logical-observer schema until C has been recovered.

# Infinity makes the core number map an isomorphism

22 October 2026. Ordinary mathematical refinement by OpenAI Codex; direct source `misc`. No independent or formal verification claim. Original arguments: [Actuality world slice, §5](../notes/actuality-world-slice-core.md#5-exact-quantified-infinity-transfer) and [Gallin core, §7](../notes/gallin-extensional-core.md#7-exact-quantified-infinity-transfer-under-gc).

## Before and after

The original core-transfer proofs construct a map h from ambient Frege numbers onto the core Frege numbers and transfer the quantified Infinity axiom. They deliberately do not assert injectivity.

**Refinement.** Under **Actuality + quantified Infinity_e**, the world-slice map h is a definable bijection on the number fields, preserving literal numerical identity, zero, successor, and the usual arithmetic graphs. Under **Gallin Comprehension + quantified Infinity_e**, the same conclusion holds for the Gallin core's h. Neither result needs Choice, BF, or boxed assumptions. This is a current isomorphism, not a necessary isomorphism or an assertion that arbitrary ambient cardinality objects are identified by their extensions.

## 1. The common setup

Let ν=(et)t and N=FiniteCardinality_e. Both original constructions provide:

* a core property field P over **all current individuals**;
* for every ambient property X, a core property X° with the same current extension;
* a core cardinality field and a represented map h, satisfying, for Y∈P,

      h(Z)(Y) is currently true iff Z(Y) is currently true;      (1)

* h(0)=0_c, and h(SZ)=S_c(hZ) for every ambient natural Z;
* h maps N onto the core number field N_c.

For the slice, X°=w∧X, where w is the actual atom, and h(Z)(Y)=w∧P(Y)∧Z(Y). For the Gallin core use its actualizer Λ: X°=Λ_et(X) and h(Z)=Λ_ν(λY.P(Y)∧Z(Y)). The original proofs verify support, comprehension, the successor equation, and surjectivity. In the Gallin case successor commutation is asserted only for coextension-invariant cardinalities, which includes all N-members; this restriction is preserved here.

## 2. The short injectivity argument

Two elementary ambient facts are used:

    N(n) and current coextension of X,Y imply nX ↔ nY;         (2)
    N(m), N(n), and mX∧nX imply m=n.                           (3)

Equation (2) is induction on finite cardinalities. Equation (3) is the current consequence of finite-cardinality exclusivity from the recorded arithmetic lemmas. They concern literal identity of number objects, not identity of their argument properties.

Quantified Infinity_e implies that **every** ambient n∈N has a current instance X with nX. For completeness, induct on n. Zero is witnessed by the empty property. Given nX, X cannot be universal, since (2) would give n⊤, contradicting quantified Infinity. Choose one a outside X. Then (X+a)−a is coextensive with X, so (2) and the successor definition make X+a an instance of Sn. This is induction proving existential statements, with no operation choosing an instance for every n.

Suppose now m,n∈N and h(m)=h(n). Realize m at X, and normalize X to X°∈P. By (2), mX°. By (1), h(m)(X°) is true, hence h(n)(X°) is true, and nX° follows. Equation (3) gives m=n. Thus h is injective on N. The original surjectivity theorem makes it a bijection. ∎

The inverse is the admitted graph

    Inv(Y,n) := N_c(Y) ∧ N(n) ∧ h(n)=Y.

Its existence uses comprehension and its functionality uses the proof above. No choice of representatives is hidden here. Under bare Actuality we do not additionally assert that this inverse graph is represented by an ambient operation of type νν; the graph is sufficient for the interpretation and all comparisons below.

## 3. Arithmetic and represented subsets

The zero and successor equations are supplied by the original transfer. With quantified Infinity, realization and the finite-cardinality lemmas give the Peano laws: zero is not a successor and successor is injective; numberhood supplies induction with all admitted parameters. The same holds in the core because quantified Infinity transfers exactly.

The bijection therefore preserves addition and multiplication graphs by induction using their zero and successor recurrences, and then preserves their definable order. This does not introduce operations with forbidden individual output.

The correspondence also preserves the **admitted numerical subsets**, rather than merely the underlying number objects. Given an ambient predicate U on N, core comprehension forms

    U_c(Y) iff ∃n∈N (h(n)=Y ∧ U(n)).

Conversely a core predicate V pulls back to the ambient predicate V(h(n)). Injectivity and surjectivity show that these are inverse at the level of current extensions. The same value-relation translation works for fixed finite tuples and for graphs. Thus rational codes, Dedekind cuts, and numerical countability comparisons can be transported without changing the represented numerical subsets or assuming external fullness. Identity of arbitrary ambient predicate representatives is not claimed.

## Exact gain and limits

The original assumptions are unchanged for the construction of h. **Quantified Infinity_e** is the additional hypothesis that supplies injectivity; neither a mere finite distinctness schema nor an uninstantiated numerical infinity assertion is substituted. The proof adds no Choice and no modal stability. It removes a specific uncertainty about whether the original N_e and the core counting base agree when the probability arguments assume quantified Infinity_e.

Sources: the two original unpaginated core notes linked above; `frege-infinity-20261022-1726.md`, Lemmas 1.1–1.3 and §7; `topics/classicism/writeups/pure-possibility-implies-axiom-of-infinity-t.md`, §1, Lemma 4, for finite-cardinality exclusivity. Only those elementary arithmetic lemmas are used, not any Maximalism hypothesis or result. The isomorphism refinement is the argument of this note.

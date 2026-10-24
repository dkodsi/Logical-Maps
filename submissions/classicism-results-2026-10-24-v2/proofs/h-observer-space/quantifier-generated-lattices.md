# Quantifier-generated lattices over H

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: misc, this note, §§1–7, unpaginated. No C, NI, BF, Choice or Functionality is a standing assumption.

## 1. The exact binary-family premise

Use S[R], the observer order and the strong quantifier qualifications from [Truth profiles and connective reducts](truth-profiles-and-connective-reducts.md). Fix a type σ and an admitted parameter B of type ttσt. Write B[p,q,x] for its explicitly left-nested application. Assume

$$
\begin{aligned}
\mathrm{BinaryRange}_\sigma(B):=\forall p,q\,[
 &\forall x^\sigma(B[p,q,x]=p\lor B[p,q,x]=q)\\
 &\land\exists x^\sigma(B[p,q,x]=p)
 \land\exists x^\sigma(B[p,q,x]=q)].
\end{aligned}
$$

Thus B[p,q,−] has exactly the values p and q as proposition objects, not merely their truth values. When p=q the two attainment conditions can have the same witness.

This is a uniform admitted constructor. The weaker assertion ∀p,q∃F:σt with this exact range does give binary bounds by the order argument below, one pair at a time. It is not silently replaced by an admitted operation selecting F for every pair. The present theorem retains B as a parameter, or existentially quantifies B in its premise; no choice of a family of witnesses is inferred.

Define the admitted binary terms

$$
\mu_B(p,q):=\forall x^\sigma B[p,q,x],
\qquad
\nu_B(p,q):=\exists x^\sigma B[p,q,x].
$$

These are initially new operations. They are not stipulated to be the primitive conjunction and disjunction.

## 2. Separation generates the meet or join

Suppose every R-observer satisfies Qσ. For every eligible E, quantifier preservation and the range identities give

$$
E\mu_B(p,q)\ \leftrightarrow\ Ep\land Eq.
\tag{1}
$$

Indeed EμB(p,q)=∀x E(B[p,q,x]) by the Qσ identity. Every term inside that universal equals Ep or Eq, and both values occur. Its H truth condition is therefore the conjunction of their truth values.

Under S[R], (1) makes μB the meet for the observer order:

$$
u\preceq_R\mu_B(p,q)
\ \leftrightarrow\ (u\preceq_Rp\land u\preceq_Rq).
\tag{2}
$$

In particular μB is associative, commutative and idempotent as a proposition-valued operation. Also p≼R q iff μB(p,q)=p. Any other exact binary-range constructor at a listed universal type gives the same values as μB, by uniqueness of meets or directly by separation and (1). No whole-operation identity between the constructors or their resulting meet operations is asserted without a further lifting argument.

Dually, if R implies Pσ, then

$$
E\nu_B(p,q)\ \leftrightarrow\ Ep\lor Eq,
$$

and S[R] makes νB the observer-order join. These statements need neither composition closure nor Functionality.

The conclusion is relative to the common class R, but not circular: ≼R is the explicit formula ∀E(R(E)→(Ep→Eq)), and μB and νB are terms fixed independently of that order. Separation proves that this previously specified formula is a partial order and that those previously specified terms supply its bounds.

## 3. Composition closure upgrades material transport to output identity

Assume the observer class is closed under composition:

$$
R(E)\land R(F)\ \longrightarrow\
R(\lambda p.F(Ep)).
\tag{3}
$$

Then S[R], R⇒Qσ and BinaryRangeσ(B) prove, for every R-observer E,

$$
E\mu_B(p,q)=\mu_B(Ep,Eq).
\tag{4}
$$

To prove (4), test its two sides with an arbitrary R-observer F. Equation (1), applied to F∘E using (3), says the first side is accepted exactly when both F(Ep) and F(Eq) are true. Applying (1) directly to F and the inputs Ep,Eq gives the same condition for the second side. S[R] identifies the two proposition objects.

The existential dual gives EνB(p,q)=νB(Ep,Eq). This upgrade is an equality of outputs. It does not yet identify the two complete binary operations.

More generally, the same argument applies whenever a proposed admitted operation t has a uniform truth-profile law

$$
F(t(p_1,\ldots,p_n))\leftrightarrow
f(Fp_1,\ldots,Fp_n)
$$

for every R-observer F, with f a fixed ordinary Boolean truth function. Composition closure and separation then give E(t(p̄))=t(Ep̄). The binary quantifier construction is a useful instance because its profile law follows solely from exact range and one quantifier law.

### Classes for which closure is available over H

Every finite conjunction of full-operation preservation requirements M,V,N,Qσ,Pσ is closed under composition. Substitute one whole-operation equality into the other: for instance E first transports a universal family, then F transports the resulting family. This is congruence between whole operations, not Functionality. The identity observer satisfies each such conjunction.

Adding endpoint-fixing conditions preserves closure. So does adding full fixing of equality judgments at any listed types: E fixes each judgment and F fixes the same judgment, so F∘E does too, with the whole-operation equation obtained by congruence. Any additional restriction can be used if its composition closure is proved separately.

Acceptance of Top and rejection of Bottom alone do **not** supply a closure proof. E(Top) may be a different true proposition on which F is false, and likewise at Bottom. Thus (3) must not be inferred just from those restrictions. This does not prevent the preservation theorem: the following larger-class argument removes the need for R itself to be closed.

### Passing to a composition-closed core

Suppose R implies K, the class K is closed under composition, and every K-observer has the profile law needed in the preceding proof. Then S[R] implies S[K]. Apply the composition argument to K: the resulting output-preservation identity holds for **every K-observer**, and therefore for every R-observer. The extra restrictions defining R need not be closed under composition.

In the present quantifier application, take K to be the class of all strong Qσ observers. This class is always closed under composition and has (1). Consequently, S[R], R⇒Qσ and BinaryRangeσ(B) already imply (4), with no additional closure assumption on R. Acceptance, rejection, or any other extra observer restriction causes no obstruction. The existential statement uses the class of all Pσ observers in the same way.

## 4. Full typed separation gives an exact strong-preservation redundancy

Let Mμ(E) denote the full composite identity for preservation of the derived operation μB:

$$
(\lambda p,q.E\mu_B(p,q))
 =(\lambda p,q.\mu_B(Ep,Eq)).
$$

Functionality at the two stages t→t and t→tt lifts (4) to Mμ(E): first identify the unary q-functions for each p, then identify the outer p-functions. No C or necessity principle is involved. The analogous lift gives Vν(E) for νB.

Full typed separation for a fixed class R itself supplies the Functionality schema, by [Typed separation and Classicism](typed-separation-and-classicism.md), §2. Consequently, under BinaryRangeσ(B) and R⇒Qσ, there is an exact equivalence over H:

$$
\mathrm{FullSep}[R]
\quad\leftrightarrow\quad
\mathrm{FullSep}[R\land M_\mu].
\tag{5}
$$

Forward, the left side proves that every Qσ-observer already has Mμ, by the composition-closed core argument in §3 and the Functionality lift; this includes every R-observer. Reverse, separating by the smaller class implies separation by the larger class. The existential dual replaces Qσ,Mμ with Pσ,Vν. If R implies both quantifier laws, both derived preservation clauses can be added simultaneously with no change of full typed separation theory. No closure of R itself is needed.

At the propositional level, the exact same equivalence holds with the two needed Functionality instances explicitly assumed. Without them, the established redundancy concerns the pointwise-output preservation law (4), not necessarily the whole-operation law.

This does not identify μB with primitive conjunction. If the output alignment ∀p,q(μB(p,q)=p∧q) is separately assumed or proved, (4) transports to pointwise preservation of primitive conjunction by substitution. The same Functionality instances then give its full preservation. Alternatively, an already established whole-operation identity between μB and primitive conjunction permits direct replacement in Mμ. The distinction is the same for νB and primitive disjunction.

## 5. One common Q/P class gives a derived distributive lattice

Suppose S[R], BinaryRangeσ(B), and R⇒Qσ∧Pσ. The two operations μB,νB are the meet and join of the **same** observer order. Moreover their profiles are intersection and union, so separation proves both distributive laws as proposition identities. Thus they form a distributive lattice, even if neither has yet been identified with its original primitive counterpart.

If R also accepts Top, then Top is greatest; if R rejects Bottom, Bottom is least. The two composition-closed core arguments in §3 show that every R-observer preserves both derived operations pointwise, even with these truth-level restrictions. With the Functionality lift, it preserves both fully.

If additional Qτ or Pτ clauses are listed, those quantifiers are respectively the GLBs or LUBs of their admitted families in this same lattice. In particular, their truth profiles prove

$$
\mu_B(p,\exists x^\tau Fx)
 =\exists x^\tau\mu_B(p,Fx)\qquad(P_\tau),
$$

$$
\nu_B(p,\forall x^\tau Fx)
 =\forall x^\tau\nu_B(p,Fx)\qquad(Q_\tau).
$$

These identities use an admitted lambda family on the right. They assert neither existence of arbitrary external suprema nor an internal choice-of-witnesses principle. Finite type lists remain external schema indices.

Separate Q-separation and P-separation assertions can give different observer orders. The conclusion here requires one common qualified class, one common separation assertion and the resulting common profiles.

## 6. A checked sufficient constructor from a endpoint selector

An explicit sufficient premise for BinaryRangeσ(B) uses an admitted selector b:σt satisfying

$$
\forall x(bx=\mathrm{Top}\lor bx=\mathrm{Bottom}),
\quad\exists x(bx=\mathrm{Top}),
\quad\exists x(bx=\mathrm{Bottom}).
$$

Also assume the following two **output identities** for the displayed Boolean conditional term C(r,p,q):=(r∧p)∨(¬r∧q):

$$
C(\mathrm{Top},p,q)=p,
\qquad C(\mathrm{Bottom},p,q)=q.
\tag{6}
$$

Then the admitted term B[p,q,x]:=C(bx,p,q) has exactly the required binary range, by substitution in the endpoint cases and their attainment witnesses. For example, the ordinary pointwise Boolean-algebra equations for the original primitives and fixed endpoints imply (6). No whole-operation identity or observer preservation of those primitives is needed merely to construct B.

This is a conditional H result. Mere material Boolean truth conditions do not prove (6), and an operator with only truth-valued endpoint behavior is not a endpoint selector. No claim that H or all-type Q-separation alone supplies such a selector or such a constructor is made.

## 7. Scope

The central positive statement is that one-sided quantifier separation generates the corresponding binary order operation from an admitted exact binary-family constructor. Composition closure of the pure quantifier-preserving core then makes that operation commute with each qualified observer as an output identity, even when the actual qualification adds restrictions that are not composition-closed. Full typed separation supplies the Functionality needed for the whole-operation identity, yielding the exact redundancy (5).

The proof uses no Boolean transport by the observers, no modal premise, no external selection of an infinite family, and no bridge from a derived operation to a primitive unless explicitly stated. The direct source is this original argument: misc, OpenAI Codex, 24 October 2026, §§1–6, unpaginated.

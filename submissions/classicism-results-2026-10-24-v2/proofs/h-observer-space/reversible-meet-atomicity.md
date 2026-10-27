# Reversible meet separation and atoms over H

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–7, unpaginated.

Reversible conjunction-preserving separation spreads one meet atom throughout the proposition order. Its conclusion is stronger than the existence of an atom below every nonbottom proposition: atoms distinguish every failure of order, and each proposition is the least upper bound of its atoms. No negation, disjunction or quantifier preservation is needed. The theorem does not assert that atomicity conversely supplies reversible separation.

## 1. Qualification, reversibility and scope

Use the fixed relational language and fixed abbreviations T for Top and B for Bottom. H proves T true, B false and T distinct from B. For an observer E of type tt put

```math
A(E):=ET,\qquad Z(E):=\neg EB,
```

```math
M(E):=(\lambda p,q.E(p\land q))
       =(\lambda p,q.Ep\land Eq)
```

Thus M is identity of the whole conjunction composites, not merely pointwise equality or material preservation. Define the admitted composition and identity terms by

```math
(E\circ F)(p):=E(Fp),\qquad I(p):=p,
```

and let

```math
\mathrm{Rev}_M(E):=
\exists F^{tt}\,[M(F)\land E\circ F=I\land F\circ E=I]
```

Both inverse equations are identities of the displayed operations. Every inverse used below is an object of the admitted tt domain.

Let K(E) be any qualification such that H, or explicit standing hypotheses, gives

```math
K(E)\ \longrightarrow\
A(E)\land Z(E)\land M(E)\land\mathrm{Rev}_M(E)
```

Assume propositional separation

```math
S[K]:=\forall p,q\left[
p=q\leftrightarrow
\forall E\,(K(E)\to(Ep\leftrightarrow Eq))
\right]
```

The basic case is K=A and Z and M and Rev_M. Additional restrictions may be retained. The core theorem does not require those additional restrictions to hold of the inverse; the separate transitivity statement below identifies exactly where closure of the restricted class is needed.

All statements through §5 concern propositions at t and are unboxed. The atom notion is for the meet order established below. It is not silently substituted for the database's Boolean-order Atomicity before C has been assumed.

## 2. Separation produces the bounded meet order

Define

```math
p\preceq_K q:=
\forall E\,[K(E)\to(Ep\to Eq)]
```

This is a preorder, and S[K] makes it antisymmetric. Every eligible observer accepts T and rejects B, so T is greatest and B least.

M, by application, gives the truth law for conjunction. Consequently

```math
u\preceq_K(p\land q)
\quad\leftrightarrow\quad
(u\preceq_K p\land u\preceq_K q)
```

Thus primitive conjunction is the meet. In particular it is associative, commutative and idempotent, with T a unit and B absorbing. Its order is exactly

```math
p\le q\quad:\!\!\leftrightarrow\quad p\land q=p
```

For the nontrivial direction of this identification, if p precedes q then every eligible observer agrees on p and p and q; separation identifies them. Conversely the displayed meet identity and its truth law imply Ep implies Eq.

Hence every qualified E is an order homomorphism. If F witnesses Rev_M(E), the inverse identities give E(Fp)=p and F(Ep)=p. Since F also preserves meet, E and F are inverse order isomorphisms. In particular they fix both bounds:

```math
ET=T,\quad EB=B,\quad FT=T,\quad FB=B
```

For example every proposition has the form Ex; since x is below T, every proposition is below ET, so ET=T. The other endpoint identities follow in the same way. This conclusion is stronger than the initial acceptance/rejection clauses, but is proved only after separation supplies the bounded order.

Define a meet atom by

```math
\mathrm{Atom}_{\land}(a):=
a\ne B\land
\forall c\,[c\le a\to(c=B\lor c=a)]
```

Every admitted meet order isomorphism preserves this property. Indeed if c is below Ea, then Fc is below a. Applying atomhood of a and then E shows that c is B or Ea. Nonbottomness is preserved because the maps fix B. The inverse direction is identical.

## 3. One atom gives a unique true atom

Assume there is a meet atom a. Since a differs from B, S[K] supplies an eligible E whose outputs on a,B disagree in truth. Z(E) makes EB false, so Ea is true. The proposition
$`w:=Ea`$
is again an atom by the order-isomorphism argument. Thus a true atom exists.

There is at most one true atom. If w and v are true atoms, their meet is true by H's conjunction truth clause and hence differs from the false B. Since it is below both atoms, atomhood gives w and v equal.

Moreover, for every true p, the meet w and p is true and nonbottom. Atomhood of w therefore gives w and p equals w, so w is below p. Conversely, if w is below p, the identity w and p equals w and the truth of w force p true. Hence

```math
\boxed{\quad p\ \leftrightarrow\ w\le p.\quad}
```

This is a material equivalence describing current truth. No claim that its two sides are identical propositions is needed.

## 4. Atoms distinguish order and represent every proposition

**Theorem.** Under the hypotheses above and the existence of one meet atom,

```math
\boxed{
p\not\le q\ \longrightarrow\
\exists a\,[\mathrm{Atom}_{\land}(a)
            \land a\le p\land a\not\le q]}
```

**Proof.** If p is not below q, then p and q differs from p. Separation supplies an eligible E whose outputs on those two propositions disagree. By M, E(p and q) has the truth value of Ep and Eq. It can disagree with Ep only when Ep is true and Eq false.

Let F be an admitted meet-preserving inverse of E and let w be the unique true atom from §3. Since Ep is true, w is below Ep. Thus
$`a:=Fw`$
is an atom below F(Ep)=p. If a were below q, applying E would give w below Eq. The material characterization of truth by w would make Eq true, a contradiction. Therefore a is not below q. ∎

This gives the exact order characterization

```math
\boxed{
p\le q\ \leftrightarrow\
\forall a\,[\mathrm{Atom}_{\land}(a)
             \land a\le p\ \to\ a\le q]}
```

Taking q=B shows that every nonbottom proposition has an atom below it. The displayed equivalence is stronger than that ordinary atomicity condition. For example the three-element chain B<a<T is atomic, but a and T have the same atoms below them.

For each p, its atoms have p as their least upper bound: p is an upper bound by definition, and any q above all of those atoms must be above p by the boxed equivalence. Thus the meet structure is atomistic in this precise order sense.

Externally, at any current evaluation point define

```math
\mathcal A(p):=
\{a:\mathrm{Atom}_{\land}(a)\text{ and }a\le p\}
```

Then

```math
\begin{aligned}
p\le q&\quad\leftrightarrow\quad
        \mathcal A(p)\subseteq\mathcal A(q),\\
\mathcal A(p\land q)&=\mathcal A(p)\cap\mathcal A(q),\\
\mathcal A(B)&=\varnothing,\qquad
\mathcal A(T)=\{\text{all meet atoms}\}
\end{aligned}
```

The map is injective, and the atom set of an atom a is the singleton {a}. These statements give a faithful representation of the bounded meet structure by sets of atoms.

They do not assert that every external set of atoms is represented, that arbitrary joins exist, or that primitive disjunction is a join. The least-upper-bound assertion concerns the atoms already lying below a given proposition. The set representation is also not an identity between higher-type characteristic terms; no Functionality is tacitly used.

## 5. Transitivity and closure of the qualified class

Every atom a can be sent to w by an eligible observer: repeat the separation argument on a,B. Its eligible image is a true atom and therefore equals w.

For any two atoms a,b choose eligible observers E_a,E_b with

```math
E_a a=w,\qquad E_b b=w
```

Let F_b be an admitted meet-preserving inverse of E_b. Then
$`G:=F_b\circ E_a`$
is an admitted meet automorphism with Ga=b. Thus all atoms lie in one orbit of the group of admitted meet automorphisms, and already of the subgroup generated by the eligible maps and their admitted inverses.

Composition here preserves the full M qualification, not merely its pointwise version. For meet-preserving U,V, rewrite the whole expression

```math
\lambda p,q.U(V(p\land q))
```

first with the full M identity for V and then with that for U. The result is

```math
\lambda p,q.U(Vp)\land U(Vq)
```

These are substitutions of given operation identities in term contexts, followed by conversion. They do not abstract a conditional pointwise identity. The inverse of F_b composed with E_a is F_a composed with E_b; its two full inverse identities follow from the given inverse identities by composition and conversion.

There is an important qualification distinction. If K includes extra restrictions not closed under inverse and composition, G need not satisfy those extra restrictions. The conclusions that each atom is sent to w by an eligible map, and that all atoms are in one admitted-automorphism orbit, remain valid. To conclude transitivity of the restricted eligible class itself, assume that class is closed under both inverse and composition. In the basic class A and Z and M and Rev_M, the bounded-order argument supplies endpoint fixing for every meet automorphism, and the required closure follows.

No inverse is assumed to satisfy an extra restriction merely because the original separating map does.

## 6. A unique atom and the typed conclusion

Under S[K], existence of a unique meet atom is equivalent to the propositional Fregean Axiom.

For the forward implication, §§3–4 apply. Let w be the unique atom. Every nonbottom proposition contains an atom and hence contains w. It then has the same atom set as T, so injectivity of the atom-set representation identifies it with T. Consequently every proposition is B or T. Since these have opposite truth values, materially equivalent propositions are identical.

Conversely, the Fregean Axiom makes every proposition equal B or T. H's truth clauses then identify primitive conjunction with the two-element meet table, and T is its unique meet atom. This converse does not require any preservation or separation premise.

For arbitrary K as in §1, full typed separation supplies Functionality. Therefore, under FullSep[K],

```math
\boxed{
\exists!a\,\mathrm{Atom}_{\land}(a)
\quad\leftrightarrow\quad
\mathrm{Extensionality}}
```

The forward proof uses propositional Fregean plus Functionality to identify coextensive relations at each relational type. The reverse follows from Extensionality's propositional instance.

For a theory-level characterization without FullSep[K] as background, suppose in addition H proves K(I). This holds for the basic reversible meet class. Then

```math
\boxed{
\mathrm{FullSep}[K]
+\exists!a\,\mathrm{Atom}_{\land}(a)
\quad\leftrightarrow\quad
\mathrm{Extensionality}}
```

In the converse direction identity qualifies and, under Extensionality, already separates every relational type. Extra restrictions must satisfy the stated identity-admission condition for this converse.

The existence of one propositional atom has not been promoted to atomicity at arbitrary relation types. Nor has any hypothesis or conclusion been boxed. If K contains preservation at a fixed finite type list, the same propositional argument uses that common qualified class; it does not combine witnesses drawn from different lists.

## 7. Sources and scope

The direct source for the atom-spreading and order-separation proof is this original argument (`misc`, OpenAI Codex, 24 October 2026, §§2–6, unpaginated). The argument distinguishes arbitrary admitted inverses from inverses satisfying additional qualifications.

The bounded meet order is the H truth-profile argument in [Truth profiles and connective reducts](truth-profiles-and-connective-reducts.md), §§2–3. Full typed separation and its exact Functionality contribution are proved in [Typed separation and the recovery of Classicism over H](typed-separation-and-classicism.md), §2. The earlier complete-logical, C-based spreading argument is in [Logical-observer hierarchy](../logical-observer-hierarchy.md), §6; the present result isolates the meet and inverse hypotheses actually needed for the stated conclusion.

No C, NI, BF, identity bivalence, negation preservation, disjunction preservation, quantifier preservation, or Choice principle is used. No converse from atomicity or atomisticity to reversible separation is asserted.

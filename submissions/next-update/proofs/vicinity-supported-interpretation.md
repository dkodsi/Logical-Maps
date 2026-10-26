# The supported C5 interpretation from Vicinity

OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026. Source: `misc`, this proof, unpaginated.

One construction supports both [Actuality theorems](../items/23-propositional-zorn-actuality.md): the [Relational Choice branch](vicinity-relational-choice-and-propositional-completeness-imply-actuality.md) and the [Zorn branch](vicinity-zorn-and-propositional-completeness-imply-actuality.md). Vicinity supplies a true support; hereditary retractions give a C5 interpretation on its supported domains. Propositional completeness transfers to this interpretation, and any supported Actuality witness is also an original Actuality witness. The two branches differ only in the additional choice principle transferred and the C5 theorem applied.

The common-core mechanism extends Christopher Sun's 19 October 2026 argument in the [5-necessity variant of Vicinity](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/principles/vicinity.yaml). The interpretation and its transfers are the new connecting arguments here.

## 1. A common support for all admitted quantifiers

Choose a true Vicinity witness w. Put

```math
A_w:=\forall r^t\, .\,(r\to w\le\Diamond r),\qquad s:=w\land A_w.
```

Both w and A_w, hence s, are currently true. For every fixed admitted argument type σ and every admitted F:σt,

```math
\bigl[\forall x^\sigma\, .\,(s\le F(x))\bigr]
\ \Longrightarrow\ s\le\forall x^\sigma F(x).
\tag{3}
```

Here and below the conclusion is an algebraic bound, not just a material implication.

For the proof let T:=∀x(s≤F(x)) be currently true. Vicinity gives
w≤◇(w∧T). Work at any accessible evaluation v where s is true. Suppose that an x available there satisfies ¬F(x). At v the A_w conjunct applies to the proposition s∧¬F(x), which is true there, and gives

```math
w\le\Diamond(s\land\neg F(x)).
```

The bound w≤◇(w∧T) obtained at the original evaluation persists to v. Since w holds at v, there is an accessible u where w∧T holds. The parameter x is available at u; this uses only the converse-Barcan direction. T supplies □(s→F(x)) at u. The bound obtained at v also persists to u, and w there gives ◇(s∧¬F(x)), a contradiction. Thus every x at every accessible s-evaluation satisfies F(x), proving (3).

This is an ordinary S4/CBF derivation expressed by evaluations. No Barcan premise, completeness, choice, or necessitation of an optional premise is involved. The same argument applies at every evaluation satisfying s, since w∧A_w holds there again. Its mechanism is the one used in Sun's recorded Vicinity argument; its all-type formulation here makes the required quantifier scope explicit.

For every current identity E=(a=b), at any type, s decides E according to its current truth. If E is true, NI gives E=1. If E is false, Vicinity gives w≤◇¬E. NI makes E persistent, so ◇¬E=¬E. Consequently

```math
s\land E=\begin{cases}s,&a=b,\\0,&a\ne b.\end{cases}
\tag{4}
```

Induction on finite formulas, using (3) at universal quantifiers and a current witness for a false universal, extends this decision property to formulas built from identities by Boolean operations and typed quantifiers. Arbitrary atomic membership assertions are not included in that claim.

There is also an exact range-bound consequence. For any admitted f:σt,

```math
s\land\exists x^\sigma f(x)
=\bigvee_{x\text{ current}}\bigl(s\land f(x)\bigr).
\tag{5}
```

The right side means the actual algebraic least upper bound of the displayed range; (5) establishes its existence without BC. Instantiation gives each upper-bound inequality. If b bounds every s∧f(x), then s≤(f(x)→b) for every current x. Equation (3) collects these bounds into s≤∀x(f(x)→b), which gives the converse inequality. The relative meet statement is dual. An index predicate decided on s may be inserted: nonmembers then contribute 0, while current members contribute their full s-restricted values.

## 2. Concrete supported domains

Define hereditary retractions by

```math
j_e(x):=x,\qquad j_t(p):=s\land p,\qquad
j_{\sigma\tau}(F):=\lambda x^\sigma\, .\,j_\tau(F(j_\sigma x)).
\tag{6}
```

The e-case is a substitution convention, **not** a term of the forbidden type ee. All other displayed retractions have admitted types. Whenever an argument type is e, the corresponding occurrence of j_e simply erases.

These are idempotent as whole operations. At t this is the Boolean identity s∧(s∧p)=s∧p, also under abstraction. Inductively, β-expansion of j_(στ)(j_(στ)F) gives

```math
\lambda x\,j_\tau\bigl(j_\tau(F(j_\sigma(j_\sigma x)))\bigr).
```

The already established lower-type whole identities reduce this to j_(στ)F. The same reduction under the outer F-abstraction proves whole-operation idempotence at the new type. All replacements are substitutions of entity identities in terms; there is no appeal to Functionality or to Logical Equivalence under an optional premise.

Set

```math
D_\tau(x):=(j_\tau x=x),
```

with D_e(x):=(x=x). Each domain is inhabited and is exactly the image of j_τ. If F and x are fixed in their respective types, β and the fixedness identities give F(x)=j_τ(F(x)), so application restricts to these domains. In particular D_t is exactly [0,s]. The predicates D_τ are identity predicates and are decided on s by (4).

In the supported interpretation, use these concrete carriers and restricted application. At t use 0 and s as the endpoints, ordinary meet and join, and relative complement p↦s∧¬p. On fixed arguments equality is

```math
\mathrm{eq}_s(x,y):=s\land(x=y).
\tag{7}
```

Its admitted unrestricted relation is s∧(j_σx=j_σy). Current truth of (7) is precisely equality of the fixed entities, since s is true.

Interpret an abstraction by evaluating its body on projected arguments and retracting its output. Quantifiers for a supported predicate F may be written

```math
\exists_s x\, .\,F(x):=s\land\exists x\,F(j_\sigma x),\qquad
\forall_s x\, .\,F(x):=s\land\forall x\,F(j_\sigma x).
\tag{8}
```

The image description shows that their current truth is exactly quantification over D_σ. Equation (5) shows that their proposition values are the actual joins and meets in [0,s] of the corresponding fixed-domain range values. Quantifier operations and the displayed logical operations are themselves projected to their appropriate higher domains. β, idempotence and the Boolean identities give exactly the clauses above on fixed arguments.

## 3. Preserving H and Logical Equivalence

The retraction interpretation preserves H by ordinary relativization to the images of idempotent maps. The required details matter because C's Logical Equivalence rule applies only to H-theorem equivalences.

Translate every variable occurrence through its j, use (7) for equality, (8) for quantification, and retract abstractions as in §2. For any finite H derivation, let E be the finite conjunction of the whole retraction identities and logical-constant identities needed in its translation. If supported parameters are left unprojected, include their fixedness identities as well. These are all **positive identities**. There is no Vicinity, quantifier-bound lemma, completeness, choice, or other optional material premise in E.

Under E and s the usual H proof translates as follows. Identity and substitution concern actual equality of projected entities. Application stays in the projected domains. β uses j²=j on the argument and output, and η uses the same whole identity at the abstraction's type. Universal instantiation uses the projected instance jx; existential introduction uses that same available term. Generalization and elimination range over all images, precisely as in (8). The propositional rules use the ordinary Boolean clauses on an evaluation where s is true. These checks give induction on the H derivation. Every translated proposition is s-supported under E, so outside s two such matrices are both false.

In particular, if H proves Φ↔Ψ, the preceding translation gives the **old-H theorem**

```math
(E\land\Phi^s)\ \longleftrightarrow\ (E\land\Psi^s).
\tag{9}
```

Apply old Logical Equivalence to (9), including the required abstraction variables. Each conjunct of E is a true identity in C and hence 1 by NI; therefore E=1. Substitution of this entity identity, and the unconditional Boolean identities under abstraction, removes E from the resulting abstraction identity. Retraction preserves that identity. This is precisely Logical Equivalence in the supported interpretation.

This argument does not substitute current semantic coextension for entity identity. Nor does it feed an equivalence proved from Vicinity into Logical Equivalence: only the H theorem (9) enters the rule, and its explicit guard is subsequently removed by identity substitution. Together with the preceding H checks it establishes a concrete interpretation of C.

## 4. C5 in the supported interpretation

For each pair of current fixed entities, (4) makes its relative equality either 0 or s. If the entities are distinct, their relative inequality is s, so it is relatively necessary: its identity to the relative top s is true and its relative box has value s. Equal pairs have zero inequality antecedent.

Thus every current instance of the ND matrix has relative value s. Equation (5) and its meet dual make the universal closure over the fixed domains s as well. Its relative box is consequently s. This proves ☐ND at every type in the interpretation, which is C5; it proves more than ND there.

No assertion that the original structure satisfies C5, ND, BF, or Functionality has been made. The new necessity operator is identity to s within the supported propositional domain, rather than original identity to 1.

## 5. Propositional completeness and Actuality

Let X be any supported predicate on D_t. Apply old BC_t to the represented current family D_t(p)∧X(p). Its actual join b lies below s, since s bounds every member; hence b belongs to D_t. Relative algebraic order on [0,s] is the original algebraic order: p∨q=q has the same meaning in both Boolean algebras. The old least-upper-bound property of b is consequently its supported least-upper-bound property. This proves supported BC_t, without ☐BC. The meet formulation is equivalent.

If the supported interpretation has a true Actuality witness u, then for every original true proposition q, the supported proposition s∧q is true. Hence u≤s∧q≤q. The same u witnesses original Actuality. This descent uses neither Relational Choice nor Zorn.

## 6. Vicinity and persistent propositions

Let O be the represented family of persistent propositions p=□p. A member of O is currently true exactly when it is 1. Then

```math
\mathrm{Vicinity}\quad\longleftrightarrow\quad
\text{O has a greatest proper member}.
\tag{10}
```

For the forward direction let w witness Vicinity and put m:=□¬w. For every proper persistent p, ¬p is true, so w≤◇¬p=¬p. Hence p≤¬w, and persistence and monotonicity give p≤□¬w=m. The proposition m is persistent and false, since w is true. It is therefore the greatest proper member of O. Conversely, given such an m, let w:=¬m, which is true. For any true q, the persistent proposition □¬q is false and hence lies below m. Taking complements gives w≤◇q, so w witnesses Vicinity.

No completeness is needed for (10). Equivalently, failure of Vicinity says that 1 is the least upper bound of all currently false persistent propositions. Indeed, any upper bound b<1 would make □b a proper persistent upper bound and hence the greatest proper member. Whether BC_t with RC at t,t or Zorn at t entails this condition remains open.

## Sources

The common-core mechanism is Christopher Sun's 19 October 2026 Vicinity argument, recorded in the linked principle. The all-type bound lemma, supported interpretation, transfers and persistent-proposition characterization are from OpenAI Codex, *Vicinity, Relational Choice and propositional completeness imply Actuality*, 25 October 2026, §§2–8, unpaginated. Their source hash and reported independent AI review are recorded with this update.

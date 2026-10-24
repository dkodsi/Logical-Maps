# Typed separation and the recovery of Classicism over H

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–7, unpaginated. The fixed language and definition of C are those in the [framework](../../source/topics/classicism/background.md): types are relational, and C is the smallest H-theory containing Logical Equivalence for H theorems.

The main conclusions are:

1. For any observer qualification, full typed separation is exactly propositional separation plus Functionality, already over H.
2. For the complete logical qualification, material, pointwise-identity and full-operation separation give the same full theory over H. The proof first recovers C; it does not identify their standalone observer classes in H.
3. Replacing translated equality substitution by reflection of equality judgments yields exactly C5 plus ordinary logical separation. Fixing equality judgments as propositions gives the same full theory.
4. A truth-functionally complete subset of H's logical primitives does not suffice to transport the omitted primitives. A single uniform model construction shows the direct recovery package is irredundant in each primitive law and each translated equality clause.

## 1. Qualification and typed scope

Let K(E) be any formula whose only free variable is E of type tt. For a relational type τ=σ₁…σₙt, define

$$
\operatorname{Sep}_{\tau}[K]:\quad
\forall X,Y^\tau\left[
X=Y\leftrightarrow
\forall E^{tt}\left(K(E)\to
\forall z_1^{\sigma_1}\cdots z_n^{\sigma_n}
\bigl(E(X[\bar z])\leftrightarrow E(Y[\bar z])\bigr)\right)\right].
$$
The tuple can be empty, giving propositional separation Sep_t[K]. FullSep[K] contains these instances at every relational type. The same notation applies to a nonempty family of qualifications, with every member included on both sides of the results below. Canonical logical qualification is indexed by all finite type lists Δ, including the empty list. No type quantifier or infinite conjunction occurs inside an axiom.

Functionality is the schema

$$
\forall X,Y^{\sigma\rho}\left[
(\forall x^\sigma\,Xx=Yx)\to X=Y\right],\qquad\rho\ne e.
$$
This is [current Functionality](../../source/topics/classicism/principles/functionality-r.yaml), not identity from current material coextension and not a rule permitting abstraction of arbitrary conditional identities.

## 2. The exact role of full typed separation

**Theorem 1.** For every K,

$$
\boxed{\mathrm H+\operatorname{FullSep}[K]
\equiv
\mathrm H+\operatorname{Sep}_t[K]+\operatorname{Functionality}.}
$$
No preservation, endpoint, existence or correctness condition on the qualified observers is needed.

**Proof.** FullSep includes its propositional instance. Suppose ∀x Xx=Yx, where X,Y have type σρ. Apply these identities to every remaining argument of the relational output ρ. Ordinary H substitution gives equality of the resulting propositions, and hence agreement in truth after applying any E. The full separation instance at σρ gives X=Y. This proves every Functionality instance.

Conversely, suppose all K-observers agree on X[\bar z] and Y[\bar z] at every current tuple. Fix that tuple and apply propositional separation: X[\bar z]=Y[\bar z]. Generalize over the tuple. Iterating Functionality, starting with the final argument and proceeding outward, gives X=Y. The other direction of the separation biconditional is ordinary substitution. ∎

For a nonempty family of qualifications, use any one member to extract Functionality; apply the converse separately to each member. The theorem also locates the finite requirements for a particular output type: only the Functionality instances along its finite argument tuple are used.

Thus a full typed observer principle has two components: its propositional separation claim and Functionality. In particular, the recovery arguments below do not establish C from propositional logical separation alone. They establish it from that propositional schema together with Functionality, equivalently from the full typed schema.

## 3. A finite H-proof transport theorem

The primitive logical-object families of H are negation, conjunction, disjunction, universal quantification, existential quantification and equality. Preserve their separate status over H. Put a:=∀p^t p, ⊤:=a∨¬a and ⊥:=a∧¬a, using the fixed abbreviations.

For finite Δ, let Good^mat_Δ(E) require the following material truth laws:

$$
\begin{aligned}
E(\neg p)&\leftrightarrow\neg Ep,\\
E(p\land q)&\leftrightarrow(Ep\land Eq),\\
E(p\lor q)&\leftrightarrow(Ep\lor Eq),\\
E(\forall x^\sigma Fx)&\leftrightarrow\forall x^\sigma E(Fx),\\
E(\exists x^\sigma Fx)&\leftrightarrow\exists x^\sigma E(Fx)
\qquad(\sigma\in\Delta).
\end{aligned}
$$
Universally close each law over its displayed input variables. Add, for each σ∈Δ,

$$
\begin{aligned}
R_\sigma(E)&:\quad\forall x^\sigma\,E(x=x),\\
L_\sigma(E)&:\quad\forall x,y^\sigma\,\forall F^{\sigma t}
\bigl(E(x=y)\to(E(Fx)\to E(Fy))\bigr).
\end{aligned}
$$
The Boolean truth laws imply E⊤ and ¬E⊥ in H. Separate endpoint-fixing identities are not required; see the [endpoint reduction](../logical-observer-endpoint-reduction.md).

**Theorem 2, finite transport.** Given a finite H proof of P from assumptions Γ, there is a finite Δ such that, for fresh E, H derives EP from Good^mat_Δ(E) and the observed assumptions {EA:A∈Γ}. The types in Δ are those needed for the proof's quantifier and equality steps. More precisely, the transformation uses only the preservation laws and translated equality clauses corresponding to the primitive rules actually used in that proof.

**Proof.** Induct on the H derivation. Propositional rules are valid after applying the displayed truth laws. Quantifier elimination and introduction use the corresponding universal or existential truth law, with E chosen fresh for generalization variables. Equality reflexivity is R. An equality-substitution step is L, applied to the lambda-defined predicate representing that substitution. For an H conversion identity A=B, obtain E(A=A) by R and rewrite its second argument with the already available H identity A=B; this gives E(A=B). Renaming and capture-avoiding term substitution preserve the construction because E is fresh. The qualification has no free variable being generalized. Enlarging the finite support at an induction step merely adds clauses to the common qualification. These steps cover hypotheses, logical rules, equality, conversion, renaming and substitution. ∎

This is a transformation of H proofs. It does not say qualified observers preserve every actual truth or every additional axiom. A sub-signature version says precisely: whenever both directions between P and Q have H derivations using only the selected primitive rules, the selected laws make EP and EQ agree in truth. Omitted logical objects may remain as opaque terms; their omitted logical rules are not thereby transported.

**Corollary 3.** FullSep[Good^mat_Δ], for all finite Δ, entails C, all BF instances and all Functionality instances over H.

For C, take an H theorem P↔Q. The transport theorem gives EP↔EQ for every qualified E, uniformly in the free variables of P,Q. Apply separation at the type of λ\bar z.P and λ\bar z.Q. Beta conversion gives

$$
(\lambda\bar z.P)=(\lambda\bar z.Q).
$$
These are exactly the Logical Equivalence instances defining C. The optional separation axioms have not been used as premises of the H theoremhood side condition.

For BF_σ, assume ∀x^σ(Fx=⊤). Every observer qualified at σ accepts each Fx, since it accepts ⊤. Its universal truth law makes E(∀x Fx) true. Propositional separation from ⊤ therefore gives (∀x Fx)=⊤. This is BF_σ after discharging the assumption. Functionality follows from Theorem 1. These are the finite proof arguments underlying the [canonical H recovery](../logical-observers.md#3-os-entails-c-and-bf-over-h); they do not require C to establish their own transport premise.

## 4. Material, pointwise and full-operation separation coincide

Let Good^pt_Δ replace each Boolean and quantifier truth law in §3 by the universally closed identity of its two proposition-valued sides. Let Good^op_Δ replace it by the identity of the entire composite operations, abstracting over the law's input variables. Keep the same R/L clauses. No endpoint-fixing clause is included in any version.

Write OS^mat, OS^pt and OS^op for the corresponding full typed separation schemas over all finite Δ.

**Theorem 4.**

$$
\boxed{\mathrm H+\mathrm{OS}^{\mathrm{mat}}
\equiv\mathrm H+\mathrm{OS}^{\mathrm{pt}}
\equiv\mathrm H+\mathrm{OS}^{\mathrm{op}}.}
$$
Application and identity substitution give Good^op→Good^pt→Good^mat in H. Since restriction to a smaller class strengthens separation, OS^op entails OS^pt, which entails OS^mat.

For the reverse implication, first use Corollary 3 to recover C from OS^mat. Fix Δ and abbreviate K(E):=Good^mat_Δ(E). Define the admitted term

$$
E^\#p:=(K(E)\land Ep)\lor(\neg K(E)\land p).
$$
H proves every requested material preservation law for E^# without assumptions. Split on K(E). In its true case E^# agrees in truth with E at every input and K supplies the requested law; in its false case E^# agrees with identity. K(E) has no free law-input variable, so the same case split works under each input quantifier. The identical argument proves R and L for E^#.

For each Boolean or quantifier law, this gives an unconditional H equivalence between its two sides, with E and the law inputs free. C's Logical Equivalence, abstracting over E and all those inputs, identifies the two composite operations. Apply that identity to E and use conversion. Thus C proves Good^op_Δ(E^#) for every E. There is no application of Logical Equivalence under the optional assumption K(E).

Now suppose all Good^op observers agree on the instances of X,Y. For any Good^mat observer E, its normalized E^# is Good^op and has the same current truth values as E. Therefore all Good^mat observers agree on X,Y. OS^mat gives X=Y, establishing OS^op. This is the [finite normalization argument](../observer-lattice.md#1-definitions-and-the-change-of-base), applied after H recovery. ∎

There is an independent shorter explanation for the pointwise/full part. FullSep already yields Functionality by Theorem 1. Functionality then identifies any two operations whose values are identical at every input, so Good^pt and Good^op become the same qualification. This observation applies to other finite packages of operation-identity requirements too, whether or not they recover C.

The theorem concerns separation theories. It does not assert material, pointwise and full qualifications are equivalent predicates in bare H. In particular, the normalization term uses the primitive Boolean operations whose object identities become available only after the recovery of C.

## 5. Replacing translated substitution by equality reflection

Define, at a fixed type σ,

$$
\begin{aligned}
\operatorname{Reflect}_\sigma(E)&:
\forall x,y^\sigma\,(E(x=y)\to x=y),\\
\operatorname{CorrectEq}_\sigma(E)&:
\forall x,y^\sigma\,(E(x=y)\leftrightarrow x=y),\\
\operatorname{FixEq}_\sigma(E)&:
(\lambda x,y^\sigma.E(x=y))=(\lambda x,y^\sigma.x=y).
\end{aligned}
$$
Over H, R_σ plus Reflect_σ is equivalent to CorrectEq_σ. For the missing direction x=y→E(x=y), use R and ordinary substitution in E(x=x). CorrectEq implies both R and L: its reflection gives x=y, and H substitution then gives E(Fx)→E(Fy). Full FixEq implies CorrectEq by application. None of these conditions is the different equation E(p=q)=(Ep=Eq).

Starting with Good^op_Δ, replace R_σ,L_σ by CorrectEq_σ for each σ∈Δ. Alternatively replace them by FixEq_σ. Thus the Boolean and quantifier requirements in this paragraph remain full composite identities. Take full typed separation at all finite Δ in either case.

**Theorem 5.** Each replacement theory is exactly

$$
\boxed{\mathrm{C5}+\mathrm{OS},}
$$
where OS is any equivalent complete logical separation theory from Theorem 4, and C5 is the database's boxed all-type ND preset.

**Forward proof.** The new qualifications imply the old ones, so their separation schemas entail ordinary OS. Thus C, BF and Functionality have already been recovered. Take Δ containing t and suppose p≠q. Every newly qualified observer rejects the identity judgment (p=q), by CorrectEq, and rejects ⊥, by its Boolean laws. Its outputs on those propositions agree in truth. Separation gives (p=q)=⊥, which in C yields □(p≠q). Hence ND_t holds. The recorded implications

$$
\mathrm{ND}_t+\mathrm{BF}_t\Rightarrow\Box\mathrm{ND}_t
\Rightarrow\Box\mathrm{ND}_{\mathrm{all}}
$$
give C5: see [the first implication](../../source/topics/classicism/results/nd-t-and-bf-t-imply-necessary-nd-t.yaml) and [its all-type extension](../../source/topics/classicism/results/necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r.yaml).

**Reverse proof.** Over C5, a true identity judgment equals ⊤ by NI and a false one equals ⊥ by ND. Every Boolean logical observer fixes these endpoints over C. It therefore fixes every identity judgment pointwise, and Functionality identifies the full λx,y composites. Consequently ordinary qualified observers and their CorrectEq/FixEq restrictions coincide under C5+OS. Ordinary separation gives both replacement schemas. ∎

The finite equality-type scope matters. In a direct replacement proof, the qualification must handle each equality type used in the transported H proof; replacing every R/L clause at σ∈Δ does this. There is also a smaller strengthening once ordinary Good is retained: add just equality reflection at type t whenever t∈Δ. The same argument yields C5+OS, because ordinary Good still transports equality at every other proof type. Dropping those other translated equality clauses altogether is a different proposal and is not justified by reflection at t.

## 6. Sharpness of the direct primitive package

The following is an irredundance statement for the displayed direct transport package, not a claim that it is the only possible axiom system recovering C. Stronger structural conditions can replace some clauses, as §5 shows.

Take D_e to have two elements, D_t={0,1}², and every higher domain to be the full set of functions of its prescribed type. A proposition (b₀,b₁) is true exactly when b₀=1. Interpret application and lambda as actual function application and abstraction. Interpret all logical operations coordinatewise in the usual two-valued way, and equality at each type by (δ,δ), where δ is actual equality of domain elements.

The two admitted observers

$$
E_i(b_0,b_1)=(b_i,b_i),\qquad i=0,1,
$$
satisfy all the full composite preservation identities and all translated equality clauses. They jointly separate propositions. Since the higher domains are full function spaces, two distinct relations differ at some complete argument tuple; the same two observers therefore separate every relational type.

Now modify just the second coordinate of one primitive operation or equality predicate. Leave every first coordinate unchanged. H remains sound: its logical rules have their usual actual truth conditions, equality truth is actual identity, and beta/eta are function identities. Each retained full operation law remains an equality of actual functions for E₀ and E₁.

| Omitted clause | Modified second coordinate | Identity required by C which fails |
|---|---|---|
| Conjunction preservation | The conjunction output is always 0 | p∧p=p at p=(0,1) |
| Disjunction preservation | c∨′d is c XOR d | p∨p=p at p=(0,1) |
| Negation preservation | The negation output is always 1 | ¬⊤=⊥ |
| Universal preservation at a chosen σ | The universal output is always 0 | (∀x^σ ⊤)=⊤ |
| Existential preservation at a chosen σ | The existential output is always 0 | (∃x^σ ⊤)=⊤ |
| R_σ | Equality at σ is (δ,0) | (x=x)=⊤ |
| L_σ | Equality at σ is (δ,1) | The Leibniz tautology identified with ⊤ |

For each modification the fixed endpoints are still ⊤=(1,1) and ⊥=(0,0), so both coordinate readers even fix the endpoints. Every non-omitted clause holds for these readers, simultaneously at all its types. Thus the entire remaining full typed separation schema holds, while C fails.

For the R row, the remaining translated L clause at σ is vacuous for E₁; E₀ reads actual equality. For the L row, E₁ satisfies R. Choose distinct x,y at σ and a full predicate F with Fx=⊤ and Fy=⊥. Then the H-valid formula

$$
(x=y)\to(Fx\to Fy)
$$
has value (1,0), rather than ⊤=(1,1). C identifies this H tautology with ⊤. This is the failure of C; a false identity merely being different from ⊥ would by itself establish only a failure of ND. Every admitted type has at least two elements in this construction, including e.

In particular, keeping conjunction, negation, both quantifier families and even full FixEq at every type does not recover primitive disjunction. The XOR join model in the table witnesses this. Similarly, preserving negation and universal quantification yields preservation of the derived existential ¬∀x¬Fx, but cannot identify it with the independent primitive existential without a bridge. Functional completeness in truth is insufficient to identify primitive logical objects over H.

## 7. Implication and what the recovery theorem does not assume

An implication-only proposal must specify whether implication is a new primitive or an abbreviation in the original primitives. Giving a new implication object its ordinary truth table and preserving it does not impose object identities on H's other primitive logical objects.

For the familiar abbreviation p→q:=¬p∨q, there is an explicit sharper example. In the preceding full-function model put

$$
\neg(b,c)=(\neg b,c),\qquad
(b,c)\lor(d,e)=(b\lor d,\neg c\lor e).
$$
Leave conjunction, all quantifiers and all equality predicates coordinatewise. The derived implication is then coordinatewise classical implication, so both coordinate readers preserve its full composite operation. They also preserve conjunction, all quantifiers and full FixEq, and fix both endpoints. They separate all relational types. Nevertheless ¬⊤=(0,1) differs from ⊥=(0,0), so C fails.

This example is stated for the specified abbreviation; it is not a redefinition of the framework's primitives. It explains why an over-C characterization using implication alone cannot be imported into an H recovery proof. The positive general rule is Theorem 2: specify the primitive rules whose proofs are to be transported, require their truth laws or stronger full identities, and use separation at the abstraction's actual relational type. Full typed scope contributes precisely the Functionality isolated in Theorem 1.

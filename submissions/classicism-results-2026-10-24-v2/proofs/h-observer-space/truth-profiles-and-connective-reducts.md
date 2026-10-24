# Truth profiles and connective reducts over H

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: misc, this note, §§1–8, unpaginated. The base throughout is H; C, NI, BF, Choice and Functionality are not standing assumptions.

## 1. Qualifications and scope

Propositions have type t and observers E have type tt in the fixed relational type system. Retain the fixed abbreviations

$$
a:=\forall p^t p,\qquad T:=a\lor\neg a,\qquad B:=a\land\neg a.
$$

Write

$$
S[R]:=\forall p,q\,[p=q\leftrightarrow\forall E(R(E)\to(Ep\leftrightarrow Eq))].
$$

The strong qualifications M, V and N are the whole-operation identities for preservation of conjunction, disjunction and negation. Qσ and Pσ are the corresponding whole-operation identities for universal and existential quantification at σ. A(E) means E(T) is true; Z(E) means E(B) is false. For example,

$$
M(E):=(\lambda p,q.E(p\land q))=(\lambda p,q.Ep\land Eq),
$$

$$
Q_\sigma(E):=(\lambda F.E(\forall x^\sigma Fx))
 =(\lambda F.\forall x^\sigma E(Fx)).
$$

A type list Δ is finite and metalinguistic. No object-language quantification over types is introduced. Every family quantified over below is an admitted term or member of its indicated type domain.

The main results concern these strong qualifications. Section 6 separately defines material qualifications and proves exact converse theorems for that weaker comparison tier. Truth equivalence, proposition identity, and whole-operation identity remain distinct.

## 2. The truth-profile representation theorem

Fix an H model and evaluation point satisfying S[R]. Let K be the set of its admitted observers satisfying R at that point, and define the external truth profile

$$
J(p):=\{E\in K:Ep\text{ is true}\}.
$$

Then S[R] says exactly that J is injective. Moreover, each preservation clause included in R gives the indicated identity of sets:

| Clause | Truth-profile identity |
|---|---|
| M | J(p∧q)=J(p)∩J(q) |
| V | J(p∨q)=J(p)∪J(q) |
| N | $J(\neg p)=K\setminus J(p)$ |
| Qσ | J(∀x:σ Fx)=⋂x∈Dσ J(Fx) |
| Pσ | J(∃x:σ Fx)=⋃x∈Dσ J(Fx) |
| A | J(T)=K |
| Z | J(B)=∅ |

For example, the full Qσ identity gives E(∀x Fx)=∀x E(Fx) at each input F. The ordinary H truth condition for the universal then says E belongs to the left profile exactly when it belongs to every profile on the right. The other rows are equally direct. K is nonempty: otherwise separation would identify T and B, contradicting their H truth conditions.

Thus the proposition domain has a faithful set representation preserving the listed operations and admitted indexed intersections or unions. This is an external representation of current truth profiles. It does not assert that every external subset of K is represented, that every external family is admitted, or that the internal terms λE.(R(E)∧Ep) form an extensional powerset object. In particular, the displayed set equations do not assert identities between those higher-type terms.

Internally, the corresponding order is

$$
p\preceq_R q:=\forall E(R(E)\to(Ep\to Eq)).
$$

It is always a preorder; S[R] is exactly its antisymmetry. Under separation, it is therefore a partial order. M makes the original conjunction its meet, and V makes the original disjunction its join. More explicitly,

$$
p\preceq_R q\ \leftrightarrow\ p\land q=p\quad(M),
\qquad
p\preceq_R q\ \leftrightarrow\ p\lor q=q\quad(V).
$$

N makes negation an order-reversing involution. A makes T greatest; Z makes B least. Each assertion follows from the displayed profile identities and injectivity, or directly by the same observer calculations in H.

### Admitted bounds and adjunctions

For Qσ and Pσ respectively,

$$
u\preceq_R\forall x^\sigma Fx
 \leftrightarrow\forall x^\sigma(u\preceq_R Fx),
$$

$$
(\exists x^\sigma Fx)\preceq_R u
 \leftrightarrow\forall x^\sigma(Fx\preceq_R u).
$$

Consequently, when both are listed, existential and universal quantification are respectively left and right adjoint to the constant-family map:

$$
\exists_\sigma\dashv(u\mapsto\lambda x^\sigma.u)\dashv\forall_\sigma.
$$

The order on admitted families is pointwise comparison. It is only a preorder on the family objects unless Functionality is separately available; the adjunction claim is a claim about preorders and does not assume Functionality. Nonempty type domains give both vacuity identities and ∀x Fx≼R∃x Fx.

The representation also yields the usual valid interaction laws whenever the requisite clauses are listed. Examples include

$$
u\land\exists x Fx=\exists x(u\land Fx)\quad(M,P_\sigma),
$$

$$
u\lor\forall x Fx=\forall x(u\lor Fx)\quad(V,Q_\sigma),
$$

and same-kind quantifier interchange at listed types. These are proposition identities. Mixed interchange gives the generally valid inequality

$$
\exists x^\sigma\forall y^\tau Fxy
 \preceq_R\forall y^\tau\exists x^\sigma Fxy
 \quad(P_\sigma,Q_\tau).
$$

No converse mixed interchange or distribution through an existentially quantified selection function follows from this calculation. Such a statement must respect the admitted selector domain and can contain a Choice principle. In particular, the recorded [Henkin model: base without a choice function](../../source/topics/classicism/models/henkin-without-relational-choice.yaml) has Extensionality, hence identity alone supplies all these separations, while Relational Choice fails. Thus all the preservation clauses together do not justify a general internal choice-of-witnesses step. The source's relative-consistency/metatheoretic condition remains part of that model claim.

## 3. Exact equational theory of the listed connective signature

Fix a connective signature Σ drawn from conjunction, disjunction and negation. Include the constant T only when acceptance is required or follows from the listed clauses, and B only when rejection is required or follows. Let R include the corresponding preservation clauses; it may contain additional clauses from §1.

For algebraic terms using only this listed signature, H+S[R] proves every equation valid in the corresponding reduct of the two-element Boolean algebra. More generally it proves every algebraic universal Horn implication

$$
\forall\bar p\,[s_1=t_1\land\cdots\land s_n=t_n\ \to\ s=t]
$$

valid in that reduct. To prove this, fix an eligible E and put hE(p)=1 exactly when Ep is true. The qualification makes hE a homomorphism for the listed operations and constants. premise identities pass to their images. The two-element implication gives equal truth values for the images of s and t, for every E, and separation gives s=t. This is also a direct H proof: expand the finite terms through the qualified observer and use the corresponding finite truth-table implication.

Conversely, any such equation or Horn implication failing in the two-element reduct fails in the ordinary full two-valued H model. The identity observer qualifies for every clause in §1 and separates its two propositions. Thus additional clauses do not remove that countermodel.

This gives the exact equational and algebraic universal-Horn theory of the listed reduct. It does **not** say that its equations conversely provide an admitted class of strong separators in every H model. For example, pointwise Boolean algebra equations alone do not manufacture internally admitted Boolean characters. Nor does the result treat unlisted primitive operations as if their usual identities had already been established.

## 4. The seven nonempty connective signatures

The following table states the proposition algebra forced by separation. “Derived” means an explicitly defined operation or bound, not an identification with an unlisted primitive.

| Signature | Structure without A or Z | Effect of A | Effect of Z |
|---|---|---|---|
| M | Meet semilattice | Fixed T is greatest | Fixed B is least |
| V | Join semilattice | Fixed T is greatest | Fixed B is least |
| N | Involutive negation | T greatest and ¬T least in the accepting observer order; no added separation strength | B least and ¬B greatest in the rejecting observer order; no added separation strength |
| M,V | Original distributive lattice | Fixed T is greatest | Fixed B is least |
| M,N | Boolean algebra with derived join ¬(¬p∧¬q), fixed least B, and greatest ¬B | Aligns T with ¬B | Already follows |
| V,N | Boolean algebra with derived meet ¬(¬p∨¬q), fixed greatest T, and least ¬T | Already follows | Aligns B with ¬T |
| M,V,N | Boolean algebra for the original connectives, with fixed T and B | Already follows | Already follows |

For MN, E(B)=E(a∧¬a)=Ea∧¬Ea is false, while E(¬B) is true. For VN, E(T)=E(a∨¬a)=Ea∨¬Ea is true, while E(¬T) is false. These give the stated fixed and derived bounds. All Boolean equations in the two-operation reduct follow from §3. In particular the MN row establishes distributivity for its derived join, not merely an orthocomplemented lattice.

Neither the MN row nor the VN row identifies its derived binary operation with the other primitive. The small models in [the observer lattice](../observer-lattice.md), §7, illustrate the MN distinction. A full-operation identity connecting a primitive to its derived expression would make its strong preservation follow by composition of the given operation identities. A mere pointwise agreement does not automatically do so over H.

### Exact endpoint additions

Let R contain any additional restrictions held fixed. The following are exact equivalences over H:

$$
S[A\land M\land R]\leftrightarrow
 S[M\land R]+\forall p(p\land T=p),
$$

$$
S[Z\land M\land R]\leftrightarrow
 S[M\land R]+\forall p(p\land B=B),
$$

$$
S[A\land V\land R]\leftrightarrow
 S[V\land R]+\forall p(p\lor T=T),
$$

$$
S[Z\land V\land R]\leftrightarrow
 S[V\land R]+\forall p(p\lor B=p).
$$

Forward, preservation and the endpoint truth condition make both sides of each equation observationally equivalent. Conversely, a meet observer rejecting a meet unit T rejects every proposition; a meet observer accepting an absorbing B accepts every proposition. Dually, a join observer rejecting an absorbing T rejects everything, and one accepting a join unit B accepts everything. Such constant truth profiles distinguish no pair, so discarding them preserves separation. The extra restriction R is unchanged throughout.

For pure negation,

$$
S[N]\leftrightarrow S[A\land N]\leftrightarrow S[Z\land N],
$$

$$
S[A\land Z\land N]\leftrightarrow S[N]+(B=\neg T).
$$

If E has the wrong endpoint truth, postcompose it with negation. The admitted operator λp.¬Ep still satisfies the full N identity, reverses its truth profile, and retains every disagreement. This proves the first line. The second follows by separation of B and ¬T in its forward direction; conversely B=¬T makes an accepting N observer reject B automatically.

The first line changes the observer order: for the bare N class, closure under post-negation makes comparison symmetric, hence equality under separation. It does not say the bare and accepting classes induce the same order. Also the normalization is not asserted when arbitrary additional clauses are present: post-negation need not preserve M or Q.

For the two complementary signatures the exact alignments are

$$
S[A\land M\land N]\leftrightarrow S[M\land N]+(T=\neg B),
$$

$$
S[Z\land V\land N]\leftrightarrow S[V\land N]+(B=\neg T).
$$

The other endpoint condition in each line already follows from qualification. For MVN both follow directly from qualification.

## 5. What endpoint fixing adds

U(E):=E(T)=T and its bottom analogue constrain the actual output objects, whereas A and Z constrain only their current truth. Replacing acceptance or rejection by fixing makes the eligible class smaller and the separation assertion stronger. The truth-profile representation records the endpoint truth facts but does not, by itself, prove these stronger output identities.

Accordingly, none of the endpoint equivalences in §4 silently replaces A or Z by fixing. Their equivalence over C uses additional reasoning from that stronger base; it is not an H consequence of the representation theorem. Special additional qualifications can give an H equivalence: fixing of identity judgments, together with accepting separation, proves (T=T)=T and thereby makes every such observer fix T. That separate argument is given in the observer-lattice note, §4.

## 6. Material qualifications give exact elementary converse theorems

Define M_m(E) by ∀p,q[E(p∧q)↔(Ep∧Eq)], and define V_m,N_m,Q_mσ,P_mσ by the analogous material laws, universally closing their inputs. Write S_m[signature] for separation with these material qualifications. A and Z retain their truth meanings. These are not the strong qualifications of §1.

### Meet

Over H, S_m[M] is equivalent to the pointwise associativity, commutativity and idempotence equations for conjunction. Necessity follows from §2's calculation, which needs only material preservation.

For sufficiency assume those equations and define the admitted principal test

$$
E_b(p):=(b\land p=b).
$$

The semilattice equations give

$$
b\land(p\land q)=b
\ \leftrightarrow\ (b\land p=b\ \land\ b\land q=b),
$$

so E_b preserves meet materially. If every principal test agrees on p and q, the tests b=p and b=q give p≤q and q≤p, hence p=q. Thus they separate.

Adding A is exactly adding the greatest-element equation p∧T=p. Adding Z is exactly adding the least-element equation p∧B=B. To obtain rejecting separating tests, choose b=p when p is not below q, or b=q in the reverse case; the chosen b cannot be B. The same argument handles both endpoint conditions together. No external filter or choice of a family of tests is used: λb,p.(b∧p=b) is an admitted term.

### Join

Dually, S_m[V] is equivalent over H to the join-semilattice equations. Use the admitted tests

$$
E_b(p):=\neg(p\lor b=b).
$$

Since p∨q≤b iff p≤b and q≤b, ordinary truth-level De Morgan reasoning proves material join preservation. If p is not below q, the test b=q accepts p and rejects q; reverse the roles for the other case.

Adding A is exactly requiring T greatest, p∨T=T; a separating cut b is then not T. Adding Z is exactly requiring B least, p∨B=p, which makes every principal cut reject B. Both can be imposed together.

### Negation

Over H,

$$
S_m[N]\leftrightarrow\forall p(\neg\neg p=p).
$$

For the converse, double negation makes negation an involution; H truth conditions already exclude p=¬p. Use the admitted tests

$$
T_b(r):=(r=b)\lor\bigl(r\land(r\ne\neg b)\bigr).
$$

At r=b the test is true, at r=¬b it is false, and off that pair it has r's truth value. Double negation therefore gives T_b(¬r)↔¬T_b(r). For distinct p,q both false, use b=p; for both true, use b=¬p. For differing truth values identity suffices. This proves separation. The endpoint-orientation arguments of §4 apply materially as well: A alone or Z alone adds nothing; both together add exactly B=¬T.

No corresponding converse from double negation to **strong** N separation is asserted here.

## 7. Exact material matching-quantifier representations

For every finite Δ, S_m[A∧M∧QΔ] is equivalent over H to the following output-level structure:

1. Conjunction is a meet semilattice with greatest element T.
2. For every σ in Δ and admitted F of type σt,
   \[

$$
u\land(\forall x^\sigma Fx)=u
\leftrightarrow\forall x^\sigma(u\land Fx=u).
$$

   \]

Necessity is the observer-order theorem. For sufficiency, the same principal test E_b(p):=(b∧p=b) from §6 accepts T and preserves meet materially. The displayed GLB equivalence says exactly that it preserves every listed universal materially. Thus a single admitted family of principal tests satisfies all the listed laws simultaneously and separates. A can be omitted if the top condition is omitted, or Z can also be added with the bottom bound and the nonbottom choice of separating b from §6.

Dually, S_m[Z∧V∧PΔ] is equivalent to a join semilattice with least B in which each listed existential is the LUB of its admitted families:

$$
(\exists x^\sigma Fx)\lor u=u
\leftrightarrow\forall x^\sigma(Fx\lor u=u).
$$

The principal cuts E_b(p):=¬(p∨b=b) preserve every listed existential materially by this LUB equivalence and ordinary quantifier duality in truth. No primitive quantifier-duality identity is assumed. Again the endpoint variants follow by the corresponding bounds.

There is also a formulation without a specified meet operation. S_m[A∧QΔ] is equivalent to the existence of an admitted binary relation ≼ on propositions that is a partial order with greatest T and makes every listed universal the GLB of its admitted families. Forward use the observer-defined relation in §2. Backward use E_b(p):=(b≼p): the GLB condition is exactly its material Q law, and the tests b=p,q establish antisymmetry-based separation. Dually, S_m[Z∧PΔ] is equivalent to an admitted partial order with least B and the corresponding existential LUBs, using E_b(p):=¬(p≼b).

These converse theorems depend on a principal test preserving the matching bounds. They do not establish that an arbitrary ordered structure with both admitted GLBs and LUBs supplies tests preserving both kinds simultaneously. These arguments alone do not give a converse from distributive-lattice or Boolean-algebra equations to joint separation without an additional admission premise.

With the explicit additional preorder Zorn instance at tt, [lattice character extension](zorn-lattice-character-extension.md), §§2–5, supplies the admitted prime filters needed for exact material joint lattice and Boolean converses. Plenitude and the stated Functionality premises then give the stronger tiers. That conditional result does not add preservation of the primitive quantifiers.

## 8. Boundaries and connection to the larger lattice

The strong main tier is a representation by internally admitted operators satisfying whole-operation equations. The material comparison tier admits elementary principal-test converses. The exact equational theory in §3 lies between these descriptions: it determines what algebraic equations strong separation forces, but does not erase the distinction between truth-preserving maps and whole-operation identities.

All proofs above are over H. For C's guard normalization, the exact C bounds, and explicit small H models keeping derived and primitive operations apart, see [the observer lattice](../observer-lattice.md), §§1–4 and 7. Those stronger-base results are not used to prove the H statements here.

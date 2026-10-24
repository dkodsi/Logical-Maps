# Injective logical observers and Boolean transversals

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–6, unpaginated.

Over C5, a currently injective logical observer has a qualified left inverse exactly when its canonical image modality admits a Boolean transversal. The transversal is a single proposition, and it determines the inverse by an explicit term. This gives a bijection between qualified left inverses and the admitted transversals, without Choice or an atom premise.

Injectivity does not by itself suffice. A full-function model based on the complete Boolean algebra 2×RO(Cantor²) has an injective observer preserving every logical operation but no qualified left inverse. Its ordinary order adjoints remain admitted left inverses; the obstruction concerns their logical qualification. The model fails ordinary logical separation, so it does not settle whether separation by injective observers has the same strength as separation by qualified left-invertible observers.

## 1. The observer and its image closure

Work over C5. Fix a finite external list Δ containing t, and an admitted currently injective Good_Δ observer E:tt. Good has the full Boolean and listed quantifier composite identities. Current injectivity means

$$
\forall p,q\,(Ep=Eq\to p=q).
\tag{1}
$$

Use 0,1 for Bottom, Top and x≤y for x∧y=x. The [canonical-adjoint theorem](canonical-adjoints-and-image-factorization.md), §§2–4, supplies admitted terms

$$
R(q):=\exists p\,[(Ep\le q)\land p],
\qquad L(q):=\neg R(\neg q),
\qquad C_E:=E\circ L.
\tag{2}
$$

They satisfy L⊣E⊣R. Since E is injective, its maximal kernel is 0, and

$$
L\circ E=I=R\circ E,
\qquad L0=0,
\qquad L1=1.
\tag{3}
$$

These are whole-operation identities where appropriate, using C5 Functionality. L preserves every admitted existential quantifier and binary join; it need not preserve meet or negation.

C_E is the least image value above its input: q≤C_E(q), its fixed points are exactly the image of E, it is idempotent, and it preserves admitted joins. It is the auxiliary image closure, not the language's original possibility operation.

We shall use the following identity, valid already for the adjoints of any Boolean logical E:

$$
L(q\land Ep)=Lq\land p.
\tag{4}
$$

For every r, adjunction and Boolean residuation give

$$
\begin{aligned}
L(q\land Ep)\le r
&\longleftrightarrow q\land Ep\le Er\\
&\longleftrightarrow q\le E(\neg p\lor r)\\
&\longleftrightarrow Lq\le\neg p\lor r\\
&\longleftrightarrow Lq\land p\le r.
\end{aligned}
\tag{5}
$$

Antisymmetry proves (4). Applying E also gives

$$
C_E(q\land Ep)=C_E(q)\land Ep.
\tag{6}
$$

All families and operators in these formulas are admitted. The earlier [type-reduction theorem](../modal-selectors-and-quantifier-reduction.md), §4, makes a $\mathrm{Good}_{\{t\}}$ observer Good at every requested finite list over C5. The same applies to any left inverse constructed below. No infinitary qualification or object-language type quantifier is introduced.

## 2. One proposition determines a qualified left inverse

Define the admitted proposition predicate

$$
\mathrm{Sel}_E(u):=
C_E(u)=1\ \land\
\forall q\,[u\land C_E(u\land q)=u\land q].
\tag{7}
$$

Call such a u a **Boolean transversal for the image closure**. This terminology abbreviates exactly (7); no set of fibers, quotient type or external selection function is presupposed. The first condition gives coverage of the image. The second says that expanding a part of u to its image ceiling creates no additional part inside u.

For any u define the admitted term

$$
F_u(q):=L(u\land q).
\tag{8}
$$

**Theorem 1.** If Sel_E(u), then F_u is a qualified logical observer at every requested finite list and

$$
F_u\circ E=I.
\tag{9}
$$

**Proof.** Since E(Lu)=C_E(u)=1=E1 and E is injective, Lu=1. Put α(p):=u∧Ep. Equation (4) gives

$$
L(\alpha(p))=L(u\land Ep)=Lu\land p=p.
\tag{10}
$$

Hence α is injective, and (10) is already the output form of (9). The second selector condition gives

$$
\alpha(F_uq)=u\land E(L(u\land q))=u\land q.
\tag{11}
$$

The map α preserves the Boolean operations relative to [0,u], including relative complement u∧¬x; its top value is u and its bottom value is 0. Equation (11) makes it onto that interval. Thus α is a Boolean isomorphism onto [0,u], with inverse the restriction of L. This is expressed by admitted ambient terms and guarded output identities, not by introducing a new interval type.

Equations (10)–(11) transfer the Boolean identities to F_u. For example, apply α to the proposed meet identity: α(F_u(p∧q))=u∧p∧q, while α(F_up∧F_uq)=(u∧p)∧(u∧q). Injectivity identifies the outputs. The same argument handles join and relative complement, giving F_u(¬q)=¬F_uq. Also F_u0=0 and F_u1=Lu=1.

For an arbitrary admitted G:σt, L's admitted-join preservation and the fixed-guard distributivity identity give

$$
\begin{aligned}
F_u(\exists x^\sigma Gx)
&=L(u\land\exists x^\sigma Gx)\\
&=L(\exists x^\sigma(u\land Gx))\\
&=\exists x^\sigma F_u(Gx).
\end{aligned}
\tag{12}
$$

Negation preservation and quantifier duality give every universal law. C5 Functionality collects all Boolean, quantifier and inverse output identities into the full composite identities. The translated equality clauses follow from Boolean qualification over C. This proves the stated qualification and (9), with no choice of preimages. ∎

## 3. Every qualified left inverse arises this way

Suppose F is Good_Δ and F∘E=I. It is onto: p is the F-image of Ep. Its maximal kernel is the admitted proposition

$$
k_F:=\exists q\,[(Fq=0)\land q].
\tag{13}
$$

The [kernel theorem](surjective-logical-observers.md), §2, gives Fk_F=0 and says F is injective on [0,¬k_F]. Put

$$
u:=\neg k_F.
\tag{14}
$$

Then Fu=1. Both u∧E(Fq) and u∧q lie below u, and applying F to either gives Fq. Interval injectivity therefore yields

$$
u\land E(Fq)=u\land q.
\tag{15}
$$

For every p, the original L⊣E adjunction now gives

$$
\begin{aligned}
L(u\land q)\le p
&\longleftrightarrow u\land q\le Ep\\
&\longleftrightarrow Fq\le p.
\end{aligned}
\tag{16}
$$

For the forward direction of the second equivalence, apply F and use Fu=1 and FE=I. Conversely, if Fq≤p, (15) gives u∧q=u∧E(Fq)≤Ep. Antisymmetry proves

$$
Fq=L(u\land q)=F_uq.
\tag{17}
$$

Taking q=1 in (17) gives Lu=1 and hence C_E(u)=1. Substituting (17) into (15) gives the other condition in (7). Thus u is a Boolean transversal.

Conversely, the kernel of the F_u constructed in Theorem 1 is exactly the principal ideal below ¬u. Equation (11) and injectivity of α give

$$
F_uq=0\quad\longleftrightarrow\quad u\land q=0
\quad\longleftrightarrow\quad q\le\neg u.
\tag{18}
$$

Its greatest kernel proposition is therefore ¬u. We have proved the exact classification

$$
\boxed{
\begin{array}{c}
\text{admitted Good}_{\Delta}\text{ left inverses F of E}
\\[2pt]
\longleftrightarrow
\\[2pt]
\text{admitted propositions u satisfying }\mathrm{Sel}_E(u),
\end{array}}
\tag{19}
$$

with mutually inverse assignments

$$
F\longmapsto\neg k_F,
\qquad
u\longmapsto\lambda q.L(u\land q).
\tag{20}
$$

Both assignments are admitted terms. Equality of the recovered observers is a whole identity by Functionality. In particular, the existence of a qualified left inverse has been replaced by a condition quantifying only over one proposition u and the proposition inputs q to the fixed image closure. No general Choice equivalence is asserted.

In a powerset interpretation, this has the familiar concrete reading. If E(p)=f⁻¹[p] for a surjective map f, then L is direct image and C_E(q)=f⁻¹[f[q]]. Condition (7) says that u meets every fiber of f in exactly one point; F_u(q)=f[u∩q]. This explains the term “transversal.” In an arbitrary Henkin model, existence of such a representative proposition remains an admission requirement, and the abstract theorem does not assume a powerset representation.

## 4. A complete Boolean algebra model with full function domains

The next construction refutes the claim that every injective logical observer over C5 has a qualified left inverse. The model has full function domains; the obstruction will be Boolean structure, not absence of an unqualified operation representing a set function.

Let $X=2^{\mathbb N}$ be Cantor space and $Z=X\times X$. Write B=RO(Z) for its regular-open algebra. For an open set U, regular open means U=int(cl(U)). The algebra has 0_B=∅, 1_B=Z, finite meet U∩V, complement $\mathrm{int}(Z\setminus U)$, and arbitrary joins

$$
\bigvee_i U_i=\mathrm{int}\mathrm{cl}
\left(\bigcup_iU_i\right).
\tag{21}
$$

Meets are obtained by complementing joins of complements. These operations make B a complete Boolean algebra. The completeness assertion follows directly from (21): any regular open upper bound of every U_i contains the regularization of their union. Complement and finite-intersection identities follow from regular openness; finite intersection distributes over (21), since intersecting an open set with a dense open subset of an open set leaves a dense subset of their intersection. These are statements about actual regular-open subsets of Z.

Put

$$
A=2\times B,
\qquad
0_A=(0,\varnothing),\quad1_A=(1,Z).
\tag{22}
$$

Interpret the proposition domain as A. A proposition (ε,U) is currently true exactly when ε=1. Let the individual domain be a singleton. Recursively, at every allowed relational arrow type take the full set of functions between the already defined domains. Application and lambda abstraction are ordinary set-function application and abstraction.

Interpret the Boolean connectives by the complete Boolean algebra operations of A. For each admitted input type σ, interpret

$$
\forall_\sigma F:=\bigwedge_{x\in D_\sigma}F(x),
\qquad
\exists_\sigma F:=\bigvee_{x\in D_\sigma}F(x).
\tag{23}
$$

Identity at every type returns 1_A for actual equality of the domain objects and 0_A otherwise. Every operation just specified is admitted, since all relevant function domains are full.

**H and C soundness.** First verify the stronger algebra-valued assertion: every H theorem evaluates to 1_A under every assignment. Propositional axioms are Boolean identities. The quantifier axioms follow from the meet/join bounds in (23), and their inference rules preserve value 1_A; fixed propositional guards distribute over the required meets or joins in a complete Boolean algebra. Equality axioms hold because equality is actual crisp identity, and contextual beta/eta hold because the higher domains are full function spaces. Substitution and generalization preserve the assertion, the latter taking a meet of values all equal to 1_A.

Consequently, when H proves φ↔ψ, their A-values are equal under every assignment: a Boolean biconditional has value 1_A exactly when its arguments are equal. The lambda abstractions of the two bodies are therefore the same actual functions. Their identity has value 1_A. This verifies C's Logical Equivalence schema with its H-theoremhood side condition. It does not infer equality merely from agreement of the designated truth bit.

The designated truth map A→2 is the first projection and preserves arbitrary meets and joins. Thus (23) also gives the ordinary classical truth clauses for every current quantifier. Equality and beta/eta give the remaining H truth requirements.

**C5 and Functionality.** Every identity judgment is 0_A or 1_A. A true distinctness judgment is therefore 1_A and its box is 1_A. Every ND instance, its universal closure and its box have value 1_A. The model satisfies C5 at all types. Functionality holds because the functions have exactly the admitted arguments and are equal when they agree at each argument. The fixed abbreviations for Top and Bottom have values 1_A and 0_A: the value of ∀p p is 0_A, and its excluded middle and contradiction have these bounds.

This is a complete-Boolean-algebra interpretation with a completely prime designated truth map. It makes no claim that arbitrary Boolean algebras, or arbitrary ultrafilters on a complete Boolean algebra, give the required current quantifier truth clauses.

## 5. An injective fully logical observer with no qualified left inverse

There is an explicit homeomorphism h:X→X×X: split a binary sequence into its even and odd coordinates. Its inverse interleaves them. Define

$$
i:B\longrightarrow B,
\qquad i(U):=h^{-1}[U]\times X.
\tag{24}
$$

Homeomorphism pullback is a complete Boolean isomorphism RO(Z)→RO(X). The cylinder map V↦V×X preserves complement and the joins (21): closure and interior commute with product by the nonempty space X. It is injective. Therefore i is a complete Boolean embedding, and its image is exactly the first-coordinate cylinders V×X with V∈RO(X).

Define the admitted observer

$$
E(\varepsilon,U):=(\varepsilon,i(U)).
\tag{25}
$$

It is injective and preserves arbitrary Boolean meets and joins. Equations (23) show that it commutes with quantifiers at every admitted type, on arbitrary predicate inputs. Since function equality is actual equality, these are the full composite operation identities. Its Boolean qualification also gives the translated equality clauses. Thus E is Good at every finite list.

Let C_B be the image ceiling for i. In particular, for nonempty clopen sets P,D⊆X,

$$
C_B(P\times D)=P\times X.
\tag{26}
$$

Indeed any image cylinder containing P×D must contain every first coordinate in P, and P×X is itself an image cylinder. The image ceiling of (25) is componentwise

$$
C_E(\varepsilon,U)=(\varepsilon,C_B(U)),
\tag{27}
$$

because its image permits either first bit independently of the cylinder component.

Suppose u=(ε,U) satisfied the Boolean transversal condition (7). Coverage C_E(u)=1_A would give ε=1 and C_B(U)=Z, in particular U≠∅. As a nonempty open subset of Cantor², U contains a nonempty clopen rectangle P×D. Cantor space has no isolated points, so D can be split into two disjoint nonempty clopen sets D₀,D₁. Put

$$
q=(0,P\times D_0).
\tag{28}
$$

Then u∧q=q. By (26)–(27),

$$
u\land C_E(u\land q)
=(0,U\cap(P\times X)).
\tag{29}
$$

The second component contains P×D₁, whereas that of u∧q is P×D₀. The sets differ, contradicting the second selector identity. Thus there is no Boolean transversal for E. By Theorem 1 and its converse, there is **no $\mathrm{Good}_{\{t\}}$ left inverse** of E, and hence no left inverse qualified at any finite list containing t.

The operators L and R from (2) are nevertheless admitted and satisfy L∘E=R∘E=I. Therefore this is not a failure of unqualified left-inverse admission. The additional Boolean/logical qualification fails. By [the native-modal commutation criterion](canonical-adjoints-and-image-factorization.md), §7, E also commutes with the original Box and Diamond. Even that natural modal qualification does not supply a qualified left inverse for the individual observer.

## 6. Why the separation comparison remains open here

This model does not satisfy ordinary logical separation. To verify that directly, B=RO(Cantor²) is atomless: any nonzero regular open contains a clopen rectangle, and splitting one coordinate gives a strictly smaller nonzero regular open. Thus A has exactly one atom,

$$
w=(1,\varnothing).
\tag{30}
$$

For any $\mathrm{Good}_{\{t\}}$ observer H in the model, compose H with the first-bit projection to obtain a truth map χ:A→2. It is a complete Boolean homomorphism. Indeed type-t quantifier preservation gives meet/join preservation for every family encoded by a function A→A; full function domains encode any external subset by returning its members and the appropriate default endpoint elsewhere. The first-bit projection preserves those meets and joins too.

Any complete Boolean character χ comes from an atom. Let b be the meet of its true elements. Completeness gives χ(b)=1, so b≠0. For every p, either b≤p or b≤¬p according as χ(p)=1 or χ(p)=0. If 0<q≤b, the second alternative for q is impossible, while the first gives b≤q. Thus b is an atom. Since (30) is the only atom, χ(p)=1 exactly when w≤p, which is exactly the original first-bit truth test.

Consequently every $\mathrm{Good}_{\{t\}}$ observer is currently truth-correct. The distinct propositions (0,U) and 0_A, for any nonempty U∈B, are both false under all these observers. This refutes OS at the single propositional list {t}, and therefore refutes its full schema as well.

The results established here are therefore:

- Qualified left inverses of a fixed injective observer over C5 are exactly its admitted Boolean transversals, with the explicit bijection (20).
- Injectivity, even together with every full logical law and native Box/Diamond commutation, does not force an individual qualified left inverse.
- If a theory guarantees such transversals for every injective observer in the requested classes, their injective and qualified-left-invertible classes coincide. This is a sufficient explicit extra condition, not an asserted equivalence with an ordinary Choice principle.
- The model does not decide whether InjSep can have the same separating power as qualified left-inverse separation through different witnesses. That separation-level comparison remains unproved by this argument.

## 7. Sources

The Boolean-transversal classification, explicit bijection with qualified left inverses, complete-Boolean-algebra H/C5 interpretation, and regular-open nonsplitting example are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–6, unpaginated.

The adjoints, image closure and their admitted-family properties are from [Canonical adjoints and image factorization](canonical-adjoints-and-image-factorization.md), §§2–7, direct source `misc`. The maximal-kernel/interval-injectivity argument used for an existing left inverse is [Surjective logical observers](surjective-logical-observers.md), §§2–4. The same-observer quantifier type reduction is [Modal selectors and quantifier reduction](../modal-selectors-and-quantifier-reduction.md), §4. The fixed H/C language and type conventions are [the topic background](../../source/topics/classicism/background.md).

The topological algebra and its observer are specified and verified here; no attribution to a published countermodel is asserted. No arbitrary external-function admission is used in the abstract theorem. The concrete model explicitly has full function domains, and its Boolean completeness is part of its construction.

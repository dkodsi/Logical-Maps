# Two models separating the upper observer principles

Ordinary mathematical arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: misc, this note, §§1–3, unpaginated.

Use the full typed OS and finite-image separation Fin defined in [the main hierarchy note](logical-observer-hierarchy.md), §1. GoodΔ requires full Boolean and quantifier composite identities, with the translated equality clauses. Over C those equality clauses are redundant. Internal finite image means the existing Frege finite-cardinality formula; no uniform bound is imposed.

The two results are:

```math
\begin{aligned}
\text{Full omega chain:}&\quad\mathrm C+\Box\mathrm{Atomicity}_t+\Box\mathrm{BF}+\Box\mathrm{OS}+\neg\mathsf{Fin},\\
\text{Root extension:}&\quad\mathrm C+\Box\mathrm{BF}+\mathsf{Fin}+\neg\mathrm{Atomicity}_t+\neg\Box\mathrm{OS}
\end{aligned}
```

Thus Fin is incomparable with C + Atomicity_t + BF and with ☐OS. The second model also fails ND_t.

## 1 Full action model on the omega chain

### Construction and positive verdicts

Take objects n∈N, with one arrow n→m exactly when n≤m, singleton individuals, and the full relational action-model domains. Evaluate at 0. This is an instance of the [full action construction](../source/topics/classicism/groups/full-action-models.yaml), Classicism §3.5, pp. 58–61, Appendix D, pp. 73–74; its application here and the observer obstruction below have direct source misc.

At n, propositions are all subsets of the tail T_n={m:m≥n}, truth is membership of n, Boolean operations are the set operations, and transport is restriction to a later tail. In particular every proposition algebra is atomic.

All arrows are epic. Their transports at every type are onto: extend any future full truth profile across the omitted initial stages, assigning arbitrary truth values there. Thus BF holds at every object, by the recorded [full-epic Barcan argument](../source/topics/classicism/arguments/full-epic-barcan.yaml), whose source is Classicism Proposition 3.24(ii), §3.5. Atomicity and BF give OS at every object by [the improved atomic theorem](observer-lattice.md), §5. Therefore ☐Atomicity at t, ☐BF and ☐OS all hold at 0.

### Internal finiteness is external finiteness here

This step is particular to the full model. For the relevant type, take the set of cardinality objects obtained by standard finite iterations of successor starting from zero. Fullness admits a property with precisely that current extension. It contains zero and is successor-closed. Therefore any internally finite cardinality belongs to that set, by the impredicative definition of finite cardinality. If it holds of a property X, the ordinary truth clauses for zero and successor show that X has a standard finite extension. In particular an internally finite image of E is externally finite as a subset of D_t(0). This argument does not identify internal and external finiteness in arbitrary Henkin models.

### No finite-image observer can satisfy Good at t

Suppose E is Good_{t} and has finite image. At 0 it is a Boolean homomorphism from P(N) to P(N), fixing both endpoints. Its image is an externally finite Boolean subalgebra. The atoms of that image form a finite partition of N into nonempty cells. At least one cell C is unbounded.

For n∈C the truth test

```math
h(p):=[n\in E_0(p)]
```

is independent of which n in C is used, because each E_0(p) is a union of whole cells. It is a Boolean truth homomorphism.

If p is finite, choose n∈C above its support. Naturality of application gives

```math
E_0(p)\restriction T_n=E_n(p\restriction T_n)=E_n(\varnothing)
```

The last proposition is empty, because the transported observer fixes Bottom. Hence h(p) is false. It follows by Boolean preservation that h accepts every cofinite proposition.

Fullness admits a property F of propositions with the following truth profile, at every m and x⊆T_m:

```math
F_m(x)\text{ is true at }m\quad\leftrightarrow\quad x\ne\{m\}
```

For a fixed p⊆N, the proposition F_0(p) is true at m iff p∩T_m≠{m}. It can fail only at the maximum of a nonempty finite p. Thus F_0(p) is always cofinite. But (∀p Fp)_0 is empty: at every m the current input x={m} falsifies F.

Choose n∈C. Since every F_0(p) is cofinite, E_0(F_0(p)) contains n. Every x⊆T_n extends to some p⊆N; naturality of F and E then shows that E_n(F_n(x)) is true at n for every x. Consequently

```math
\begin{aligned}
&\forall x\,E_n(F_n(x))\text{ is true at }n,\\
&E_n(\forall x\,F_n(x))=E_n(\varnothing)\text{ is false at }n
\end{aligned}
```

This contradicts the transported full Q_t identity. The comparison must be evaluated at n∈C, not necessarily at 0. Hence no finite-image Good_{t} observer exists at 0. Since Top and Bottom are distinct, the (t,{t}) finite-image separation instance fails.

## 2 Root truth-profile extension of qualitative contrast

### Retained model and new predecessor

Let B be the existing qualitative-contrast action model, keeping its two objects W0,W1, its groupoid of bijections, and its admitted domains. At W0 it satisfies C5 and ☐BF, fails Boolean separation, and has a true atom A. The complementary W1-target component d is nonzero and atomless. See the [recorded construction](../source/topics/classicism/models/symmetric-qualitative-contrast.yaml), [Boolean-separation obstruction](observer-countermodel.md), §§2–4, and [local observer proof](local-observers.md), §§2–4. The underlying symmetric construction and its source qualifications are retained unchanged.

Adjoin a fresh predecessor * with an arrow i:*→W0. The arrows from * to an old object V are g∘i for old g:W0→V. There is no arrow from an old object to *. Define root domains recursively. Write π for transport along i. For individuals use A_e=B_e(W0), π_e=id. For each relational type τ=σ₁…σ_k t, including k=0 for t, put

```math
A_\tau=\{0,1\}^{A_{\sigma_1}\times\cdots\times A_{\sigma_k}}\times B_\tau(W_0),
\qquad\pi_\tau(f,b)=b
```

Thus A_t={0,1}×B_t(W0). Root truth is its first coordinate. Every projection π_σ is onto, and later transports are the old g_σ composed with π_σ.

Application sections the first truth function and applies the second component to the projected argument. In particular, if F=(f,b) has type σt and x∈A_σ,

```math
F(x)=(f(x),b(\pi_\sigma x))
```

For curried types the same rule returns the section f(x,−) together with the old curried application. Boolean operations act by ordinary Boolean operations on root truth functions and by the old Boolean operations on tails. For a predicate F=(f,b),

```math
\begin{aligned}
\forall_\sigma F&=(\forall x\in A_\sigma\,f(x),\forall_\sigma^B b),\\
\exists_\sigma F&=(\exists x\in A_\sigma\,f(x),\exists_\sigma^B b)
\end{aligned}
```

The equality proposition of x,y∈A_σ is

```math
\bigl(\delta(x,y),\,(\pi_\sigma x=\pi_\sigma y)^B\bigr)
```

Lambda abstraction takes the actual root truth function of its body and the old abstraction evaluated under the projected assignment. This rule is well-defined recursively at every admitted type.

### Soundness and Barcan

The root truth clauses are the ordinary classical clauses, with actual equality. Application and abstraction satisfy beta and eta: sectioning gives beta, and a function and its lambda re-expansion have the same truth function and the same old tail. Transport commutes with application and each interpretation, by its definition on the old components. Hence the H rules are sound.

For C's Logical Equivalence, H-equivalent formula bodies have the same root truth function for every root assignment. Their old abstractions are identical in B, since B is a C model. Their root pairs are therefore equal. This verifies the actual schema on abstractions, not only equivalence of their current truth values. Thus the new model is a C model.

Every π_σ is onto; every old arrow acts bijectively at every type. All root-to-future transports are therefore onto. BF follows directly: if every current F(x) is Top, its old values are Top on every old argument by surjectivity, and its current truth values are all true, so ∀F is Top. BF already holds at all old objects. Thus ☐BF holds in the extension.

### Qualified observers with finitely many outputs

At W0, retain the admitted principal observer

```math
B_A(p):=\Box(A\to p)
```

It reads the W0-target component, is endpoint-valued, and satisfies every finite Good list by full composite identities. The direct proof at each old object is in the local observer proof §4: transported A remains the atom of all W0-target arrows; Boolean operations and the admitted quantifiers preserve its two-valued reading. The groupoid's bijective type actions supply the universal and existential laws.

For every old arrow g:W0→V define a root observer E_g=(f_g,B_A), and define E_*=(f_*,B_A), by

```math
\begin{aligned}
f_g(p)&:=\text{the truth at }V\text{ of }g_t(\pi_t p),\\
f_*(p)&:=\text{the root truth of }p
\end{aligned}
```

All are admitted because the root truth function is unrestricted. Their values are

```math
\begin{aligned}
E_g(p)&=(f_g(p),B_A(\pi_t p)),\\
E_*(p)&=(f_*(p),B_A(\pi_t p))
\end{aligned}
```

Each image is contained in the finite list of pairs (ε,Bottom_B) and (ε,Top_B), ε∈{0,1}. Such a finite list witnesses the internal finite-cardinality formula, so each has finitely many outputs in the required sense.

For Boolean composite identities, the root truth functions agree because f_g and f_* are evaluations, and the old components agree because B_A satisfies the old full identities.

For Q_σ of E_g, the root truth of the left side at F=(f,b) is the truth at V of ∀_σ g(b), equivalently the truth of g(b)(y) for every y∈B_σ(V). The root truth of the right side says the truth of g(b)(g_σπ_σ x) for every x∈A_σ. These agree by surjectivity of g_σπ_σ. For E_* both sides are just ∀x f(x). The existential calculation is the same with ∃. The old components of these composites are identical by B_A's qualification. Consequently the pairs defining the whole λF operations are identical, establishing full composite preservation. The translated equality clauses then follow from C and Boolean qualification, or directly from these truth evaluations.

The same observer E_g or E_* qualifies for every finite list. This semantic fact about these witnesses is not a new infinitary object-language formula.

### Full separation and failures

If two root propositions differ in their first coordinate, E_* distinguishes them. If their old tails differ, the old proposition sets disagree at some outgoing arrow g, and E_g distinguishes them. Thus the observers separate propositions.

For relations of type σ₁…σ_k t, differing root truth functions are detected at some root tuple, followed by E_*. If the old tails differ, old Functionality supplies an old tuple on which their proposition values differ. Lift the tuple through the surjective projections π_σ, then use an E_g detecting that old proposition difference. This proves the full typed Fin schema.

The root Boolean algebra is 2×B_t(W0). The element (0,d) is nonzero and has no atom below it: any nonzero (0,b)≤(0,d) can be split further because d is atomless in the old algebra. Thus Atomicity_t fails.

The accessible object W0 still fails Boolean separation, the (t,empty) OS instance. Hence ☐OS fails at the root. Finally p=(0,Bottom_B) and q=(1,Bottom_B) are distinct root propositions with the same old tail. Their equality proposition is (0,Top_B), so their distinctness proposition is (1,Bottom_B), not Top=(1,Top_B). This explicitly refutes ND_t.

## 3 Consequences and limits

Writing At for C + BF + Atomicity_t and Nec for ☐OS, the models give

```math
\mathsf{At}+\mathsf{Nec}\ \nvdash\ \mathsf{Fin},\qquad
\mathsf{Fin}+\Box\mathrm{BF}\ \nvdash\ \mathsf{At},\qquad
\mathsf{Fin}+\Box\mathrm{BF}\ \nvdash\ \mathsf{Nec}
```

In particular Fin and At are incomparable, and Fin and Nec are incomparable. Fin + Nec is a genuine stronger node than either alone. The two-object-chain model satisfies it and fails ND_t, so it remains strictly weaker than endpoint separation.

The omega-chain proof uses the cited full-action construction; the root extension includes its C soundness proof. The unresolved comparisons are listed in [Relations among observer principles](observer-lattice.md#8-sources-and-unresolved-comparisons).

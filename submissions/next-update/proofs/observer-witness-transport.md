# When logical observers make current principles necessary

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi. Direct source for the new transport arguments: `misc`, this note, unpaginated. Earlier results and constructions retain the attributions below.

## 1. Results and the common explanation

An observer changes the truth values supplied by a relation. A current existence principle can be reused after that change when its witnesses can still perform the required job. Two sufficient mechanisms are:

* the witness is used as an argument or an operation producing arguments, so it can be reused without transformation;
* the witness is used as a predicate, but its qualification makes its values fixed by the observer.

These mechanisms give the following conclusions, with finite, instancewise versions below:

```math
\begin{array}{rcl}
 C+OS+\mathrm{FunctionalChoice}&\Longrightarrow&\Box\mathrm{FunctionalChoice},\\
 C5+OS+\mathrm{RigidComp}&\Longrightarrow&\Box\mathrm{RigidComp},\\
 C5+OS+\mathrm{RelationalChoice}&\not\Longrightarrow&\Box\mathrm{RelationalChoice}
\end{array}
\tag{1}
```

The first implication does not need C5. The second works separately for each relation type, and also for Persistent and Gallin Extensional Comprehension. The third is refuted by the existing qualitative-contrast model evaluated at its trivial-symmetry object, where Relational Choice holds at every type but fails at an accessible object. That evaluation even satisfies separation by observers with qualified left inverses.

All schemas are collections of finitary formulas. No infinitary language, quantification over types, observer surjectivity, or external reindexing of witness domains is used in the positive results.

## 2. The separation step

Use the exact whole-operation qualification $`\mathrm{Good}_\Delta(E)`$ from [Logical observer separation and its hierarchy](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/logical-observer-hierarchy.md), §1. Here E has type tt and Δ is a finite external type list. Its Boolean and quantifier preservation requirements are identities of composite operations, not merely current truth agreement.

Write $`S_{t,\Delta}`$ for propositional separation by these observers. If A is any proposition and

```math
\forall E\,[\mathrm{Good}_\Delta(E)\to E(A)],
\tag{2}
```

then every eligible observer agrees on A and Top, since Good observers fix Top over C. Separation therefore gives A=Top, exactly □A. Consequently it suffices to show that each observer accepts the currently assumed principle. No optional premise is necessitated in this argument.

For a relation $`R^{\sigma_1\cdots\sigma_n t}`$, its pointwise transform is the admitted lambda term

```math
 R^E:=\lambda\bar x.\,E(R[\bar x])
\tag{3}
```

At zero arity this is ER. This construction needs neither an operation returning individuals nor a choice of observer preimages.

## 3. Transport with witnesses used as arguments

The following fragment extends the predicate-universal reflection mechanism to operation witnesses. It is stated explicitly to prevent an illicit extension to arbitrary existential predicate heads.

Fix finitely many outer relation variables $`\bar R`$. Let

```math
A:=\forall\bar R\,\varphi(\bar R)
\tag{4}
```

The matrix φ is built using Boolean operations and arbitrary ordinary quantifiers over admitted object types. Its atoms are applications $`R_i[\bar u]`$, Top and Bottom. Each argument term u is an admitted term containing none of the distinguished R variables. Such terms may contain bound operation variables and their applications: $`f x`$, for example, is allowed. A quantified entity of relational type may be used this way as an argument or operation; it is not separately asserted as a predicate head. A variable of type t used as an argument remains an argument, rather than a bare asserted proposition. Every variable is bound in A.

An optional extension permits additional tests $`B_j(\bar u)`$ not containing the distinguished R variables, provided the current background proves, for every eligible E and every relevant assignment,

```math
 E(B_j(\bar u))=B_j(\bar u)
\tag{5}
```

Treat these as whole tests: their internal quantifiers do not need to be moved through E. For instance, under current ND at a type, identity judgments between terms of that type are endpoints by NI and ND, and hence are fixed by Boolean observers. Under C5 this applies at every type. An equality involving a distinguished R inside its terms is excluded: an arbitrary observer need not reflect equality between the transformed relation values.

Let Δ contain each outer relation type and each type of a binder exposed in φ. A binder wholly inside a fixed test (5) or an opaque argument term is not exposed: E is not pushed into either.

**Argument-witness transport theorem.** Over C, with (5) when such tests are used,

```math
 S_{t,\Delta}\quad\Longrightarrow\quad A\to\Box A
\tag{6}
```

**Proof.** Fix an eligible E and assume current A. Move E through the exposed Boolean operations and binders, using the stipulated composite identities. Every atom $`E(R_i[\bar u])`$ is precisely $`R_i^E[\bar u]`$ by beta conversion. The argument terms remain the same; in particular an operation witness f remains f, even in the term fx. Each fixed test after expansion has the same current value by (5). Thus E(A) has the same current truth as

```math
 \forall\bar R\,\varphi(\bar R^E)
\tag{7}
```

For each tuple R, its tuple of transforms is admitted. Instantiate current A at that tuple. This makes every instance of the matrix in (7) true, including its existential quantifiers with their original admitted domains. Hence E(A) is true. Apply §2.

The initial expansion is contextual rewriting with identities of operations, not an inference from pointwise identity to whole function identity. Replacing fixed tests by their current values is done only after expansion, inside ordinary truth reasoning with the exposed quantifiers. No Functionality or BF premise is hidden in (6). ∎

The theorem requires no native-Box commutation. If native boxes occur, they must be covered by a separate fixed-test or transformation argument; they cannot be inserted freely into φ.

### Functional Choice

For admitted σ,τ with τ≠e, write

```math
\mathrm{FC}_{\sigma,\tau}:=
\forall U^{\sigma\tau t}
 [(\forall x^\sigma\exists y^\tau U[x,y])\to
  \exists f^{\sigma\tau}\forall x^\sigma U[x,fx]]
\tag{8}
```

The theorem applies without any fixed tests, with

```math
\Delta=\{\sigma\tau t,\sigma,\tau,\sigma\tau\}
```

Therefore

```math
\boxed{C+S_{t,\Delta}+\mathrm{FC}_{\sigma,\tau}
\Longrightarrow\Box\mathrm{FC}_{\sigma,\tau}}
\tag{9}
```

Only that choice instance is assumed. The same direct proof handles finite input tuples by listing their binder types and the corresponding selecting-operation type. Individual inputs are allowed; an individual-valued operation is never requested. The explicit expansion is in [the Choice proof](observer-choice-transport.md), §2.

### Boolean completeness and representation by operations

The known BC reflection theorem is an instance of the same mechanism. In

```math
\mathrm{BC}_\rho=
\forall Y^{\rho t}\exists y^\rho\forall z^\rho
 [ (\forall r^\rho(Yr\to z\le r))\leftrightarrow z\le y],
\tag{10}
```

Y is the only transformed predicate head. The existential bound y is an object, and the order judgments are identities between terms of type ρ. Current ND_ρ fixes those judgments. Thus C + ND_ρ + $`S_{t,\{\rho,\rho t\}}`$ gives $`\mathrm{BC}_\rho\to\Box\mathrm{BC}_\rho`$. The previously proved C5 version follows; see [Finite colour patterns](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/h-observer-space/finite-colour-propositional-completeness.md), §5. This is a local modal-premise refinement of that existing argument, not a new all-type completeness claim.

Likewise, for a functional relation U from σ to relational τ, Plenitude asks for an operation f with $`U[x,y]\to fx=y`$. Current ND_τ fixes all output-identity tests in functionality and representation. Theorem (6) therefore gives instancewise

```math
C+\mathrm{ND}_\tau+S_{t,\Delta}+\mathrm{Plen}_{\sigma,\tau}
 \Longrightarrow\Box\mathrm{Plen}_{\sigma,\tau},
\tag{11}
```

on the same finite Δ as (9). This does not infer an operation from a relation graph without the assumed Plenitude instance; it transports the operation witness the instance actually supplies.

## 4. Transport with fixed predicate witnesses

Existential predicate heads require an additional mechanism. A useful general form is

```math
A:=\forall\bar R\,[\alpha(\bar R)\to
  \exists\bar Y(K(\bar Y)\land\beta(\bar R,\bar Y))]
\tag{12}
```

Here α and β have the preceding Boolean/quantifier grammar, now allowing the Y variables as asserted predicate heads in β. They do not contain the distinguished R or Y as opaque argument terms. Other bound variables, including operation witnesses used in argument terms, are allowed. Assume each eligible E satisfies

```math
 E(K(\bar Y))=K(\bar Y),\qquad
 K(\bar Y)\to
 \bigwedge_i\forall\bar x\,[E(Y_i[\bar x])=Y_i[\bar x]]
\tag{13}
```

The conjunction is finite. Include all exposed binder types, including the R and Y types, in Δ; do not expand the internal binders of K.

**Fixed-predicate-witness transport theorem.** Under these conditions, $`S_{t,\Delta}`$ implies $`A\to\Box A`$.

**Proof.** For each eligible E, expose the binders and Boolean operations of E(A). Fix arbitrary R and suppose the resulting antecedent α(R^E) is true. Apply current A to R^E. It supplies an admitted tuple Y satisfying K(Y) and β(R^E,Y). Conditions (13) make this very tuple satisfy the exposed existential matrix: the guard is accepted, and every occurrence of E(Y[x̄]) has Y[x̄]'s current value. No preimage tuple is chosen. Consequently E(A) is true for every eligible E; §2 finishes. As in §3, the pointwise facts (13) establish current matrix truth and are not promoted to lambda identities. ∎

### Persistent, Rigid and Gallin comprehension

For $`\tau=\sigma_1\cdots\sigma_n t`$, let

```math
\mathrm{Comp}_{Q,\tau}:=
 \forall X^\tau\exists Y^\tau
 [Q(Y)\land\forall\bar x(X[\bar x]\leftrightarrow Y[\bar x])]
```

Take Q to be the native Persistent, Rigid, or Gallin qualification, preserving every outer box in their definitions. Under current ND_t, every native boxed proposition is an endpoint: NI covers its true case, and ND_t its false case. Every Boolean observer therefore fixes the entire Q(Y), which is a box or a finite Boolean combination of boxes.

Already in C, persistence gives $`Y[\bar x]=\Box Y[\bar x]`$ for each tuple. Indeed CBF exposes the necessarily true implication from Y[x̄] to its box; the reverse implication is necessarily true by T; propositional Intensionality identifies the two. Under ND_t, each application is consequently observer-fixed. All three qualifications imply persistence, so (13) holds.

The exact local conclusion is

```math
\boxed{
C+\mathrm{ND}_t+S_{t,\Delta}+\mathrm{Comp}_{Q,\tau}
\Longrightarrow\Box\mathrm{Comp}_{Q,\tau},
\quad\Delta=\{\tau,\sigma_1,\ldots,\sigma_n\}}
\tag{14}
```

The argument includes τ=t and individual argument types. It uses no comprehension instance at a different type. In particular it proves C5 + OS + RC_τ ⇒ ☐RC_τ. [The comprehension proof](observer-comprehension-reflection.md), §§1–4, gives the full definitions and independent derivation.

Full OS + ND_t already implies C5: OS supplies BF_t, and the recorded ND_t + BF_t bridge supplies □ND_t and then all-type C5. Thus (14)'s smaller modal premise is a local refinement, especially when Δ omits t; it is not a weaker full observer theory. Full C5 + OS + Rigid Comprehension also reaches the known atomic regime through Actuality. The value of (14) is its direct, type-local witness mechanism, which avoids that stronger all-schema route.

## 5. The limit: Relational Choice can be contingent

Use the Bacon–Dorr qualitative-contrast construction with two copies W₀,W₁ of ℕ, all bijections as arrows, finite pinning, full permutation symmetry at W₀, and trivial symmetry at W₁. Evaluate at W₁. This changes the designated evaluation of the existing model; it does not transfer the recorded W₀ flags to W₁.

All arrows are invertible, so C5 holds. Existing observer proofs give full ordinary separation at W₁ and even SplitMono, with whole-operation identities and every finite qualification list.

The new current-choice check is simple but requires the admission argument. For any external relation R on a finite tuple of typed domains at W₁, give it the same row R at every arrow ending at W₁ and the empty row at every arrow ending at W₀. Parallel arrows have identical rows, so the intension is empty-pinned. The W₁ symmetry requirement is trivial; empty rows satisfy the W₀ requirement. Curried sections acquire only the finite pins of their inserted arguments. Hence this is an admitted relation at every required type. External choice in ZFC now supplies a selector graph for every current serial relation, proving the full current Relational Choice schema.

At W₀ the recorded finite-support transposition argument forbids a selector from every nonempty property of individuals. A proposed selector has a finite pin F; the property of lying outside F is fixed by a transposition exchanging its selected individual with another individual outside F. Symmetry then gives two different outputs at the same input. The failed instance has input et and output e. Replacing outputs by individual haecceities gives a failed instance with both input and output et. W₀ is accessible from W₁, so both necessary instances fail at W₁.

Thus

```math
\boxed{C5+\mathrm{SplitMono}+\mathrm{RelChoice}_{\rm all}
 +\neg\Box\mathrm{RelChoice}_{et,e}
 +\neg\Box\mathrm{RelChoice}_{et,et}}
\tag{15}
```

is satisfied in this model. The full construction, higher-type admission check, and exact failure arguments are in [the Choice proof](observer-choice-transport.md), §§3–5. Its underlying model and W₀ selector obstruction are existing work; the current all-type W₁ verdict and resulting propagation boundary are the present combination.

The obstruction is exactly the missing predicate witness in (12). Translating Relational Choice by E asks for S whose transformed relation S^E selects from U^E. Current Relational Choice supplies a selector of U^E, but does not ensure that it is the transform of an admitted S. Unlike a rigid witness, that selector need not be fixed. Unlike an FC operation witness, S is itself used as an asserted relation head. The countermodel proves that this is a real failure of the implication.

Qualified left inverses do not solve this image problem. They supply injectivity of the observer, not the missing witness in its image. Over C5 they also yield native-Box commutation, so the counterexample applies even with BoxSep. This sharpens the syntactic boundary of [universal modal-law reflection](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/h-observer-space/native-box-reflection.md): existential relation heads still need their own witness theorem.

## 6. Full-schema consequences and exact strength

The first line of (1) combines with established implications to give a useful equivalence:

```math
\boxed{C+OS+\mathrm{FunctionalChoice}
\quad\equiv\quad C+\Box\mathrm{FunctionalChoice}}
\tag{16}
```

Forward, apply (9) separately at every instance. Conversely, boxed Functional Choice implies C5 and Atomicity through the recorded boxed-Plenitude route. The existing endpoint-observer theorem then gives full OS, while T gives ordinary Functional Choice. This invokes actual proved implications, not necessitation of an assumed schema. Formula (16) is an equivalence of theories, not one object-language conjunction over all types.

The full equivalence also follows from earlier results: Functional Choice gives Plenitude; OS with its (t,t) instance gives endpoint separation; endpoint separation gives No Pure Contingency; and No Pure Contingency makes the closed pure Functional Choice instances necessary. Thus the direct finite-instance theorem is the refinement, while (16) consolidates an already available full-schema route.

For Relational Choice, a useful extra premise is Weak Rigid Comprehension. Recorded results give Weak Rigid Comprehension + ND ⇒ Plenitude and Relational Choice + Plenitude ⇒ Functional Choice. Therefore

```math
C5+OS+\mathrm{WeakRigidComp}+\mathrm{RelChoice}
\Longrightarrow\Box\mathrm{FunctionalChoice}
\Longrightarrow\Box\mathrm{RelChoice}
\tag{17}
```

These are all-type schema premises. The direct fixed-witness theorem also supplies a route with fully rigid selector witnesses. Neither route claims that an arbitrary single weak-comprehension instance suffices for every choice type.

Full necessary Functional Choice already entails the established strong structural and analytic consequences. They are consequences of the new observer bridge, not new proofs of the older arrows. In particular, no new analytic-necessity result is claimed here.

## 7. Attribution and scope

The reusable results are (6) and the fixed-predicate-witness theorem. Their substantive native instances are the no-C5, instancewise Functional Choice reflection, the local comprehension reflections, and the qualitative-contrast boundary (15). The stronger theory equivalence (16) makes the role of observers in ordinary Functional Choice precise.

Several pieces were already known locally: Boolean-completeness reflection, universal modal reflection under BoxSep, the endpoint/C5-plus-Atomicity correspondence, qualitative contrast and its W₀ choice obstruction, and its W₁ observer verdict. These retain their own attribution. Full C5 + OS + Rigid Comprehension already had an indirect route through Actuality and Atomicity; (14) supplies a more local explanation. 

Core definitions and modal facts: Bacon and Dorr, *Classicism*, 16 May 2023 draft, §§1.3–1.5 and §2.1, pp. 13–22; comprehension and choice, §2.3, pp. 28–33. The qualitative-contrast model is Appendix D, p. 79. The symmetric ideally-full formulation is Dorr, *Boolean Completeness does not imply Rigid Comprehension*, draft 30 July 2026, Definitions 15–18, p. 8 and Lemma 21, p. 10. The linked proofs give the source details and the new W₁ admission argument.

The proofs retain the fixed relational grammar, exact current/necessary distinction, full observer identities, and theoremhood restriction on necessitation and Logical Equivalence. They assume no arbitrary observer surjectivity, no unproved higher-type reindexing, and no equality preservation beyond the stated fixed tests. 

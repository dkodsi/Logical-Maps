# OS has no finite equivalent axiomatization over C

The [direct Boolean-algebra proof](observer-no-finite-basis-direct.md) gives the theorem without a generic extension or first-order extraction. This alternative proof retains the comparison with a specified ground standard model.

**Theorem.** In ZFC metatheory, full relational OS has no finite equivalent axiomatization over C in the original typed language. The finite axioms may mention both $`e`$ and $`t`$ and arbitrary higher relational types; they need not be observer axioms.

More strongly, no set of sentences of uniformly bounded elaborated type order, even an infinite set, is equivalent to OS over C. The same conclusion holds for every deductively closed theory $`T`$ with

```math
\mathrm C+\mathrm{BF}\ \subseteq\ T\ \subseteq\ \mathrm C+\mathrm{OS}
```

In particular it applies to the full schemata BF, Functionality and Tractarianism. The [one-type schema reduction](observer-single-type-schema.md) remains valid: its external type parameter is unbounded. Finite stronger theories such as the [Rev presentation](reversible-separation-single-sentence.md) and [End presentation](endpoint-separation-finite-presentation.md) can imply OS. The theorem concerns an **equivalent** basis.

## 1. What must be preserved

Define type order by

```math
\mathrm{ord}(e)=\mathrm{ord}(t)=0,
\qquad
\mathrm{ord}(\sigma\tau)
=\max\{\mathrm{ord}(\sigma)+1,\mathrm{ord}(\tau)\}
```

Count every type in the fully elaborated formula, including logical constants and lambda subterms. For example, $`Q_\sigma`$ has type $`(\sigma t)t`$ and order $`\mathrm{ord}(\sigma)+2`$. Counting only the bound variable's type would understate the formula's scope.

The construction will preserve the complete theory of a full two-stage OS model at all types of order at most a prescribed $`n`$, while refuting BF at a higher type. It therefore addresses arbitrary finite tests, including mixed types involving individuals.

The [coherent-profile construction](observer-term-closed-profile-models.md) takes a full two-valued leaf hierarchy $`L`$ and a collection $`N_\sigma\subseteq L_\sigma`$ closed under full-leaf denotations of all finite terms. Its root profiles have future components in $`N`$. The transport image at each type is exactly $`N_\sigma`$. When $`N_\sigma=L_\sigma`$ at the required types, identity and the terminal reader supply relational OS. A nonempty leaf family $`F\in N_{\sigma t}`$ with no member in $`N_\sigma`$ instead supplies a higher BF failure.

An elementary submodel would not provide this last feature: elementarity would supply an existential witness. The construction needs term closure without that witness property.

## 2. A high family with no term-definable member

Begin with the ground full hierarchy $`L^V`$ over individuals $`\omega`$ and two truth values. Fix $`n<\omega`$, and put

```math
\mu=\beth_n,\qquad \kappa=\mu^+
```

Every type of order at most $`n`$ has a ground domain of cardinality at most $`\mu`$. To see this, induct on the finite type tree. At an arrow of order $`k\ge1`$, the input order is at most $`k-1`$ and the output order at most $`k`$, so

```math
|L^V_{\alpha\beta}|
\le(\beth_k)^{\beth_{k-1}}
=\beth_k
```

The bases are countable or finite. There are countably many types, so all order-at-most-$`n`$ domains together still have cardinality at most $`\mu`$.

Set $`\rho_0=e`$, $`\rho_{j+1}=\rho_jt`$ and $`\nu=\rho_{n+1}`$. Then

```math
|L^V_{\rho_n}|=\mu,
\qquad |L^V_\nu|=2^\mu\ge\kappa
```

Choose a ground injection $`b:\kappa\to L^V_\nu`$. Use the forcing

```math
\mathbb P=\mathrm{Fn}(\kappa\times\kappa,2,{<}\kappa),
```

ordered by reverse inclusion. A condition specifies fewer than $`\kappa`$ bits, with its first coordinate indicating a column. Since $`\kappa`$ is regular, unions of descending sequences shorter than $`\kappa`$ remain conditions. The decision recursion for closed forcing adds no sequences of ground objects of length below $`\kappa`$, and hence no subsets of ground sets of size at most $`\mu`$.

Induction on type trees now shows that every order-at-most-$`n`$ domain remains unchanged. A new function between preserved domains of size at most $`\mu`$ would give a new short sequence of ground values. The domain $`L_\nu`$ also remains unchanged: its elements are subsets of $`L_{\rho_n}`$, whose size is $`\mu`$. This last assertion does not require the entire powerset $`L_\nu`$ to have size at most $`\mu`$.

In the extension use the full hierarchy $`L=L^{V[G]}`$. Let $`a_i\subseteq\kappa`$ be generic column $`i`$, and let $`c_i:L_\nu\to2`$ be the characteristic function of $`b[a_i]`$. Put

```math
\sigma=\nu t,
\qquad F=\{c_i:i<\kappa\},
```

identifying $`F`$ with its characteristic predicate of type $`\sigma t`$. It is nonempty. Distinct columns force distinct $`c_i`$: below any condition choose a coordinate unused in two specified columns and assign different bits there. The injection $`b`$ preserves the difference.

Generate $`N`$ from $`F`$ and **every object of every preserved domain of order at most $`n`$**, by taking all denotations of finite typed terms with finitely many generator parameters. There is a set of such terms and parameter assignments. This gives nonempty domains at every type, contains the logical constants, and is closed under all finite term constructions by substitution. Moreover,

```math
N_\tau=L_\tau\qquad\text{when }\mathrm{ord}(\tau)\le n
```

**Nonselection lemma.** No member of $`F`$ belongs to $`N_\sigma`$.

Suppose a term with parameters $`F`$ and finitely many preserved ground objects selected a member. Strengthen a condition to choose an index $`i`$ such that

```math
p\Vdash u(F,\bar a)=c_i
```

Choose $`j\ne i`$ outside the column support of $`p`$. Let $`\pi`$ transpose columns $`i,j`$. It fixes the ground parameters and the unordered family $`F`$ as names up to forced equality. Interpretation of each fixed typed term in the full hierarchy is uniquely definable from its parameters, including when it quantifies over changed high domains. Forcing equivariance therefore gives

```math
\pi(p)\Vdash u(F,\bar a)=c_j
```

The conditions $`p`$ and $`\pi(p)`$ are compatible. At column $`i`$ only the former can have entries; at column $`j`$ only the latter can have entries; elsewhere they agree. Their union is still a condition. It forces $`c_i=c_j`$, contradicting the forced distinction. This proves the lemma.

This uses symmetry of forcing names and conditions, not a membership automorphism of the well-founded universe. It also explains the use of $`\kappa`$ columns: a condition could mention every column of a countable family. Only genuinely preserved lower domains supply ground parameters; functions whose argument domains enlarged are not imported as if their types were unchanged.

Thus $`F\in N_{\sigma t}`$ is nonempty at the leaf and has no member in $`N_\sigma`$, while all required lower domains are fully covered. The defective type is $`\sigma=\rho_{n+2}`$.

## 3. Preserving an entire bounded-order theory

Let $`B`$ be the ground full two-stage chain model with constant individual domain $`\omega`$. At its root every compatible current/future function profile is admitted. All type transports are onto, by the profile-lifting induction with $`N=L`$. Identity and the terminal reader therefore give full relational OS in $`B`$.

Its root domains also satisfy $`|D_\tau|\le\beth_n`$ for order-at-most-$`n`$ types. The bases are countable and four-valued; the same exponential estimate bounds the profile pairs at arrow types. Consequently the forcing preserves these low root domains as well as the low leaf domains. It introduces no new current functions at the types being compared.

Apply the coherent-profile construction to $`L,N`$ from §2, giving the defective model $`M`$ in the extension. Since $`N_\tau=L_\tau`$ at each preserved type, induction on types identifies its low root and leaf domains, transports and applications with those of $`B`$. Logical constants in the bounded elaborated language have the same interpretations. A term induction then gives agreement on every sentence in this fragment.

Let $`\mathrm{Th}_n(B)`$ contain every true closed sentence in that fragment, including the negation of each false one. The forcing produces a C model satisfying $`\mathrm{Th}_n(B)`$ and refuting BF at $`\rho_{n+2}`$. The higher BF formula lies outside the fragment whose complete theory was preserved.

Concretely, the failure predicate has constant-Top current function and future predicate $`\neg F`$. Every current argument transports outside $`F`$, but $`F`$ has leaf members. Therefore

```math
\forall x^\sigma\, .\,\Box Hx
\qquad\text{holds, while}\qquad
\Box\forall x^\sigma\, .\,Hx
\qquad\text{fails}
```

The same predicate and constant Top are distinct relation profiles with identical outputs on every current argument. This directly refutes Functionality and relational OS, even for an empty observer qualification list.

## 4. Extracting a ground Henkin model

The preceding forcing argument is a proof in ZFC using the forcing relation. Generic-extension notation introduces no separate countable-transitive-model hypothesis.

Use a countable many-sorted first-order presentation of typed Henkin structures: a sort for each type, application, logical constants and truth, together with symbols for parameterized finite lambda terms and their defining axioms, or equivalent abstraction-value formulas. This presents the four-valued profile structure; it does not identify propositions with current truth values. The verified term interpretation and equality clauses give a set-coded model of this presentation.

Let $`T_n`$ be the ground first-order theory containing that presentation, the translations of all C axioms, $`\mathrm{Th}_n(B)`$, and the displayed higher BF failure. The forcing proves that a model of $`\check T_n`$ exists.

If $`T_n`$ had a finite contradiction proof in the ground universe, that finite proof, its axiom memberships and its rule calculations would remain valid after forcing. First-order soundness would contradict the forced model. Hence $`T_n`$ is consistent in the ground metatheory. Many-sorted first-order completeness supplies a ground model, whose Henkin interpretation gives the required general C model.

The extracted model retains the specified sentences. It need not retain the original domains, their cardinalities, full leaf function spaces or standard natural numbers. No completeness theorem for full standard higher-order semantics is used. For a purely proof-theoretic nonfinite-basis argument, persistence of a proposed finite derivation already gives the contradiction; completeness is needed only for the explicit ground-model conclusion.

## 5. Nonfinite and bounded-order axiomatizability

Take any finite set $`\Gamma`$ of sentences that hold in all C + OS models. Choose $`n`$ covering all types in their elaborated syntax. Since $`B`$ satisfies OS, it satisfies $`\Gamma`$. The ground model extracted in §4 satisfies the same bounded theory, hence $`\Gamma`$, but fails BF and OS. Thus $`\Gamma`$ cannot be equivalent to OS over C.

The same argument handles an infinite $`\Gamma`$ with one fixed finite type-order bound: every member belongs to $`\mathrm{Th}_n(B)`$. Consequently no uniformly bounded-order set of consequences of C + OS, together with C, entails full BF.

A syntactic version makes explicit that no bound on proof types is assumed. If a finite $`\Gamma`$ were equivalent to OS, its finitely many proofs from C + OS would use finitely many OS instances $`\Delta`$. Choose the bound only after those proofs, covering $`\Delta`$. The constructed model satisfies C + $`\Delta`$, hence $`\Gamma`$, while failing OS. Intermediate proof types can be arbitrarily high without affecting this argument.

Finally suppose a deductively closed theory $`T`$ lies between C + BF and C + OS. An equivalent bounded-order basis $`\Gamma`$ for $`T`$ would consist of C + OS consequences. The same countermodel satisfies C + $`\Gamma`$ but fails BF, contradicting the lower inclusion. This proves the theorem for all such $`T`$. The familiar equivalence of BF, Functionality and Tractarianism over C supplies the stated special cases.

## 6. Sources and scope

New bounded-order construction, forcing nonselection argument and axiomatizability conclusions: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`). The [companion model proof](observer-term-closed-profile-models.md) supplies lambda closure, equality, exact C soundness and whole-operation observer preservation. The [manifest](../evidence/source-manifest.json) records source correspondence; [review evidence](../evidence/proof-reviews.json) concerns the source arguments.

Standard forcing inputs are in Asaf Karagila, [*Forcing & Symmetric Extensions*](https://karagila.org/files/Forcing-2023.pdf), updated 24 August 2026: Theorem 4.9, printed p. 21; Theorem 4.16 and Corollary 4.17, pp. 22–23; and Symmetry Lemma 10.8, p. 48. These supply closure, preservation of short sequences and forcing equivariance. No GCH or symmetric-inner-model preservation theorem is used.

The BF–Functionality–Tractarianism equivalence is the existing Bacon–Dorr result, *Classicism*, 16 May 2023 draft, Proposition 2.1, note 27, pp. 20–21. The contribution here is the nonfinite-axiomatizability consequence. The earlier [common-retract reduction](observer-single-type-schema.md) remains valid and explains how one external varying type parameter suffices despite this obstruction to fixed-type axioms.

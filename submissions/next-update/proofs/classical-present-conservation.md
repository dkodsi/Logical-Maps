# Standard current mathematics without new necessary consequences

Strong Actuality and Transversal Choice can be added to any theory of positive disequality sentences over C without adding positive identity consequences. In a countable relational signature, the entire true standard second-order theory of a chosen countably infinite structure can be added as well. In particular, standard relational second-order arithmetic can hold actually while leaving every necessary consequence unchanged.

## 1. The exact fragments and theorem

Work in the original fixed typed language with a fixed relational signature $`\Sigma`$, possibly empty. Let $`\mathcal E^+`$ contain formulas built from typed identities by conjunction, disjunction and either object quantifier. Let $`\mathcal D^+`$ use typed disequalities with the same outer grammar. Terms inside these identities or disequalities are unrestricted: they may contain abstraction, quantification and modal operators. Parameters at every type are allowed.

For this proof only, write $`\mathsf{Sel}`$ for Strong Actuality together with Transversal Choice at every type. If $`T\subseteq\mathcal D^+`$ and $`P\in\mathcal E^+`$ are sentences, then

```math
\mathrm C(\Sigma)+T+\mathsf{Sel}\vdash P
\quad\Longleftrightarrow\quad
\mathrm C(\Sigma)+T\vdash P.
```

The model argument below is explicit. The derivability formulation uses ordinary general-Henkin completeness for C; it does not use completeness for full standard higher-order semantics. The constructed models also satisfy every Relational Choice instance and admit every external current relation, so these can be added to the semantic conclusion too.

## 2. Two preservation directions

The [general root construction](classical-present-over-arbitrary-model.md) gives, over any general model $`K`$, a model $`R`$ satisfying $`\mathsf{Sel}`$ and maps $`q_\sigma:R_\sigma\to K_\sigma`$ commuting with every term. Choose the individual map onto, for example identity on $`K_e`$. Then every typed projection is onto. Lift each signature constant with its old interpretation as second component, keeping the same signature and reference theory.

For compatible valuations,

```math
R\models P(\bar a)\ \Longrightarrow\ K\models P(q\bar a)
\quad(P\in\mathcal E^+),
```

```math
K\models N(q\bar a)\ \Longrightarrow\ R\models N(\bar a)
\quad(N\in\mathcal D^+).
```

A true identity in $`R`$ is identity of its denotations. Term projection preserves it in $`K`$, and therefore reflects a disequality from $`K`$ to $`R`$. Conjunction and disjunction use their ordinary truth clauses. An existential identity-formula witness maps down; for a universal identity formula, lift an arbitrary old object using surjectivity. Dually, universal disequality formulas transfer using projected assignments, and existential witnesses lift. This proves the statements with arbitrary mixed quantifier prefixes.

Surjectivity is essential for universal identity conclusions and existential disequality premises. The arbitrary-map version of the root construction does not by itself give those individual-quantifier steps.

## 3. Conservation, necessity and Maximalism

If $`\mathrm C(\Sigma)+T`$ fails to entail $`P`$, take a general model $`K`$ satisfying the whole theory and falsifying $`P`$. Its root $`R`$ still satisfies every sentence of $`T`$ by disequality preservation, satisfies $`\mathsf{Sel}`$ by construction, and cannot satisfy $`P`$ by identity preservation. This proves the nontrivial direction. The reverse follows from inclusion of the theories. The same construction preserves consistency and gives the analogous consequence statement with compatible parameter assignments.

The theorem covers every necessary conclusion because $`\Box B`$ is the typed identity $`B=\top`$. It also covers arbitrary conjunctions, disjunctions and object quantifiers built from such identities. In particular,

```math
\mathrm C(\Sigma)+T+\mathsf{Sel}\vdash
\forall\bar x\, .\,\Box B(\bar x)
\quad\Longleftrightarrow\quad
\mathrm C(\Sigma)+T\vdash
\forall\bar x\, .\,\Box B(\bar x).
```

The box remains on both sides. No optional premise is necessitated. Conversely $`\Diamond B`$ is $`B\ne\bot`$, so the retained premise theory may be any positive combination of possibility assertions with arbitrary object quantifiers.

Pure and signature Maximalism fit directly: their native axioms are closed disequalities, with reference theories C and $`\mathrm C(\Sigma)`$ respectively. Thus these packages can be added to either Max theory without new positive identity or necessary consequences. This does not assert that Max proves those current packages, or that every actual conclusion is conserved.

## 4. Prescribing the full second-order theory of a standard structure

Suppose $`\Sigma`$ is countable and relational, with no individual constants imposing extra naming constraints. Let $`\mathcal A`$ be a fixed countably infinite structure for a relational subsignature. Write $`\mathrm{Th}_{\mathrm{SO}}(\mathcal A)`$ for all its true full second-order sentences translated into the relational fragment on individuals. Relation variables are only applied to individual tuples; equality is individual equality. If relation equality is used in the classical source, translate it as coextension, not native relation identity. There are no modal operators or higher-order argument positions in this fragment.

Then

```math
\mathrm C(\Sigma)+T+\mathsf{Sel}
+\mathrm{Th}_{\mathrm{SO}}(\mathcal A)\vdash P
\quad\Longleftrightarrow\quad
\mathrm C(\Sigma)+T\vdash P
\qquad(P\in\mathcal E^+).
```

Take a general countermodel for the right side. Its many-sorted first-order presentation has countably many types and term-operation symbols. Downward Löwenheim–Skolem supplies a countermodel $`K`$ with countable sorts, preserving the whole theory $`T`$, including when it is nonrecursive. Choose the current individual set to be the domain of $`\mathcal A`$ and an onto map to the nonempty, at most countable $`K_e`$.

Build $`R`$ with each prescribed signature relation having its $`\mathcal A`$-table as current extension and its unchanged $`K`$ interpretation as old component. The [second-order truth lemma](classical-present-over-arbitrary-model.md#5-standard-second-order-truth-without-relativization) makes every sentence of $`\mathrm{Th}_{\mathrm{SO}}(\mathcal A)`$ actually true, without a core translation. Disequality preservation retains $`T`$, identity preservation keeps $`P`$ false, and the construction supplies $`\mathsf{Sel}`$.

Take, for example, the standard natural numbers with

```math
\mathsf{Zero}:et,\qquad \mathsf{Succ}:eet,\qquad
\mathsf{Add}:eeet,\qquad \mathsf{Mul}:eeet.
```

The current relations are the standard zero predicate and operation graphs. Their old interpretations remain those of $`K`$. All true full second-order arithmetic sentences of this presentation can therefore be added as actual truths without new positive identity consequences, even over signature Maximalism for this same signature.

This is arithmetic in the specified relational presentation on individuals. It is distinct from the database's pure Frege cardinality interpretation, whose established arithmetic results remain unchanged. Countability is needed for prescribing this entire fixed individual structure while retaining an onto old projection; it is not required by the general conservation theorem in §1.

## 5. What the theorem leaves open

All external current graphs exist in the constructed root, but their operation representatives must satisfy the [projection compatibility condition](classical-present-over-arbitrary-model.md#6-exactly-which-current-functions-are-operations). The root fails Plenitude at every relational-input/relational-output instance. Thus standard actual mathematics and a full standard core do not remove the distinction between relation selection and admitted operations.

The conserved fragment is $`\mathcal E^+`$, and the retained premise fragment is $`\mathcal D^+`$. The theorem does not conserve all formulas or all possibility assertions. Likewise, the core's existence does not make the ambient model extensional or give every unrelativized higher-order sentence its standard truth.

## Sources and contribution

General conservation and prescribed second-order theory: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`), `general-observer-principles/metatheory.txt`, §§1–5a, with the construction in `models.txt`; unpaginated. Exact source versions appear in the [manifest](../evidence/source-manifest.json).

Positive-formula preservation by surjective homomorphisms is a standard method. The contribution here is the construction within fixed C preserving arbitrary intensional models while adding the stated current package, and its application to arbitrary disequality theories and complete actual second-order theories. Earlier special profile roots and pure-necessity conservation arguments are acknowledged in the companion construction.

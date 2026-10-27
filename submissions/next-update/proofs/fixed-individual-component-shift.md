# Component-shift symmetry with fixed individuals

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi. Direct source: `misc`, this note, §§1–6, unpaginated.

**Result.** Over the fixed relational type system, first-order endpoint-parameter noncontingency does not imply reversible logical separation, even with C5 and necessary qualified left-inverse separation:

```math
\boxed{\mathrm{C5}+\Box\mathrm{SplitMono}
 +\Box\mathrm{EPNC}_{e}\not\models\mathrm{Rev}}
```

The countermodel is the existing component-shift symmetric finite-pinning model with any nonempty set D as its individual domain and the trivial action on D. One may take $`D=\mathbb N`$. Its pinning carrier, arrows and symmetries remain unchanged. Its proposition-only hierarchy therefore retains the obstruction to Rev, while fixed individuals make all permitted endpoint relation parameters invariant under transport. Boxes of the two displayed schemata are read instance by instance after universal closure. No separate verdict about an object-language infinity axiom is needed or asserted.

## 1. Exact parameter schema

Fix finitely many relation variables $`R_i:e^{n_i}t`$, where $`n_i\geq1`$, and finitely many individual variables $`\bar x`$. Let $`P(\bar R,\bar x)`$ be a pure formula whose free variables are among those displayed. Bound variables may have any admitted type. Put

```math
\mathrm{End}(\bar R):=
\bigwedge_i\forall\bar y^{\,e}
 \bigl(R_i[\bar y]=\top\lor R_i[\bar y]=\bot\bigr)
```

The schema $`\mathrm{EPNC}_e`$ consists of the universal closures of

```math
\mathrm{End}(\bar R)\longrightarrow
 \bigl(P(\bar R,\bar x)\leftrightarrow
       \Box P(\bar R,\bar x)\bigr)
\tag{1}
```

This is exactly the schema in [Component-shift symmetry](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/h-observer-space/component-shift-symmetry-reversible-gap.md), §6. It excludes free higher-order relation parameters and free proposition parameters, while allowing arbitrary higher-order quantification inside P. Bracketed application is explicitly left-nested.

## 2. The modified model

Let $`\mathcal M`$ be the component-shift model from the cited note, §§1–2. Recall its external data:

- The pinning carrier is $`X=\mathbb Z\times\mathbb N`$, with components $`C_n=\{n\}\times\mathbb N`$.
- On even components the designated finite blocks have all positive even sizes, infinitely many of each size. On odd components their sizes are powers of two, infinitely many of each size.
- The symmetry group $`G`$ independently permutes each designated block internally.
- The one-object arrow group $`K`$ consists of bijections taking every $`C_n`$ to $`C_{n+k}`$ for one common integer k. Within the component maps they are arbitrary. In particular $`G\leq K`$.
- Relational domains admit all symmetric profiles pinned by a finite subset of X.

Fix any nonempty external set D. Define $`\mathcal M_D`$ using these same data but put $`D_e=D`$, with every arrow acting trivially on D. Keep the recursive symmetric finite-pinning construction for every relation type, using the new individual domain wherever e occurs.

The support carrier X is not the object-language individual domain. The special case of singleton D is explicitly part of the recorded construction: [Symmetric ideally-full models](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/topics/classicism/groups/symmetric-ideally-full.yaml), `parameters.individuals.values.singleton`, says that the original base continues to supply the arrows, pinning sets and symmetry groups. The distinction is also explicit in [Symmetric ideally-full map categories](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/rc-symmetric-ideal-full-categories.md), §1. The extension here to an arbitrary constant nonempty D is verified below, rather than attributed to that recorded singleton option.

To spell out the relevant closure facts, a relational profile satisfies

```math
A(gh;\rho(g)\bar u)=A(h;\bar u)\quad(g\in G),
\qquad
(\rho(k)A)(h;\bar u)=A(hk;\bar u)
```

Finite pins and these symmetry clauses are defined using X, K and G, not by quantifying over $`D_e`$. They are preserved by transport exactly as in the original construction. The constant individual action is coherent and bijective, and every individual parameter has empty support.

The remaining closure checks are those of the full symmetric profile construction. Primitive individual equality has the same extension at every arrow because D is fixed. Quantification over e ranges over the same D at every arrow; its profile is likewise independent of the arrow coordinate, and its symmetry follows from equivariance of its predicate argument. Both primitives are empty-pinned. At a higher type, each symmetry acts bijectively, so equality is preserved and quantifier symmetry follows by reindexing its entire admitted domain. These logical-constant profiles are also empty-pinned. Application is the profile application of the action construction. For lambda abstraction the free parameters contribute a finite union of their pins; bound arguments are supplied at the current target and do not require a uniform pin for all possible values. The standard abstraction calculation preserves symmetry using the coherent action on those arguments. The extra individual case causes no new obligation, since its action is the identity and its parameters have empty pins. Thus the same structural induction admits every interpreted term. Nonemptiness at e is the sole requirement on D here.

Consequently this replacement meets the same symmetric ideally-full model conditions and has C soundness by the existing construction proof. No restricted collection of higher relations is being proposed or left to a Henkin completion. This paragraph checks the additional constant-D cases; it does not replace or newly attribute the general construction theorem.

All arrows remain invertible, so transports at every type are bijections. Identity and distinctness are necessary throughout $`\mathcal M_D`$, giving C5. The category still has one object. Naturality of every closed pure proposition makes it constant on K, so No Pure Contingency holds for the entire new language, including types containing e.

## 3. Every requested parameter instance is noncontingent

Fix an assignment satisfying $`\mathrm{End}(\bar R)`$ at the identity. For every i and every tuple $`\bar a\in D^{n_i}`$,

```math
R_i[\bar a]\in\{\top,\bot\}
```

These are proposition identities, so each displayed proposition has constant truth on K. Since every arrow fixes $`\bar a`$, its value at h is exactly the raw profile value $`R_i(h;\bar a)`$. Therefore

```math
R_i(h;\bar a)=R_i(1;\bar a)
\qquad(h\in K,\ \bar a\in D^{n_i})
\tag{2}
```

It follows that right precomposition fixes the entire relation profile: $`\rho(h)R_i=R_i`$. Every assigned individual is fixed as well. For a nonsingleton D, the relation may distinguish different individual tuples; the assertion is transport-invariance, not that its actual extension is either empty or universal.

Naturality for pure terms now gives, for every $`h\in K`$,

```math
\rho(h)P(\bar R,\bar a)
 =P(\rho(h)\bar R,\rho(h)\bar a)
 =P(\bar R,\bar a)
\tag{3}
```

For a proposition, transport is right precomposition on its K-profile. Evaluating (3) at the identity says that its truth at h equals its truth at the identity. Its profile is therefore either all of K or empty. This proves (1) under the arbitrary assignment and hence its universal closure.

There is no bound on the types of quantified variables in P: the naturality theorem applies to every pure term of the model. The argument fixes only the displayed free parameters. In the singleton special case, each relation is the constant Top or Bottom relation and one can alternatively substitute those closed pure terms and universally close the vacuous individual variables. For general D the semantic transport argument is needed.

Thus $`\mathcal M_D\models\mathrm{EPNC}_e`$. Every universally closed instance is itself a closed pure sentence. One-object naturality therefore also proves its boxed instance: $`\mathcal M_D\models\Box\mathrm{EPNC}_e`$.

## 4. The proposition-only hierarchy is unchanged

Call a type t-generated if it is built from t using the permitted arrow constructor and has no occurrence of e. For every such type $`\tau`$,

```math
D_\tau^{\mathcal M_D}=D_\tau^{\mathcal M},
\tag{4}
```

with the same action, application and identity interpretation.

This follows by induction through the recursive profile construction. At t, admitted propositions are the symmetric finitely pinned subsets of the unchanged arrow group K; the individual domain does not enter that definition. At a relation type with t-generated argument types, the profile sets, tuple domains, symmetry actions and pinning clauses are identical by the induction hypothesis. Hence exactly the same profiles are admitted, with exactly the same transports. Logical operations at these types are unchanged as well: Boolean operations are unchanged at t, identity uses the unchanged actions, and each quantifier ranges over the unchanged corresponding domain.

It follows by term and formula induction that every sentence using only t-generated types has the same truth value in $`\mathcal M`$ and $`\mathcal M_D`$. This statement concerns the full such fragment, not merely the Boolean reduct.

## 5. Failure of Rev transfers

Use the finite characterization from [Reversible fixed propositions](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/h-observer-space/reversible-fixed-proposition-characterization.md), §§1–3. Let $`B(E)`$ be its finite whole-identity qualification for $`\mathrm{Good}_{\{t\}}`$, let $`I=\lambda p^t.p`$, and put

```math
\begin{aligned}
A(E)&:=B(E)\land\exists F^{tt}
 [B(F)\land E\circ F=I\land F\circ E=I],\\
\mathrm{Inv}(p)&:=\forall E^{tt}[A(E)\to Ep=p],\\
\mathrm{TrivialFix}&:=\forall p^t
 [\mathrm{Inv}(p)\to(p=\bot\lor p=\top)]
\end{aligned}
```

Every type and logical operation occurring in this sentence is t-generated. In particular the qualification uses the type-t quantifier, not an implicit infinite list of quantifier types.

The established theorem is

```math
\mathrm{C5}\models
 (\mathrm{Rev}\leftrightarrow\mathrm{TrivialFix})
\tag{5}
```

The original component-shift model satisfies C5 and fails Rev by its §§6–8, so it falsifies TrivialFix. Equation (4) transfers that same finite-sentence failure to $`\mathcal M_D`$. Since $`\mathcal M_D`$ also satisfies C5, (5) gives

```math
\mathcal M_D\models\neg\mathrm{Rev}
```

More concretely, the old model has a nonzero, currently false proposition fixed by every admitted reversible $`\mathrm{Good}_{\{t\}}`$ observer. The same proposition, observer domain, qualification and truth evaluation remain in the modified model. Its old definition using the moving individual domain and a binary relation need not remain expressible there. Its existence as a proposition object and its fixedness do remain, which is precisely why it can obstruct Rev without violating the restricted parameter schema.

The original model's stronger positive observer verdict also transfers. Its propositional qualified left-inverse separation instance for the finite qualification list $`\{t\}`$ uses only t-generated types: it quantifies over propositions and admitted operations $`E,F:tt`$, with qualifications $`\mathrm{Good}_{\{t\}}(E)`$, $`\mathrm{Good}_{\{t\}}(F)`$ and the whole identity $`F\circ E=I`$. Hence that instance remains true by (4). Over C5, the same-observer type-reduction theorem gives both E and F every requested finite quantifier qualification. C5 Functionality then lifts the propositional separation to every relational output type. This gives full SplitMono in $`\mathcal M_D`$. Its separately closed instances are pure, so one-object naturality gives $`\Box\mathrm{SplitMono}`$. This uses the same finite type reduction already invoked by the fixed-proposition characterization, not an assumption that types containing e stayed unchanged.

## 6. Independent check: erasing singleton individual arguments

The singleton special case has an additional independent soundness check. This check is not asserted to erase a nonsingleton D. Without identifying individuals with the pinning carrier, define for relational types

```math
t^\#=t,\qquad
(e\to\rho)^\#=\rho^\#,\qquad
(\sigma\to\rho)^\#=\sigma^\#\to\rho^\#
 \quad(\sigma\ne e)
```

Interpret a new relational type $`\rho`$ in an old model by its $`\rho^\#`$-domain, and interpret e by a singleton. Application to an e argument and lambda abstraction over an e variable delete that dummy argument or binder. Other applications and abstractions translate normally. The primitive constants require these explicit cases:

- $`=_e`$ translates to Top, since its erased type is t.
- $`\forall_e`$ and $`\exists_e`$ translate to $`\lambda p^t.p`$, since their erased type is tt.
- At every relational type $`\sigma`$, equality and quantifiers translate to the corresponding old constants at $`\sigma^\#`$.

In the pure language, terms of individual type are only individual variables, so deleting these variables is coherent. Reflexivity and substitution at e translate to tautologies; beta and eta at dummy e arguments reduce to identities; the remaining logical axioms and rules translate in the usual typed way. In particular an H proof of an equivalence translates to an H proof of the erased equivalence. The C Logical Equivalence instance therefore translates to an old C instance, with erased e binders removed. This preserves its theoremhood side condition rather than treating a conditional equivalence as a Logical Equivalence premise.

C5 translates type by type, with its e instance trivial. A closed pure sentence translates to a closed pure sentence, so NPC is preserved. Every t-generated type and term is fixed by the translation, which supplies the same transfer of TrivialFix failure. This independently explains the essential mathematical mechanism of the direct profile construction above.

## Sources

The underlying symmetric ideally-full model theorem is attributed in the local records to Cian Dorr, *Boolean Completeness does not imply Rigid Comprehension*, draft of 30 July 2026, Definitions 15–18, p. 8, and Proposition 20; see the exact construction citations in the component-shift note, §9. The general intensional action background is Bacon and Dorr, *Classicism*, draft of 16 May 2023, Appendix D, pp. 73–79. The singleton option and separation of the pinning carrier from the individual domain are explicitly recorded in the group file and profile-construction note cited in §2.

The component-shift countermodel and its original Rev failure are the 24 October research argument cited in §§1–2 and 5. The finite characterization is the separate 24 October research argument cited in §5. This note supplies the arbitrary fixed-individual modification, the exact endpoint-parameter argument and the preservation proof, with singleton erasure as an independent fallback; it does not attribute those new consequences to the published or human-authored background sources.

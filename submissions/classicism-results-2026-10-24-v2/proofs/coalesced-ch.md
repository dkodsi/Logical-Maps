# Coalesced sum of two extensional models disagreeing about CH

The construction below specializes Dorr’s two-component coalescence to disagreement about the Continuum Hypothesis. The CH specialization and its Maximalism consequence were developed with OpenAI Codex at Daniel Kodsi’s request on 23 October 2026. The generic coalescence and its structural arguments retain their original attribution; see the sources below.

## 1. The two components

Work in classical set-theoretic metatheory with Choice and assume Con(ZFC). The relative consistency results for CH and its negation, followed by first-order completeness and downward Löwenheim–Skolem, give countable first-order models

$$
N_+\models\mathrm{ZFC}+\mathrm{CH},\qquad
N_-\models\mathrm{ZFC}+\neg\mathrm{CH}.
$$

For each component, take its individual domain to be its own set of real numbers, its proposition domain to be its two-element Boolean algebra, and each admitted arrow domain to be the function set formed inside that component. Externalize membership and function evaluation. Internal extensionality ensures that two function objects with the same values on every available argument are identical. For each standard finite typed formula, Separation and Replacement supply the function denoted by its lambda abstraction; induction on terms and formulas establishes agreement with the corresponding set-theoretic interpretation. This yields a one-world extensional Henkin model of C at each component.

These domains contain the functions and subsets available in the relevant set-theoretic model. They need not contain every external function or subset of their externally countable domains. Neither transitivity nor external standardness of the component’s natural numbers is required.

Interpret the map’s real-structure tuple at type e using the component’s real field, its field operations and order, and its natural numbers. Its completeness condition quantifies over the component’s available subsets, exactly as the typed quantifiers do. The same applies to the least-inductive-property clause. Injections and bijections in the map’s CH formula are relational graphs; each such internal graph is in the appropriate admitted type. Satisfaction induction therefore gives

$$
M_+\models\exists\mathfrak R\,
  (\mathrm{Real}_e(\mathfrak R)\land\mathrm{CH}(\mathfrak R)),
\qquad
M_-\models\exists\mathfrak R\,
  (\mathrm{Real}_e(\mathfrak R)\land\neg\mathrm{CH}(\mathfrak R)).
$$

The witnesses use the same admitted type e. Each component also satisfies Well-Ordering at every type: its internal well-orders have least elements for every nonempty admitted property, which is precisely the required Henkin reading.

## 2. Coalescence and CH variation

Apply the coalesced-sum construction of *Classicism*, Appendix E, with one new root and a distinguished arrow to each component. Root individuals are pairs of component individuals. At a relational type, a root entity has an arbitrary current extension and one entity from each component. Write it as

$$
Y=(E,Y_+,Y_-).
$$

Transport to component i sends Y to its i-component, and sends individual pairs to their i-coordinate. Every root-to-component transport is surjective at every admitted type. Moreover, any pair of component entities has a common root preimage. These statements also hold coordinatewise for finite tuples. The cited construction validates C and leaves both component models intact.

At the root, both displayed existential sentences from §1 are possible. Hence the type-e instance of Non-contingency of CH fails: its first boxed alternative is refuted at the negative component, and its second at the positive component. Necessity of Second-Order Analysis fails as a consequence.

## 3. The structural principles that survive

The following arguments are generic for this coalescence of extensional components with Well-Ordering. They do not depend on arithmetic disagreement in the earlier model.

**☐Strong Leibniz and ☐Atomicity, at every relational type.** For each point and argument tuple, the root domain contains a relation true just at that tuple and point, with empty extensions elsewhere. At a component this uses its definable singleton. Such a relation decides every relation of its type in the Boolean order. Its transports are either the corresponding singleton or bottom, so it is strong. Every nonzero relation contains one of these singletons. The same argument applies at the leaves, including the nullary type t.

**☐BF.** Surjectivity of transport ensures that every component argument is the image of a root argument. Thus a predicate necessarily true of every current argument is true of every argument at either component. At a leaf modality is idle. This proves BF and its necessity at every admitted type, including e.

**☐Tame Rigidity, ☐Rigid Rigidity and ☐Weakly Rigid Weak Rigidity.** Let pi_i map root argument tuples to component tuples. A root relation Y is weakly rigid exactly when

$$
Y_i=\pi_i[E]\quad(i\in\{+,-\}),
$$

with those images admitted by their respective components. For necessity, weak persistence gives pi_i[E] contained in Y_i. If b were an additional member of Y_i, choose a test relation whose current and other component extensions are universal, and whose i-extension excludes only b. Every current Y-instance necessarily satisfies this test. Weak inextensibility contradicts the alleged extra member. Conversely, the displayed equalities give persistence and imply that any necessary cover of the current instances covers each component extension, which proves weak inextensibility.

All relations are rigid at the extensional leaves, so weak rigidity and rigidity coincide at the root. This proves Tame Rigidity throughout.

For any admitted component relation A at side i, take E to be its inverse image under pi_i. Its i-image is A, and its other image is universal when A is nonempty and empty otherwise. Both are admitted. Thus every leaf relation is the transport of some rigid root relation. The predicate Rigid consequently has universal images at both components, matching its component extensions; the criterion just proved makes that predicate rigid. WeaklyRigid has the same extension at the root and at each component, so the corresponding weak-rigidity conclusion follows too. At the leaves both conclusions are immediate. This proves all three boxed schemata.

**Modal Well-Ordering and ☐Well-Ordering.** For a fixed type, choose an external well-order of its root domain and an internal well-order at each leaf. These three relations are the components of an admitted root relation. Each well-orders the relevant domain with respect to all properties admitted at that point, so the relation is necessarily a well-order. Its persistence also yields ☐Well-Ordering.

**☐Intensional Choice.** For a necessarily inhabited relation, choose one instance at the root and one at each component. The three singleton extensions form an admitted subrelation which is necessarily instantiated and necessarily single-valued at the specified tuple of argument types. At a leaf this is the ordinary singleton argument.

**☐Distinctness-Preserving Collapse and ☐Boolean Completeness at t.** The root-only proposition supplies the distinctness-preserving necessity witness for each actual truth; at the leaves modality is idle. The propositional Boolean algebra has eight elements at the root and two at each leaf, so every admitted propositional family has its Boolean join and meet.

Consequently, even the joint package of ☐Atomicity, ☐BF, ☐Strong Leibniz, ☐Rigid Rigidity, ☐Weakly Rigid Weak Rigidity, ☐Tame Rigidity and Modal Well-Ordering does not entail Non-contingency of CH. The quantifiers over relational types range over the original admitted grammar throughout. The metatheoretic assumption is Con(ZFC), in the classical set-theoretic setting specified in §1.

## 4. The short Maximalism consequence

Let P and Q be the two closed pure type-e existential sentences displayed in §1. The component models establish their separate consistency with C. For any C-consistent closed pure sentence P, C does not prove the identity neg P = top. Pure Maximalism therefore supplies neg P != top, equivalently possibility P. Apply this to P and Q. Their simultaneous possibilities contradict both alternatives of Non-contingency of CH. Hence

$$
\mathrm{Max}(C)+\text{Non-contingency of CH}\ \vdash\ \bot.
$$

The consistency justification uses the metatheory of §1. No verification of the coalesced model’s structural flags is needed for this deduction. It also follows using Bacon’s same-type CH witnesses at et in place of the components above.

## 5. Existing source result: the C5 boundary

Bacon’s Theorem 5.1, printed p. 22, already supplies CH variation with C5 and **Rigid Comprehension**. Appendix B.2, printed pp. 7–10 (PDF pp. 41–44), uses e = omega and the Boolean algebra 2 × RO(Add(omega, omega_2)), evaluated at its isolated atom; the real structures have type et. This is distinct from the database’s singleton-individual, one-Cohen specialization.

At the isolated atom, the full function domains also give current Relational Choice: select one actual output for each actual nonempty fibre and use its graph, valued top on selected pairs and bottom elsewhere. Fullness admits this relation. Thus C5 plus current Relational Choice does not entail Non-contingency of CH. This paragraph does not assert ☐Relational Choice.

## Sources and scope

- The map’s definitions of real structures and CH: [Background, Analysis](../evidence/database-records/ch-20261023/background.md).
- Bacon and Dorr, *Classicism*, draft of 16 May 2023, Appendix E, Definition E.2, pp. 80–83: [coalesced-sum construction record](../evidence/database-records/ch-20261023/groups/coalesced-sums.yaml).
- Dorr’s construction of 19 October 2026 and the accompanying recorded verifications by Claude: [the arithmetic-disagreement model](../evidence/database-records/ch-20261023/models/coalesced-two-extensional-arithmetics-root.yaml), arguments `strong-leibniz`, `one-world-components`, `well-ordering`, `boolean-completeness-t`, and the rigidity characterization used by `rigid-rigidity`. Their generic arguments are used above; the earlier model’s arithmetic and Rigid Power failures are not transferred to this new model.
- Andrew Bacon, [*Could the truths of mathematics have been different?*](https://andrew-bacon.github.io/papers/Could%20mathematics%20have%20been%20different.pdf), draft of 9 October 2025, Theorem 5.1 and Appendix B.2: the separate source result in §5.

The CH component selection and the deductions in §§1–4 have direct source `misc`. Database registration is handled separately from this synthesis. All claims here are ordinary mathematical arguments; no certificate status is changed.

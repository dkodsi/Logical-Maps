# Probability contribution and verification boundary

Current author-owned scope: AtomicProbability* and ProbabilitySymmetry*. Ordinary external finite algebra is explicitly separated from the C-language constructions. The repaired external finite algebra, complete-additivity and normalization sources now have fresh locked checks. The generic SupportedReals and original NaturalOrder C certificates also pass. Supported number operations, addition and multiplication pass ordinary Lean; their separate C-certificate run timed out without diagnostics and remains incomplete.

The internal source chain constructs actual supported number operations, nonnegative fraction class codes, signed additive rational codes, their dense linear order and Archimedean bounds, then a nontrivial complete order of supported rational cuts with concrete addition. The new CutCrossing source derives adjacent crossing and an arbitrarily small gap from internal number induction and the proved-in-source rational bounds; ConcreteRealInverse uses it to supply the reverse additive-inverse inclusion, literal cancellation and the guarded subtraction/order equivalence. Neither step is added as a hypothesis. These internal sources remain pending their gate/type/object-derivation check chain.

Premises are a current ActualWorld w and quantified AxiomOfInfinity at the counting type, except lemmas whose proofs need fewer hypotheses. All constructed output types are relational. Completeness refers to represented families; no external-standardness, full powerset, Plenitude, Choice or boxed conclusion is silently supplied.

Full mathematical context: [local propositional probability](../proof-refinements/local-propositional-probability.md) and [canonical atomic probability](../proof-refinements/canonical-atomic-probability.md). Exact remaining obligations and evidence are maintained in [verification status](probability-verification-status.md) and the lane's [live update](verification-updates/probability_internal_constructions.json).

New full argument: [internal cut crossing and additive inverses](probability-cut-crossing-proof.md).

The full internal probability equivalence remains uncertified; the established components and outstanding mathematical obligations are listed below.
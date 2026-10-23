# Extensional mathematics inside any rigid domain

Research theorem, 22 October 2026 (`misc`). This strengthens the C5-only core interpretation in `rigidity-actualization.md` section 13. No database record has been edited; literature novelty and formal verification are not claimed.

## Theorem and scope

Assume unboxed ND and Rigid Power at all relational types. Let D be a nonempty rigid property of individuals. Then the fixed relational type hierarchy contains an internal extensional Henkin interpretation of ordinary higher-order logic whose individual domain is D. No BF, C5, Actuality, Atomicity, Rigid Comprehension, or Choice assumption is used.

The interpretation supplies intrinsic comprehension and extensionality. It does not assert that every external subset is represented, that every arbitrary ambient relation can be imported into the core, or that Choice or Infinity follows. If the chosen rigid D has an appropriate interpreted Infinity witness, that witness is retained. In particular this theorem can be used with a specified infinite rigid mathematical domain, but it does not produce one or assert a new transfer equivalence for ambient Infinity.

Proved-only Engine queries from ND+RP do not derive C5, BF, RC or TR in the current records. This is a check of the absence of recorded shortcuts, not an independence result for any of those conclusions.

## 1. Three closure lemmas

All references to rigidity use the database's full definition.

**Products.** Products of rigid domains are rigid in C. For two domains A(x),B(y), persistence is immediate. If every current A(x) and B(y) pair necessarily satisfies Z(x,y), weak inextensibility of B first gives, for each current A-member x, the necessary statement forall y(By→Zxy). Weak inextensibility of A then gives the required necessary universal statement for the product. The same reasoning applies at every reached world and iterates to finite products. This avoids incorrectly treating an unbounded cylinder as a rigid relation.

**Sections.** Under ND, every section of a rigid relation is rigid. Current relation-members decide equality with the fixed argument necessarily; weak inextensibility seals the decision within the rigid relation; the decided-cut lemma and existential projection give the section. The detailed proof is `rigid-boolean-closure.md` section 7. Only unboxed ND at the fixed argument's type is needed.

**Decided matrices.** If A is rigid and a matrix phi(xbar) is top or bottom on every current A-tuple, then A∧phi is rigid. The current endpoint identities make each decision necessary, so weak inextensibility gives A<=lambda xbar.(box phi or box not phi). The decided-cut lemma applies. In particular no BF is needed to extend these current decisions to the possibly enlarged rigid domain.

## 2. The domains

Recursively put H_e=D. For tau=sigma_1...sigma_n t define

    A_tau(xbar) := conjunction_i H_sigma_i(x_i),
    H_tau(F) := Rigid(F) and F<=A_tau.

For n=0, A_t=top and H_t={bottom,top}. The recursion is metalinguistic on finite types, not quantification over types. D is a rigid nonempty domain by assumption. Products make A_tau rigid once the lower H-domains are rigid. RP at tau makes its rigid power H_tau rigid. This proves rigidity of every interpreted domain.

Every relational core domain is nonempty because it contains bottom_tau; it also contains its supported top A_tau. D's nonemptiness is necessary: an actual witness persists in a rigid relation. More generally every nonempty rigid relation is necessarily nonempty.

Application preserves the core. Fixing a core argument in a core relation gives a rigid section by the sections lemma, and the support inequality gives the section's lower support. Thus the resulting object lies in the appropriate H-domain.

Core extensionality follows from support. If two core relations agree on all core argument tuples, they agree on every actual tuple, since both vanish off support. Coextensive weakly rigid relations are identical in C, so these core relations are identical.

## 3. Intrinsic formulas are bivalent

Induct on a target formula with variables bounded to the H-domains and core parameters. Atomic application ends at H_t, hence has value top or bottom. Identity is top or bottom by ND and NI. Boolean operations preserve endpoints.

Consider a bounded universal Q:=forall x(H_sigma(x)→phi(x)) with all its free parameters in the core. If Q is true, the inductive hypothesis gives box phi(x) for every current H_sigma-member. Weak inextensibility of the rigid domain H_sigma therefore gives H_sigma<=phi, which is box Q. If Q is false, choose a current H_sigma-member x with not phi(x). Its domain membership persists and phi(x)=bottom, so not Q is necessary. Hence Q is top or bottom. Existentials are dual.

This is exactly where rigidity of the bounded quantifier domain replaces BF. No inference is made about quantifying over the whole ambient type.

## 4. Comprehension and the interpretation

For a target formula phi on core arguments, use the ordinary ambient term

    F:=lambda xbar . A_tau(xbar) and phi(xbar).

Section 3 makes phi bivalent on every current support tuple. The decided-matrices lemma makes F rigid, and its defining conjunction gives F<=A_tau. Thus F belongs to H_tau and represents the target comprehension instance.

Relational-valued abstractions are handled by currying their core-supported matrices. Application remains in the core; on core inputs the support conjunct is true and the resulting section agrees with the intended value. Both are rigid, so core extensionality gives identity and hence beta. Eta and ordinary extensionality follow the same way. At base type e the translation uses variable restriction only; no forbidden individual-valued function type is added.

The result is therefore an internal Henkin interpretation of extensional higher-order logic over D in exactly the original allowed relational type system. Its operations are given by ordinary available lambda terms. It is a local theorem from unboxed ND+RP: the closure of the interpreted domains supplies the stability needed for its own bounded reasoning.

## 5. Useful choices of the individual domain

The earlier C5 construction takes D to be the whole individual domain. Making that domain rigid is equivalent to boxed BF_e, which C5 supplies. It also supplies ND and RP. Thus the earlier theorem is a special case. More precisely, ND+RP+boxed BF_e already interprets the full current individual domain; no BF instance at a relational argument type is needed in this proof.

Alternatively, RC_et supplies a rigid D actually coextensive with the universal individual property. This again interprets all current individuals, while its fixed rigid domain need not contain every future individual. Thus ND+RP+RC_et supplies the same actual-domain interpretation.

A singleton rigid D exists already in C, but its extensional hierarchy has a trivial individual base. Nontrivial arithmetic claims require an explicitly suitable nontrivial or infinite D and the corresponding interpreted witness. The theorem supplies the logic and stable hierarchy, not an unproved infinity transfer.

This distinction is useful when studying theories weaker than C5: a nonrigid or expanding ambient universe can still contain an ordinary stable extensional mathematical hierarchy. The present theorem says exactly what assumptions support that hierarchy and does not identify it with the whole ambient intensional universe.

## 6. Rigid Comprehension and transfer of Choice

The independently audited new theorem ND+RC=>RP, in `maximalism-modal.md` section 24, supplies RP from ND and RC. Choosing by RC_et a rigid representative of the current universal individual property therefore gives:

    ND + RC interprets extensional Henkin HOL on all current individuals.

The core's individual domain is that fixed rigid representative; future ambient individuals outside it need not be included. The core's higher domains are the supported hereditary rigid domains just proved.

Adding ambient Relational Choice transfers ordinary relational Choice to this core. Given a core relation R serial on a core input domain A with outputs in a core domain B, extend R to all ambient inputs by a fixed B-default on non-A inputs. Ambient Relational Choice selects a functional subrelation. Restrict this chosen graph to A times B and use RC at its graph type to obtain a rigid relation G with the same actual graph. Every actual G-member lies in the rigid support A times B; persistence of the support and WI(G) seal G<=A times B. Thus G is a core graph and still selects exactly one permitted core output for every core input. Core extensionality and intrinsic comprehension are already available, so this proves the target choice schema.

For allowed relational output types, the corresponding functional choice operation also transfers. ND+RC implies Plenitude by recorded consequences. Apply Plenitude to a total version of the selected ambient graph to get an operation f whose values on A are the selected B-objects. Form the core-supported curried matrix of f and use RC to make it rigid. Its sections are rigid by ND; on every current core input, its section is actually coextensive with the selected output, which is itself core and rigid. Coextensive-rigid uniqueness therefore makes those outputs identical. The support argument puts the resulting operation in the appropriate hereditary core domain.

Thus

    ND + RC + Relational Choice

interprets extensional Henkin higher-order logic with the applicable ordinary Choice schemas on all current individuals, with no BF or boxed-Plenitude assumption. Choice whose output is e is represented by a functional binary graph, respecting the fixed framework's prohibition on types ending in e. No external fullness or Infinity consequence is inferred.

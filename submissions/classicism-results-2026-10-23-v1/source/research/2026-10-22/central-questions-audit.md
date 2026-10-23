# Central question audit

22 October 2026. This audits the **25 displayed rows** of OPEN-QUESTIONS.md §2: five rows under each of no extra assumptions, C5, C5 + Atomicity, Extensionalism, and pure Maximalism. It does not recompute all ranked questions, count all equivalent formulations as separate questions, or change the database.

The audit extracts a simple new corollary from the session's pure-term permutation arguments. **Twelve displayed rows have negative answers as signature-uniform claims.** They were not separately verified in the earlier saved reports. The other thirteen rows are not settled by the arguments identified here. Consequently this is a new audit finding, not a claim that the earlier reports already explicitly answered twelve rows.

## The signature and the two models

The fixed framework explicitly allows any signature containing at least one relational constant, with no further requirement: see `topics/classicism/background.md`, lines 351–365. Choose the permitted signature

    Sigma = { c : et }.

For a set E with at least two members, take the full one-world extensional typed model: D_e=E, D_t={false,true}, and at every admitted arrow type sigma→tau, D_(sigma tau) is the full function set D_tau^D_sigma. Interpret application, lambda abstraction, equality and quantification in the usual extensional way. No type with output e is added. This is the ordinary full model of C, and Box and Diamond both act as the identity on propositions.

Interpret c as a proper nonempty subset A of E. We use:

- **M2:** E={0,1}, A={0}.
- **MN:** E=N, A={0}, in ordinary ZFC metatheory.

The element named 0 here is part of the external model description, not an additional constant in Sigma.

## Independence holds

Let pi be any permutation of E. Extend it recursively through the full hierarchy: pi acts trivially on D_t, and on a function f:sigma→tau by

    (pi f)(x) = pi_tau(f(pi_sigma^(-1)(x))).

These bijections preserve application. They preserve identity, Boolean operations and quantifiers because the quantified domains are permuted bijectively. Induction on pure terms, including lambda abstraction, therefore proves equivariance of their interpretation. In particular every closed pure term is fixed by every such automorphism of the pure reduct.

For a closed pure term of type et, its denotation is consequently a subset of E invariant under every permutation of E. The permutation action on E is transitive, so the only such subsets are empty and E. The chosen A is neither. Thus

    c != T

for every closed pure term T:et.

The exact Independence(Sigma) schema says c is not a closed pure operation applied to distinct *other* constants. Since Sigma contains only c, the only instances have no other constants, namely the inequalities just proved. Hence both M2 and MN satisfy the entire Independence(Sigma) schema for this signature.

The automorphisms need not preserve c: they are automorphisms of the **pure reduct**, which is exactly what fixes pure denotations. Functional Choice is an existential principle here, not a named logical choice operator. Its truth does not change the pure-term symmetry argument.

This is the same covariance mechanism developed in [homogeneity and amalgamation](notes/homogeneity-amalgamation-lane.md), §7, and [the algebraic report](notes/structural-algebraic-core.md), §§35–36. The explicit signature expansion and central-row application are supplied by this note.

## Other verified properties

Both models satisfy Extensionality, C5, all-type Atomicity and Boolean Completeness. Full function domains represent every functional graph; metatheoretic Choice supplies selectors for every serial relation, giving Functional Choice and its boxed form. In M2 every particular type domain is finite, so the relevant selections can also be made finitely. Intensional Choice holds: in a one-world model a nonempty property admits a singleton subproperty, which is uniquely instantiated there.

No Contingency(Sigma) and Modal Freedom(Sigma) hold since Box and Diamond are the identity. Truth implies ND-necessity also holds directly. For true p take q=top in

    Box_ne p := exists q [q and Box(Diamond q -> p)].

M2 fails both individual and propositional quantified Infinity, and both corresponding Infinity schemata: its e-domain and t-domain each have two members. MN satisfies individual quantified Infinity and its schema, but its proposition domain still has just two members and fails propositional Infinity. The ordinary full extensional interpretation validates the intended Frege finite-cardinality definitions in these examples.

Neither construction is claimed to satisfy Logical Necessity, Witnessed Possibility or signature Maximalism. Indeed, the witness to the pure formula x=top does not make c=top possible in a one-world model where c is a proper subset, so Witnessed Possibility fails.

## The twelve displayed rows

Each entry below is a negative answer to the displayed entailment. In the rows with conclusion false, the model witnesses consistency relative to the stated metatheory. An absent arrow alone is never used as evidence.

| Background and row | Displayed entailment, using a representative of the listed class | Witness |
| --- | --- | --- |
| C5, 3 | Independence(Sigma) + boxed Functional Choice implies false | M2 |
| C5, 5 | Independence(Sigma) + Functional Choice implies false | M2 |
| C5 + Atomicity, 1 | Independence(Sigma) + Truth implies ND-necessity implies false | M2 |
| C5 + Atomicity, 2 | Independence(Sigma) + No Contingency(Sigma) implies Infinity Schema_t | M2 |
| C5 + Atomicity, 3 | Independence(Sigma) + Intensional Choice implies Infinity Schema_t | M2 |
| C5 + Atomicity, 4 | Independence(Sigma) + Modal Freedom(Sigma) implies Infinity Schema_t | M2 |
| C5 + Atomicity, 5 | Independence(Sigma) + No Contingency(Sigma) implies quantified Infinity_t | M2 |
| Extensionalism, 1 | Independence(Sigma) + quantified Infinity_e implies false | MN |
| Extensionalism, 2 | Independence(Sigma) + Infinity Schema_e implies false | MN |
| Extensionalism, 3 | Independence(Sigma) + Functional Choice implies false | M2 |
| Extensionalism, 4 | Independence(Sigma) implies quantified Infinity_e | M2 |
| Extensionalism, 5 | Independence(Sigma) + Functional Choice implies quantified Infinity_e | M2 |

The totals are **0/5** under no extra assumptions, **2/5** under C5, **5/5** under C5 + Atomicity, **5/5** under Extensionalism, and **0/5** under pure Maximalism: **12/25** overall.

Some rows are the same general obstruction viewed under different backgrounds; twelve rows do not mean twelve independent new theorems. The remaining C5 Choice bridges receive only conditional progress from the new Relational Choice + Boolean Completeness theorem. Its completeness premise cannot be removed merely by calling the implication an artifact of the session.

## Signature qualification

These models refute the proposed claims **uniformly over the map's permitted signatures**, since one permitted signature is enough to disprove a universal implication. They do not establish compatibility for every separately prescribed richer signature. In particular, in a one-world model a proposition constant must be either top or bottom, so a signature containing a proposition constant cannot satisfy Independence by this construction. More generally, multiple named constants require their full mutual nondefinability obligations to be verified.

Thus the central questions conceal a material signature parameter. They should not be presented as open uniform implications after this counterexample, nor should the counterexample be promoted to an all-signature existence theorem. The declared fixed signature convention must be retained in any eventual model record.

## Remaining priorities

Among the displayed rows still unclosed, **signature Maximalism + Weakly Rigid Power implies false** is a direct test of a simple positive strengthening of maximalism. **Logical Necessity implies Actuality** is a strong structural target: recorded consequences show that a positive answer also closes the displayed Vicinity and Weak Inextensible Comprehension questions, and the BF_t-assisted Strong Actuality row. The C5 Choice bridges ask whether available forms of witness selection provide enough coherent representation to recover the other forms.

The two pinned-root Rigid Power verdicts under pure Maximalism remain genuine construction-specific targets. No new profile or retract model automatically supplies a verdict for either unchanged recorded construction.

Independent mathematical checks: the choice and rigidity research agents separately checked the signature, covariance, modal, Choice and Infinity arguments. This is ordinary agent auditing, not human certification, Lean verification, or a literature-novelty claim. If integrated, the direct source for the new signature-expansion argument is `misc`. Database records and generated rankings remain unchanged.

# Extensional models with one independent predicate

For the permitted signature Sigma={c:et}, a full one-world extensional model with at least two individuals can satisfy the entire Independence schema while c denotes a proper nonempty subset. Thus Independence is compatible with Extensionality and necessary Functional Choice. With two individuals both Infinity schemata fail; with N individuals individual Infinity holds while propositional Infinity still fails.

This is a counterexample to implications intended uniformly over the map's permitted signatures. It is **not** an existence theorem for every separately fixed richer signature. In particular a proposition constant in a one-world model would denote a pure endpoint and violate Independence.

## 1. Construction and full typed soundness

Take D_e=E and D_t={0,1}; at each permitted arrow type sigma tau use the full function set D_tau raised to D_sigma. Interpret application, abstraction, quantification and equality in the ordinary extensional way. No individual-valued arrow type is added. This validates H and its conversion principles. Any H-theorem equivalence holds at all assignments, so its abstractions are identical actual functions, giving C's restricted Logical Equivalence rule.

There is one world. Native Box p=(p=Top) and Diamond both equal p. Interpret the sole nonlogical constant c as A={0}. In the first construction E={0,1}; in the second E=N. The external label 0 is not an extra language constant.

## 2. Independence at the exact signature

For any permutation pi of E, extend it through the hierarchy by fixing D_t and setting

    (pi_(sigma tau) f)(x) = pi_tau(f(pi_sigma^-1(x))).

Every map is a bijection of the full admitted domain. They preserve application; they also preserve equality and Boolean constants, and the quantifiers since the quantified domains are permuted bijectively. Lambda/application induction proves equivariance of all pure terms. Every closed pure term is therefore fixed by every such transformation of the pure reduct.

A closed pure term of type et must denote a subset of E invariant under all permutations. Transitivity of the individual action implies that subset is either empty or E. The chosen A is neither, so c is unequal to every closed pure et term.

There is no other nonlogical constant in Sigma. Therefore every native Independence instance c != T(d_1,...,d_n), whose constants must be distinct, has n=0. The preceding argument verifies the entire schema. The automorphisms need not preserve c: they act on the pure reduct, exactly as required for invariance of pure terms. The existential Choice axiom is not a named choice operation and introduces no extra pure term.

## 3. Choice, modality and finite cardinalities

Full extensional semantics gives Extensionality. External Choice supplies the graph of a selector for each serial relation, and every needed relational-output function is admitted, proving Functional Choice. At the two-element construction every individual type is finite, so each selector can also be obtained by finite selection. One-world modality makes FC necessary.

Intensional Choice holds by choosing one instance of each fixed inhabited property and its singleton predicate. It is also derived from Extensionality in the map. No Contingency(Sigma), Modal Freedom(Sigma), C5, Atomicity and Boolean Completeness follow from the native Extensionality closure; their direct one-world semantics is immediate. These derived flags need not be repeated in the model records.

In the two-individual model both e and t have exactly two elements. The native Frege cardinality definitions are standard in these full extensional domains: the second finite cardinality holds of the universal property, and the third lower-bound schema instance fails. Thus quantified Infinity and the Infinity schema fail at each type.

In the N-individual model every finite individual cardinality is realized, but none holds of the universal individual property. To see that the internal definition admits no extra finite cardinalities, the full higher domains contain the actual family of standard finite cardinalities; it contains zero and is successor-closed, and therefore bounds the native inductive definition. Conversely finite induction supplies all the standard finite cardinalities. Hence the quantified individual Infinity axiom and its schema hold. The proposition domain remains two-element, so both propositional Infinity formulations fail.

Finally Witnessed Possibility fails directly: the pure formula X=Top_et has a witness, while the proper c cannot possibly equal Top_et in this one-world model. In the native record this failure is derived from No Contingency(Sigma), preserving the direct proof here.

## 4. Scope and sources

Direct source: OpenAI Codex, prompted by Daniel Kodsi, *Central question audit*, 22 October 2026, sections “The signature and the two models”, “Independence holds”, “Other verified properties” and “Signature qualification”, unpaginated. The source reports separate ordinary agent checks of the covariance, signature, Choice and Infinity arguments. This integration independently rechecks those arguments against the current native definitions.

The base semantics and signature conventions are the native [background](https://github.com/zwlgzwlg/Logical-Maps/blob/6f15ef5c491fcb117d4d11d8837545a9baaa042d/logical-maps/topics/classicism/background.md); Independence is Bacon, *Logical Combinatorialism*, Philosophical Review 129 (2020), §4 p.568 and n.53. The specific singleton-predicate expansions and comparison are the AI source arguments, not attributed as theorems from that paper. No historical-priority, named-human-review or Lean claim is made. These two models do not establish Logical Necessity or signature Maximalism; both fail Witnessed Possibility.

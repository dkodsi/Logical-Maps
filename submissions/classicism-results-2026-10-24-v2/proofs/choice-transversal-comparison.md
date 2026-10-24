# Relational Choice and Boolean Completeness imply Transversal Choice

Integration and comparison by Codex (OpenAI), prompted by Daniel Kodsi,
23 October 2026. The conjecture is Zachary Goodsell's, communicated on
27 September 2026. The direct proof and refinements reproduced below are
independent Codex research, prompted by Daniel Kodsi, from 22 October 2026.
Published background and the older components of the composition retain
 their own attribution.

## 1. The settled statement and the two proofs

In the fixed framework C, with the map's relational type system,

$$
\mathrm{Relational\ Choice}+\mathrm{Boolean\ Completeness}
\;\Longrightarrow\;\mathrm{Transversal\ Choice}.
$$

All three schemata are unboxed. Here **RC means Relational Choice**, not
Rigid Comprehension. The stable conjecture ID and its original certificate
date are retained.

There are two useful proofs. The short database composition is

$$
\begin{aligned}
\mathrm{RC}+\mathrm{BC}&\Rightarrow\mathrm{Actuality},\\
\mathrm{BC}+\mathrm{Actuality}&\Rightarrow\mathrm{Weak\ Rigid\ Comprehension},\\
\mathrm{RC}+\mathrm{Weak\ Rigid\ Comprehension}&\Rightarrow\mathrm{TC}.
\end{aligned}
$$

The first implication is the independent Codex research prompted by Daniel
Kodsi, recorded in
[RC+BC implies Actuality](../evidence/database-records/results/relational-choice-and-boolean-completeness-imply-actuality.yaml)
and its [full proof](../source/topics/classicism/writeups/relational-choice-and-boolean-completeness-imply-actuality.md).
The second is Cian Dorr's Proposition 1, p. 2, in the draft of 30 July 2026,
[recorded here](../source/topics/classicism/results/completeness-and-actuality-imply-weak-rigid-comprehension.yaml).
The third is the proof recorded on 25 September 2026 by Claude Fable 5.1
(Anthropic), prompted by Zachary Goodsell following Christopher Sun's
observation,
[RC+Weak Rigid Comprehension implies TC](../source/topics/classicism/results/relational-choice-and-weak-rigid-comprehension-imply-transversal-choice.yaml).
BC and RC remain available for the second and third steps respectively;
there is no claim that Actuality alone gives Weak Rigid Comprehension.

The **direct proof** does not pass through either Actuality or Weak Rigid
Comprehension. It builds a partially ordered collection of partial
transversals, proves closure under the required algebraic joins, and obtains
a fixed point of a guarded progressive construction. Its contribution is
therefore retained in full below, together with its refinements. No proof of
this new implication is attributed to Bacon or to a paper supplying only
its definitions.

## 2. Exact local strengths retained from the direct proof

Fix an admitted type $\sigma$, including $e$, and put $\rho=\sigma t$.
Write $\mathrm{RC}_{\alpha,\beta}$ for relational selection with input type
$\alpha$ and output type $\beta$, and $\mathrm{BC}_\tau$ for Boolean
Completeness at the relational type $\tau$.

A **represented** family means an admitted predicate in the language of C.
Let $\mathrm{ChainBC}_\tau$ require joins of represented families totally
ordered by the algebraic Boolean order; let $\mathrm{WOChainBC}_\tau$
require them only for represented families which that order internally
well-orders. These are descriptions of local formulas, not new principle
records or external set-theoretic completeness assumptions. The empty
family has the already available bottom as its join.

| Premises over C | Conclusion | Evidence retained below |
| --- | --- | --- |
| $\mathrm{RC}_{\rho,\sigma}+\mathrm{WOChainBC}_\rho$ | $\mathrm{TC}_\sigma$ | Direct argument plus guarded point-output refinement |
| $\mathrm{RC}_{\rho,\rho}+\mathrm{WOChainBC}_\rho$ | $\mathrm{TC}_\sigma$ | Original functional-graph argument |
| $\mathrm{RC}_{\tau,\tau}+\mathrm{WOChainBC}_\tau$ | $\mathrm{BC}_\tau$ | Cut and fixed-point argument |
| $\mathrm{RC}_{\tau,\tau}+\mathrm{CBC}_{\kappa,\tau}+\mathrm{CCC}_{\kappa,\tau}$ | $\mathrm{BC}_\tau$ | Countable disjoint-increment argument |
| $\mathrm{RC}_{\rho,\sigma}+\mathrm{CBC}_{\kappa,\rho}+\mathrm{CCC}_{\kappa,\rho}$ | $\mathrm{TC}_\sigma$ | The same disjoint-increment argument applied directly to the guarded operation |

In particular, the first two conclusions hold with ChainBC or BC in place
of WOChainBC. The point-output choice premise is the useful later
refinement of the original choice instance; the two displayed original
proofs remain independently readable.

Here $\mathrm{CBC}_{\kappa,\tau}$ means that every represented
$\kappa$-countable family of $\tau$-entities has a Boolean join, and
$\mathrm{CCC}_{\kappa,\tau}$ means that every represented disjoint family
of nonbottom $\tau$-entities is $\kappa$-countable. Countability is the map's
Frege-countability notion: there is a represented relation to
$\mathbb N_\kappa$ such that two family members share a numerical label
exactly when they are identical. Labels have the appropriate Frege number
type $\nu_\kappa$; the construction does not assume a single-valued
labeling, a selected enumeration, externally standard numbers, or Infinity.

For clarity, the last row follows without upgrading the point-output
choice premise to $\mathrm{RC}_{\rho,\rho}$. Under failure of
$\mathrm{TC}_\sigma$, the guarded operation $g$ of Part B is strict on
all partial transversals. Form the represented union $A$ of its internal
$g$-chains as in Part A. No completeness is needed to form $A$ or prove it
internally well-ordered. For $F\in A$, put

$$
d_F=g(F)\wedge_\rho\neg_\rho F.
$$

Strictness makes $d_F$ nonbottom. If $F<G$ in $A$, its defining predecessor
condition gives $g(F)\le G$, so $d_F\wedge_\rho d_G=0$. Thus the
represented image of the increments is disjoint and the increment map is
injective. CCC supplies numerical labels for that image; composition with
the represented increment graph labels $A$. CBC therefore gives the one
join of $A$ needed by the final step of the fixed-point proof. Evaluation's
adjunction, already proved in Part A, ensures that this join is a partial
transversal. The fixed point contradicts strictness. This is the point-output
refinement recorded in
[the structural handoff, §1](../source/research/2026-10-22/notes/structural-lane-handoff.md).
Part C retains the full, separate BC-upgrade proof at arbitrary $\tau$.

The composition offers a different locality advantage. The Actuality
result needs only $\mathrm{RC}_{t,t}+\mathrm{BC}_{tt}$. Christopher Sun's
[Actuality implies Transversal](../source/topics/classicism/results/actuality-implies-transversal.yaml)
and
[Transversal plus RC implies TC](../source/topics/classicism/results/transversal-and-relational-choice-imply-transversal-choice.yaml)
then give

$$
\mathrm{RC}_{t,t}+\mathrm{BC}_{tt}+\mathrm{RC}_{\sigma t,\sigma}
\Rightarrow\mathrm{TC}_\sigma.
$$

Consequently all-type RC with BC at $tt$ alone suffices for all-type TC.
This is complementary to the direct proof's completeness premise at
$\sigma t$; it does not erase that proof or its chain/CBC+CCC refinements.

## 3. Shared limits and useful consequences

The direct construction works for an equivalence relation that is an
equivalence relation only actually. It uses no ND, BF, Plenitude, or
identity of actually coextensive property entities. Its crucial
partial-transversal predicate has **$\forall x\,y\,\Box$** scope.
A separate final purification, given in the original direct proof, gives a witness with
**$\Box\forall x\,y$** partiality. That normalization is not substituted
into the chain-join argument.

The internal fixed-point proof uses admitted predicates and represented
graphs, not an external ordinal iteration. The guarded operation of Part B
is a term built for this particular purpose; it is not a representation
of arbitrary functional graphs and gives no Plenitude conclusion.

With BC, the recorded TC⇒RC, TC⇒Zorn, Zorn⇒Well-Ordering and
Well-Ordering⇒TC arrows make RC, TC, Zorn and Well-Ordering equivalent.
Necessitating the discharged implication gives the boxed conditional
$\Box\mathrm{RC}+\Box\mathrm{BC}\Rightarrow\Box\mathrm{TC}$.
Neither step permits necessitation of an optional unboxed premise.
The RC-alone⇒TC question remains separate.

## 4. Provenance and exact verification boundary

The frozen submission's
[catalog entry rigidity.16](../CATALOG.md#rigidity.16)
identifies the direct theorem. Its three source notes are linked below; their mathematical text is preserved in this package:

- [Original direct proof, §§1–9](../source/research/2026-10-22/notes/relational-choice-boolean-completeness-transversal-proof.md).
- [Guarded operation, §§1–6](../source/research/2026-10-22/notes/rc-guarded-progressive-operation.md).
- [Countable-completeness and CCC proof, §§1–4](../source/research/2026-10-22/notes/relational-choice-countable-completeness-ccc.md).

Their statements about no record edit, no formalization, or an unchanged
map describe the drafts when written. They are retained as historical
source text, not as current database-status assertions. The current exact
status is: the three component implication records in §1 have separate
verified Lean certificates; the generated statement for **this stable
conjecture ID remains `lean: stated`**. No machine certificate for every
local strengthening in §2 is asserted here. No human checker is claimed.

The canonical record's short proof is the composition; the linked
independent argument remains part of its mathematical documentation.

---

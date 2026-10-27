# Infinity propagation: finite bounds, quantified finiteness, and observers

Ordinary mathematical research by OpenAI Codex, 25 October 2026. Direct source for the combinations and the new two-stage model below: `misc`, this note, §§2–6, unpaginated. Existing results and constructions keep their attribution in §7. No database, human proof, or formal-verification status is changed.

**Results.** C5 already makes each quantified Axiom of Infinity necessary when true; observers add nothing to that implication. Ordinary logical separation alone does not do so, even when separation and BF hold necessarily. At the individual type this failure remains possible with necessary ND_e and every standard finite lower bound necessary. Thus propagation of the Infinity Schema and propagation of the quantified Infinity axiom are genuinely different questions.

## 1. Exact native definitions

Fix an admitted counting type σ, which may be e or t. Put ν=(σt)t and use the actual Frege definitions:

```math
\begin{aligned}
0_\sigma&:=\lambda X^{\sigma t}.\forall x^\sigma\neg Xx,\\
S_\sigma Z&:=\lambda X^{\sigma t}.\exists y^\sigma
 [Xy\land Z(\lambda x.\,Xx\land x\ne y)],\\
N_\sigma(Z)&:=\forall W^{\nu t}
 [(W0_\sigma\land\forall Y^\nu(WY\to W(S_\sigma Y)))\to WZ],\\
\mathrm{Fin}_\sigma&:=\exists Z^\nu
 [N_\sigma(Z)\land Z(\lambda x^\sigma.\top)],\\
\mathrm{Inf}_\sigma&:=\neg\mathrm{Fin}_\sigma
\end{aligned}
\tag{1}
```

N is exactly FiniteCardinality, not an externally imposed standard natural-number sort. Inf is the quantified Axiom of Infinity. The different Infinity Schema consists of the individual formulas

```math
L_{n,\sigma}:=\exists x_1\ldots x_n
 \bigwedge_{i<j}x_i\ne x_j\qquad(n\ge1)
\tag{2}
```

For comparison define the finite upper bound

```math
U_{n,\sigma}:=\exists x_1\ldots x_n\forall y^\sigma
 \bigvee_{i=1}^n y=x_i\qquad(n\ge1)
\tag{3}
```

These say at least n and at most n, respectively. The external integer n indexes a finite formula, not a hidden quantifier over cardinalities. No Dedekind-infinity replacement is used.

## 2. Finite lower and upper bounds have different modal requirements

For each fixed n, ordinary C proves the following finite-premise implications:

```math
\mathrm{ND}_\sigma+L_{n,\sigma}
 \Longrightarrow\Box L_{n,\sigma},
\tag{4}
```

```math
\mathrm{BF}_\sigma+U_{n,\sigma}
 \Longrightarrow\Box U_{n,\sigma}
\tag{5}
```

For (4), choose the current n distinct witnesses. Current ND_σ makes every pairwise inequality necessary. There are only finitely many inequalities, so normal modal reasoning boxes their conjunction. Necessitated existential introduction, instantiated at the witnesses by CBF, then gives □L_n. The n=1 instance is already a theorem because every type is nonempty. No BF or observer assumption is used.

For (5), choose the current finite covering tuple. For every current y, some identity y=x_i is true and NI makes it necessary. Finite disjunction gives $`\Box\bigvee_i y=x_i`$. BF_σ collects this under the y-quantifier, yielding a necessary cover by the same tuple. Necessitated existential introduction then gives □U_n. ND is unused.

Classical finite reasoning gives $`\neg U_n\leftrightarrow L_{n+1}`$ and, for n≥2, $`\neg L_n\leftrightarrow U_{n-1}`$. Consequently ND_σ+BF_σ makes both the truth and falsity of every fixed lower or upper bound necessary. In particular it preserves every fixed exact finite size.

Thus ND_σ alone propagates the entire Infinity Schema **instance by instance**. It does not convert that schema to the quantified formula Inf_σ. The model in §5 makes this distinction concrete even with necessary BF and necessary ordinary separation.

## 3. Quantified finiteness persists under BF; C5 propagates Infinity too

The recorded [Possible Infinity plus BF proof](../../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/possible-infinity-t-and-bf-t-imply-axiom-of-infinity-t.md) is schematic in σ. In its contrapositive form it proves the C theorem

```math
\mathrm{BF}_\sigma\to
 (\mathrm{Fin}_\sigma\to\Box\mathrm{Fin}_\sigma)
\tag{6}
```

Its proof uses induction over the native N_σ predicate. It counts a property whose noninstances remain noninstances; the base uses BF_σ, and a successor step adds the removed instance back inside a boxed finite cover. It concludes that **some** finite cardinality counts the future whole domain; it does not claim that the same cardinality survives possible identifications. Only current BF_σ is needed for (6), and no external identification of N_σ with ω is used.

Hence ordinary OS, which supplies BF at each type, already propagates current quantified finiteness. Equivalently, under OS, possible quantified Infinity implies current Infinity. This is the opposite direction from the user's current-to-necessary Infinity question.

A useful local sufficient condition for the latter is

```math
\boxed{
C+\mathrm{ND}_t+\Box\mathrm{BF}_\sigma
\quad\vdash\quad
\mathrm{Inf}_\sigma\to\Box\mathrm{Inf}_\sigma
}
\tag{7}
```

To prove it, necessitate the discharged C theorem (6), then use □BF_σ and K to obtain

```math
\Box(\mathrm{Fin}_\sigma\to
                  \Box\mathrm{Fin}_\sigma)
\tag{8}
```

Current ND_t gives the propositional 5 law, by the recorded Proposition 2.2 argument; with T this implies the current B dual $`\Diamond\Box q\to q`$. Explicitly, if ¬q then T gives ◇¬q, and 5 gives □◇¬q, contradicting ◇□q. Now (8) sends ◇Fin_σ to ◇□Fin_σ, and B sends that to Fin_σ. Contraposition yields (7).

The premise in (7) is propositional ND_t, not merely ND at the counting sort σ. Section 5 shows that replacing it by even □ND_e is unsound when σ=e. Under (7)'s assumptions, (6) and (7) make both Fin_σ and Inf_σ noncontingent. Indeed each is equivalent to its own box and diamond.

C5 supplies ND_t and □BF_σ for every admitted σ. Therefore

```math
\boxed{C5\vdash
 (\mathrm{Inf}_\sigma\leftrightarrow\Box\mathrm{Inf}_\sigma)
 \land(\mathrm{Fin}_\sigma\leftrightarrow\Box\mathrm{Fin}_\sigma)}
\tag{9}
```

This uses neither OS, Choice nor comprehension beyond C. The necessitated implication is a discharged theorem of C; no optional BF or Infinity premise is itself necessitated.

## 4. An existing model refutes Infinity propagation under necessary OS

Use the recorded [Coalesced sum: root over all finite individual domains](../../../classicism-results-2026-10-24-v2/source/topics/classicism/models/coalesced-all-finite-individual-domains.yaml), with its [construction and proof](../../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/coalesced-all-finite-individual-domains.md). Its leaves M_n are full extensional one-world models with n individuals, for n≥1. At the root, individuals are threads in $`\prod_{n\ge1}\{1,\ldots,n\}`$; propositions are subsets of the root-plus-leaf set. Every relational type has an arbitrary current truth row and its component relations.

The root has both quantified Inf_e and Inf_t. This is proved internally in the linked construction: because the root truth row of every higher predicate is arbitrary, the external set of standard numeral denotations is an admitted current inductive predicate. Thus root N_σ contains precisely those numeral denotations. Every such numeral counts exactly its standard finite number of current objects. Both root domains are externally infinite, so no numeral counts the whole domain. This is where fullness of current higher predicates matters; external infinitude alone would not establish the quantified formula in an arbitrary Henkin model.

Every root-to-leaf type projection is onto, giving BF at the root at every type, while BF holds at every extensional leaf. Hence □BF holds. The root proposition algebra is complete and atomic. The established ordinary atomic-observer theorem, C+Atomicity_t+BF⇒OS, gives full typed OS at the root; identity gives OS in each leaf. Thus every separately boxed OS instance holds at the root as well. This is a check of the models' evaluations, not necessitation of root OS.

Each leaf has finitely many entities at every fixed type, so each leaf refutes both quantified Inf_e and Inf_t. Consequently the unchanged recorded construction verifies

```math
\boxed{
C+\Box OS+\Box BF+\mathrm{Inf}_e+\mathrm{Inf}_t
 +\Diamond\neg\mathrm{Inf}_e
 +\Diamond\neg\mathrm{Inf}_t
}
\tag{10}
```

Its recorded necessary RC and necessary Relational Choice may also be retained. ND fails at the root, so (10) does not challenge (9). The same model refutes propagation of the lower-bound schemas under OS alone: the root satisfies every fixed L_n, but its one-individual leaf refutes L_2,e and its two-proposition leaves refute L_3,t.

## 5. Stronger individual boundary: all finite bounds persist while quantified Infinity fails

Here is a new ordinary construction, in ZFC metatheory. It verifies

```math
\boxed{
C+\Box OS+\Box BF+\Box ND_e
 +\{\Box L_{n,e}:n\ge1\}
 +\mathrm{Inf}_e+\Diamond\neg\mathrm{Inf}_e
}
\tag{11}
```

It has two stages r→s. The individual projection is the identity. The failure therefore concerns internal counting resources, not a collapse or loss of individuals.

### 5.1 The leaf: internally finite, externally infinite

For each positive integer m let F_m be the full extensional one-world relational type hierarchy with m individuals and two propositions. Take a nonprincipal ultrafilter U on the positive integers, and form the many-sorted Henkin ultraproduct

```math
M=\prod_m F_m/U
\tag{12}
```

The language includes a sort for every admitted type, application symbols, the logical constants and quantifier operations, truth at t, and parameterized lambda-term operations with their beta equations. Each quantifier truth clause and each lambda equation is a first-order sentence of this presentation. Łoś's theorem therefore preserves the actual Henkin quantifier clauses and lambda closure, not just a bare applicative algebra. It preserves every fixed H theorem and every fixed C schema instance. Equality at each sort is the ultraproduct quotient equality. The finite proposition sort remains exactly {0,1}, so M is extensional and its native modality is truth.

Every fixed L_n,e holds in all factors with m≥n, hence holds in M. Thus E:=D_e(M) is externally infinite. On the other hand, each finite factor satisfies the single fixed formula Fin_e. Łoś gives M⊨Fin_e. Concretely the sequence of m-th numeral denotations supplies an ultraproduct cardinality Z satisfying N_e(Z) and Z(Top_e), although it is not any fixed standard numeral. Thus M's externally infinite individual domain is **internally Frege-finite**. Its higher predicates do not contain the external standard cut as an inductive predicate; otherwise the displayed nonstandard counting witness could not be N_e.

No assertion of full external function spaces in M is made. The distinction between a full hierarchy in each finite factor and a Henkin ultraproduct is essential.

### 5.2 The root: full current rows and the same individuals

Set D_e(r)=E, with projection π_e=id_E to the leaf. Recursively, for every flattened relational type $`\tau=\sigma_1\cdots\sigma_k t`$, define

```math
D_\tau(r)=
 \mathcal P\!\left(\prod_{i=1}^k D_{\sigma_i}(r)\right)
 \times D_\tau(M)
\tag{13}
```

For k=0 this is D_t(r)=2×2. Projection π_τ takes the second component, so it is onto. Application takes the section of the current row and applies the leaf relation to the projected argument. Equivalently, for a tuple ā,

```math
(S,F)[\bar a]=
 (\mathbf1_{\bar a\in S},\ F[\pi\bar a])
\tag{14}
```

Every type projection is onto, including the individual projection, and preserves application. Current truth is the first proposition coordinate; truth at s is the second.

Boolean operations act coordinatewise. A quantified formula has its ordinary current truth value over the root domain as first coordinate, and its M-quantified value as second. Surjectivity makes the latter agree with quantifying the leaf projections of root assignments. A lambda term is interpreted by its arbitrary current extension together with the M interpretation of that lambda term. Its current extension is allowed by (13); its leaf component belongs to M by the Henkin lambda closure proved in §5.1. Hence abstraction is admitted at all types, with arbitrary admitted parameters.

Identity of root objects is the first coordinate of the identity proposition; leaf identity of their projections is its second coordinate. These equalities coincide with the native Leibniz equalities. Root haecceity rows separate distinct root objects; at the leaf, surjectivity of predicate projections gives exactly M's equality test. Application respects these equalities. Extensionality in M ensures that two distinct leaf relations differ at some current leaf tuple, and surjective type projections lift that tuple. Therefore no two different root relation objects have identical full application behaviour.

H holds at each evaluation by the ordinary typed truth clauses. If an H theorem equates two formulas, their abstractions have identical root rows and identical leaf components, the latter by extensionality in M. Thus C's Logical Equivalence holds with its actual theoremhood restriction. This verifies a C model; no optional root claim has been used in Logical Equivalence.

At the root, $`\Box p`$ is true exactly when p=(1,1); at the leaf it is simply the second bit of p. Hence r sees r and s, and s sees only s.

### 5.3 Necessary ND_e, BF and OS

Because π_e is identity, the identity proposition of any two individual parameters has equal coordinates. Distinct individuals stay distinct. ND_e is true at r and at the extensional leaf, so □ND_e holds.

For each σ, if ∀x Box(Fx) is true at r, every root instance has both truth coordinates equal to 1. Onto π_σ then makes the leaf universal true, while the root universal is already true. Thus Box(∀x Fx) holds. BF_σ is also true at s. This proves □BF at every admitted type.

Full observer admission can be checked explicitly. Besides identity I, let J:tt have root row p↦p_s and leaf operation the identity on {0,1}. Then

```math
J(p_r,p_s)=(p_s,p_s)
\tag{15}
```

It is admitted by (13). Boolean laws hold coordinatewise. For every σ, the current truth of J(∀x F x) is the M-universal truth of the leaf predicate. The current truth of ∀x J(Fx) is the same, by onto π_σ. The existential calculation is identical with ∃. At s the observer is identity. Hence the Boolean and quantifier comparisons agree at both evaluations for arbitrary inputs; they are identities of whole operations, not merely their current shadows. J is Good for every finite list Δ; so is I.

I and J separate the two coordinates of any distinct root propositions. They give full relational separation too: if two root relation objects differ in their root row, I detects them at a root argument tuple; if their leaf components differ, extensionality in M supplies a distinguishing leaf tuple, surjective projections lift it to a root tuple, and J detects it. Thus OS holds at r at every type and every finite qualification list. It holds at s by extensionality and identity. Therefore □OS holds, instance by instance.

### 5.4 Quantified Infinity changes despite unchanged individuals

Let T be the external set of root denotations of standard numeral terms $`S_e^k0_e`$, k≥0. At the root there is an admitted predicate W on ν_e with current row the characteristic function of T and any leaf component, for example the universal predicate. Its current extension contains zero and is successor-closed. Consequently the defining universal quantifier of N_e forces every root number into T. Conversely every standard numeral belongs to N_e by finite induction. Thus root N_e is exactly T.

At r, the k-th numeral counts exactly k current individuals: this follows by the usual finite induction directly from the zero and successor definitions and actual root equality. Since E is externally infinite, no such numeral counts all of E. Hence r⊨Inf_e.

At s, the original M interpretation is unchanged, so s⊨Fin_e by §5.1. Thus Inf_e has proposition value (1,0), and r⊨◇¬Inf_e. Meanwhile every fixed L_n,e is true at both stages because both individual domains are E and M satisfies that formula; therefore □L_n,e holds for every standard n.

The model does not satisfy ND_t: for example the root-only proposition (1,0) is distinct from Bottom at r and identical to Bottom at s. C5 fails, as required by (9). Its proposition domain at r has only four elements, so no propositional Infinity claim is made for this stronger individual counterexample.

## 6. What the two boundary models establish

The existing model (10) handles quantified Infinity at e and t simultaneously and shows that necessary separation and necessary BF do not suffice. The new model (11) proves a sharper individual statement: neither stable individual identity nor preservation of every finite lower bound repairs the quantified-Infinity implication. Replacing the native quantification over N_e by the external standard numerals would incorrectly erase this counterexample.

The positive theorem uses propositional modal symmetry, supplied by ND_t, together with necessary BF at the counting type. C5 supplies both, so there is no open C5+OS Infinity propagation question left. No general claim that ordinary observers preserve the full impredicative finite-cardinality apparatus is needed or made.

## 7. Sources, attribution and verification status

The native Infinity definitions and finite-cardinality apparatus are in [Background](../../../classicism-results-2026-10-24-v2/source/topics/classicism/background.md), the [individual axiom](../../../classicism-results-2026-10-24-v2/source/topics/classicism/principles/axiom-of-infinity-e.yaml), and the [propositional axiom](../../../classicism-results-2026-10-24-v2/source/topics/classicism/principles/axiom-of-infinity-t.yaml). Their source locators are Bacon and Dorr, *Classicism*, 16 May 2023 draft, §2.3, n. 47, p. 32, and Cian Dorr's formulation of 19 September 2026.

The key existing internal-induction theorem (6) is the linked write-up and the records `possible-infinity-t-and-bf-t-imply-axiom-of-infinity-t` and `possible-infinity-e-and-bf-imply-axiom-of-infinity-e`: suggestion of Cian Dorr, proof by Claude Fable 5.1, 20 September 2026. C5⇒□BF is the recorded Prior–Lemmon route, *Classicism* Proposition 2.3, p. 22; ND_t⇒5 is Proposition 2.2, p. 22. The current-to-necessary combination in §3 is written out here and not attributed to the source as a separately stated theorem.

The existing model in §4 retains Claude Fable 5.1's 20 September construction and later recorded verification history. The general coalesced-root technique is Bacon–Dorr, Appendix E, pp. 80–83. Section 5 is a new specified root over an internally finite Henkin leaf; it is not a new verdict silently attached to that older model.

The ultraproduct methodology and distinction between external infinitude and internal finiteness were already developed locally in [Structural world representation](../../../classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/structural-world-representation.md), §7, and [Gallin comparison](../../../classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/gallin-comparison.md), §3. Here they are applied to one-world finite factors, and the lambda/quantifier and root-extension obligations are supplied explicitly.

A proved-only `scripts.pmap.load_topic` / `Engine` check with empty background and the single existing model confirms both quantified Infinity axioms, Atomicity_t, □BF, □RC and □Relational Choice, with no model conflict. It also confirms the recorded C5⇒□BF arrow. The engine does not supply OS or the new two-stage model verdicts; those are the ordinary arguments above. Repository validation passed: 132 principles, 448 results, 162 models.

All results in this note are ordinary mathematics. No Lean work, compilation, publication or native-record edits were performed.

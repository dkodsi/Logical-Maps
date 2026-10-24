# Exact implication order for primitive preservation packages

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–5, unpaginated. The argument combines the individually proved corruption models in [Typed separation and Classicism](typed-separation-and-classicism.md), §6. It is a classification over H, not over C.

## 1. The family being classified

Let Γ be any fixed finite set of primitive preservation requirements, selected from

$$
M,\quad V,\quad N,\quad Q_\sigma,\quad P_\sigma.
$$

at specified types σ. M,V,N concern primitive conjunction, disjunction and negation; Qσ,Pσ concern the independent primitive universal and existential quantifiers. They do not concern derived versions of those operations. A(E) means E accepts Top and Z(E) means E rejects Bottom.

For J⊆Γ, let T_J be H together with separation by the common class

$$
A(E)\land Z(E)\land\bigwedge_{j\in J}j(E).
$$

Fix one of the material, pointwise-identity or whole-operation preservation tiers, and fix either propositional or full typed separation. Use that same choice throughout the family T_J. The theorem below holds for each of these six choices.

## 2. Exact order theorem

For every J,K⊆Γ,

$$
T_K\vdash T_J\quad\Longleftrightarrow\quad J\subseteq K.
$$

If J⊆K, every K-qualified observer is J-qualified. Separation by the smaller K-qualified class therefore entails separation by the J-qualified class. This proof is already in H.

For the converse suppose $j\in J\setminus K$. The model in §3 satisfies every other primitive preservation requirement simultaneously, with a full typed strongly separating class fixing both endpoints. It fails even propositional material separation for j. Hence it satisfies T_K and refutes T_J in each of the six fixed presentations. This proves the reverse implication.

Thus there are exactly 2^|Γ| distinct theories in each displayed family, with precisely the implication order given by inclusion of the clause sets. There are no additional implications among these packages. This is a statement about the specified family, not a classification of every theory between its members or of cross-tier comparisons.

## 3. Uniform separating models

Take D_e to have two elements, D_t={0,1}² with truth read from the first coordinate, and all higher domains to be full function spaces. Initially interpret the logical operations coordinatewise and equality at every type as the diagonal value of actual equality. The two diagonal readers E_i(b₀,b₁)=(b_i,b_i) jointly separate all relational types.

Change just the second coordinate of the omitted primitive j as follows, leaving every other primitive unchanged:

| Omitted j | Modified second coordinate | Identity forced by material j-separation which fails |
| --- | --- | --- |
| M | Conjunction is constantly 0 | p∧p=p |
| V | Disjunction is XOR | p∨p=p |
| N | Negation is constantly 1 | ¬¬p=p |
| Qσ | The selected universal is constantly 0 | (∀x^σ Top)=Top |
| Pσ | The selected existential is constantly 0 | (∃x^σ Top)=Top |

The first coordinate retains every H truth condition; actual function interpretation validates contextual beta and eta. The fixed endpoint abbreviations still give Top=(1,1) and Bottom=(0,0) in every row. Both readers fix those endpoints and satisfy all non-omitted full-operation identities. Equality is unchanged, so the readers also fix all equality judgments. Full function domains make their propositional separation lift to all relation types.

The displayed failures are explicit. For M or V take p=(0,1). For N take p=(0,0), whose double negation is (0,1). In either quantifier row the selected quantifier applied to the constant-Top family has value (1,0).

Material M/V separation forces the corresponding idempotence identity by observing p and the idempotent composite. Material N separation similarly forces double negation. With A, every eligible Qσ or Pσ observer accepts the selected constant-Top quantification, as well as Top; nonemptiness of σ handles the existential case. Separation would identify them. Thus the relevant material separation fails in each row, and any stronger tier fails too.

These models also establish cross-tier non-implications whenever the target requires an omitted primitive. They do not imply a cross-tier positive arrow merely from clause inclusion. The full construction and the separate equality-clause sharpness arguments are in the linked source note, §6.

## 4. The empty package and the limits of the classification

H proves propositional S[A∧Z]. For distinct propositions with different truth values, identity distinguishes them. For two distinct true propositions choose one, a, different from Top and use the admitted test E(r):=r∧(r≠a). It accepts Top, rejects Bottom, and is false at a but true at the other proposition. For two distinct false propositions choose a different from Bottom and use E(r):=r∨(r=a). It again satisfies A,Z and distinguishes the pair. These exhaust the cases.

Consequently T_∅ is just H in the propositional presentation. In the full typed presentation it is exactly H plus Functionality, by [the general typed theorem](typed-separation-and-classicism.md), §2.

The inclusion classification holds separately in each presentation. For example, whole-operation propositional M-separation is strictly stronger than pointwise M-separation, as shown by [the hidden-proposition model](local-tiers-and-models.md), §3. At full typed scope those two tiers coincide because separation itself supplies Functionality.

## 5. Why this is not the entire theorem lattice

The map J↦T_J embeds the powerset inclusion order in the order of theories by strength. It need not preserve their joins. In particular,

$$
S[A\land Z\land M]\quad\text{and}\quad S[A\land Z\land V]
$$

can be strictly weaker than

$$
S[A\land Z\land M\land V].
$$

The [diamond-meet/chain-join model](two-orders-model.md) proves this even with full typed separation, endpoint-valued witnesses, equality fixing, and the matching universal/existential packages on the separate sides. A theory join combines the two assertions; it does not impose both qualifications on each witness.

Derived-operation clauses can introduce further equivalences because their actual term definitions matter. Identity fixing, endpoint fixing, factivity, reversibility, finiteness and admission hypotheses also add directions not covered by the independent primitive index set. The other notes study precisely those parts of the H space.

The direct source for this classification and empty-package argument is this note (`misc`, OpenAI Codex, 24 October 2026, §§2–4, unpaginated); the displayed model construction is proved in the linked companion notes.

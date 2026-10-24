# Necessary logical separation and one atom

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–5, unpaginated.

Necessary logical separation needs only one atom to give full atomicity under C5. In fact, the only separation premise needed for that implication is one boxed propositional instance, qualified at the proposition type. Consequently any countermodel to the proposed converse from C5 plus necessary logical separation to reversible separation must be atomless.

## 1. Exact statements and scope

Use the fixed relational language and the whole-operation qualification Good_Δ from [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md), §1. Every type list Δ is a finite external list. Write

```math
S_t:=\forall p,q^t\left[p=q\leftrightarrow
\forall E^{tt}\bigl(\mathrm{Good}_{\{t\}}(E)
\to(Ep\leftrightarrow Eq)\bigr)\right].
```

Thus S_t is one closed formula: its output type is t and its quantifier-preservation list is exactly {t}. Its Boolean and quantifier laws remain full composite identities. Over C, the equality clauses of Good are consequences of the Boolean qualification. By that Boolean qualification, the material-agreement formulation above is equivalent to the formulation using E(p↔q).

Let

```math
\mathrm{OneAtom}:=\exists a^t\mathrm{Atom}(a),
\qquad
\mathrm{Actuality}:=\exists a^t(\mathrm{Atom}(a)\land a).
```

Here Atom and Atomicity_t are the usual Boolean-order notions in C; in particular an atom is required to be distinct from Bottom. C5 means C together with the schema □ND at the relational types. It is not an abbreviation for unboxed ND.

Write OS, Rev and End for the full relational separation schemas with ordinary, reversible and endpoint-valued Good_Δ observers respectively. A boxed schema consists of its separately boxed, object-variable-closed instances; it is not an infinite object-language conjunction.

**Theorem.** Over C,

```math
\boxed{\mathrm{C5}+\Box S_t+\mathrm{OneAtom}
\quad\Longrightarrow\quad\mathrm{Atomicity}_t.}
\tag{1}
```

Together with the previously established observer characterizations, this gives the exact theory equivalences over H:

```math
\boxed{
\mathrm{End}
\ \Longleftrightarrow\ \mathrm{C5}+\mathrm{Atomicity}_t
\ \Longleftrightarrow\ \mathrm{C5}+\Box S_t+\mathrm{OneAtom}
\ \Longleftrightarrow\ \mathrm{C5}+\Box\mathrm{OS}+\mathrm{OneAtom}.}
\tag{2}
```

The right sides explicitly contain C as part of C5. The first equivalence uses the full typed endpoint-separation theorem that recovers C from H. The new argument itself does not recover C from the single formula □S_t.

## 2. Modal facts with their premise discipline

Three established facts are used.

1. **C5 supplies the relevant Barcan instances and makes □ S5.** In particular it supplies BF_t and its necessary form. In C, □p is p=Top. ND_t applied to ¬p and Top gives ◇p→□◇p; its boxed form supplies that law throughout the modal range. With C's normal S4 laws this gives S5, including ◇□A→A. Each particular use employs finitely many instances of the C5 schema.

2. **Atoms persist under C5.** For clarity, use

```math
   \mathrm{Atom}(a)\equiv a\ne\bot\ \land\
   \forall p\bigl[(a\land p=a)\lor(a\land\neg p=a)\bigr].
```

   ND_t makes a≠Bottom necessary. For each p, either displayed identity supplies its own necessity by NI, so the disjunction is necessary. BF_t then moves that necessity past ∀p. Hence Atom(a)→□Atom(a). This is a derivation under stated C5 instances, not an application of necessitation to Atom(a).

3. **Atomicity persists under C5.** The recorded route is Atomicity_t+BF⇒Atomicity at all relational types, followed by C5+Atomicity⇒necessary Atomicity. For the present conclusion only the final type-t instance is used. Its finite proof can be packaged as a closed C theorem

```math
   K_2\land\mathrm{Atomicity}_t\to
   \Box\mathrm{Atomicity}_t,
   \tag{3}
```

   where K_2 is the finite conjunction of C5 instances occurring in that proof. Axiom 4 makes those instances persistent.

Likewise the established local converse from [Atomic observers and finite stabilizers](../operator-representation.md), §3, uses the single propositional separation formula S_t:

```math
K_1\land\mathrm{Actuality}\land S_t
\to\mathrm{Atomicity}_t.
\tag{4}
```

Here K_1 is a finite conjunction of C5 instances. Briefly, a true atom gives a correct endpoint evaluator. Compose it with an ordinary separating observer qualified at t. The resulting endpoint observer is still qualified at t; its universal diagonal produces an atom below any prescribed nonbottom proposition. No separation instance for a longer type list is needed in this local converse.

Equations (3) and (4) are closed finite-premise C theorems, so their necessitations are available. By contrast, none of OneAtom, Actuality, S_t or Atomicity_t is necessitated as an optional premise. We use the explicitly assumed □S_t. The finite conjunction K_1∧K_2 and the few C5 instances needed for the modal laws can be enlarged once at the outset; C5 supplies that conjunction and its necessity by 4.

## 3. Proof of the new implication

Assume C5, □S_t and OneAtom. Choose an atom a. Since a≠Bottom, C's Boolean/modal laws give ◇a. Atom persistence gives □Atom(a). Therefore

```math
\Diamond\bigl(\mathrm{Atom}(a)\land a\bigr),
\quad\text{hence}\quad\Diamond\mathrm{Actuality}.
\tag{5}
```

Necessitate the closed implication (4). Necessary K_1 and the premise □S_t then give

```math
\Box\bigl(\mathrm{Actuality}\to
\mathrm{Atomicity}_t\bigr).
```

Combining this with (5) yields ◇Atomicity_t. Now necessitate the closed implication (3). Necessary K_2 gives

```math
\Box\bigl(\mathrm{Atomicity}_t\to
\Box\mathrm{Atomicity}_t\bigr),
```

so ◇□Atomicity_t. The S5 consequence ◇□A→A finally gives Atomicity_t. This proves (1).

For (2), End is already equivalent to C5+Atomicity_t. That package gives separately necessary ordinary separation for every finite list and every relational output type. Atomicity_t applied to Top supplies OneAtom. Conversely, either necessary-separation package in (2) contains □S_t, so (1) yields C5+Atomicity_t and hence End. The implication to Rev is the established atom-swap construction of qualified involutions; the new proof does not construct inverses for arbitrary observers.

## 4. Exact single-witness consequences

Fix C5+□S_t, or the stronger background C5+□OS. Over either background, the following are equivalent:

```math
\begin{gathered}
\mathrm{OneAtom},\
\mathrm{Actuality},\
\mathrm{Atomicity}_t,\
\exists E^{tt}\,[\mathrm{Good}_{\{t\}}(E)
\land\mathrm{End}(E)],\
\exists E^{tt}\,[\mathrm{Good}_{\{t\}}(E)
\land\mathrm{FinIm}(E)],\
\mathrm{End}.
\end{gathered}
\tag{6}
```

The last entry is a schema, so the equivalence involving it is between theories. FinIm is the internal finite-image formula of the hierarchy note, not external finite cardinality and not a uniform bound on all observers.

Here are the remaining connections, beyond (1). Atomicity_t yields an atom below Top, and C5+Atomicity_t yields necessary Actuality. Actuality immediately yields OneAtom. Under C5, any atom a supplies the endpoint observer E_a(p)=□(a→p), qualified at t and indeed at every fixed finite list. Conversely an endpoint Good_{t} observer yields its diagonal atom. The finite-image theorem in the hierarchy note, §5, takes one finite-image Good_{t} observer, uses a finite image atom and the universal diagonal, and supplies an endpoint Good_{t} observer. The converse holds because an endpoint observer has at most two outputs. These constructions require no prior global Atomicity or Actuality; their C5 premise is present here.

In particular, replacing OneAtom in either package of (2) by Actuality or by the existence of one internally finite-image Good_{t} observer leaves the exact endpoint characterization unchanged. That single observer need not itself be separating.

This settles the converse from necessary ordinary separation to reversible separation on the entire non-atomless part of C5. The [finite-block symmetry model](finite-block-symmetry-reversible-gap.md) subsequently settles the other side: it is an atomless model of C5+□OS failing Rev. The finite-support permutation model shows that atomlessness itself does not prevent Rev; the distinction is therefore substantive.

## 5. Sources

The new bridge and the equivalences assembled from it are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–4, unpaginated.

The exact single-list local converse is [Atomic observers and finite stabilizers](../operator-representation.md), §3. The endpoint characterization, atom/evaluator correspondence, finite-image reduction and reversible consequences are [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md), §§3–6 and 8. They are ordinary mathematical results; this note creates no additional formal certification.

The background atomicity stability route is recorded in [Atomicity_t and BF imply Atomicity](../../source/topics/classicism/results/atomicity-t-and-bf-imply-atomicity.yaml) and [C5 and Atomicity imply necessary Atomicity](../../source/topics/classicism/results/c5-and-atomicity-imply-necessary-atomicity.yaml). The latter cites Bacon and Dorr, *Classicism*, draft of 16 May 2023, Proposition 2.6, pp. 25–26, and the concluding equivalences on p. 33. The necessary Barcan consequence of C5 is recorded in [Necessary distinctness implies necessary Barcan](../../source/topics/classicism/results/necessary-distinctness-necessary-r-implies-necessary-barcan-r.yaml). The S5 calculation is also explicitly recorded in [Boxed propositional ND and the necessity hierarchy](../../source/topics/classicism/results/necessary-distinctness-necessary-t-implies-necessary-two-hat-implies-nd.yaml).

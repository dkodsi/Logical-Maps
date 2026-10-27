# Generic-point Boolean models: observer separation with contingent CH and analysis

Ordinary mathematical research by OpenAI Codex, 25 October 2026. Direct source for the generic-point observer construction and combinations: `misc`, this note §§1–9, unpaginated. The full Boolean-valued hierarchy and its extensional forcing interpretation are the earlier construction audited in [C5 and Functional Choice versus analysis](../dependencies/c5-functional-choice-analysis.md). The decisive change here is the designated truth evaluation. No native records, human proofs, or formal-verification statuses are changed.

## 1. Result and exact metatheory

There are relative models of relational C satisfying

```math
\boxed{\mathrm{C5}+\mathrm{SplitMono}+\mathrm{BoxSep}
 +\Box\mathrm{BF}_{\rm all}+\Box\mathrm{RelationalChoice}_{\rm all}}
\tag{1}
```

in which first-order analytical truth and CH can be contingent. SplitMono and BoxSep are the full, current separation schemas, with every finite qualification list and every relational output type. In particular ordinary OS holds. Neither necessary OS nor Rev holds.

Two versions distinguish the direction of change:

* Starting with a countable model of ZFC + V=L and forcing with Add(ω,ω₂), the designated evaluation satisfies universal **¬CH** and the first-order analytical sentence “there exists a nonconstructible real”. Both fail at the isolated-atom evaluation.
* Starting with a countable model of ZFC + ¬CH and using a homogeneous countably closed collapse of the old continuum onto ω₁, the designated evaluation satisfies universal **CH**, while ¬CH holds at the isolated-atom evaluation.

Actual real structures exist at the same carrier type t at both evaluations. Thus these are nonvacuous failures of current-to-necessary propagation. The first version also refutes Necessity of Analysis; both refute Non-contingency of CH.

The precise metatheory is an ambient ZFC universe containing a countable model M of the indicated first-order set theory. **M need not be transitive or externally well founded.** We use an external filter generic for the internal Boolean algebra of M. This countable-model assumption is explicit; no additional consistency-strength claim is needed below.

## 2. Internal Boolean values and an external generic truth evaluation

In M choose an atomless complete Boolean algebra A. Let

```math
B=2\times A,
\qquad a=(1,0_A),\qquad b=(0,1_A)
```

All algebras, maps, subsets and joins called *internal* are objects or computations of M. Their externalizations use the membership relation of M. Thus A is an ordinary external countable Boolean algebra, but it need not be externally complete. Its internally asserted completeness is used only on families that belong to M.

Let G be an external filter on A meeting every subset D of A which belongs to M and which M regards as dense in A\{0}. Such a filter exists: externally enumerate these countably many dense sets and successively choose a descending nonzero condition meeting each. Include the dense decision sets for every internal Boolean element; equivalently these are already among the enumerated sets. Consequently G is an ultrafilter on the externalized algebra. The same construction can begin below any specified nonzero element.

Designate truth in B by

```math
\mathcal U_G=\{(\epsilon,c)\in B:c\in G\}
\tag{2}
```

This differs from the earlier isolated-atom evaluation, which designated truth by the first coordinate ε.

### The exact quantifier lemma

Let I and f:I→A belong to M, with I interpreted externally as its members in M. Let j=∨_{i∈I} f(i), computed internally. Define internally

```math
D_f=\{c\ne0:c\le\neg j\ \text{or}
              \exists i\in I\ (c\le f(i))\}
\tag{3}
```

M proves D_f dense. Given c>0, either c∧¬j>0, or c≤j. In the latter case some c∧f(i)>0, since finite meets distribute over arbitrary internal joins. In either case refine c to a member of D_f. These assertions about a fixed internal family translate to the corresponding external assertions about its members.

If j∈G, a point of G∩D_f cannot lie below ¬j, so f(i)∈G for some i. The converse follows because f(i)≤j. Thus

```math
\bigvee_{i\in I}f(i)\in G
\quad\Longleftrightarrow\quad
\exists i\in I\ [f(i)\in G]
\tag{4}
```

Complementation gives the universal version

```math
\bigwedge_{i\in I}f(i)\in G
\quad\Longleftrightarrow\quad
\forall i\in I\ [f(i)\in G]
\tag{5}
```

The empty-family conventions agree. Applying this to the A-coordinate of an internal B-valued family proves the same truth clauses for (2). No external completeness of A, external standardness of M, or arbitrary ultrafilter completeness is assumed. Genericity for the specifically displayed internal dense sets is what supplies the quantifier clauses.

## 3. The typed C5 model

Build the full relational type hierarchy internally in M:

```math
D_e=\omega^M,\qquad D_t=B,\qquad
D_{\sigma\to\tau}=(D_\tau)^{D_\sigma}\quad(\tau\ne e)
\tag{6}
```

At each standard finite type expression, externalize the corresponding internal set. Application is M's function application. Internal extensionality makes distinct internal functions distinguishable at an internal argument, so externalized application is a well-defined ordinary function operation. Every formula used here has a fixed finite syntactic translation into M; there is no reliance on a nonstandard syntax or an external recursion through M's ordinals.

Boolean operations are those of B. Quantifiers are the internal meets and joins of the internal predicate values. Lambda abstraction produces the corresponding internal function. M's Separation and Replacement supply closure for every fixed formula with internal parameters. Equations (4)–(5), together with the ultrafilter laws, show that designated truth has the ordinary classical Boolean and quantifier truth conditions.

Defined Leibniz equality is crisp at every type. If x=y as members of M, every property has equal values on them. If x≠y, the internal characteristic function of the singleton {x} belongs to the full property domain and has values 1 and 0 at x and y. Therefore the B-value of x=y is 1_B or 0_B according as the two entities are identical or distinct. In particular

```math
\|\Box p\|=\|p=1_B\|=
\begin{cases}1_B,&p=1_B,\\0_B,&p\ne1_B\end{cases}
\tag{7}
```

The algebraic soundness argument for H and Logical Equivalence is internal to M. A fixed H-proof is finite. Its usual Boolean-valued soundness proof shows its conclusion has B-value 1 at every internal assignment. H-equivalent formulas therefore have identical B-values at every argument; internal function extensionality identifies the lambda abstractions. This verifies C's theoremhood-restricted Logical Equivalence rule. It does not apply that rule to equivalences derived from optional premises.

Since identity and inequality have endpoint values, ND holds at every type with value 1, and so does its box. Hence this is a C5 model. The same reasoning works at the isolated-atom evaluation ε=1; there the first coordinates of meets and joins immediately have the ordinary classical quantifier clauses. We shall use that evaluation to exhibit possible disagreement.

### Necessary BF

For every admitted predicate F, both ∀x□Fx and □∀xFx have value 1 exactly when every internal value Fx is 1; otherwise both have value 0. Internal completeness gives ∧_x Fx=1 iff every Fx=1. Thus every all-type BF instance has value 1, and its box has value 1.

### Necessary Relational Choice

This holds internally as a Boolean-valued formula and consequently at both designated evaluations. Given a relation U:σ×τ→B, internally well-order D_τ and put

```math
S(x,y)=U(x,y)\wedge\neg\bigvee_{z<y}U(x,z)
\tag{8}
```

Internal Choice and Replacement in M supply this admitted binary relation. The row values S(x,y) are pairwise disjoint, lie below U(x,y), and have the same join as the U-row. Consequently S is single-valued with value 1, its totality has the same value as Serial(U), and S⊆U has value 1. The implication from Serial(U) to the existential functional-subrelation conclusion therefore has value 1. Quantifying over U preserves 1. This argument takes place inside M, so its well-order and transfinite Boolean calculation do not presume external well-foundedness. It uses relation graphs even when τ=e; no forbidden individual-valued function type is formed.

Thus □RelationalChoice holds at every admitted input/output type.

## 4. Weak homogeneity supplies ordinary logical separation at the generic point

Assume M has a set Γ of complete Boolean automorphisms of A such that

```math
\forall c,d\ne0\ \exists\alpha\in\Gamma\quad
\alpha(c)\wedge d\ne0
\tag{9}
```

This is weak homogeneity, asserted internally. For c>0, the internal set

```math
D_c^{\rm orb}=\{d>0:\exists\alpha\in\Gamma\ d\le\alpha(c)\}
\tag{10}
```

is dense: first use (9), then refine to the positive intersection. Genericity therefore gives an internal α with α(c)∈G.

Consider the following internally admitted operations B→B:

```math
E_0(\epsilon,c)=(\epsilon,\epsilon\cdot1_A),
\qquad
E_\alpha(\epsilon,c)=(\epsilon,\alpha(c))
\tag{11}
```

Each is a unital Boolean homomorphism preserving all internal joins and meets. Thus, for every admitted type σ and every internal F:D_σ→B,

```math
E\left(\bigwedge_xF(x)\right)=\bigwedge_xE(F(x)),
\quad
E\left(\bigvee_xF(x)\right)=\bigvee_xE(F(x))
\tag{12}
```

These identities hold for every member of the entire internal predicate domain. Internal function extensionality gives the required identities of the composite quantifier operations. The Boolean operation identities are handled in the same way. Equality judgments are crisp and E fixes both endpoints, so the equality qualifications hold. Thus each operation in (11) is Good_Δ for every finite type list Δ, with qualification value 1_B. These are whole-operation identities, not current truth agreements.

Every nonzero r=(ε,c) is accepted by some such observer at $`\mathcal U_G`$: if ε=1, E₀r=1; otherwise c>0 and (10) supplies α with Eαr true. For unequal propositions p,q apply this to their Boolean symmetric difference. Boolean preservation then says Ep and Eq have different actual truth values.

For unequal higher relational entities X,Y, internal function extensionality supplies a tuple u with X[u]≠Y[u]. Apply the preceding propositional argument to that pair of values. Conversely identical entities have identical observed values. Equations (4)–(5) convert this external verification over actual internal-domain members into truth of each universally quantified separation formula. Hence **full OS holds at the generic point**, for every output type and finite qualification list.

The reader E₀ need not preserve native Box; this is repaired for the forcings below by a different witness, without weakening ordinary qualification.

## 5. Self-similarity strengthens the witnesses to SplitMono and BoxSep

Suppose there is an internal nonzero proper c∉G and an internal complete Boolean isomorphism

```math
h:A\longrightarrow A\mathbin{\upharpoonright}c
```

Define internal operations

```math
\begin{aligned}
E(\epsilon,d)&=(\epsilon,\ (\epsilon\cdot\neg c)\vee h(d)),\\
F(\epsilon,d)&=(\epsilon,\ h^{-1}(d\wedge c))
\end{aligned}
\tag{13}
```

Both preserve endpoints, Boolean operations and all internal joins and meets. For E, on the interval below ¬c the value is the first-coordinate bit; on the interval below c it is h(d). For F, intersect with c and apply the complete relative-algebra isomorphism. These observations verify preservation including complements and empty joins/meets. Both are therefore fully Good by §4.

Moreover F(E(ε,d))=(ε,d), because the part below c of E's second coordinate is h(d). Thus F∘E=I is a whole internal operation identity. Since c∉G, ¬c∈G, so E accepts every r whose first coordinate is 1. The automorphisms Eα handle all r with a nonzero second coordinate as before, and have qualified inverses E_{α^{-1}}. Replacing E₀ by E in the separation proof yields **full SplitMono**.

Every witness just used is internally injective. An injective unital Boolean homomorphism reflects 1, so (7) gives E(□p)=□(Ep) for every p. Internal extensionality makes this a whole-operation identity. The same witnesses therefore also establish **full native-Box separation**. The left inverse F itself need not commute with Box, and no such condition is used in SplitMono.

Both forcing algebras used below have the required self-similarity below every nonzero basic condition. Choose two incompatible internal basic conditions. At least one is outside G, and the associated isomorphism belongs to M. This gives the c and h required here without assuming G belongs to M.

These are current schemas. Section 8 proves that their necessary versions cannot all hold.

## 6. The exact real-structure and analytical transfer

At σ=t the carrier labels are B. Assume internally

```math
|\mathbb R^M|\le|B|,
\qquad
1_A\Vdash|\mathbb R|\le|\check B|
\tag{14}
```

Both forcings below satisfy (14). Choose distinct labels s₀,s₁∈B, an internal ground injection j₀:ℝ→B taking 0,1 to these labels, and an internal name for an injection $`\dot j:\mathbb R\to\check B`$ forced to take 0,1 to the same labels. Internal Choice and the maximum principle give the name; a finite permutation of its range anchors the two constants.

Pull the ground field, order and N back along j₀; pull the forced real field and N back along $`\dot j`$. Pair their characteristic and Boolean values. For example, the resulting sum graph at labels x,y,z has value

```math
\left(
 \mathbf1_{\text{ground sum}(x,y,z)},
 \|\text{forced sum}(\check x,\check y,\check z)\|_A
\right)
```

Internal Replacement makes this an admitted ternary relation B³→B. The domain, N, order and product graphs are admitted in the same way; s₀,s₁ supply the individual constants of the real structure. This forms a tuple $`\mathfrak R_*`$ with

```math
\|\mathrm{Real}_t(\mathfrak R_*)\|=1_B
\tag{15}
```

Here is the quantifier check needed for (15), not just the field axioms. Every internal name for a subset of $`\check T`$, for an internal set T, is equivalent to the canonical name with coefficients

```math
t\longmapsto\|\check t\in\dot Y\|_A
```

Conversely every internal map T→A supplies such a name. At T=B^k these maps are exactly the A-coordinates available in the full k-ary relational domains; their first coordinates can be independently chosen. Thus the native relation quantifiers cover all internal forcing names for subsets of the carrier and its finite powers. Element quantifiers over $`\check B`$ are the corresponding meets and joins over ground labels; arbitrary mixed names for its elements do not add cases, by the usual Boolean-valued bounded-quantifier interpretation. All these are fixed set-theoretic assertions proved inside M.

Therefore native completeness means precisely nonempty bounded-set completeness in each coordinate, and least inductive N has the right interpretation. No higher-type intensional identity is identified with forcing equality: this transfer concerns only the extensional real-structure formulas, with relations used by application and carrier identity used between labels. CH's injections and bijections are represented by binary relations, so its definition belongs to this fragment too.

For a first-order analytical sentence φ, or an extensional finite second-order analytical sentence such as CH, put

```math
U_\varphi=\forall\mathfrak R
 [\mathrm{Real}_t(\mathfrak R)\to\varphi(\mathfrak R)]
```

Let εφ be the ground truth value of φ in M's standard real field, and let pφ be its internal forcing Boolean value. Then

```math
\boxed{\|U_\varphi\|=(\epsilon_\varphi,p_\varphi),
\qquad \|U_{\neg\varphi}\|=(1-\epsilon_\varphi,\neg p_\varphi)}
\tag{16}
```

For completeness, categoricity of complete ordered fields is applied internally in each coordinate, and below the Boolean support of Real for a partially real tuple. It implies every implication Real→φ has value at least (εφ,pφ). Taking the universal meet preserves this lower bound. The tuple in (15) gives the reverse bound, hence equality. This is the previously audited extensional forcing-transfer proof, now carried out inside M.

Nonstandard M causes no change in this argument. Each cited coding equivalence, forcing calculation, and complete-field theorem is a fixed first-order theorem of ZFC interpreted in M. We do not identify its naturals or reals with the external ones. Equations (4)–(5) then externalize the typed model's actual truth. In particular (15) establishes actual real-structure existence at both evaluations; it is not inferred from a vacuous universal truth.

## 7. Two explicit forcing choices

### 7.1 Current ¬CH and a nonconstructible real

Assume M⊨ZFC+V=L. Internally let κ=ω₂ and A be the regular-open completion of Add(ω,κ), the finite partial functions κ×ω→2.

This forcing is weakly homogeneous: finite bit flips make any two conditions compatible, and induce complete Boolean automorphisms. Its completion is atomless. Below any basic condition the remaining coordinates are again in bijection with κ×ω, so its relative completion is internally isomorphic to A. Thus §§4–5 apply.

Internally the forcing is ccc, preserves ω₁ and κ, and forces the continuum to be κ. Under V=L, GCH gives |A|=κ: there are κ conditions, and each regular-open element is determined by a countable antichain; κ^{ℵ₀}=κ. Distinct coordinate Boolean generators give the matching lower bound. Consequently the old continuum ω₁ and the forced continuum κ both inject into $`\check B`$, verifying (14).

Let φ_L be the finite parameter-free first-order analytical sentence “every real is constructible”, in the ordered-field language with N. Its explicit second-order-arithmetic coding into that language, and the standard parameter-free Σ¹₂ definition of constructible reals, are audited in [Analytical sentence audit](../dependencies/analytical-sentence.txt). The internal ZFC coding theorem applies in M and its Boolean-valued forcing calculation.

M satisfies CH and φ_L. The forcing gives ¬CH and adds a real outside the old constructible universe, hence forces ¬φ_L. Equation (16) yields

```math
\|U_{\rm CH}\|=\|U_{\varphi_L}\|=a,
\quad
\|U_{\neg\rm CH}\|=\|U_{\neg\varphi_L}\|=b
\tag{17}
```

At the generic evaluation b is true and a is false. Both are nonzero and neither is 1_B. By (7), the true propositions in (17) are not necessary and their opposites are possible. This gives current universal ¬CH and current universal existence of a nonconstructible real, with possible opposite universal truths. It refutes Necessity of Analysis and Non-contingency of CH under the package (1).

### 7.2 Current CH with possible ¬CH

For the particular direction CH→□CH, assume M⊨ZFC+¬CH. Internally set κ=2^{ℵ₀} and take

```math
P=\{p:p\text{ is a countable partial function }
                   \omega_1\to\kappa\},
```

ordered by extension, with A its regular-open completion.

P is countably closed internally: the union of a descending ω-sequence is still a countable partial function. It therefore preserves ω₁ and adds no reals. The generic union is a total surjection ω₁→κ: each coordinate can be added, and each α<κ can be placed at a fresh coordinate. Thus the old set of reals is unchanged but has cardinality ω₁ after forcing. The forcing therefore forces CH.

P is weakly homogeneous. Given p,q, an internal permutation of ω₁ moves dom(p) away from dom(q); both are countable. Reindexing p by this permutation makes it compatible with q. The permutations induce complete automorphisms of A, and the argument extends from basic conditions to arbitrary nonzero Boolean elements by refinement. A is atomless because every condition can be extended with incompatible values at a fresh coordinate.

Below a fixed condition p, removing its fixed graph leaves countable partial functions on ω₁\dom(p) with values in κ. An internal bijection ω₁≅ω₁\dom(p) gives P≅P↓p and hence A≅A↾[p]. This supplies §5's self-similarity.

The Boolean algebra has at least κ elements, since the conditions assigning the various α<κ to one fixed coordinate form an antichain of size κ. The ground reals therefore inject into B. After forcing, ω₁ is preserved and the real field has size ω₁; B contains an old injection of ω₁ and so has enough ground labels. This proves (14) without requiring an exact cardinality for A.

Now (16) gives

```math
\|U_{\rm CH}\|=b=(0,1_A),
\qquad
\|U_{\neg\rm CH}\|=a=(1,0_A)
\tag{18}
```

Hence the generic evaluation satisfies actual real-structure existence, current universal CH, and possible universal ¬CH. In particular

```math
\boxed{\mathrm{C5}+\mathrm{OS}+H_t+U_{t,\rm CH}
\not\models\Box U_{t,\rm CH}}
\tag{19}
```

The stronger current SplitMono/BoxSep and necessary BF/Relational Choice premises in (1) can all be added to the left side.

This countably closed variant is used for CH, not for φ_L: because it adds no reals, it does not supply the earlier change in that first-order analytical sentence. Variant 7.1 supplies the separate analytical counterexample.

## 8. Why this does not conflict with Functional Choice propagation

The earlier full Boolean-valued counterexample was evaluated at the isolated atom. That evaluation has current Functional Choice, because internal Choice selects witnesses from its serial first-coordinate relation. It does not have OS. The present generic evaluation has OS but fails Functional Choice.

An exact failed instance uses input and output type t. Put

```math
R(p,q)=(p\wedge(q=\top))\vee(\neg p\wedge(q=\bot))
\tag{20}
```

Its seriality has value 1. For a selecting operation f:B→B, let

```math
c_f=\bigwedge_{p\in B}R(p,f(p))
```

If c_f>0, then for every p it lies either below p or below ¬p; if f(p) is neither endpoint, the corresponding factor is 0. A nonzero c_f is therefore an atom of B. Since A is atomless, the only atom is a. Conversely the internal selector choosing the endpoint according to p's first bit has c_f=a. Thus the existential selector value is exactly a, and the FC_{t,t} instance has value a. Its box has value 0.

At the generic evaluation a is false. Therefore there is no counterexample to the established implication OS+FC⇒□FC: its FC premise fails.

At the isolated-atom evaluation, FC_{t,t} is true while □FC_{t,t} is false. The finite-instance transport theorem in [Witness transport](../../../next-update/proofs/observer-witness-transport.md), §3, then shows that the propositional separation instance with

```math
\Delta=\{t,tt,ttt\}
```

is false there. Since it is true at the generic evaluation, its B-value is not 1. Its box is false, and its negation is possible. Thus **necessary OS fails** in the present model. Necessary SplitMono and necessary BoxSep fail a fortiori, since their unboxed instances imply the corresponding ordinary separation instances.

Finally, the universal analytical/CH propositions in (17) or (18) are closed pure propositions and contingent. Rev implies No Pure Contingency by the previously established conjugation theorem. Hence Rev fails too. Qualified left inverses therefore remain insufficient to propagate these mathematical truths, even in C5.

No unboxed or boxed Boolean Completeness, Rigid Comprehension, or Functional Choice verdict at the generic point is borrowed from the isolated-atom evaluation. Their current truth can change with the evaluation. Only the explicitly verified flags above are asserted.

## 9. What defeated the finite-pinning obstruction

The component-shift symmetric model suggested as an initial candidate cannot give the required universal analytical contingency: it is one-object and has No Pure Contingency. There is also a broader obstruction for unrestricted symmetric ideally-full profiles. Fix the finite support of a current real structure. Its stabilizer fixes the field data and every standard rational. The external set of standard natural iterates is invariant, hence admitted by the invariant-current-relation lemma. Completeness makes this set unbounded, giving external Archimedeanity. Rational density then makes every stabilizer automorphism fix every carrier element. Every external subset and finite relation on the carrier is consequently invariant and admitted. Such a structure is the ambient complete real field with its full external relation powers; varying finite-block or infinite-block symmetry does not change its analytical mathematics.

The present model is a genuine Henkin escape from that obstruction. Its typed domains contain all functions internal to M, not every function on their externalized domains. At the generic evaluation, admitted extensions depend on G; arbitrary external invariant subsets need not be available. Genericity supplies exactly the truth clauses for internal families without restoring external powerset fullness. Weak homogeneity nevertheless supplies enough internally admitted complete Boolean maps to separate all proposition distinctions. This is the new combination.

The Boolean construction and the exact extensional transfer are sourced and proved in [the earlier model note](../dependencies/c5-functional-choice-analysis.md), §§2–7, using Bacon's *Could the truths of mathematics have been different?*, Appendix B.2. The observer qualifications and finite FC implication are [Witness transport](../../../next-update/proofs/observer-witness-transport.md), §§2–3. The generic-point separation and strengthened self-similar witnesses are the ordinary arguments given here. No claim of historical novelty is made.

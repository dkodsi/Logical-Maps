# Plenitude turns material observers into two-output pointwise observers

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the normalization theorems: `misc`, this note, §§2–6, unpaginated. The pre-existing Plenitude principle is attributed separately in §§1 and 7.

The single instance of Plenitude with both input and output type t supplies an admitted conditional selector into any chosen true/false pair. If that pair has the correct operation tables as object identities, composition with the selector turns every material observer into a two-output pointwise observer with the same entire truth profile. This gives a standard admission hypothesis for the infinite material/pointwise comparison, without finiteness, identity bivalence, ND, NI or C.

## 1. The exact Plenitude instance

Use the existing [Plenitude](../../source/topics/classicism/principles/plenitude-r.yaml) formulation at σ=τ=t:

$$
\begin{aligned}
\mathrm{Plen}_{t,t}:\quad
\forall U^{ttt}\bigl[&\forall p\,\exists y\,
(U(p,y)\land\forall z(U(p,z)\to z=y))\\
&\to\exists f^{tt}\,\forall p\,U(p,fp)\bigr].
\end{aligned}
\tag{1}
$$

This is a single closed formula in the fixed relational language. Its premise is current total single-valuedness of an admitted relation; its conclusion is an admitted operation representing that relation. Neither Functionality nor a whole-operation identity is built into it. No individual-valued output or quantification over types is introduced.

The principle is sourced to Bacon and Dorr, *Classicism*, draft of 16 May 2023, §2.3, pp. 31–33. Here its displayed formula is an explicit additional premise over H. The fixed C background of the database is not silently imported with the record.

## 2. One selector for a chosen truth pair

Let b₁ be true and b₀ false. They are distinct by equality substitution. The admitted relation

$$
U(p,y):=(p\land y=b_1)\lor(\neg p\land y=b_0)
\tag{2}
$$

is total and single-valued by ordinary H truth reasoning: in the true case its unique output is b₁, and in the false case its unique output is b₀. Apply (1). It gives an admitted χ:tt satisfying

$$
\forall p\left[(p\to\chi p=b_1)
\land(\neg p\to\chi p=b_0)\right].
\tag{3}
$$

Consequently χ has at most two outputs, χp↔p for every p, χb₁=b₁, and χb₀=b₀. It is pointwise idempotent. These are output equations; no whole idempotence identity is inferred without Functionality.

For any admitted E define the admitted composite

$$
E^\chi(p):=\chi(Ep).
\tag{4}
$$

This single χ works for every E at once. Every composite (4) retains E's entire current truth profile and takes values in {b₀,b₁}. In particular A, Z and any restriction depending only on that profile are retained. Arbitrary identity-based restrictions such as endpoint fixing, invertibility, or an identity involving E are not claimed to survive.

## 3. The truth-table subalgebra lemma

Fix a finite list Σ of admitted propositional operations, with specified H truth tables. Suppose the chosen pair {b₀,b₁} realizes each such table as object identities. For an n-ary operation f with Boolean truth table $\widehat f$ this means the finite list of equations

$$
f(b_{\epsilon_1},\ldots,b_{\epsilon_n})
=b_{\widehat f(\epsilon_1,\ldots,\epsilon_n)}
\qquad(\epsilon_i\in\{0,1\}).
\tag{5}
$$

The list and the zeros/ones in (5) are external finite notation. They do not introduce a type of truth values into H. No material truth-table agreement is substituted for these output identities.

**Normalization lemma.** Under H+Plen_{t,t} and (5), every materially Σ-preserving E has a two-output pointwise Σ-preserving replacement E^χ with exactly its truth profile.

Indeed, both E^χ(f(p₁,…,pₙ)) and f(E^χp₁,…,E^χpₙ) lie in {b₀,b₁}; for the second expression this follows from (5). Material preservation and (3) give them the same truth value. The pair has only one member of each truth value, so the two output objects are equal. This proves every listed pointwise law. The same χ handles the entire finite list.

If Σ includes preservation of a designated constant c, the pair must additionally satisfy c=b₀ or c=b₁ according to c's truth value. Then material fixedness Ec↔c upgrades to E^χc=c. Without that extra alignment the lemma retains only the endpoint truth condition, not fixing of the original endpoint object.

Whenever the structural consequences of material separation provide such a pair, the lemma gives

$$
S[O\land\mathrm{Mat}_\Sigma]
\quad\longleftrightarrow\quad
S[O\land\mathrm{Two}\land\mathrm{Pt}_\Sigma],
\tag{6}
$$

where O is none, A, Z or A∧Z. Forward, normalize each separating observer; reverse, a pointwise observer is material. The use of material separation to obtain the pair is essential in the applications below.

## 4. All nonempty primitive connective signatures

For each nonempty subset Σ of {M,V,N}, its material separation principle supplies a truth-faithful two-element Σ-subalgebra. The required algebraic consequences are the exact H output theorems of [Truth profiles and connective reducts](truth-profiles-and-connective-reducts.md), §§3–4. The following table specifies a suitable pair; b₀ is false and b₁ true.

| Signature | Pair and its actual operation tables |
| --- | --- |
| M | Choose true t; b₁=t and b₀=t∧¬t. Semilattice identities give b₀≤b₁ and the two-element meet table. |
| V | Choose false b; b₀=b and b₁=b∨¬b. The join-semilattice identities give the two-element join table. |
| N | Choose true t; b₁=t and b₀=¬t. The double-negation identity makes N exchange the pair. |
| M,V | Choose the M pair. The original operations form a distributive lattice, so its comparable pair has both tables. |
| M,N | Use b₀=Bottom and b₁=¬Bottom, the bottom and derived top of the Boolean algebra with derived join. |
| V,N | Use b₀=¬Top and b₁=Top, the derived bottom and top of the Boolean algebra with derived meet. |
| M,V,N | Use the fixed Bottom and Top of the original Boolean algebra. |

Thus (6) holds over H+Plen_{t,t} for all seven signatures and every A/Z orientation. In the first two rows only the named semilattice identities are used; primitive negation appears in the construction merely to provide an input of opposite truth. In the M,N and V,N rows the missing primitive connective is not identified with its derived Boolean operation.

In particular Plenitude closes the unrestricted infinite material/pointwise M and V comparisons under this explicit additional premise. It also closes the material/pointwise negation gap, whose failure without Plenitude is witnessed by [the relational-clone model](relational-clone-model.md). It does not imply that any of these converses hold over bare H.

## 5. Affine operations and verified quantifier extensions

### Each separate affine operation

Fix an operation + whose H truth table is XOR or biconditional, with its chosen syntactic expansion held fixed. Material + separation supplies the elementary abelian 2-group equations, as proved in [Term closure and affine branches](term-closure-and-affine-branches.md), §4. Let 0 be the group identity. For XOR, 0 is false; choose any true c. For biconditional, 0 is true; choose any false c. In either case {0,c} is a subgroup, since c+c=0, and its addition table has exactly the correct truth values.

Apply §3 to this pair. Over H+Plen_{t,t}, material affine separation is equivalent to two-output pointwise affine separation, for each separate affine operation and every A/Z orientation. This holds without Fin_t(All) or finite observer images. It complements the explicit finite constructions in [Finite affine normalization](finite-affine-normalization.md).

This is a collapse of preservation tiers, not an assertion that group equations alone supply separating admitted material characters in the infinite case. The latter admission problem remains distinct. No joint XOR/biconditional or extra-connective preservation is inferred from a theorem about one operation.

### Matching universal and existential bounds

The same selector handles a quantifier when its action on admitted families valued in {b₀,b₁} has the required two-element table. A sufficient verified condition is that b₀≤b₁ in a semilattice order and the quantifier supplies its admitted bounds.

For a universal GLB, if every family value is b₁, its GLB is b₁; otherwise there is a b₀ value, which is itself the GLB. The proof uses the GLB defining property, antisymmetry and nonemptiness of the argument type. H supplies nonemptiness at every admitted type. Dually an existential LUB is b₁ if some family value is b₁, and b₀ otherwise. These are identities of the resulting proposition objects, with no equality of family objects assumed.

Consequently, if E has the material quantifier law, E^χ of the quantified proposition and the quantifier of E^χ's family values select the same member of the pair. This proves pointwise commutation.

The intrinsic material representation theorems therefore give the following exact instances over H+Plen_{t,t}:

- A+M+QΔ: the same bounded meet-semilattice/admitted-GLB structure characterizes material and two-output pointwise separation.
- Z+V+PΔ: the dual bounded join-semilattice/admitted-LUB structure characterizes both tiers.
- M+V+QΔ+PΓ, with any A/Z orientation: material and two-output pointwise separation coincide. Material separation supplies a common distributive-lattice order and the listed admitted bounds; its false/true chain has both binary and quantifier tables.

For the joint case the bounds can be checked directly. Let R be the whole material qualification and put p≤_R q iff every R-observer accepting p accepts q. Separation and M/V identify this admitted observer order with the original lattice order. The material Q law gives u≤_R∀xGx iff ∀x(u≤_R Gx); the material P law gives (∃xGx)≤_R u iff ∀x(Gx≤_R u). These are ordinary H truth manipulations of the observer and object quantifiers, not Barcan inferences. They establish exactly the GLB/LUB premises used above.

The two finite lists Δ and Γ are external type lists. They may be empty and need not contain t. The assertions use the same observer for the entire stated package. For the joint package the conclusion is a tier equivalence; distributive-lattice equations and bounds alone are not here claimed to produce admitted material lattice characters. No general quantifier-only or pure N-plus-quantifier converse is asserted.

## 6. Whole operations, higher types, and the remaining boundary

The normalized preservation laws are pointwise output identities. At propositional separation scope, their whole-operation versions require the appropriate local Functionality instances: Fun_(t,t) and Fun_(t,tt) for a binary operation, Fun_(t,t) for negation, and Fun_(σt,t) for each listed quantifier. The selector's mere existence does not supply these.

At full relational separation scope, the [typed factorization theorem](typed-separation-and-classicism.md), §2, supplies Functionality. Hence the full typed material, two-output pointwise and two-output whole-operation versions of each displayed package are equivalent under Plen_{t,t}. The proof normalizes each observer's truth profile on all proposition inputs, so it preserves its ability to separate relation values at every argument tuple. No infinitary qualification or type quantifier is inserted into H.

Plen_{t,t} is an admission principle, not C or Extensionality in disguise. For example, the full-function four-proposition H corruption models used in [Primitive-package classification](primitive-package-classification.md), §3, satisfy this Plenitude instance: every current single-valued relation on the proposition domain has its actual function in the full function domain. They can retain distinct true proposition objects and violate a chosen primitive C identity. No coextension-to-identity rule follows merely from admitting a selector.

This result does not settle the infinite material/pointwise M or V comparison over bare H. It identifies a standard pre-existing premise under which the missing admission step is available. The finite-image normalizations obtain comparable replacements by explicit terms and internal finite induction; this note uses Plenitude to admit one global truth selector instead.

## 7. Sources

Plenitude and its relational output restriction are Bacon and Dorr, *Classicism*, draft of 16 May 2023, §2.3, pp. 31–33, as recorded in the linked principle. The background type system and H/C distinction are those of [Background, Framework](../../source/topics/classicism/background.md).

The selector normalization, its applications to the seven connective signatures and separate affine operations, and the scoped quantifier and full-typed consequences are new arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§2–6, unpaginated. Their algebraic inputs and tier-lifting lemmas are explicitly linked above. Independent agent review is not a named human check or a Lean certificate. No database verdict, generated file or publication artifact is changed by this note.

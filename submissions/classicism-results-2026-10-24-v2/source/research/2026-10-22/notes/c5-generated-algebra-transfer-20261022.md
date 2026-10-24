# C5 transfer of finite-sorted impredicatively generated algebras

22 October 2026. Original research formulation by an OpenAI Codex audit agent. Ordinary mathematics, not human checked or Lean formalized; no literature-novelty claim. Direct source: this note. It abstracts the proved raw-restriction/image argument in `audit-infinity-transfer-20261022.md` without assuming a free algebra or external standardness.

## 1. Precisely bounded theorem

Work in C5 over the fixed original relational type system. There are finitely many ambient carrier types μ₁,…,μ_m and target carrier types ν₁,…,ν_m, all relational. This restriction ensures every operation and map written below has an admitted original type. It does not prohibit an interpreted arithmetic carrier built over original individuals: (et)t is relational.

The ambient algebra has finitely many given generators c_a and finitely many finitary given constructor terms f_b, with specified input and output carrier types. Let G_i(x) be the ordinary simultaneous impredicatively generated predicates: membership in every tuple of predicates containing the generators and closed under the constructors.

For each target carrier let H_i:ν_i t be a nonempty rigid predicate. Target generators d_a lie in the corresponding H_i. Target constructor terms γ_b carry tuples of H-members to H-members. Target predicates admitted for induction are exactly

    CorePred_i(V) := Rigid(V) ∧ V≤H_i.

Let K_i(y) assert H_i(y) and membership in every tuple of these supported rigid predicates that contains the d_a and is closed under the γ_b. These are the internally generated predicates for the target supported structure.

Suppose given available maps q_i:μ_iν_i satisfying:

1. q_i(c_a)=d_a for each generator of sort i.
2. For each constructor f_b:μ_(i₁)…μ_(i_k)μ_j, whenever H_(i_r)(q_(i_r)(x_r)) holds for every input, then

       q_j(f_b[x̄]) = γ_b[q_(i₁)(x₁),…,q_(i_k)(x_k)].

Then q maps the ambient generated carriers **onto** the target generated carriers:

    G_i(x) → K_i(q_i(x)),
    K_i(y) → ∃x [G_i(x) ∧ q_i(x)=y].

No Actuality, Bivalent Evaluation, Rigid Comprehension, Atomicity, Choice, external fullness, or external-standardness hypothesis is needed. The theorem is conditional on the displayed admitted maps and commuting identities; it does not assert such maps exist for arbitrary algebras.

## 2. Why every G_i is rigid under C5

The ambient impredicative definition gives theorems of C stating that each generator is generated and that generated inputs have generated constructor outputs. These statements hold with the generator and constructor parameters free.

Put W_i(x):=□G_i(x). Necessitation of the generator theorem puts every generator in W. Necessitation of each constructor-closure theorem, followed by modal universal instantiation and K, makes W constructor-closed. The simultaneous induction defining G therefore gives G_i(x)→□G_i(x).

Necessitating the universally closed theorem gives persistence with the required outer box. Under C5, persistence is equivalent to rigidity. Thus each G_i is rigid and its membership propositions are top or bottom. This generalizes the already recorded argument that natural cardinalities are necessarily natural cardinalities; the impredicative definition itself, rather than an external finite construction sequence, supplies the induction.

## 3. Forward transfer

First simultaneously induct to show H_i(q_i(x)) for G_i(x). The generator equations handle the bases. The guarded commutation equations and target constructor closure handle each constructor step.

Let V_i be any tuple of supported rigid target predicates closed under the target constructors and containing the target generators. Pull it back to the available ambient predicates

    U_i(x):=H_i(q_i(x)) ∧ V_i(q_i(x)).

The same equations make U generator-containing and constructor-closed. Ambient simultaneous induction therefore gives U_i(x) for G_i(x). Since V was arbitrary, K_i(q_i(x)). The pullbacks U need not be rigid; the original impredicative definition quantifies over every available ambient predicate, so that causes no problem.

## 4. Reverse transfer by a rigid image

Define

    I_i(y):=H_i(y) ∧ ∃x^μ_i [G_i(x) ∧ q_i(x)=y].

Each I_i is a supported rigid predicate. H_i and G_i have settled membership; equality has settled truth under C5; BF makes the existential settled. Consequently every application value of I_i is top or bottom, so I_i is rigid. Its explicit H_i conjunct gives I_i≤H_i.

The I_i contain the target generators by the generator equations. For a target constructor applied to I-members y₁,…,y_k, take their finitely many ambient preimages x₁,…,x_k. Ambient closure makes f_b[x̄] generated, and guarded commutation makes it a preimage of γ_b[ȳ]. Thus I is closed under every target constructor. Only finitely many displayed existential witnesses are combined in a constructor step; no choice principle is being used.

Target simultaneous induction gives K_i(y)→I_i(y), proving surjectivity. The crucial point is that the image is an *available rigid predicate*, established syntactically from C5. No invocation of an external image subset or full power set is involved.

## 5. When the transfer is an isomorphism

Suppose in addition there are admitted maps ℓ_i:ν_iμ_i with

    ℓ_i(d_a)=c_a,

and, for target-domain input tuples,

    ℓ_j(γ_b[ȳ]) = f_b[ℓ_(i₁)(y₁),…,ℓ_(i_k)(y_k)].

Simultaneous ambient induction applied to

    H_i(q_i(x)) ∧ ℓ_i(q_i(x))=x

gives ℓ_i q_i=id on G_i. Hence q_i is injective there. If K_i(y), surjectivity gives y=q_i(x) for some generated x, so ℓ_i(y)=x is generated and q_iℓ_i(y)=y. Thus q and ℓ are mutually inverse on the generated carriers.

The proof does not require the algebras to be free. The ambient and target generated structures may satisfy constructor equations, possess overflow values, or have nonstandard internal members. The commuting maps account for those possibilities. Calling this a free-algebra theorem would add a claim not proved here.

## 6. Application and limits

For natural cardinalities, μ=ν=(σt)t, H=B, q is restriction to rigid σ-properties, and ℓ tests for a rigid coextension of the argument property. The generators and constructors are zero and successor. `audit-infinity-transfer-20261022.md` supplies every commutation identity, so the theorem applies at each original counting type σ.

For a proper rigid subdomain D, restriction still supplies q and the onto theorem. The proposed coextension lift generally fails to commute with unrestricted ambient successor because a new element may lie outside D. Accordingly the generic isomorphism theorem does not apply; indeed injectivity can fail. This is a concrete reason the inverse-map hypotheses cannot be omitted.

For lists, trees, syntax, or other finite-sorted inductive structures, the theorem supplies a research template only after the relevant carrier predicates, constructor terms, and commuting maps are explicitly given and checked. It does not by itself construct those representations or prove their external standardness.

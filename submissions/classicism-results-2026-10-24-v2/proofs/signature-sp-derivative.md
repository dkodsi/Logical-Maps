# Signature SP and the Henkin witness derivative

Original mathematical argument, direct source misc; unpaginated.

## 1. Fixed target and result

Throughout,

```math
\Sigma=\{c:e\to t\},\qquad M=\mathrm{Max}(C(\Sigma)),
```

with no individual constant in the original signature. The language and types are the original **finitary relational** ones. Write

```math
H P:=\exists q\bigl(q\land\Box(\Diamond q\to P)\bigr),
\qquad D P:=\neg H\neg P
```

The target theory is

```math
\mathrm{SP}_\Sigma=C(\Sigma)+
\{DP:\ P\text{ closed in }\mathcal L(\Sigma),\
                    \mathrm{Con}(M+P)\}
```

Every SP side condition below uses this same **signature-relative** M. Neither pure Maximalism nor C-consistency is substituted for it.

The new checkpoint is:

1. In the existing profile construction, making the proposition-profile map injective forces the profile map to be injective at **every** type. The higher-type extension coordinates cannot independently retain extra witnesses.
2. This repair route therefore asks for a Henkin truth ultrafilter on the fixed countable algebra of one-marker signature-term profiles. A canonical decreasing sequence of closed sets characterizes its existence exactly, and stabilizes at a countable ordinal. A nonempty stable set yields an SP_Σ model.
3. A true arithmetic sentence constructed using the proof predicate of the correct signature-relative theory supplies an explicit nonempty clopen set removed at the first stage. All valuations surviving through stage ω must agree with standard first-order arithmetic.

Nonemptiness of the stable set remains unproved. Its emptiness would rule out this profile-injective route, **not** prove SP_Σ inconsistent.

## 2. Existing inputs and their scope

The [signature comparison](../source/research/2026-10-22/notes/audit-signature-to-pure-sp-20261022.md), §§1–4, already proves

```math
\mathrm{SP}_\Sigma\vdash\mathrm{SP}_{\mathrm{pure}}
\quad\Longleftrightarrow\quad
\mathrm{SP}_\Sigma\text{ is inconsistent}
```

Its pure atom splitter is a completed obstruction to conservativity, not a consistency proof for the present target. The [SignatureSplit delivery](../source/research/2026-10-22/lean-formalization/sp-core-verification-status.md) certifies the splitting and its two C-consistency models; it does not certify the separate pure-profile construction.

We use these previously established ordinary mathematical inputs:

- The [profile construction](../source/research/2026-10-22/notes/profile-root-construction-20261022.md), §§1–3, and its [audit](../source/research/2026-10-22/notes/audit-profile-20261022.md), §§2–4: singleton root, complete component family, arbitrary actual extensions paired with term profiles. The construction relativizes to the fixed relational-only signature by using Σ-terms and C(Σ)-complete components.
- [Signature comparison](../source/research/2026-10-22/notes/audit-signature-to-pure-sp-20261022.md), §§9–10: signature-relative unary Possibility+, harmless addition of one fresh individual name to a signature having none, and SP_Σ's actual singleton-individual conclusion.
- [Universal-core analysis](../source/research/2026-10-22/notes/reflection-universal-core-20261022.md), §§2–7: the identity-density formulation of D, universal identity reflection, and the algebraic/actual-truth distinction. These proofs relativize to a fixed signature; their SP side conditions remain relative to that signature's Max theory.
- The fixed-algebra truth-ultrafilter problem already appears in [Henkin-minimal analysis](../source/research/2026-10-22/notes/sp-henkin-minimal-20261022.md), §4. This report adds the all-sort rigidity of the profile repair, the canonical closed-set criterion, and its signature-specific arithmetic analysis. Merely restating that earlier ultrafilter problem is not counted as a new result.
- Necessary numberhood is a theorem of C itself: [arithmetic write-up](../source/topics/classicism/writeups/c5-implies-necessity-of-arithmetic.md), Lemma 1. The later C5 lemmas in that write-up are not used. Standardness of the profile root's numerical field follows from its arbitrary actual extension coordinate, as in [profile construction](../source/research/2026-10-22/notes/profile-root-construction-20261022.md), §5, and [Max degree](../source/research/2026-10-22/notes/max-degree.md), §§10.1–10.2. The latter explains the Sum and Prod graph argument with their actual definitions.

The published background is Bacon–Dorr, *Classicism*, the map's 16 May 2023 draft, §2.6 p.42 and Appendix E pp.80–83. The restricted profile model and this report's deductions are not attributed to that paper.

## 3. The common signature-term algebra

Introduce one **auxiliary** individual marker a:e. It is used to describe a candidate root, not added to the signature of the requested SP schema. For each type σ let

```math
B_\sigma=
 \{\text{closed terms of type }\sigma\text{ in }\mathcal L(\Sigma\cup\{a\})\}
 /{=_{C(\Sigma,a)}}
```

Include every term operation in this many-sorted algebra, including application, identity-valued operations and quantifier-valued operations. Omit external actual truth. In particular B_t is a countable Boolean algebra. There is only one individual term, a, since no admitted operation returns an individual.

The same B embeds into the full term reduct of every M-model after choosing any actual individual as a. To verify injectivity, suppose C(Σ) does not prove ∀x S(x)=T(x). The open formula S(x)≠T(x) is C(Σ)-consistent. Signature-relative unary Possibility+ gives

```math
M\vdash\forall x\,\Diamond(S(x)\ne T(x))
```

NI makes equality at an actual x inconsistent with this possibility. Thus M proves the uniform disequality. Conversely a C-provable identity holds in every model. Consequently equality between one-marker term denotations is exactly their C(Σ,a)-provable equality.

This argument also verifies that every M-model, expanded by any actual a, satisfies Max(C(Σ,a)). Restriction gives the converse for its original-language axioms. It is the specific no-prior-individual-name extension lemma; no general Max conservativity claim is used.

## 4. Proposition-profile injectivity forces all-sort injectivity

Consider a **genuine** C(Σ)-root model A equipped with the profile projection

```math
\pi_\sigma:A_\sigma\twoheadrightarrow B_\sigma
```

preserving every logical term operation. This is the projection of the profile construction. Surjectivity is also forced for a term-closed repair containing c and a with all their original profiles.

**Lemma.** If π_t is injective, every π_σ is injective.

Suppose π_σ(x)=π_σ(y). Preservation of the identity-valued operation gives

```math
\pi_t(\mathrm{eq}_\sigma(x,y))
 =\mathrm{eq}_\sigma(\pi_\sigma x,\pi_\sigma y)
 =\top_B=\pi_t(\top_A)
```

Injectivity at t gives eq_σ(x,y)=top_A. In the genuine source model this proposition is true, so literal identity gives x=y. This proves the lemma at every admitted type, including e.

Hence π is an isomorphism of the entire logical term algebra. A proposed repair cannot remove the duplicate proposition truth bits while retaining arbitrary independent higher-type extensions with the same profiles. Every current extension is then determined by a single truth assignment on B_t.

The qualification “genuine” matters: arbitrary abstract algebras must not be assumed to have the identity-separation implication eq(x,y)=top ⇒ x=y without proof. Preservation of quantifier-valued operations also does **not** itself imply their external Henkin truth clauses.

## 5. The compact space and its witness requirements

Let E₁ abbreviate ∀x^e y^e(x=y). For b∈B_t, write

```math
\widehat b=\{U\in\mathrm{Stone}(B_t):b\in U\}
```

Define K to consist of the Boolean ultrafilters U such that E₁∈U and, for every type σ and b,d∈B_σ,

```math
\mathrm{eq}_\sigma(b,d)\in U
\quad\Longleftrightarrow\quad b=d\text{ in }B_\sigma
\tag{I}
```

K is a closed subspace of a compact metrizable Stone space, hence compact and metrizable. It is nonempty: restrict actual truth from the singleton signature-profile Max model to its faithful term subalgebra. This restriction is only a truth assignment on B; it is not yet a term-domain Henkin model.

Equivalently, K is the Stone space of complete consistent extensions of

```math
T_\Sigma:=\mathrm{Max}(C(\Sigma,a))+E_1
```

Indeed (I) imposes exactly the maximalist ground equality/disequality diagram in the marked language. C-theorems are top in B, and the ordinary deduction theorem transfers any finite consequence of those ground literals and E₁ to every such ultrafilter. Conversely any complete extension gives the corresponding Boolean truth ultrafilter. Section 3 justifies this use of the marker; the SP reference theory remains M.

For every F∈B_{σt}, define the relatively open set

```math
W_F=\widehat{\neg\exists_\sigma F}\ \cup
            \bigcup_{b\in B_\sigma}\widehat{F(b)}
       \quad\subseteq K
\tag{W}
```

There are countably many requirements. Instantiation already gives F(b)→∃_σF. Membership in W_F adds the converse **witness condition** whenever the existential proposition is true. All formula instances with term parameters are covered, by lambda abstraction.

**Proposition.** Put $`\mathcal H=\bigcap_F W_F\subseteq K`$. A U∈K gives a genuine C truth interpretation with exactly the domains B_σ if and only if U∈𝓗.

Necessity is the existential semantic clause. For sufficiency, Boolean truth is supplied by the ultrafilter, identity by (I), and existential quantification by (W); universal quantification follows by negation. Induction on terms/formulas supplies the truth lemma. All C theorem identities already hold in B. Alternatively retain the original complete component family and give each profile its unique root extension determined by U. Distinct profiles are separated by those components; application and abstraction use substitution, and (W) verifies root quantifiers. This gives the corresponding profile-only action model.

Every individual-sort requirement holds throughout K: E₁ and C's actual equivalence

```math
E_1\to\bigl(\exists x^e F(x)\leftrightarrow F(a)\bigr)
```

already supply its witness. This conditional equivalence is not promoted to an entity identity.

**Why a point of 𝓗 yields SP_Σ.** Such a model N satisfies M and every actual proposition is Q(c,a) for a one-individual Σ-term Q. Fix a closed P with Con(M+P) and a true q=Q(c,a). Since Q(c,x) is C(Σ)-consistent, unary Possibility+ makes M prove ∀x◇Q(c,x). In an M+P model, P∧◇Q(c,x) therefore holds of an individual, and is C(Σ)-consistent. Unary Possibility+ in N gives

```math
\Diamond\bigl(P\land\Diamond Q(c,a)\bigr)
```

This holds for every true q, so the exact dual definition

```math
DP\leftrightarrow\forall q\bigl(q\to\Diamond(P\land\Diamond q)\bigr)
```

gives DP. Every instance uses Con(M+P), as required. Thus 𝓗≠∅ is sufficient for consistency of the requested theory. No necessity for arbitrary SP models is asserted.

## 6. An exact closed-set procedure for this construction

Write Z_F=K\W_F. Define

```math
\begin{aligned}
K_0&=K,\\
K_{\alpha+1}
 &=K_\alpha\setminus
       \bigcup_F\mathrm{Int}_{K_\alpha}(Z_F\cap K_\alpha),\\
K_\lambda&=\bigcap_{\alpha<\lambda}K_\alpha
                 &&(\lambda\text{ a limit ordinal})
\end{aligned}
\tag{D}
```

Equivalently, the successor is the intersection, over F, of the closures in K_α of W_F∩K_α. All stages are closed and compact. Every point of 𝓗 survives every stage: it is in none of the bad sets. Their closure in K survives as well.

The sequence stabilizes at a countable ordinal γ. To check this without an effectiveness assumption, every strict successor deletion has a basic open set meeting K_α and missing K_{α+1}. Once removed, that basic set misses every later stage and cannot witness another strict deletion. A countable base prevents uncountably many strict successors. If no countable stage stabilized, every countable stage would be a strict successor change, a contradiction. Limit stages are intersections and introduce no exception to this argument.

At stability, every W_F∩K_γ is relatively dense open. If K_γ is nonempty, the Baire theorem for compact Hausdorff spaces gives a dense set of points lying in all these countably many opens. They are exactly 𝓗. Since 𝓗 was never removed,

```math
\boxed{\quad K_\gamma=\overline{\mathcal H}^{\,K},\qquad
 K_\gamma\ne\varnothing\iff\mathcal H\ne\varnothing.\quad}
\tag{K}
```

This is an exact criterion for the profile-injective repair route. It does not claim density of every W_F in the original K, nor give a computable bound for γ. The next section proves that some requirements are not dense in K.

## 7. The unary constant supplies no nonstandard numerical term witnesses

Let ν_e=(et)t, let N_e be the established finite-cardinality predicate, and let $`\bar n`$ be the standard numeral terms.

The ordinary singleton Σ-profile root has externally standard N_e. The property whose actual extension is exactly the standard numeral values is admitted by the arbitrary root extension coordinate; induction excludes other numbers. Distinctness follows from complete finite extensional components. For Sum and Prod, admit the root relations having exactly the standard addition/multiplication recursion graphs as their actual extensions, with a fixed harmless component profile. They exclude incorrect standard triples. The named c changes the component profiles, not the availability of these actual extensions.

**Canonicity lemma.** For every U∈K and T∈B_{ν_e},

```math
N_e(T)\in U\quad\Longrightarrow\quad
T=\bar n\text{ in }B\text{ for some external }n\in\mathbb N
\tag{N}
```

C proves N_e(T)→□N_e(T), where □N_e(T) is the identity N_e(T)=top. If N_e(T)∈U, that identity belongs to U. Correct identity truth (I) therefore forces [N_e(T)]=top in B, so C(Σ,a) proves N_e(T). Evaluate T in the standard singleton Σ-profile root: it equals some numeral $`\bar n`$. The common term diagram from §3 turns that equality into a C(Σ,a)-provable equality. This proves (N). Conversely each numeral's numberhood is a C-theorem.

Thus adding the generic unary constant does not provide nonstandard numerical **term** witnesses. Arbitrary SP models may still contain unnamed numerical elements; they are not ruled out by (N).

### A nonempty bad clopen set removed at the first stage

Use the proof predicate of **T_Σ**, not that of pure Max and not merely that of M. T_Σ has a standard-arithmetic model by the singleton profile construction and §3, so its arithmetical consequences are true in the standard natural numbers. Its theoremhood has a Σ⁰₂ definition: a finite proof certificate has finitely many non-C-provability conditions for its Max inequalities, each Π⁰₁, alongside recursively checkable proof data. E₁ is one additional axiom.

The arithmetic diagonal lemma, composed with the effective Frege-arithmetic translation A↦A#, supplies a Π⁰₂ sentence G_T with

```math
\mathrm{PA}\vdash
G_T\leftrightarrow\neg\mathrm{Pr}_{T_\Sigma}
                             (\ulcorner G_T^\#\urcorner)
```

If T_Σ proved G_T#, arithmetic soundness would make G_T true, while its standard fixed-point equivalence would deny that very proof. Hence it does not prove G_T#. The same equivalence makes G_T standardly true; arithmetic soundness also rules out a proof of its negation. Thus both signs are T_Σ-consistent. This specifies G_T effectively by the fixed-point construction; no explicit numerical Gödel code was computed.

Write G_T in Π⁰₂ normal form $`\forall n\exists m\,R(n,m)`$, with the usual recursive arithmetic matrix and its original-language relational translation. Let

```math
F(n):=N_e(n)\land
           \forall m\bigl(N_e(m)\to\neg R^\#(n,m)\bigr)
```

Then ∃nF(n) is ¬G_T#. For each standard k choose a standard l with R(k,l). Its finite arithmetic verification is supplied by PA in the fixed Frege interpretation. Consequently T_Σ refutes F(\bar k). By (N), no U∈K makes F(b) true for any b∈B_{ν_e}: nonnumeral terms fail the first conjunct, and numeral terms fail the second.

Therefore the witness open for F is exactly

```math
W_F=\widehat{G_T^\#}\cap K,
\qquad
Z_F=\widehat{\neg G_T^\#}\cap K
```

The second set is nonempty because T_Σ+¬G_T# is consistent. It is clopen and is wholly removed at K₁. This explicitly disproves the naive claim that all witness requirements are dense in the initial compact truth space.

Forgetting the auxiliary a in models of either sign verifies Con(M+G_T#) and Con(M+¬G_T#). Hence the requested SP_Σ supplies both D G_T# and D¬G_T#. A standard actual numerical domain does not contradict either modal assertion.

## 8. Successor stages impose a numerical omega rule

Let θ(n) be any fixed original-language formula with old term parameters; its internal terms may contain other quantifiers. Suppose every U∈K_α contains θ(\bar k) for every standard k. Define

```math
F(n):=N_e(n)\land\neg\theta(n),\qquad
A:=\forall n\bigl(N_e(n)\to\theta(n)\bigr)
```

By (N), no F(b) belongs to any U∈K_α. On K_α the witness open W_F is therefore precisely the clopen truth set of A. Its complementary truth set is relatively open inside the bad set and is removed at the next stage. Thus

```math
\bigl[\forall k\in\mathbb N\ \forall U\in K_\alpha,
                     \theta(\bar k)\in U\bigr]
\quad\Longrightarrow\quad
\forall U\in K_{\alpha+1},\ A\in U
\tag{Omega}
```

This is a metatheoretic rule about the closed-set procedure, not a new infinitary object-language axiom.

Ground arithmetic on numeral terms is correct throughout K₀: Max entails the weak Infinity antecedent used by the fixed PA interpretation, and C+that antecedent proves the ground numeral facts. Induct on finite arithmetic quantifier depth, using negation-normal form. A true existential sentence has a standard witness and follows already from the induction hypothesis for that instance. For a true universal sentence, all standard instances are true at the preceding stage, and (Omega) supplies its universal closure at the next. Apply the same argument to the standardly true negation of any false sentence. Every arithmetical sentence has finite depth, so

```math
U\in K_\omega\quad\Longrightarrow\quad
\bigl(A^\#\in U\ \Longleftrightarrow\ \mathbb N\models A\bigr)
\quad\text{for every first-order arithmetic sentence }A
\tag{A}
```

This remains a conditional statement if K_ω is empty. In particular any genuine truth ultrafilter on B, encoded by its truth bits on syntactically enumerated terms, computes full standard arithmetic truth; it cannot be arithmetical in that syntax presentation.

This is a restriction on the fixed-profile route, not an arithmetic-soundness theorem for arbitrary SP models. Nor does it prohibit standard arithmetic at an SP point. The previously studied root-region obstruction needs the additional admitted nonzero proposition r with r=◇r and r≤G_T#. Only **then** does r witness H G_T#, contradicting SP_Σ's D¬G_T#. Standardness by itself supplies no such r.

## 9. Two smaller search restrictions

These clarify failed approaches rather than count as solutions.

**Individual-only outer identity constraints.** If U=∀x₁^e…x_n^e θ(x̄) is a finite Boolean combination of typed identities with only individual outer variables and Con(M+U), then M+E₁ proves U. Diagonalize the tuple to x. Section 3 uniformly decides every resulting identity in M; consistency forces the diagonal matrix to be true. E₁ makes every tuple diagonal. Thus these constraints coexist in the already available singleton profile model. This is the fixed-signature specialization of the stronger earlier individual-negative disjunction argument in [Henkin-minimal analysis](../source/research/2026-10-22/notes/sp-henkin-minimal-20261022.md), §5, not a newly discovered general disjunction theorem.

**Invertible substitutions do not create extra finite-cell splitting.** If c↦T(c) has a C-provable definable one-sided inverse, its action on the finite set of interpretations of c in any fixed finite full hierarchy is a bijection. Definability makes it equivariant under the pointed automorphism group, so it permutes that group's interpretation orbits. It cannot split them or change the previously proved finite-cell counts. The known 2n atoms below the n-individual Fregean cell are therefore not contradicted by such a substitution. Arbitrary added independent constants are not definable inverses of this kind.

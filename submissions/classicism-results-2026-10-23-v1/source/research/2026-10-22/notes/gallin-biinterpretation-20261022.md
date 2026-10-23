# Two-sided reconstruction of the relational Gallin presentation

22 October 2026. Original mathematical audit/reconstruction by the Gallin-audit agent, following the parent's proposed comparison. No human check, Lean verification, main-database edit, or literature-novelty claim. This note concerns the explicit countable many-sorted presentations in `positive-effective.md` §3 and `rigidity-actualization.md` §§13–14. It does not concern arbitrary bare category/action codes.

## 1. Exact claim and exact languages

Let H_0 be the auxiliary extensional general/Henkin theory with base sorts e,s,o, with o={0,1}, a distinguished w_0:s, all arrow types α→β with β neither e nor s, application, extensionality, and definable comprehension for every first-order formula with arbitrary finite parameters. No Choice is assumed. Let B=C+□Plenitude, equivalently C5+Atomicity, in the original fixed relational type language.

The forward translation from an H_0 model M produces a B-model I(M) with

    T(e)=e, T(t)=s→o, T(στ)=T(σ)→T(τ),
    D_σ^(I(M))=D_(T(σ))^M.

Original truth is evaluation at w_0. Original equality is auxiliary identity represented by a constant world proposition. The verified forward soundness proof uses comprehension and genuine extensionality, not external fullness.

The converse construction J from a B-model uses original individuals as e, propositional atoms as s, {bottom,top} as o, and hereditary rigid relations supported on those base fields as the higher auxiliary domains. Its original-type transport j_σ,k_σ is stated and audited in `rigidity-actualization.md` §14 and the companion audit.

**Model-reconstruction theorem.** In addition to I(J(N)) being isomorphic to every original B-model N by j,k, the other composite J(I(M)) is isomorphic to every auxiliary H_0 model M by uniform, recursively specified definable maps described below. These are sortwise interpretations in countably many sorts with definable inverse isomorphisms. This note does not assert an unchecked syntactic definitional equivalence of two axiom lists.

## 2. Ambient code types and recovered fields

For an auxiliary type α define its original code type c(α) by

    c(e)=e, c(s)=t, c(o)=t,
    c(αβ)=c(α)c(β).

This is admitted in the original type grammar: auxiliary arrow outputs are relational, so their c-images are never e. Different auxiliary sorts may have the same original code type; their field predicates distinguish them.

In N=I(M), let K_e be all original individuals, K_s the propositional atoms, and K_o={bottom,top}. For relational α=α_1…α_n o define K_α to consist of original objects F:c(α) that are rigid and satisfy

    F ≤ λx_1…x_n . ⋀_i K_(α_i)(x_i).

These are exactly the domains used in J(N). The n=0 case gives K_o. Under B, rigidity is equivalent to every pointwise instance having value bottom or top, and the support inequality means F vanishes outside the indicated argument fields. Intrinsic comprehension, restricted application, and extensionality for K have already been checked in the cited core theorem.

Write C_α for the map from D_α^M to K_α, and D_α for its inverse. The symbols C_α,D_α here name metamathematical definable maps; they do not add forbidden original function types. At the bases e and s, a needed inverse can be used by its unique-value graph rather than by an operation returning a forbidden base type.

## 3. The bases

At e, C_e and D_e are identity substitution. No term of type e→e is required.

At o, C_o(b) is the constant world predicate v↦b. Thus C_o(0)=bottom and C_o(1)=top. These are distinct because M's world sort is nonempty and 0≠1. The inverse is D_o(p)=p(w_0), restricted to p∈K_o. These maps are admitted/definable by comprehension and plainly inverse.

At s, define

    C_s(w)=δ_w,   δ_w(v)=1 iff v=w.

Singleton comprehension supplies δ_w∈D_(so), which is the original proposition domain. Every δ_w is a nonzero Boolean atom. Conversely, any original atom p is nonzero as a world predicate. Extensionality therefore gives some w with p(w)=1. The available δ_w is nonzero and below p, so atomhood yields p=δ_w. Finally δ_u=δ_v implies u=v by evaluation at u. Hence C_s is a bijection from M's world sort to K_s, and its inverse is the unique-value relation

    D_s(p)=w iff p=δ_w.

This does not require an auxiliary operation returning s. The distinguished recovered actual world is δ_(w_0), since it is the unique atom true at w_0. Therefore the pointed-world designation is preserved.

## 4. Relational-type induction

Suppose C_(α_i),D_(α_i) are inverse bijections for all argument types of α=α_1…α_n o. For f∈D_α^M define the original object C_α(f):c(α) by the auxiliary formula

    C_α(f)[x_1,…,x_n](v)=1
      iff ∃a_1:α_1 … a_n:α_n
           [⋀_i C_(α_i)(a_i)=x_i ∧ f[a_1,…,a_n]=1].          (1)

The final v:s is the original proposition's evaluation-world argument. It does not occur on the right. Every C_(α_i) can be supplied by its already defined unique-value graph, so (1) is an ordinary auxiliary first-order formula with parameter f. H_0 comprehension supplies its characteristic function at T(c(α)); that is exactly an original entity of type c(α). No selector or Choice is used.

The result is pointwise constant across v, hence rigid in I(M). The witnesses ensure that it vanishes when any x_i lies outside K_(α_i). Thus C_α(f)∈K_α.

Conversely, for F∈K_α define D_α(F) by

    D_α(F)[a_1,…,a_n]
      = F[C_(α_1)(a_1),…,C_(α_n)(a_n)](w_0).              (2)

The right side is a Boolean value in M. Again H_0 comprehension supplies the corresponding relation in D_α^M, uniquely by extensionality. The use of w_0 causes no loss: the given F is rigid, so its pointwise values are independent of the world argument.

### First inverse equation

Substitute x_i=C_(α_i)(a_i) into (1). By inductive injectivity, its witnesses b_i must equal a_i. Therefore (2), applied to C_α(f), agrees with f at every argument tuple. Auxiliary extensionality yields

    D_α(C_α(f))=f.

### Second inverse equation

Let F∈K_α and consider arbitrary original-code arguments x_i and arbitrary world v. If any x_i lies outside K_(α_i), support makes F[x](v)=0, and (1) is also false. Otherwise use inductive surjectivity to write x_i=C_(α_i)(a_i). Equation (1) for C_α(D_α(F)) then reduces to F[x](w_0)=1. Rigidity makes this equivalent to F[x](v)=1. Hence the two objects agree at every tuple and every world. Iterated auxiliary extensionality gives

    C_α(D_α(F))=F.

This completes the induction, establishing the claimed bijections at every auxiliary relational type. The recursive definition is effective on finite type syntax.

## 5. Preservation of application and the whole structure

For an auxiliary arrow α→β, compare

    C_β(fa)    and    C_(αβ)(f)(C_α(a)).

Flatten β into its finite argument list ending in o. Evaluating both sides at an arbitrary tuple of code arguments and an arbitrary world reduces, by (1), to the same existential statement; injectivity of C_α identifies the first decoded argument with a. Outside the remaining support fields both sides vanish. Extensionality proves their equality. Thus C preserves application. Equality is preserved and reflected by injectivity.

The Boolean constants and distinguished world are preserved by §3. The structural bijections and application preservation imply preservation of all ordinary sorted first-order formulas by induction, including quantifiers because each C_α is surjective onto the corresponding recovered field. The logical operations or λ-constructors that are added as definitional expansions are preserved by their unique defining equations. Hence C is an isomorphism of the entire specified pointed many-sorted H_0 structures, not merely of their original-type reducts.

There is no gap concerning “extra” auxiliary types involving s or o: the induction ranges over **every** auxiliary type, not only types syntactically of the form T(σ). That was the missing direction beyond the existing original-type maps j_σ,k_σ.

All arguments are internal first-order reasoning with H_0 comprehension and extensionality, together with the already verified B rigidity characterization in its C reduct. Thus the isomorphism maps have uniform defining formulas. No external powersets, full-function assumption, or metatheoretic Choice occurs in the reconstruction theorem.

## 6. Effective scope and numbering precautions

The preceding maps provide effective semantic translations when the source code can decide the needed formulas. A complete auxiliary elementary diagram computes all the original logical operations and term interpretations by unique-value search, as in `positive-effective.md`. Conversely an adequate original code with parameterized term interpretation and actual truth computes the complete auxiliary diagram of J(N), since every field and auxiliary formula has an effective original translation. The inverse-on-models proofs show these constructions preserve the relevant model, up to the specified definable isomorphisms.

For a supplied numbered **original B-model**, exact degree preservation is obtained by numbering each auxiliary sort T(σ) with the given source D_σ labels via j_σ, and other sorts by tagged ambient-core labels. The original code is then recovered exactly from the auxiliary diagram. The details and required domain-membership convention are in `audit-gallin-20261022.md` §11.

For a supplied arbitrarily numbered **auxiliary H_0-model**, the naïve C reduct may forget numbering information on auxiliary sorts not in the image of T. Recovering an isomorphic auxiliary model does not by itself recover that arbitrary original numbering. In particular c(s)=c(o)=t and many other auxiliary code types can coincide. Thus the model-level theorem above should not silently be restated as equality of every pair of naïvely encoded diagram degrees.

The safe immediately justified claims are: both adequate representation tasks compute one another uniformly; the transformations preserve the supplied structures up to the displayed definable isomorphisms; and the original-to-auxiliary construction admits the explicit degree-preserving inherited numbering just described. Exact degree preservation in the reverse direction can also be arranged with additional deliberate numbering/coding, but is a separate presentation lemma. No conclusion about bare category/action or application-only codes is asserted.

## 7. Exact reverse degree preservation by deliberate disjoint type coding

The numbering issue in §6 can be repaired without adding any semantic objects or any new nonlogical symbols. Here is the explicit presentation lemma for the fixed pure H_0 signature.

Let D be a complete diagram of a numbered H_0 model M, including membership in each numbered sort. Enumerate the auxiliary types without repetition as α_0,α_1,…. For each i start from the original code type c(α_i) and apply the type operation ρ↦ρt repeatedly, at least once, to obtain a type τ_i whose syntax-tree size is strictly larger than that of τ_(i−1). Thus the τ_i are pairwise distinct, and membership in their range, with the associated index and number of lifts, is decidable: enumerate until the sizes exceed that of a queried type.

At any original type ρ, the haecceity map

    x↦λy^ρ(y=x)

is an allowed operation into ρt and is injective. Let L_i be its chosen finite iterate from c(α_i) into τ_i. Composing the definable C_(α_i) of §§3–4 with L_i gives a definable injection

    H_i:D_(α_i)^M → D_(T(τ_i))^M.

The source complete diagram decides whether a given target element b lies in its image, by the first-order formula ∃a(H_i(a)=b). No image-membership jump is needed because D is an elementary diagram.

Re-present the ordinary C reduct I(M) as follows. At a reserved type τ_i use the domain

    {2a : a is a source label in D_(α_i)^M}
      ∪ {2b+1 : b is a source label in D_(T(τ_i))^M
                    and b is not in the image of H_i}.

Interpret 2a by H_i(a), and 2b+1 by b. This is a genuine bijective numbering, because H_i is injective and the two clauses divide its image from its complement. At all unreserved original types retain the source labels from the corresponding T(σ) sort. Both domain membership and the coding bijections are D-computable. Their inverses are also D-computable: test image membership and, when positive, search the source α_i sort for its unique preimage. Transport application, original term interpretation and truth through these bijections. The resulting adequate original B-model code E satisfies E≤_T D.

Conversely E decides membership in every original source auxiliary sort: a is a source α_i label iff 2a belongs to its τ_i sort. Given a source auxiliary formula with parameters a_j:α_(i_j), regard 2a_j as parameters of the original types τ_(i_j). In the recovered rigid core, existentially decode each through the formula

    K_(α_(i_j))(x_j) ∧ L_(i_j)(x_j)=2a_j.

There is exactly one decoded core value, namely C_(α_(i_j))(a_j). Translate the auxiliary formula to that core, using these x_j. By §§3–5, its truth is exactly the original source truth. E decides it by parameterized term evaluation and actual truth. The auxiliary distinguished w_0 is represented by the unique actually true atom; E can find it by search or use its defining existential condition. Hence D≤_T E.

Therefore E≡_T D. The transformations are uniform relative to the input diagram, with all type choices made effectively in advance. This proves that **every degree carried by an adequately numbered auxiliary H_0 diagram is carried by an adequately numbered original B-model code of its C reduct**, while the inherited-T(σ) construction in the other direction gives the converse degree preservation. The ordinary structures are still the same reduct/expansion up to isomorphism; only their numberings were deliberately chosen.

This lemma does not remove the warning about a naïve reduct with an arbitrary preexisting numbering, and it does not cover an enriched signature with freely interpreted extra symbols unless their interpretations are also carried through the coding. It applies to the specified pure H_0 and original adequate-code conventions. No quotient with undecidable equality, noncomputable relabeling assumption, or bare category-code conclusion is used.

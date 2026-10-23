# Exact degrees of completions and adequate countable models

OpenAI Codex (GPT-6), 22 October 2026. Supplement to `audit-degrees-20261022.md` and `audit-effective-representation-coding-20261022.md`. Ordinary mathematical proof, not a human check or a Lean result. No main database edits. No claim of novelty in the computability literature.

Independent agent audit: the parent ordinary-mathematics agent read the recursion splitter, reversible bit coding, and Γ-preserving Henkin construction and reported them sound. It also independently checked the weak-Infinity finite-trace input in `positive-effective.md` §16. This records an AI-agent audit only and is not a human `checked_by` attribution.

## 1. Verdict and scope

**PROVED:** the earlier oracle-capacity conclusions can be sharpened to exact degree realizations across the entire class of completions and adequate countable BBK models of each fixed theory below.

1. If T is any fixed consistent c.e. pure extension of C plus the Infinity schema at one admitted type, the degrees of complete consistent pure extensions of T are exactly the PA degrees. The degrees of canonical adequate countable BBK model codes of T are exactly the same degrees. In particular this includes the positive packages with either weak Infinity schema or a strong Frege Infinity axiom, and any consistent c.e. strengthening of those packages.
2. If T is any fixed consistent 0′-c.e. pure theory whose consequences include Max_C, the corresponding two sets of degrees are exactly the degrees computing a binary DNR function relative to 0′, called PA degrees over 0′ here.
3. For every supplied complete consistent pure theory Γ extending C, uniformly in its characteristic function one can construct a countable BBK model M with **exactly** that complete pure theory and with canonical operational-plus-truth code of degree exactly deg(Γ).

Statement 3 corrects the computational caution in `positive-effective.md` §15.2: preserving a supplied complete Γ does not require a higher oracle. The distinction from starting with an incomplete theory remains essential.

The degrees in statements 1–2 range over all models of T. These are not the degree spectra of the copies of one fixed isomorphism type. Model codes include the numbered sorted domains, equality, uniform interpretation of all finite original terms under numbered parameters, and actual truth valuation. Canonical coding excludes aliases and unrelated padding. No conclusion about a bare action/category code follows without an effective representation result.

The exact-degree construction is reversible. Its extra information occurs in the truth values of original pure sentences. It does not hide the desired degree in redundant presentation bits.

## 2. The abstract finite-output hypothesis

Fix an oracle A, a consistent A-c.e. theory T in an effective classical language, and an ordinary computable map e↦h_e to closed sentences such that

    φ_e^A(e)↓=0  ⇒  T ⊢ h_e,
    φ_e^A(e)↓=1  ⇒  T ⊢ ¬h_e.                 (2.1)

The proof enumeration must remain A-c.e. after adjoining finitely many sentences, uniformly in their codes. This is the case for the fixed C calculus: Logical Equivalence instances are enumerated with their H-proof certificates, and the ordinary deduction theorem applies to added closed premises. Optional assumptions are never silently necessitated.

For the positive application, A=∅ and h_e is the bounded-register-trace sentence H_e of `positive-effective.md` §16.2. Its Lemmas 16.1–16.2 give (2.1) already over C+InfSchema_σ. The decisive finite-run argument is sound: finite equality-defined time/value domains witness a genuine output-0 run; in a purported output-0 trace, external induction through a genuine finite output-1 run forces the same successive states and finite initial value segments until the halting-state contradiction. An externally infinite or nonstandard trace cannot avoid those finitely many forced steps. No internal arithmetic interpretation is required for this application.

For Max, A=0′ and

    h_e = H_0(numeral e,J),   J(n)=□(I→h(n)),

using `max-degree.md` §8. The correct standard J-literals verify each genuine finite oracle computation. The interpreted PA(J) determinism theorem makes a verified output-1 run imply ¬H_0. The arithmetic and oracle-literal obligations were checked in `audit-degrees-20261022.md` §§3–4. Additional axioms in T preserve these proof facts.

Every complete consistent Γ extending T computes binary DNR^A by

    d_Γ(e)=1 iff h_e∈Γ.

Indeed, the two cases of (2.1) force the opposite output bit. This is the lower bound for the degree theorem.

## 3. Uniformly obtain an independent sentence after each finite extension

**Lemma 3.1.** Under (2.1), there is an ordinary computable function Δ↦θ_Δ such that whenever Δ is a finite sentence set and T+Δ is consistent, neither θ_Δ nor its negation is provable in T+Δ.

Fix an A-oracle index enumerating T-proofs. The parameterized recursion theorem supplies an ordinary computable index p=p(Δ) for the following A-oracle program. It ignores its external input, knows p, and searches the T+Δ proof enumeration for these two sentences:

    if a proof of h_p appears, output 1;
    if a proof of ¬h_p appears, output 0.

Set θ_Δ=h_p. There is a fixed tie convention, immaterial under consistency.

If T+Δ proves h_p, consistency excludes a proof of ¬h_p. Thus the program eventually outputs 1. By (2.1), T itself proves ¬h_p, a contradiction. If T+Δ proves ¬h_p, the program instead outputs 0, so T proves h_p, again a contradiction. Therefore neither sentence is provable. Classical logic and the deduction theorem then make both T+Δ+θ_Δ and T+Δ+¬θ_Δ consistent.

The map p(Δ) does not query A. It compiles an oracle program whose execution will query A. The enumeration index for T and the sentence compiler e↦h_e are fixed numerical parameters. The oracle recursion theorem is uniform at the syntactic index level, so this distinction remains valid when A=0′.

This proof is a direct effective-inseparability argument. It eliminates the need for a separate Rosser sentence or for an internally represented proof predicate for T. In particular, no soundness assumption about T, no standardness of its interpreted arithmetic, and no general Rosser theorem for arbitrary arithmetically definable theories has been used.

## 4. A reversible construction of completions of exact degree

Fix a recursive enumeration ψ_0,ψ_1,… of all original-language sentences. Let d be binary DNR relative to A. We construct finite consistent decision sets Δ_n, beginning with ∅. The following two operations make stage n.

**Decide the next sentence.** Compile an A-oracle program q(Δ_n,ψ_n), ignoring its input, which searches T+Δ_n proofs and returns 0 on finding ψ_n and 1 on finding ¬ψ_n. If d(q)=1 add ψ_n; if d(q)=0 add ¬ψ_n. Call the resulting set Δ'_n.

If one side was already forced, DNR chooses that side. If neither was forced, both choices are consistent. Thus T+Δ'_n is consistent. This compilation does not run either proof search or the oracle A.

**Encode the next bit.** Compute the independent sentence θ_n=θ_(Δ'_n) from Lemma 3.1. If d(n)=1 add θ_n; if d(n)=0 add ¬θ_n. Let this be Δ_(n+1). Both choices are consistent.

Every finite stage is consistent with T and every original sentence is eventually decided. The selected truth assignments therefore define a complete consistent deductively closed extension Γ of T. A finite contradictory proof from the union would occur at a finite stage, so compactness here is only the usual finitary proof property.

To compute Γ(ψ), locate ψ in the fixed sentence enumeration and simulate through that decision stage using d. Thus Γ≤_T d, uniformly.

Conversely Γ reconstructs the finite construction without access to d or A. Given Δ_n, ask Γ whether ψ_n is true; this recovers Δ'_n, since the construction's chosen sign must agree with its complete limit. Compute θ_n=θ_(Δ'_n), and read

    d(n)=1 iff θ_n∈Γ.

Add that sign to reconstruct Δ_(n+1), and continue. Thus d≤_TΓ uniformly on the image of the construction. In particular

    Γ ≡_T d.                                     (4.1)

The two Turing functionals are uniform in the fixed proof-enumeration and h-indices. There is no hidden jump in the inverse: the independent-sentence compiler is ordinary computable, even in the relative case.

**Realizing an arbitrary PA-over-A degree.** Suppose X computes some binary DNR^A function d, but deg(d) might be smaller than deg(X). Use d for the first operation and encode X(n), rather than d(n), in the second operation. Then Γ≤_T X and the same decoder recovers X from Γ, so Γ≡_T X. This construction is uniform given X and a specified index witnessing d≤_T X. It does not claim a single functional can discover such an index from an arbitrary unspecified PA-degree oracle.

Alternatively, the map in (4.1) is already fully uniform on actual binary DNR functions and preserves their exact degrees. Binary DNR^A functions themselves compute A: for the ordinary computable index e(k) of the oracle program returning its oracle's kth bit, A(k)=1−d(e(k)). Hence the stated relative degree convention includes the base oracle.

In particular (4.1) is a uniform continuous degree-preserving embedding of the binary DNR^A solution class into the original pure completion space, with a computable decoder on its image. It is not a computable parametrization of that entire completion space by arbitrary binary sequences. The separate `completion-space-parametrization-audit-20261022.md` proves the exact stronger oracle requirement for such a global parametrization.

Together with the lower bound of §2, this proves the exact complete-theory degree classifications in §1.

## 5. Construct a model preserving any supplied complete theory

**Theorem 5.1.** From the characteristic function of any complete consistent pure Γ⊇C, one uniformly computes a complete witness theory D in a fixed fresh-constant language and its countable BBK model M. The original pure theory of M is Γ. The canonical adequate code K(M) satisfies K(M)≡_TΓ, uniformly in both directions.

Use an effective countably infinite supply of new constants at every admitted type. The expanded logical background is the entire fixed C proof schema in this language. This is conservative over pure C under interpretations of the new constants: an H-theorem involving fresh constants can be generalized after replacing them by variables, and Logical Equivalence keeps its original H-theoremhood restriction. We do not impose a new Max schema on terms containing these constants.

For a finite set Δ of expanded-language sentences, list all its fresh constants as c_1,…,c_k, replace them simultaneously by appropriately typed fresh variables, and form the pure existential closure

    E_Δ := ∃x_1…∃x_k (AND δ∈Δ δ[x̄/c̄]).

Then

    Γ+Δ is consistent in the expanded C language
       iff E_Δ∈Γ.                                (5.1)

Here is the exact justification. If Γ+Δ is consistent but E_Δ∉Γ, completeness of Γ gives ¬E_Δ∈Γ, while Δ proves E_Δ by existential introduction, a contradiction. Conversely, if E_Δ∈Γ, take a BBK model of Γ by the general completeness theorem and choose witnesses for these finitely many existential quantifiers. Interpret c̄ by them. That expansion satisfies Δ and the expanded logical background, so Γ+Δ is consistent. Equivalently, the converse follows syntactically by the fresh-constant deduction/generalization argument. There is no use of full higher-order model compactness.

Now enumerate all sentences χ_0,χ_1,… in the fixed expanded language. Maintain a finite Δ consistent with Γ. At stage n, compute E_(Δ∪{χ_n}) and query its membership in Γ. If yes, add χ_n; otherwise add ¬χ_n. Equation (5.1) and classical logic preserve consistency.

Whenever the positive sentence selected is existential, say ∃x η(x), choose the first constant c of the right type not occurring in the current finite Δ or in that existential sentence, and add η(c). The ordinary witness argument preserves consistency. Every true existential sentence is eventually considered, so the limit has witnesses. The fresh-constant supply also yields a nonempty term domain at every type; all their relevant reflexive identities are logical consequences.

The resulting D is complete, consistent, and witness-complete. Its characteristic function is Γ-computable: to decide χ, simulate through its place in the fixed enumeration. It extends Γ, and its restriction to the original pure language is exactly Γ.

For each type take the least numerical code of a closed expanded term in each D-equality class as its canonical representative. The representative-domain predicate is D-decidable, because a candidate has only finitely many smaller term codes. To interpret an original term under a finite assignment of such representatives, substitute their closed terms and choose the least equivalent representative. To evaluate a proposition representative P, ask whether P∈D. The fixed C schemas in D guarantee that these are the well-defined BBK term operations and truth valuation; this is the general witness-theory construction used in Bacon–Dorr's completeness theorem, not an extensional quotient construction.

This gives K(M)≤_T D≤_TΓ uniformly. Conversely K(M) evaluates every original pure sentence, and its theory is Γ, so Γ≤_T K(M) uniformly. Therefore K(M)≡_TΓ.

The input being a **complete characteristic theory** is essential to the consistency test (5.1). The same algorithm does not decide consistency over an arbitrary c.e. incomplete T. The existence of a complete Γ, or the DNR oracle used to obtain one, remains the noncomputable step in the earlier model-existence classifications.

## 6. Consequences for the positive and maximalist comparisons

Combining §§4–5 proves the exact adequate-model degree statements. Every code computes a complete theory, so its degree is in the required PA class. For every degree in that class, §4 produces a completion of exactly that degree and §5 realizes it by a model code of the same degree.

For a positive theory with B=□Plenitude, the same exact degree result holds for canonical equality-and-parameterized-term codes even when the truth map is omitted. `audit-effective-representation-coding-20261022.md` gives the reason: there is a true atom whose single finite index computes the original truth map by a≤p, and equality plus term interpretation decides that relation. Uniform repointing to the first detectable atom yields an isomorphic pointed pure model; for the mere degree equality, hardcoding the original true atom is sufficient. Actuality alone gives the same nonuniform truth recovery, so the equality-only exact-degree conclusion also applies to any consistent 0′-c.e. Max extension which entails Actuality.

If the audited effective Gallin conversion is applied to a B-completion's model, its inherited-numbering inverse recovers the source operational data and its complete auxiliary diagram has the same degree. Thus exact realizations transfer to that explicitly coded auxiliary representation. A further claim for an auxiliary atomic diagram must use its separate effective truth-recovery theorem, not just classical model equivalence.

There is still no classification here of the copies of one fixed model. Different encoded choices generally change its complete original theory, hence change its elementary equivalence class. The construction does not promise standard arithmetic, full function domains, effective categoricity, or low isomorphisms between independently obtained copies.

For finite positive packages without any Infinity requirement, §2's finite-output hypothesis need not hold. Their known computable completions prevent the PA-only spectrum conclusion. Nothing in this supplement changes that boundary.

## 7. Source and audit accounting

The fixed framework and principle meanings were read in `topics/classicism/AGENTS.md`, `topic.yaml`, `background.md`, and the records for pure Maximalism, the Infinity schema, strong Infinity and Actuality. The mathematical inputs from the research notes are identified at their use above.

The standard oracle recursion theorem, including the distinction between compiling indices and running an oracle program, is described in Andrew Marks's author-hosted *Computability Theory*, §15, [relative computability notes](https://math.berkeley.edu/~marks/notes/computability_notes_v1.pdf). Sections 3–4 above supply the actual application and inverse decoding, rather than invoking an unproved exact-spectrum slogan.

The general BBK completeness/witness-model construction is Bacon–Dorr, *Classicism*, accessible draft dated 1 July 2022, Theorem 3.2 and n.64, printed pp.44–45, [author-hosted draft](https://andrew-bacon.github.io/papers/Classicism.pdf). These locators are version-specific and are not transferred to the bundle's 16 May 2023 source version. The complete-theory-preserving oracle construction in §5 is written out here so its computational costs are explicit.

The bare non-r.e. character of Max is already in Bacon–Dorr, accessible 2022 draft n.52, and is not a novelty claim. Exact-spectrum assertions here are proved applications of standard effective-inseparability and Henkin ideas; their priority in the literature has not been investigated.

Validation: no main records were edited. The required bundle validator is run after writing this supplement; its result is reported separately.

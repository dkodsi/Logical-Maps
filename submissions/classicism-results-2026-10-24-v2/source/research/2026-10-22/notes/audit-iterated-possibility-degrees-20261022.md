# Audit of the finite iterated-possibility hierarchy

22 October 2026. Independent hostile audit by an OpenAI Codex research agent. Ordinary mathematical verification only: no human checking, Lean work, database edits, or claim of literature novelty.

Target: `.reproduction/classicism-research/iterated-possibility-degrees.md`, as read on 22 October 2026. The companion notes `max-degree.md` and `strong-possibility-degree.md` were consulted for their explicit arithmetic, recursion-theorem, and BBK constructions. The topic guide, `topic.yaml`, framework/signature/modal conventions in `background.md`, and the matching Max, SP, arithmetic and Vicinity records were checked.

## 1. Verdict and exact scope

**PASS, with the proof-expansion and presentation qualifications recorded below.** I found no invalid higher-jump induction, no hidden standard-arithmetic-model premise, no switch to signature Strong Possibility, and no necessitation of an optional axiom. The stated consistency conditions are indispensable and are retained throughout. In particular this audit supplies no consistency proof for SP or any higher stage.

The finite theories are the specifically defined research objects

    T_0=C,
    T_(n+1)=T_n+{D_n P: P is closed pure and Con(T_n+P)},
    O_0=Box, O_(n+1)=hat O_n, D_n P=¬O_n¬P.

The underlying consequence relation is finitary consequence over fixed C, with its original theoremhood restrictions. It is not closure under necessitating every accepted optional sentence. T_1 is pure Max and T_2 is pure SP, using the recorded SP⇒Max implication. For n≥3 this is a newly defined hierarchy. Its side condition genuinely changes to T_n because that change is explicit in the definition; it must not be substituted into any original Max/SP record.

For every fixed n≥1, conditional on Con(T_n), the five numbered claims in §3 pass: 0^(n)-c.e. axiomatizability, Σ^0_(n+1)-complete pure theoremhood, Π^0_(n+1)-complete finite pure extension consistency, binary-DNR-over-0^(n) oracle capacity for adequate models, and the exact cone above 0^(n) for consistent oracle-c.e. strengthenings. The strict modal steps, completion-space statements, and actual-Vicinity corollary also pass under their displayed hypotheses.

## 2. Modal induction: PASS

All O_n are fixed finite pure terms of type tt. No quantification over types, infinite conjunction, internal natural-number-indexed family, or individual-output function is needed.

I checked the cited primary source directly: Dorr, Hawthorne, with Yli-Vakkuri, *The Bounds of Possibility* (2021), [Appendix D](https://fitelson.org/piksi/piksi_22/the_bounds_of_possibility.pdf). D14, printed p.406 (PDF index419), establishes the necessary NK preservation used here. D22, printed p.409 (PDF index422), gives the necessary hat fixed-point law for necessarily NKB operators. D23's collapse of the second and third hats has the stronger HS4R subscript; it is not imported into bare C. These source statements support the note's stated uses. The additional preservation of 4 is supplied by the note's own argument, expanded next.

Write H=hat X and Dq=¬X¬q. Assume X is necessarily normal S4. Suppose q is true and Box(Dq→p), so q witnesses Hp. At a base-accessible point where Dq is true, choose r=Dq. The dual of X's necessary 4 law gives

    Box(DDq→Dq).

The original Box(Dq→p) persists by base 4, so at that point Box(Dr→p). Thus r witnesses Hp there. Consequently Box(Dq→Hp) holds at the original point, where the same true q now witnesses HHp. This proves Hp→HHp. No future witness needs to be pulled back, and no Barcan principle is used.

For T, X's T law entails q→Dq. A true witness q and Box(Dq→p) therefore give p. Normality can also be verified directly: Box p has the witness top, and two witnesses q,r for H(p→s),Hp combine to q∧r using D(q∧r)→Dq∧Dr. Because the hypotheses on X are necessary, these arguments hold throughout the base cone. Applying them to each fixed closed O_n gives actual C-theorems of necessary normal S4.

The order is in the direction stated. If X≤Y necessarily, then D_Yq≤D_Xq; any witness for hat X p is therefore a witness for hat Y p. Also Box≤hat Box. Induction gives O_j≤O_(j+1), hence D_(j+1)≤D_j. Finally Box≤Box_5 and the Box_5 hat fixed-point law bound every finite O_n above by Box_5.

## 3. Finite-support reflection: PASS

This is the key protection against illicit optional-premise necessitation. Suppose T_n⊢A, n≥1. A finite proof has a finite support consisting of axioms D_j P, j<n. Let Q be their conjunction. Then

    C⊢Q→A,     T_n⊢Q.

For each supported conjunct D_jP the following is a chain of C-theorems:

    D_(n−1)Q → D_jQ → D_jD_jP → D_jP.

The first arrow is the dual operator order. The second is normal monotonicity applied to the propositional theorem Q→D_jP. The last is dual 4 for O_j. Hence C⊢D_(n−1)Q→Q and, by the deduction theorem above,

    C⊢D_(n−1)Q→A.

Only this discharged C-theorem is necessitated. T_n's actual Q then witnesses

    ∃q(q∧Box(D_(n−1)q→A))=O_nA.

For empty support choose Q=top; equivalently use C-theorem necessitation and Box≤O_n. No optional axiom D_jP was itself boxed. This argument does not assert T_n⊢A implies T_n⊢Box A.

Exact next-stage reflection follows syntactically, not merely semantically. If T_n⊢A, the preceding lemma and inclusion give T_(n+1)⊢O_nA. If T_n⊬A, finitary classical deduction gives Con(T_n+¬A), so the next-stage axiom is D_n¬A=¬O_nA. Thus every correct signed O_n literal is a theorem of T_(n+1). For a consistent T_(n+1) no opposite signed literal can also be provable. The model equivalence and the consistency dual in equation (2) follow. The explicit consistency hypothesis prevents a vacuous model claim from being mistaken for a complexity theorem.

## 4. Uniform oracle predicates at higher stages: PASS, expanded

This is the most easily hidden obligation. A many-one reduction k↦an arbitrary sentence does not by itself provide one numerical formula defining the reduced set. Here the special form of the recursion-theorem reduction does provide one.

Use the fixed Frege number type ν=(et)t and the source-backed arithmetic interpretation in C+I. Max entails I. The impredicative definition of N provides induction for every admitted definable predicate on ν, including predicates containing the finitely iterated O_j. Consequently the interpreted arithmetic can verify standard finite computations and prove determinism for oracle computations using J_j. Nothing below requires all internal numbers to be standard.

Inductively maintain both of these statements for each stage j≥1:

1. a fixed closed pure numerical predicate J_j has its correct signed standard numeral instances provable in T_j, with extension 0^(j) on the standard numerals;
2. every consistent 0^(j)-c.e. strengthening U of T_j has a computable many-one hardness reduction of the special form

       k∈0^(j+1) iff U⊢H_0(p(k),J_j),

   where p is an ordinary total computable index map and H_0 is one fixed oracle-halting formula.

The base J_1 is supplied in `max-degree.md`: J_1(v)=Box(I→h(v)). Positive finite computations are C-theorems after discharging I; negative standard instances follow from the full extensional standard-arithmetic countermodel and pure Max. The n=2 companion formula is a particularly direct instance of the same mechanism.

Here I is the stipulated possible arithmetic-structure condition Diamond I*, not actual individual Infinity. The recorded singleton-individual consequence of SP therefore does not obstruct this interpretation: Frege number entities can remain distinct without being the cardinalities of arbitrarily large actual individual extensions. No actual e-Infinity premise is used.

For the general induction step, take U=T_(j−1), for j≥2, in the special-form hardness statement of the preceding stage. Let p be the resulting ordinary computable reduction of 0^(j) to Th(T_(j−1)). Let Comp_p(v,w) be the interpreted arithmetic relation saying that a fixed ordinary program computing p halts on v with output w. Put, with number guards on arithmetic quantifiers,

    Q_j(v):=∃w(Nw∧Comp_p(v,w)∧H_0(w,J_(j−1))),
    J_j(v):=O_(j−1)Q_j(v).

For every external standard k let m=p(k). The actual finite computation of p(k) can be verified in PA. PA also proves uniqueness of a deterministic program's output, so T_(j−1) proves both Comp_p(k,m) and

    ∀w(Nw∧Comp_p(k,w)→w=m).

Therefore T_(j−1) proves the sentence-level material equivalence

    Q_j(k) ↔ H_0(m,J_(j−1)).

This establishes the required theoremhood equivalence *before* exact reflection is applied. One must not infer equality or necessary equivalence merely from this optional-theory equivalence. Instead use

    T_(j−1)⊢Q_j(k)
      iff T_(j−1)⊢H_0(p(k),J_(j−1))
      iff k∈0^(j),

and then exact reflection in T_j. It yields the correct J_j(k) or ¬J_j(k) as a T_j theorem. Global PA-provable totality of p is unnecessary: each individual standard run and uniqueness suffice. No internal truth predicate, self-applicable truth scheme, externally standard T_(j−1) model, or 0^(j)-oracle program hidden inside Comp_p is being assumed.

The recursion is well founded. J_(j−1) gives hardness at stage j−1; that hardness gives J_j; then J_j gives hardness at stage j. There is no use of the stage-j hardness theorem to construct the very predicate needed to prove it.

## 5. Ordinary computable hardness: PASS

Let A=0^(n) and let U be a consistent A-c.e. strengthening of T_n. Put

    V_b={k:U⊢H_b(k,J_n)},    b=0,1.

These sets are A-c.e. Consistency plus interpreted deterministic arithmetic makes them disjoint. Each contains the actual diagonal A-oracle halting set K_b^A: a convergent standard run uses only finitely many oracle questions, whose correct J_n literals are all theorems of T_n, so U verifies that finite run. No claim that arbitrary U proofs or nonstandard computations are arithmetically sound is used.

The parameterized oracle recursion theorem supplies an ordinary computable p(k) indexing an A-oracle machine that ignores its input and dovetails:

1. simulate the kth A-oracle machine on k; if it halts, output0;
2. enumerate V_0 using A; if p(k) enters V_0, output1.

The enumeration program for V_0 is a fixed finite parameter. The compiled program uses A, but the compiler producing its index p(k) does not query A. This is why the many-one reduction is computable, not merely A-computable.

If k∉A′ but p(k)∈V_0, only the second search can eventually win, so p(k)∈K_1^A⊆V_1, a contradiction. If k∈A′ but p(k)∉V_0, only the first search can win, so p(k)∈K_0^A⊆V_0, also a contradiction. Thus

    k∈A′ iff p(k)∈V_0 iff U⊢H_0(p(k),J_n).

This proves the claimed computable many-one hardness. The A-c.e. upper bound gives Σ^0_(n+1)-completeness. In particular the argument is valid for arbitrary consistent A-c.e. strengthenings, without an arithmetic-soundness assumption.

For finite pure conditions F, combine F to one sentence P. By classical deduction,

    Con(T_n+P) iff T_n⊬¬P.

Taking complements of the theoremhood reductions gives the stated Π^0_(n+1)-completeness. The guards “pure,” “finite,” and “consistent T_n” are material.

## 6. Axiom oracles and adequate-model capacity: PASS

The induction on enumerability is correctly indexed. Th(T_(n−1)) is c.e. in 0^(n−1), hence decidable in 0^(n). So 0^(n) decides which closed pure P satisfy Con(T_(n−1)+P), enumerates the new axioms, and also enumerates all earlier stages. Thus T_n is 0^(n)-c.e.; its theoremhood is c.e. in the same oracle.

If a consistent X-c.e. U entails T_n, then U proves exactly the externally correct sign of every O_(n−1)A. Race U-proof searches for that literal and its negation. One appears, and consistency prevents both. This computes Th(T_(n−1)), of degree 0^(n). For n=1 use the Σ^0_1-complete C theoremhood base. Conversely an oracle computing 0^(n) enumerates T_n itself, which is consistent under the standing hypothesis. Thus the axiomatization cone is exactly the stated one.

Given a complete consistent pure extension Y of T_n, define d(k)=1 if Y accepts H_0(k,J_n), and d(k)=0 otherwise. An actual output0 forces H_0, and an actual output1 forces H_1 and therefore ¬H_0. Thus d is binary DNR relative to A=0^(n). Nonstandard apparent halting on genuinely divergent inputs does not hurt DNR: divergent inputs impose no requirement.

Conversely let d be binary DNR relative to A. It computes A: uniformly compile an oracle program e(k) that ignores its input and returns its oracle's kth bit, obtaining A(k)=1−d(e(k)). Expand C by a computable stock of fresh Henkin constants and witness axioms; retain the T_n schema only on the original pure language and with the original recursively specified reference theories. No new Max/SP instances involving witness constants are added. Fresh constants may have type e; this is permitted and does not introduce functions with output e.

The consistent witness theory is A-c.e. At a finite consistent choice set Δ and the next expanded-language sentence φ, compile an A-oracle program e(Δ,φ) that outputs0 if it finds a proof of φ, outputs1 if it finds a proof of ¬φ, and diverges if neither is found. Add φ when d(e)=1 and ¬φ when d(e)=0. If one side is forced, DNR selects it; if neither is forced, either extension is consistent. This produces a d-computable complete witnessed theory.

The companion's term-model construction is effective in that theory: equivalence of closed terms is decided by the accepted identities; a term is the least representative of its class iff none of its finitely many smaller same-type terms is equivalent to it; substitution plus least-equivalent search gives uniform term interpretation; accepted proposition sentences give actual truth. The resulting countable BBK model is adequate in exactly the sense required by the lower bound.

These are claims about the ability of X to compute *some* adequate model. They are not claims about exact presentation-degree spectra, models with a prescribed complete theory, or bare action/category codes without effective term interpretation and valuation. Likewise, “PA degree relative to A” here has the explicit binary-DNR meaning used in the note. That meaning includes computing A; it is stronger than merely having an arbitrary unbounded DNR function relative to A.

The Low Basis conclusion also has the right strength. An A-c.e. witnessed completion problem is a nonempty Π^0_1(A) class. A relatively low path yields an adequate model code D with D′≤A′. The lower bound gives A≤D and binary DNR over A, hence A<D and D′≥A′. Thus D′=A′; D=A′ would then imply D′=A′′, so D<A′. No exact-degree preservation of the completion-to-model map is needed for these inequalities.

## 7. Strict hats, topology, and Vicinity: PASS

Assume Con(T_(n+1)). The inclusions T_n⊆T_(n+1), together with their distinct theoremhood degrees, give a closed pure A with T_(n+1)⊢A but T_n⊬A. Finite-support reflection yields O_(n+1)A; exact reflection yields ¬O_nA. Both are actual theorems of T_(n+1). Existential generalization therefore supplies a pointwise separating proposition and refutes the operator identity. The n=0 case is supplied by the known strict Max extension (or by the base theoremhood degrees). No necessitation of the separation witness is asserted.

The published-source assumptions behind the finite hat bound do not supply finite stabilization in C. Conversely all-finite consistency gives compactness for the increasing union and every external finite strictness sentence. It does not automatically exhibit one internal hat-closed separating family or prove the stronger `No Collapse` sentence. The note preserves this distinction.

For nowhere density, let F be any finite pure condition consistent with T_n. Then T_n+F is a consistent 0^(n)-c.e. theory. It cannot entail all of T_(n+1), by the next-stage axiomatization lower bound. Choose one unentailed next-stage axiom α. Then F∧¬α is consistent with T_n and defines a nonempty relative basic open subset disjoint from the T_(n+1) locus. Closedness follows because accepting each axiom is clopen and the locus is their intersection. This argument also covers n=0 using the companion's Max lower bound.

For n≥1, an isolated completion would be the unique complete theory of T_n+F for some finite F. Racing proofs makes that theory decidable in 0^(n), contradicting its binary-DNR lower bound. Relative-low completions exist after every consistent finite condition by Low Basis. With nonemptiness, compactness, metrizability and zero-dimensionality, the completion spaces are Cantor spaces. The restriction n≥1 matters: finite categorical pure C conditions can isolate completions of C.

Finally I checked `vicinity-implies-five-implies-two-hat.md` and the Actuality⇒Vicinity record. They provide the actual implication

    Vicinity → ∀p(Box_5p→O_2p).

Together with the C-theorem O_2≤O_3≤Box_5, actual Vicinity makes O_2 and O_3 agree pointwise. The T_3 separation contradicts that. Thus, conditional on Con(T_3), T_3 entails ¬Vicinity and ¬Actuality. This uses actual Vicinity at the evaluation point; neither boxed Vicinity nor boxed Actuality has been smuggled in. Nothing in this argument establishes the analogous failure from SP alone.

## 8. Presentation recommendations and unresolved boundary

These are clarifications, not mathematical repairs to a failed claim:

- When citing the uniform-predicate step, retain the explicit Comp_p formula and the distinction between sentence theoremhood equivalence and necessary equivalence. The former is sufficient; the latter was not proved from optional premises.
- Say “complete consistent theory” whenever a DNR lower bound is invoked.
- In the Henkin upper bound, explicitly freeze all possibility schemata to the original pure language. Adding logical witness constants is conservative; enlarging the schema's reference signature would define a different theory and is not justified here.
- Keep all exact complexity and model-existence claims conditional on the relevant Con(T_n), and all degree claims tied to the specified effective coding.

No open mathematical gap remains in the finite induction as stated, conditional on the companion's source-backed arithmetic interpretation and ordinary BBK completeness. The major unresolved matter is consistency of SP and the higher optional stages. The hierarchy's increasing computability demands do not settle that question.

> Integration note, 23 October 2026: source prose is preserved below. Draft-time status statements are historical; the completed certificate and its scope are indexed in the frozen submission and in the integration report. Original work by Codex (OpenAI), prompted by Daniel Kodsi; construction and literature credits in the source remain in force.

# Strong Leibniz and Rigid Comprehension propagate

22 October 2026. Ordinary mathematical audit in the original C, by Codex. The coordinating chat supplied the relational-argument propagation candidate; this note checks its scopes and supplies a haecceity-coding completion. No database, source proof, or Lean file is changed. No human or formal verification is claimed.

**Conclusion.** The candidate survives the audit. Moreover, the individual-argument restriction can be removed:

    Strong Leibniz + Rigid Comprehension
      ⇒ □Rigid Comprehension at every admitted argument tuple
      ⇒ □Boolean Completeness at every relational type.

Here Rigid Comprehension is the rigidity principle, not Relational Choice. Both initial premises are unboxed. BF_e is not assumed or derived in this proof. The first conclusion uses the coding lemma in §3; merely performing the first proof with σ=e would indeed leave a gap.

## 1. Inputs from the saved sealed-cover proof

Use `research/2026-10-22/strong-leibniz-rigid-bottom-cut.md`, §§1–4 and 6. Under the stated premises it supplies:

- a rigid A:tt whose current members are exactly the strong propositional worlds together with ⊥;
- □A⊥ and □∀w(Aw→D(w)), where D(w):=∀q(w≤q ∨ w≤¬q);
- J(A)=⊤, where J(A):=∃w(Aw∧w), hence □∃w(Aw∧w);
- □BF_ρ for every relational ρ≠e.

The cover conditions remain available at future points. The boxed Barcan theorem is a dependency supplied by that saved argument, not an inference from the absence of a database separator. Its proof uses the recorded Atomicity + Rigid Comprehension ⇒ Rigid Power theorem and the sealed bottom-cut representation.

## 2. The supplied propagation argument, with scopes checked

Fix a relational argument type σ≠e and a current X:σt. Write

    E_X := ∃Y^(σt) [Rigid(Y) ∧ ∀z^σ(Xz↔Yz)].

For a current A-member w, D(w) says that w≤Xz or w≤¬Xz for every current z. Root Rigid Comprehension supplies rigid P,Q:σt coextensive with the respective predicates λz(w≤Xz) and λz(w≤¬Xz).

For each current P-member z, w≤Xz gives □(w→Xz). Test weak inextensibility of P on λz(w→Xz). It gives

    □∀z(Pz→(w→Xz)).                                  (1)

Likewise Q gives

    □∀z(Qz→(w→¬Xz)).                                 (2)

The actual P- and Q-extensions cover D_σ. Their persistence therefore gives ∀z□(Pz∨Qz), and BF_σ gives

    □∀z(Pz∨Qz).                                      (3)

At any future point where w is true, (1)–(3) say X and P are coextensive: P implies X; and an X-instance cannot be a Q-instance, so coverage makes it a P-instance. Thus

    □(w→∀z(Xz↔Pz)).

Rigid(P) is necessary. Necessary existential introduction now gives □(w→E_X). Equivalently one can use CBF with the current witness P. Only a theorem of C is necessitated at this step; neither the optional root coextension nor the root comprehension premise is necessitated. The bottom case is harmless because its antecedent is false everywhere.

We have shown, for the fixed current X,

    ∀w(Aw→□(w→E_X)).

The choices of P and Q may depend on w. They have been eliminated inside E_X, so no uniform choice function or simultaneous collection of representatives is required. Test weak inextensibility of A on Z:=λw(w→E_X), obtaining

    □∀w(Aw→(w→E_X)).

The sealed □∃w(Aw∧w) then gives □E_X. Generalize over current X, and use BF_(σt), another relational-type Barcan instance, to obtain

    □∀X^(σt) ∃Y^(σt)[Rigid(Y)∧∀z^σ(Xz↔Yz)].        (4)

The two Barcan applications are exactly BF_σ in (3) and BF_(σt) at the final quantifier shift. All other future universal quantifiers come from weak inextensibility or from ordinary necessarily valid logical implications. In particular there is no silent BF_e application.

Only the **root** instances of those two BF schemata are used here. The boxed BF supplied by §1 is stronger than this propagation step needs. The deciding cover A uses Strong Leibniz only at t. Consequently, after the coding step below, the same proof also establishes the separate dependency refinement

    Strong Leibniz at t + Rigid Comprehension + BF at relational types
      ⇒ □Rigid Comprehension + □Boolean Completeness.

Here all three premises are unboxed. This does not remove the BF premise from the propositional Strong Leibniz version: the original all-type Strong Leibniz premise is what supplies it through the saved sealed-cover theorem.

## 3. Coding removes the individual-argument gap

The following is a separate uniform C derivation. Let σ̄ be any finite admitted tuple of argument types, allowing individuals and the empty tuple. Put δ:=σ̄t, which is always relational, and define the haecceity code

    H_x̄ := λz̄(z̄=x̄),          Code(H):=∃x̄(H=H_x̄).

C proves H_x̄=H_ā ↔ x̄=ā. For the empty tuple the unique code is ⊤. No function with output e is introduced.

Suppose Rigid Comprehension is available for predicates on δ. Given X:σ̄t, apply it to

    F(H):=∃x̄(H=H_x̄ ∧ X[x̄])

and obtain rigid P:δt actually coextensive with F. Put

    Y:=λx̄ P(H_x̄).

The injectivity of the codes gives actual coextension Y≈X. We must check full rigidity, not just persistence.

**First seal the code image.** Every current P-member H equals H_ā for some current ā. Necessity of identity and necessary existential introduction give □Code(H), with the same ā supplying a witness at each future point. Weak inextensibility of P therefore gives

    P≤Code, i.e. □∀H(PH→Code(H)).                    (5)

No rigidity of Code itself is assumed. Equation (5) is what ensures that *every* future P-member, including a new one, is a code at that future point.

Persistence of Y follows immediately from persistence of P and the definitional transport of H_x̄. To prove inextensibility, work at an arbitrary future point and suppose Z:σ̄t satisfies

    ∀x̄(Y[x̄]→□Z[x̄]).

For each current P-member H, (5) supplies a current ā with H=H_ā. Then Y[ā], so □Z[ā]. Necessity of H=H_ā and the necessarily valid injectivity of haecceities give

    □∀x̄(H=H_x̄→Z[x̄]).

For clarity, this is obtained by necessitating the C theorem

    (H=H_ā ∧ Z[ā]) → ∀x̄(H=H_x̄→Z[x̄]),

and applying it to the two necessary antecedents. It does not move a quantified premise through □. Apply weak inextensibility of P at this point to

    Q(H):=∀x̄(H=H_x̄→Z[x̄]).

It yields P≤Q. At any further point, instantiate H with H_x̄: P(H_x̄) implies Z[x̄]. Thus Y≤Z. Since the argument works at every future point using the necessary rigidity of P and (5), Y is inextensible and therefore rigid.

We have proved, uniformly in C,

    Rigid Comprehension for predicates on δ=σ̄t
      ⇒ Rigid Comprehension for relations on σ̄.       (6)

There is no BF premise in this coding lemma. It does not require any future individual to be the image of a current individual; its code and its code witness are chosen at the point where they are used. There is also no selection of one code witness for every member.

Apply (4) with the relational argument type δ and then apply the necessarily valid implication (6) at each future point. This proves the full □Rigid Comprehension schema, including individual and mixed argument tuples.

## 4. Boxed Boolean Completeness

Use the recorded C theorem Rigid Comprehension ⇒ Boolean Completeness, Bacon–Dorr, *Classicism*, draft 16 May 2023, Proposition 2.8, p.29 and n.39. Its boxed form is recorded as `necessary-rigid-comprehension-r-implies-necessary-boolean-completeness-r`.

At any future point, for F:τt with τ relational choose a rigid coextension R. The usual meet

    M:=λz̄ ∀U^τ(RU→U[z̄])

is a greatest lower bound of F. A lower bound V gives necessary V≤U for each actual R-member U; weak inextensibility of R transfers this to the boxed universal statement and gives V≤M. Conversely persistence of R makes M≤U for each actual R-member, hence for each actual F-member. The future Rigid Comprehension required here has been proved in §§2–3. Therefore □Boolean Completeness follows at every relational τ.

Together with §5 of the saved sealed-cover proof, this also shows that every instance of the original Strong Leibniz and Rigid Comprehension premises becomes necessary. This is a schema-level consequence; it does not introduce an infinitary conjunction of all instances into C.

## 5. Audit status

Before adding any new argument to an engine, proved-only queries with premises `strong-leibniz-r` and `rigid-comprehension-r` found no entailment, exclusion, or recorded separator for either boxed conclusion. This reports the unchanged records only.

The first part of the candidate is sound under the saved sealed-cover/BF theorem. The first potential gap—using BF_e for coverage—has been removed by (6), not assumed away. The key additional check is the necessary inclusion of P in the code image, obtained by weak inextensibility; without that step the naive pullback argument would not establish future inextensibility.

The BF boundary is real: the proved records include `full-two-object-chain-new-individual`, a model of Strong Leibniz and Rigid Comprehension in which one individual becomes two, BF holds at every relational type, and BF_e fails. The coding proof is compatible with this example and does not upgrade its conclusion to all-type BF. A fresh proved-only query also confirms that Converse Barcan and necessity of identity, used in the audit, are C theorems.

This is an ordinary proof and self-audit, with the coordinating chat carrying out a separate check. No result from that separate check is presumed here. The new propagation and coding arguments should have direct source `misc` if later integrated; the existing meet theorem retains its published attribution. The frozen archive and all database records remain unchanged.

## 6. What the BF assumption says about a rigid universal representative

There is a useful exact C identity behind the proof. For T_σ:=λx^σ.⊤,

    WeaklyRigid(T_σ) ↔ BF_σ,
    Rigid(T_σ) ↔ □BF_σ.

The first equivalence is immediate by expanding weak inextensibility: its necessary-cover premise is ∀x□Xx, and its conclusion T_σ≤X is □∀xXx. Weak persistence of T_σ is a theorem. Necessitating this defining equivalence gives the second, since rigidity is necessary weak rigidity.

Suppose U is rigid and actually universal, ∀x Ux, as supplied by the relevant Rigid Comprehension instance. Then

    BF_σ ↔ U=T_σ.

For the forward direction persistence gives ∀x□Ux, BF gives □∀x Ux, and hence U=T_σ. For the reverse direction U=T_σ and rigidity give □BF_σ by the preceding equivalence, hence BF_σ. In particular this local comprehension instance plus BF_σ already gives □BF_σ.

Thus under Rigid Comprehension the missing BF instance is exactly the possibility that a rigid relation which is universal now becomes a proper subrelation of the future universal relation. Actual coextension alone does not rule this out. The [four-world construction](../../../../submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/followup/propagation-without-barcan-countermodel.md) develops a proposed counterexample to dropping BF_rel from the propositional-SL version: it preserves root Rigid Comprehension and even □SL_t and □BF_t, but has a future newly represented family whose image on a ground-limited terminal branch is not representable. Its name quotient, closure and rigidity arguments are supplied explicitly; independent checking remains outstanding. The all-type Strong Leibniz proof and the full haecceity pullback in §3 are unchanged.

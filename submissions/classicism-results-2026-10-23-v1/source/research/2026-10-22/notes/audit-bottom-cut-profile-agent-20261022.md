# Independent adversarial audit: bottom cuts, Strong Leibniz, and Barcan

22 October 2026. OpenAI Codex research-agent audit; ordinary mathematics, not named-human checking or Lean verification. No database edits. Direct source of the new proof is `/tmp/rigid-bottom-cut-proof.md`; the separate boxed-Strong-Leibniz consequence is in `/tmp/classicism-research/rigidity-actualization.md` §7. This report independently reconstructs the arguments and sharpens the typewise premises. It does not amend the attribution or mathematical text of the existing published-proof record.

**Verdict: pass.** The bottom-cut proof controls the newly quantified future Y and Z using one actual rigid A. It does not assume Rigid Comprehension at those future worlds. The inclusion of bottom exactly repairs the case of a currently excluded world that later collapses to bottom. The following statements are supported:

1. SL_σ + RC_(σt) ⇒ □SL_σ.
2. SL_σ + RC_(σt) + RigidPower_(σt) ⇒ BF_σ.
3. A sharper replacement for item 2: SL_σ + RC_(σt) + Atomicity_((σt)t) ⇒ □BF_σ.
4. Consequently, at schema level, unboxed Strong Leibniz plus unboxed Rigid Comprehension implies boxed Strong Leibniz and boxed BF at every relational type.

Here σ is any relational type, including t. RC_τ means the single type instance of rigid comprehension whose entities are of type τ. Item 3 is a local sharpening supplied in this audit: it uses only the weak inextensibility part of the existing atom/RC power proof. The needed Rigid Power hypothesis need not be separately assumed.

## 1. Exact fixed definitions and records

For relational σ=σ₁…σₙt set b=bottom_σ and

    D(W) := ∀Y^σ (W≤Y ∨ W≤¬Y),
    SW(W) := W≠b ∧ □D(W),
    J(B) := λx̄ ∃W^σ (BW ∧ W[x̄]).

Algebraic ≤ is identity of Boolean terms, equivalently necessary pointwise implication. A relation is persistent when its members remain members necessarily, with the outer box in the official definition. It is inextensible when its weak inextensibility holds necessarily. Thus C proves Rigid(B)→□Rigid(B). This follows from 4 and the leading boxes; it is not a necessitation of an optional premise.

The independent background results used are the exact existing records:

- `atomicity-and-rigid-comprehension-imply-rigid-power`, especially Steps 1–2 of its writeup (Bacon's Lemma C.6 composition).
- `rigid-comprehension-implies-tame-rigidity` (coextensive weakly rigid relations are identical).
- `tame-rigidity-and-bf-relational-imply-necessary-bf-relational` (typewise upgrade).
- `atomicity-and-bf-relational-imply-strong-leibniz` for the converse in Section 7 below.

The old record `necessary-strong-leibniz-and-rigid-comprehension-imply-necessary-bf-relational` is currently conjectured and was not used as evidence. The proved-only Engine was queried with optional assumptions in the premise set, not background. For P={strong-leibniz-r, rigid-comprehension-r}, it reports no recorded entailment, exclusion, or separating model for each of barcan-relational, necessary-barcan-relational, and necessary-strong-leibniz-r. This is a database-location observation, not mathematical evidence against the new proof.

## 2. Construction of one stable cover

Assume SL_σ and RC_(σt). Choose A:σt rigid and actually coextensive with SW(W)∨W=b. Establish:

    (N1) Rigid(A),
    (N2) □A b,
    (N3) □∀W (AW→D(W)),
    (N4) J(A)=top_σ.

N2: A b holds by actual coextension, and persistence gives □A b.

N3: every actual A-member W is a strong world or bottom. In either case □D(W). Weak inextensibility of A, tested on the entire predicate D, gives A≤D. That is N3. The quantifier over Y within D has stayed within the conclusion's box. The argument does not first establish an unboxed universal statement and then incorrectly box it.

N4: if W is an actual strong world, then AW and persistence give □AW. At every future object and tuple, W[x̄] therefore witnesses J(A)[x̄]; hence W≤J(A). If ¬J(A) were nonbottom, actual SL_σ would give an actual strong world W below ¬J(A). It would also lie below J(A), making W bottom. So J(A)=top_σ.

Let N(A) be the conjunction N1–N4. C proves N(A)→□N(A): N1 uses the leading boxes/4; N2–N3 use 4; N4 uses NI because it is an identity. This explicit stable hypothesis is a clean way to discharge the later box scopes. Neither SL nor RC has been boxed.

## 3. The cut lemma, with future parameters exposed

Assume N(A). For Y:σ put

    R_Y(W) := AW ∧ W≤Y.

We prove C⊢N(A)→∀Y Rigid(R_Y). The proof at a generic evaluation point uses only N(A). Stability then gives its fully boxed universal form.

Persistence is immediate: A is persistent and the second conjunct is a necessarily persistent identity. To prove inextensibility, work at an arbitrary further point v and take any current Z:σt satisfying

    ∀W (R_Y(W)→□ZW).

At v, N2 gives A b; b≤Y is a C theorem. Thus R_Y(b), and the premise gives □Zb.

Now let W be any current A-member at v. N3 gives W≤Y or W≤¬Y.

- In the first case, W is currently an R_Y-member, so □ZW and therefore □(R_Y(W)→ZW).
- In the second case, NI preserves W≤¬Y at every further point. At any such point where R_Y(W) holds, W≤Y also holds. Boolean algebra gives W=b there. Since □Zb was already obtained at v, Leibniz substitution gives ZW there. Therefore □(R_Y(W)→ZW) also holds in this case.

Consequently every current A-member necessarily satisfies the predicate H(W):=R_Y(W)→ZW. Weak inextensibility of A at v gives A≤H. Since R_Y≤A, this implies R_Y≤Z. Thus R_Y is weakly inextensible at every v and is inextensible at the original point.

No Z from v has been replaced by an earlier/root Z. Inextensibility of A quantifies over all Z existing at v. Likewise Y may first appear at v: the proof is a C derivation from N(A) for arbitrary Y at its evaluation point, and N(A) remains true there. Formally, necessitate the *discharged C theorem* N(A)→∀Y Rigid(R_Y), then use N(A)→□N(A). This avoids any illicit necessitation from RC.

The bottom condition is essential to this proof. Without A b, a W lying below ¬Y can later become bottom and thereby satisfy W≤Y without giving the earlier premise any representative from which □Zb follows. The proof has not silently assumed nonbottomness persists.

## 4. Representation of all future entities by rigid cuts

Under N(A), C proves, and by stability proves necessarily,

    ∀Y^σ [Rigid(R_Y) ∧ R_Y≤A ∧ Y=J(R_Y)].

Only the identity needs checking. At any subsequent point and tuple, a witness W for J(R_Y)[x̄] entails Y and satisfies W[x̄], so Y[x̄]. Conversely, if Y[x̄], N4 gives J(A)[x̄], hence a current W with AW and W[x̄]. N3 gives W≤Y∨W≤¬Y. The second case contradicts the current truths W[x̄] and Y[x̄]. The first makes W an R_Y-witness. This is necessary coextension over all subsequent points and tuples; C's Intensionality gives identity.

Thus

    □∀Y ∃R [Rigid(R) ∧ R≤A ∧ Y=J(R)].

This formula explicitly quantifies over future Y and supplies R there by the uniform lambda expression R_Y. No future application of RC is involved. This is the decisive difference from the documented gap in the book's earlier proof.

## 5. Pullback through the rigid-subset property

Put P_A(R):=Rigid(R)∧R≤A. To derive BF_σ, it is enough that **P_A is weakly inextensible at the actual point**. Full rigidity of P_A is stronger than necessary.

Assume ∀Y^σ □XY. For each actual P_A-member R, the actual entity J(R) exists, so □X(J(R)). Weak inextensibility of P_A, tested on R↦X(J(R)), gives

    □∀R [P_A(R)→X(J(R))].

At every future point, the representation in Section 4 gives, for every current Y, some current R with P_A(R) and Y=J(R). Hence XY. Therefore □∀Y XY, which is BF_σ.

Rigid Power at σt supplies full rigidity, and hence weak inextensibility, of P_A from Rigid(A). This verifies the three-premise typewise theorem in the draft.

For the sharper local theorem, use only Steps 1–2 of `atomicity-and-rigid-comprehension-imply-rigid-power.md`. Applied to the rigid F=A of type σt, those steps show:

    Atomicity_((σt)t) + RC_(σt) ⇒ WeaklyInextensible(P_A).

The atom is at the type of the power predicate (σt)t. The rigid replacement constructed in the pullback lemma is at σt, exactly the RC instance already used for A. Step 3's extra RC at (σt)t merely upgrades the power predicate to full rigidity, which Section 5 does not need. Therefore

    SL_σ + RC_(σt) + Atomicity_((σt)t) ⇒ BF_σ.

Finally RC_(σt) yields Tame Rigidity at that type. BF_σ says that the universal predicate top_(σt) is weakly inextensible; it is persistent in C. Tame Rigidity makes it rigid, whose inextensibility is □BF_σ. Thus the same three localized premises imply **□BF_σ**, without an additional higher-type RC assumption.

## 6. The separate boxed-Strong-Leibniz theorem

N(A) alone implies □SL_σ. At an arbitrary future point take Y≠b. Suppose no current nonzero A-member lies below Y. For each current AW, N3 says W≤Y∨W≤¬Y. In the first case the supposition makes W=b, so W≤¬Y anyway. Hence every current A-member lies below ¬Y.

Each inequality W≤¬Y is an identity, and NI makes it necessary. Weak inextensibility of A applied to W↦W≤¬Y gives

    □∀W (AW→W≤¬Y).

It follows that J(A)≤¬Y. N4 makes the left side top, so Y=b, contradiction. Thus some current W is nonbottom, satisfies AW, and lies below Y. Persistence of A and N3 give □D(W), so this W is a strong world. This proves SL_σ at the arbitrary point. No Atomicity at another type and no Rigid Power was used.

Accordingly SL_σ+RC_(σt)⇒□SL_σ. It is useful to record this separately from the Barcan result because its hypotheses are substantially smaller.

## 7. Consequences and limits

At the all-relational-type schema level, SL supplies the localized Atomicity needed in Section 5. Hence

    SL + RC ⇒ □SL + □BF_rel.

In particular this proves the mathematical claim of the old conjectured record, whose premise □SL is stronger. The proof is new source material; the old source proof should retain its documented gap rather than be silently rewritten as though the book contained the repair.

Together with the existing Atomicity+BF_rel⇒SL theorem, RC therefore gives the exact relative equivalence

    SL ⇔ (Atomicity + BF_rel).

Under RC either side also entails the boxed versions of SL and BF_rel. This does not prove boxed RC, C5, ND, or BF_e. The root proof genuinely permits strong worlds to collapse to bottom. The distinction between relational types and the individual type remains essential.

## 8. Validation

The first `python3 scripts/pmap.py validate` attempt used a shell runtime lacking PyYAML/jsonschema. The requested command was then rerun with the already-installed `/tmp/classicism-research-venv/bin` on PATH and passed: 132 principles, 447 results, 162 models, OK. Existing informational notes remain. This report and the companion profile audit are separate temporary research files; no record status or certificate has been changed.

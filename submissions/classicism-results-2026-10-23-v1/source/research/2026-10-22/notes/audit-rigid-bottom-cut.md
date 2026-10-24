# Audit: a rigid cover containing bottom

Independent mathematical audit, OpenAI GPT-6, 22 October 2026.

Audited proposal: `/tmp/rigid-bottom-cut-proof.md`. No Lean work, database edits, or build was performed. The argument below is a reconstruction and strengthening of the proposed new argument; it is not attributed to the published sources whose definitions and background lemmas it uses.

## Verdict

I find the proposal sound in the fixed relational Classicism C, subject to the recorded ordinary C theorems about algebraic entailment, S4, and necessity of identity. In particular, no instance of Rigid Comprehension at a future world is tacitly used. Adding bottom to the initial rigid cover repairs the specific future-collapse problem that otherwise prevents its cuts from being inextensible.

There is a useful direct strengthening:

> At each relational type σ, Strong Leibniz at σ and Rigid Comprehension at σt imply □Strong Leibniz at σ.

This direct implication uses neither Rigid Power nor Atomicity at any extra type. Together with the proposal and the recorded auxiliary results, the schema-level conclusion is

> Strong Leibniz + Rigid Comprehension ⇒ □Strong Leibniz + □BF at every relational type.

It says nothing about BF at individual type e.

## Exact background checked

The topic guide, `topic.yaml`, and `background.md` §§Framework, Notation (algebraic order, rigidity), and strong/weak worlds fix the following conventions. A relational type is σ=σ₁…σₙt, including σ=t. Put b=⊥σ and

D(W) := ∀Y^σ (W≤Y ∨ W≤¬Y).

Strong-worldhood is W≠b ∧ □D(W). Rigid(A) means persistence plus boxed weak inextensibility. Thus both conjuncts carry a leading box, and rigidity is inherited at all accessible worlds. Algebraic order is equivalent in C to necessary universal implication and is itself necessary, because it is an identity. Necessary coextension implies identity by C's Intensionality theorem. These uses do not infer identity from merely actual coextension under an optional premise.

The relevant local records are:

- `principles/strong-leibniz-r.yaml`, `principles/rigid-comprehension-r.yaml`, `principles/rigid-power-r.yaml`, and `principles/barcan-relational.yaml`.
- `results/strong-leibniz-necessary-rigid-comprehension-and-rigid-power-imply-bf-relational.yaml` (Dorr's existing salvage, whose □RC assumption the proposed cut lemma removes).
- `writeups/necessary-strong-leibniz-and-rigid-comprehension-imply-necessary-bf-relational.md` (the previously diagnosed gap).
- `writeups/atomicity-and-rigid-comprehension-imply-rigid-power.md`.
- `results/rigid-comprehension-implies-tame-rigidity.yaml` and `results/tame-rigidity-and-bf-relational-imply-necessary-bf-relational.yaml`.

Published/source locators supplied by those records: Classicism, draft 16 May 2023, §1.5 pp. 16–17 (Intensionality, T and the elementary modal framework), §2.2 pp. 23–24 (Boolean lattice), §2.3 pp. 28–30 (rigidity); Bacon, A Philosophical Introduction to Higher-Order Logics, §8.2 pp. 165–166 (strong worlds), pp. 169–170 (the theorem with the identified gap); Bacon, Could the truths of mathematics have been different?, draft 9 October 2025, Appendix C.2 pp. 15–16 (the Rigid Power argument used in the map). I inspected the local definitions/proofs, not those entire source documents.

## 1. Construct and seal the cover

Assume SLσ and RCσt. Choose A^(σt) rigid and actually coextensive with

λW (SWorldσ(W) ∨ W=b).

Write J(B):=λx̄ ∃W^σ(BW ∧ W[x̄]), for B^(σt).

Three facts are available at the initial point:

(1) □Ab. Actual Ab follows from the stipulated coextension. Persistence of A gives □Ab.

(2) □∀W(AW→D(W)). If actual AW, then W is a strong world or W=b. In the first case □D(W) is its definition. In the second case □D(W) follows by NI and the Boolean theorem that bottom lies below everything. Thus ∀W(AW→□D(W)). Apply weak inextensibility of A to λW D(W). The result A≤λW D(W) is exactly (2). Crucially, the quantifier over Y in D stays *inside* the resulting box.

(3) J(A)=⊤σ, equivalently □∀x̄ J(A)[x̄]. For every actual strong world W, actual AW and persistence give □AW. Hence W≤J(A): at any accessible world any W-instance witnesses the existential in J(A). The dual form of SLσ implies J(A)=⊤σ. This dual form uses SL only at the initial point.

Let H(A) be the conjunction of Rigid(A), (1), (2), and (3). Every conjunct of H(A) is a necessary condition: use S4 for the explicit boxes, and NI for (3), or its displayed boxed formulation. Hence H(A)→□H(A) is an instance of elementary C reasoning. The optional initial coextension does *not* occur in H(A), and is never transported.

## 2. The bottom-cut lemma

Assume H(A). Fix an arbitrary accessible world v and an entity Y^σ present there. Define at v

R_Y := λW (AW ∧ W≤Y).

This is an admitted term of type σt; no comprehension axiom is needed to form it. It is persistent because A is persistent and algebraic entailment is necessary.

To prove inextensibility, work at any further world u, with an arbitrary predicate Z^(σt) there such that

(*) ∀W(R_Y W → □ZW).

The same parameters A,Y and the cut term are interpreted at u by ordinary term transport. We prove R_Y≤Z at u.

Since □Ab and b≤Y, the bottom entity belongs to R_Y at u. By (*) we have □Zb at u.

Now fix a current A-instance W at u. By (2), W≤Y or W≤¬Y.

- If W≤Y, then current R_Y W, so □ZW by (*), and consequently □(R_Y W→ZW).
- If W≤¬Y, NI makes that entailment persist at every later world. At any such world where R_Y W holds, W≤Y also holds. Boolean algebra gives W≤Y∧¬Y=b, and therefore W=b *at that later world*. The already established □Zb then gives ZW there. Consequently □(R_Y W→ZW) also in this case.

Thus every current A-instance satisfies □(R_Y W→ZW). Weak inextensibility of A at u, applied to the actual predicate λW(R_Y W→ZW), gives

□∀W(AW→(R_Y W→ZW)).

By definition R_Y≤A, so R_Y≤Z. This proves weak inextensibility of R_Y at arbitrary u, and hence its inextensibility at v. Together with persistence, R_Y is rigid at v.

The argument is a C derivation from H(A). Since H(A) is necessary and v was arbitrary, it gives

□∀Y^σ Rigid(R_Y).

There is no necessitation of a theorem obtained merely from unboxed optional SL or RC. Those premises were used once to produce A and H(A); the later argument uses only H(A).

### Why bottom is decisive

If A lacked bottom, a current A-instance W below ¬Y could later collapse to bottom and enter the Y-cut. Such W need not have been an actual cut member, so (*) would supply no □ZW. With bottom in the cut, □Zb is already known, and local W=b handles precisely this case. The proof never needs W≠b to be necessary; it permits collapse explicitly.

## 3. Representation at every world

At v, for arbitrary Y, prove Y=J(R_Y) by necessary coextension.

At any u accessible from v:

- A witness W to J(R_Y)[x̄] satisfies W≤Y and W[x̄], so Y[x̄].
- If Y[x̄], (3) gives a W with AW and W[x̄] at u. By (2), W≤Y or W≤¬Y at u. The second case would imply ¬Y[x̄], contradiction. Thus W≤Y and W witnesses J(R_Y)[x̄].

All quantifiers here are local to u: the tuple x̄ and the witness W need not have existed at v or at the initial point. Nothing is transported backwards. Because (1)–(3) hold throughout the accessible region, the argument proves

□∀Y^σ (Y=J(R_Y) ∧ R_Y≤A ∧ Rigid(R_Y)).

The identity uses C's necessary-coextension theorem, not an unrestricted application of Logical Equivalence under optional assumptions.

## 4. Direct necessary Strong Leibniz

This is the additional consequence worth recording separately if records are later authorized.

At arbitrary v, take any Y^σ with Y≠b. The cut R=R_Y is rigid and Y=J(R).

Suppose there were no W at v with RW and W≠b. Then every current R-instance W equals b. By necessity of identity, every such W satisfies □(W=b). Weak inextensibility of R, applied to the predicate λW(W=b), yields

R≤λW(W=b), i.e. □∀W(RW→W=b).

It follows that J(R)=b: at every accessible u, any hypothetical witness W to J(R)[x̄] would be bottom and hence could not hold of x̄. Necessary coextension with bottom gives identity. This contradicts Y=J(R) and Y≠b at v.

Therefore some W exists at v with RW and W≠b. By RW, AW and W≤Y. Persistence of A gives □AW; (2) gives □(AW→D(W)) for this current W. Hence □D(W). Thus SWorldσ(W), and W≤Y.

This proves SLσ at arbitrary v from H(A), so □SLσ at the initial point. The complete typed implication is

SLσ + RCσt ⇒ □SLσ.

## 5. Direct necessary BF

Further strengthening proposed by the coordinating agent and audited here: the same construction proves **□BFσ directly**, without the separate Tame Rigidity lemma.

Assume also Rigid Power at σt, at the initial point only. Applied to rigid A, it makes

P_A := λR^(σt) (Rigid(R) ∧ R≤A)

rigid. Rigidity is a necessary condition, so P_A remains rigid at every accessible world. This is one initial application of Rigid Power, not an assumption of its boxed form.

Now fix an arbitrary accessible v and an arbitrary **local** X^(σt) there satisfying ∀Y^σ □XY. Every current P_A-instance R satisfies □X(J(R)), simply by universal instantiation at the current term J(R). Weak inextensibility of P_A at v, applied to λR X(J(R)), gives

□∀R(P_A R→X(J(R))).

The sealed boxed representation from §3 provides, at each u accessible from v and for each Y local to u, a local R with P_A R and Y=J(R). Substitution yields XY at u. Therefore □∀Y XY at v.

Thus BFσ holds at arbitrary v, with its X and Y quantifiers interpreted locally. All supporting conditions—H(A) and Rigid(P_A)—were sealed at the initial point. We have proved the sharper typed implication

SLσ + RCσt + RigidPowerσt ⇒ □BFσ.

Combined with §4, these premises give □SLσ and □BFσ directly. The proof never transports the optional BF antecedent ∀Y□XY from the initial point; it is assumed anew for arbitrary X at each v, as required by □BF.

At the schema level, SL gives Atomicity, and the checked local theorem Atomicity + RC gives Rigid Power. Thus SL + RC gives both boxed conclusions. Tame Rigidity and the recorded BF-to-boxed-BF theorem remain a valid alternative route, but are not needed for this direct proof.

### Dependency accounting

- §§1–4: SL at σ and RC at σt only.
- □BFσ via §5: additionally Rigid Power at σt, initially only.
- Deriving that instance of Rigid Power using the recorded proof needs Atomicity at (σt)t, RC at σt, and RC at (σt)t.
- No additional instance of Tame Rigidity, □RP, □RC, or BF is needed to box the result.
- All these are admitted relational types even when σ contains individual arguments; no forbidden function type ending in e appears.
- No Choice, BF, □RC, ND, C5, extensionality, or future SL was silently used in §§1–4.

## 6. Recorded evidence versus new work

I ran a narrow query through `scripts.pmap.load_topic` and `Engine` using proved results and proved models only, with no optional engine background. The explicit premise set was `['strong-leibniz-r', 'rigid-comprehension-r']`.

For each of `barcan-relational`, `necessary-barcan-relational`, and `necessary-strong-leibniz-r`, `entails` returned false, `excludes` returned None, and `separates` returned no model. This means the local database had neither a recorded proof nor a recorded separation for these implications; it makes no claim about the literature.

For `rigid-power-r`, `entails` returned the recorded chain `strong-leibniz-r-implies-atomicity-r` followed by `atomicity-and-rigid-comprehension-imply-rigid-power`.

The only corrections I recommend to the proposal are expository: spell out the C Intensionality/algebraic-inequality route to identities; explicitly say that all Y,Z introduced later are locally quantified; and include §4 if the claimed conclusion includes □SL. I found no mathematical defect requiring a repair.

## 7. Scope check: no proof of necessary completeness or necessary rigid comprehension

The sealed covers do not immediately provide □Boolean Completeness or □Rigid Comprehension. Neither conclusion is established in this audit.

At a future v let X^(σt) be an arbitrary family of σ-entities. Every current Y has its rigid cut R_Y⊆A. The tempting union

    B := λW ∃Y (XY ∧ R_Y W)

is an admitted property, and is the actual union of the chosen cuts. But its defining index condition XY is arbitrary and may cease to hold. Even though each individual R_Y is rigid, B need not be persistent or inextensible. Consequently J(B) has not been shown to be an algebraic upper bound, much less a least upper bound, of the current X-family. Replacing the family by its upward- or downward-closure does not on its own repair the missing transport of membership.

Rigid(P_A) supplies inextensibility for the property of already-rigid subproperties of A. It does not assert that every arbitrary current subcollection has a rigid representative, or that every arbitrary current subset of A is represented by a member of P_A. Assuming either of those fullness properties at v would reintroduce the local comprehension obligation we are trying to derive.

There is also no valid general shortcut from the obtained boxed lattice/modal consequences to boxed Rigid Comprehension. The local record `necessary-atomicity-completeness-bf-imply-rigid-comprehension.yaml` is explicitly conjectured and refuted by `models/ultralimit-fork.yaml`: that model has □Atomicity, □Boolean Completeness, □BF and □Actuality but fails Rigid Comprehension. This does not refute the present stronger premises or sealed-cover data; it shows that any additional propagation proof must use that data substantively.

By contrast, □Strong Actuality is an immediate recorded consequence of the new □SL schema: apply the necessary version of Strong Leibniz at t ⇒ Strong Actuality. This is a legitimate consequence and does not address the missing local family-rigidity step above.

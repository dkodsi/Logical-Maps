# Strong Leibniz and Rigid Comprehension imply BF at relational types

Proposed new argument, GPT-6 (OpenAI), 22 October 2026. This is a mathematical proof draft, not a claim of Lean verification. All premises are unboxed unless explicitly displayed.

Fix a relational type sigma = (sigma_1 ... sigma_n)t, allowing n = 0, and let b = bottom_sigma. Put

D(W) := forall Y^sigma . (W <= Y or W <= not Y).

Thus SWorld(W) says W != b and box D(W). For A^(sigma t), put

J(A) := lambda xbar . exists W^sigma . A W and W[xbar].

We use the ordinary modal and Boolean theorems of C, especially S4, necessity of identity, and the identification of algebraic entailment with necessary universally quantified implication. Nothing identifies coextensions merely from an optional assumption.

## 1. A rigid cover by deciding entities, including bottom

Assume Strong Leibniz at sigma and Rigid Comprehension at sigma t. Choose A rigid and actually coextensive with

lambda W . SWorld(W) or W = b.

We have:

(a) box A b, since A b and A is persistent.

(b) box forall W . (A W -> D(W)). Every actual A-instance W is either a strong world, in which case box D(W) by definition, or b, which necessarily decides every Y. Thus forall W . A W -> box D(W), and weak inextensibility of A, tested on lambda W . D(W), gives A <= D, which is precisely (b). This step covers newly existing future Y: D's universal quantifier remains inside the transferred box.

(c) J(A) = top_sigma, equivalently box forall xbar . J(A)[xbar]. For every actual strong world W, A W and persistence give box A W. Consequently W <= J(A). The dual of Strong Leibniz at sigma makes J(A) the top element. Equivalently, if its Boolean complement were nonbottom, Strong Leibniz would give a strong world W below that complement and below J(A), a contradiction.

Rigidity of A and (a)-(c) are necessary: rigidity has a leading box; (a)-(b) already carry boxes and 4 propagates them; (c) is an identity of rigidly denoting terms (and the displayed boxed formulation directly propagates by 4).

## 2. Bottom makes the cuts rigid

This lemma is the new step. Suppose A is rigid and satisfies (a)-(b). For any Y^sigma define

R_Y := lambda W . A W and W <= Y.

Then R_Y is rigid. Its persistence follows from persistence of A and of algebraic entailment. To prove its weak inextensibility at an arbitrary accessible world v, take any predicate Z satisfying

forall W . R_Y W -> box Z W

there. Because A b holds at v and b <= Y, R_Y b holds, and hence box Z b. Take any current A-instance W at v. By (b), either W <= Y or W <= not Y.

- If W <= Y, then R_Y W, so box Z W, in particular box(R_Y W -> Z W).
- If W <= not Y, that entailment is necessary. At every further world where R_Y W holds, W <= Y also holds. Boolean reasoning then gives W = b, and box Z b gives Z W. Hence again box(R_Y W -> Z W).

Therefore forall W . A W -> box(R_Y W -> Z W). Apply weak inextensibility of A to the predicate lambda W . (R_Y W -> Z W). We get

box forall W . A W -> (R_Y W -> Z W).

Since R_Y <= A, this yields R_Y <= Z. Thus R_Y is weakly inextensible at v. The argument applies under a box, using only the necessary conditions on A and the currently quantified Y and Z, so R_Y is inextensible at the initial point. Together with persistence, R_Y is rigid.

In particular this construction works at every accessible world and for every Y existing there. It does NOT use Rigid Comprehension at that world. The inclusion of bottom in A is essential: otherwise a world below not Y can enter the cut by becoming bottom, without having a previously included representative.

## 3. Every entity is the join of its cut

Under (a)-(c), at every accessible world and for every Y of type sigma,

Y = J(R_Y), and R_Y <= A.

The latter is definitional. For the identity, at any further world and tuple xbar, J(R_Y)[xbar] implies Y[xbar], since every witness W entails Y. Conversely, suppose Y[xbar]. By (c), choose W with A W and W[xbar]. By (b), W <= Y or W <= not Y. The second case contradicts Y[xbar] and W[xbar]. Thus W <= Y, hence R_Y W and J(R_Y)[xbar]. This is necessary coextension, so identity in C; equivalently prove both algebraic inequalities.

Combining sections 2 and 3 gives

box forall Y^sigma . exists R^(sigma t) . Rigid(R) and R <= A and Y = J(R).

## 4. Rigid Power gives BF

Assume Rigid Power at sigma t. Its instance at rigid A says that

P_A := lambda R^(sigma t) . Rigid(R) and R <= A

is rigid. Let X^(sigma t) satisfy forall Y^sigma . box X Y. For each actual R with P_A R, the entity J(R) exists at the evaluation point, so box X(J(R)). Weak inextensibility of P_A, applied to lambda R . X(J(R)), gives

box forall R . P_A R -> X(J(R)).

Together with the boxed representation in section 3 this gives box forall Y . X Y. That is BF at sigma.

Therefore, type by type:

Strong Leibniz at sigma + Rigid Comprehension at sigma t + Rigid Power at sigma t -> BF at sigma.

At the schema level, Strong Leibniz implies Atomicity, and the recorded theorem Atomicity + Rigid Comprehension -> Rigid Power supplies the third premise. We conclude

Strong Leibniz + Rigid Comprehension -> BF (relational types).

Rigid Comprehension also gives Tame Rigidity, and the recorded theorem Tame Rigidity + BF (relational types) -> box BF (relational types) yields the stronger conclusion

Strong Leibniz + Rigid Comprehension -> box BF (relational types).

This implies the recorded conjecture with box Strong Leibniz as premise, by T. It does not address BF at the individual type e.


## 5. Strong Leibniz itself becomes necessary

The stable cover from section 1 gives a further conclusion before any use of Rigid Power. At any accessible point take Y≠b and put R=R_Y. Sections 2–3 give R rigid and Y=J(R). If every actual R-member W were bottom, necessity of identity would give □(W=b) for every such member. Weak inextensibility of R, applied to λW(W=b), would then give □∀W(RW→W=b), and hence J(R)=b. This contradicts Y≠b. Therefore some current W satisfies RW and W≠b. Since AW, persistence of A together with the necessary deciding condition (b) gives □D(W). Thus W is a strong world below Y. The proof works at every accessible point using only the stable cover, so

    SL_sigma + RigidComprehension_(sigma t) -> box SL_sigma.

At schema level, the two strengthened conclusions are therefore

    Strong Leibniz + Rigid Comprehension
      -> box Strong Leibniz + box BF (relational types).

This is an ordinary mathematical repair of the existing conjecture, with weaker initial premises. Independent mathematical audits found no hidden future comprehension, Barcan, or necessitation assumption. No human check or Lean verification is claimed, and the published proof and database record remain unchanged.

## 6. The boxed Barcan conclusion is already type-local

Later independent audits sharpen section 4's dependency statement. The exact typed result is

    SL_sigma + RigidComprehension_(sigma t) + RigidPower_(sigma t)
      -> box BF_sigma.

Indeed, the root Rigid Power instance makes P_A rigid and hence necessarily rigid. The cover conditions and the representation in section 3 are already necessary. At any reached world, take its locally quantified predicate X with forall Y box X Y. Every current P_A-member R supplies the current entity J(R), so box X(J(R)). Weak inextensibility of P_A gives box forall R(P_A R -> X(J(R))), and the sealed representation gives box forall Y X Y. Thus BF holds at every reached world directly. This needs neither Tame Rigidity, boxed Rigid Power, future Rigid Comprehension, nor transport of a root universally quantified premise. The all-schema corollary in section 4 remains valid and has this shorter dependency route.

This refinement was checked independently in the audit report `notes/INDEPENDENT-AUDIT-REPORT-01a164ea.md` and `notes/audit-rigid-bottom-cut.md`. It is an addition to this session's proof draft, not an alteration of the existing source proof or database record.

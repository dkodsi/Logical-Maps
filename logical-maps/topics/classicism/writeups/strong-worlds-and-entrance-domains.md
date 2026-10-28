# Strong worlds and restricted entrance domains

Necessary Strong Atomicity does not supply relational Barcan. Conversely, current full Strong Atomicity together with current full Barcan and necessary Atomicity does not ensure that either Strong Atomicity or Barcan persists. The two models below give these conclusions at exact admitted types in ordinary ZFC.

These are the existing 26 October 2026 constructions. This integration independently checks the all-type domain restrictions, closure under lambda abstraction and quantifiers, the behavior of whole-profile atoms, and the explicit Barcan witnesses. Individuals remain a fixed singleton in both models. In particular no failure involving individuals is substituted for a relational-domain failure.

The source's common abstraction-closure argument is retained in full, since a proposition-algebra sketch would not establish soundness for C. The source's separate positive Strong-Actuality theorem is already handled by another staged result and is not duplicated here.

## 2 Definitions and a profile semantics lemma

For τ=σ₁⋯σₙt, with n possibly zero, write 0_τ for bottom, ≤_τ for the Boolean entailment order, and

\[
\begin{aligned}
\operatorname{Dec}_\tau(W)
  &:=\forall Y^\tau\,(W\le_\tau Y\lor W\le_\tau\neg_\tau Y),\\
\operatorname{SWorld}_\tau(W)
  &:=(W\ne0_\tau)\land\Box\operatorname{Dec}_\tau(W),\\
\mathrm{SL}_\tau
  &:=\forall X^\tau\,(X\ne0_\tau\to
       \exists W^\tau(\operatorname{SWorld}_\tau(W)\land W\le_\tau X)).
\end{aligned}
\]

The universal quantifier in the boxed Dec clause ranges over the whole domain at the reached object. It is never restricted to transports of source entities.

We use ordinary full action-model intensions at a target object s, then put a carefully restricted domain at one new entrance object r. The construction of those restricted domains, including abstraction closure, is part of the proof.

### 2.1 The full target hierarchy

Let the target's endomorphism monoid be M. Its individual domain is a singleton, with trivial action. Define the relational domains recursively by

\[
D_s(\tau)=\mathcal P\left(M\times
       \prod_{i=1}^nD_s(\sigma_i)\right).
\tag{2.1}
\]

For an empty argument tuple this is P(M), the proposition domain. Equivalently, F is an arbitrary profile m↦F_m, where F_m is a subset of the product of the target argument domains. These are sets at each finite type.

Transport is precomposition on the arrow coordinate:

\[
(m\cdot F)_u=F_{um}.
\tag{2.2}
\]

An application to assigned arguments is evaluated at u using the transported arguments u·a_i. Thus partial application has profile

\[
(Fa)_u(\bar b)=F_u(u\cdot a,\bar b).
\tag{2.3}
\]

A bound variable newly quantified at an arrow ranges over the target's full domain. The Boolean operations are pointwise. Equality has the actual diagonal as its extension at every arrow; applying it to transported parameters gives the usual possibly coalescing identity propositions. Quantification at the identity uses all current target arguments, and its operation has the same profile at every arrow. These are the standard full action semantics.

In particular every logical constant is fixed by every monoid action. Structural induction gives naturality for every term T:

\[
m\cdot\llbracket T\rrbracket_s(\rho)
 =\llbracket T\rrbracket_s(m\cdot\rho).
\tag{2.4}
\]

The λ step evaluates a future bound variable over the whole target domain. It does not assume surjectivity of m on that domain.

### 2.2 Entrance profiles and their soundness obligations

At r the individual domain is again a singleton. At a relational type τ, a root entity consists of:

- an arbitrary current extension A⊆∏D_r(σ_i); and
- a permitted compatible family of target entities, one for each arrow r→s.

The families allowed in the two models are specified below. The current extension A is unrestricted, including when the argument types are themselves relational. The domains are defined recursively on types using these two clauses.

Application is (2.3), with the appropriate arrow's transport of a root argument. Root equality uses equality of complete root entities, not merely equality of their current extensions. Root quantification uses the entire root argument domain. Their target components are exactly the target logical operations.

Here is the needed soundness check. In each construction:

1. the target components of all logical constants are permitted;
2. permitted target families are closed under application;
3. the target component of a λ-abstraction with finitely many root parameters is permitted.

The unrestricted current-extension clause supplies the root component of every abstraction. Once (1)–(3) hold, β and η hold by evaluation at every current and future profile coordinate. H's quantifier, identity and Boolean truth rules hold at each object. If H proves two matrices equivalent, they agree at every profile coordinate and every assignment of the abstracted variables. Their λ-abstractions are therefore the same profile. This verifies C's Logical Equivalence rule with its **H-theoremhood restriction**. No equivalence under an optional assumption is used to identify operations.

This is an admissible profile restriction of the action semantics, rather than a claim that every profile remains admitted at r. The closure proofs below are what license the restricted construction.

## 3 Model A with an eventually stationary entrance

Take M=(N,+), with identity 0 and successor action S=1·. The category has objects r,s, no arrows s→r, only identity at r, and arrows h_n:r→s for n≥0 with

\[
k_mh_n=h_{m+n}.
\]

At s use the full hierarchy (2.1). Define the eventual-stationarity subset of each target relational domain by

\[
\operatorname{ES}_\tau
 :=\{b\in D_s(\tau):\exists N\ (S^{N+1}b=S^Nb)\}.
\tag{3.1}
\]

The integer N is external construction data. No object-language arithmetic or choice principle is assumed. At r put

\[
D_r(\tau)=
\mathcal P\left(\prod_iD_r(\sigma_i)\right)
\times\operatorname{ES}_\tau.
\tag{3.2}
\]

Transport sends (A,b) along h_n to S^n b. This is compatible with composition. An eventual fixed point stays fixed, so (3.1) equivalently says that the raw target extensions b_n are constant for all sufficiently large n.

### Closure and C

The target components of logical constants are fixed by S and therefore belong to ES. If b and c become fixed after stages N and L, naturality of application makes bc fixed after max(N,L).

For an arbitrary λ-term with root free parameters a₁,…,a_j, choose one stage N beyond the eventual-stationarity stages of all their target components. At that stage the transported environment is fixed by S, including individual parameters because the individual domain is a singleton. By (2.4), the target interpretation of the entire λ-term is then fixed by S. This proves abstraction closure, uniformly over all values of its bound variables. An infinite target domain causes no problem: only the finitely many **free** parameters need a common stage. The lemma of §2.2 now proves C.

### Every atom is strong at both objects

At r the following singleton-coordinate relations are admitted at every relational type:

- a single current root argument tuple, with zero target component;
- a single target profile coordinate (n,ā), with empty root extension.

The second has target component δ_(n,ā), which becomes zero after n+1 shifts, so belongs to ES. Every nonzero root relation has a nonempty current extension or a nonempty target coordinate. It consequently contains one of these singleton-coordinate relations. They are atoms because the Boolean order is inclusion of the complete profiles.

A current-coordinate atom becomes zero along every h_n. A target-coordinate atom becomes δ_(j−n,ā) along h_n when n≤j, and zero otherwise. At s the same computation applies to shifts. Every nonzero image is a singleton profile and hence an atom in the **full target domain**, not merely among transported objects. Zero also decides every target relation. Each displayed atom thus satisfies Box Dec and is a strong world.

The full target hierarchy itself has all singleton-coordinate atoms, with exactly this stability property. Therefore SL_τ holds at r and s for every relational τ, and

\[
\mathcal A,r\models\Box\mathrm{SL}_\tau
\quad\text{for every relational }\tau.
\tag{3.3}
\]

### A pure propositional Barcan counterexample

A root proposition is a bit ε for its truth at r together with a finite or cofinite subset B⊆N. At s, propositions are arbitrary subsets of N. Define the admitted, pure predicate

\[
P(p):=\Diamond\Box p\lor\Diamond\Box\neg p.
\tag{3.4}
\]

Every finite/cofinite B is eventually constantly false/true. Thus P(p) holds at r for every root p, and at every successor for its transported value. Hence

\[
\mathcal A,r\models\forall p\,\Box P(p).
\]

At s take the proposition of even integers. Neither it nor its complement ever becomes necessary, so P is false of it. Consequently

\[
\mathcal A,r\not\models\Box\forall p\,P(p).
\tag{3.5}
\]

This is a direct failure of BF_t with a pure definable predicate. It does not infer BF failure merely from nonsurjectivity of a transport.

### The failure extends to each relational quantified type

Fix a relational type τ. In the full target there is an admitted operation L_τ:ττ whose action is b↦Sb. Its raw profile is independent of the outer arrow coordinate: on an input b and remaining tuple ā it reads b's coordinate 1 at ā. Applying it at coordinate m therefore reads b at m+1. Thus L_τ itself is S-fixed.

Choose a root operation E_τ:ττ with target component L_τ and any current extension, for example empty. It is admitted by (3.2). Put

\[
P_\tau(Y):=\Diamond(E_\tau Y=Y).
\tag{3.6}
\]

Every root Y has an eventually stationary target component. Therefore (3.6) holds at r and at every successor for every such transported Y: eventually the shift equals itself. This proves ∀Y Box P_τ(Y) at r.

In the full target, take Z with raw extension all tuples at even coordinates and no tuples at odd coordinates. It never becomes fixed by S. Therefore P_τ(Z) is false, and Box ∀Y P_τ(Y) fails at r. The type ττ is admitted because τ is relational. This supplies a direct BF_τ counterexample for every τ≠e.

BF_e holds necessarily: every individual domain is the same singleton and all individual transports are identity. At s, all relational transports are surjective because an arbitrary profile can be extended backwards by finitely many arbitrary coordinates; full action semantics then gives BF at every type there. The counterexample is specifically the restricted entrance.

## 4 Model B with a cofinite entrance to an idempotent action

Take M={1,k}, with k²=k≠1, and use the full target hierarchy (2.1). Add r with arrows

\[
h_n:r\to s\quad(n\in N),\qquad b:r\to s,
\]

where kh_n=b and kb=b. There are no arrows s→r and only identity at r. Associativity follows from k²=k.

At a relational type τ, a root entity has an arbitrary current extension A and target data

\[
(d_\infty,(d_n)_{n\in N})
\]

such that

\[
k\cdot d_\infty=d_\infty,
\qquad k\cdot d_n=d_\infty\ (\forall n),
\qquad d_n=d_\infty\text{ for all but finitely many }n.
\tag{4.1}
\]

Its images at b and h_n are d_∞ and d_n respectively. Equivalently, write a target relation as its two raw extensions (U,V). Then d_∞=(V,V), each d_n=(U_n,V), and U_n=V for all but finitely many n. The finite exceptional set is external construction data, with no common bound across entities.

### Closure and C

Logical constants have constant target profile and satisfy (4.1). Compatibility under k is preserved by term naturality. For a λ-term with finitely many free parameters, take the union of their finite exceptional sets. Outside it, the environments at h_n and b are identical; the target interpretations of the whole λ-term are therefore identical. At b the environment is k-fixed, so naturality makes the result k-fixed as well. Application is included in the same argument. All arbitrary current extensions needed for root abstraction are permitted. Section 2.2 therefore proves C.

### Full current Strong Atomicity

The root admits singleton atoms at a current root tuple, and at a coordinate (h_n,ā) with ā a target tuple. For the latter, take d_n=δ_(1,ā), all other d_m=0, and d_∞=0. This satisfies (4.1) because k·δ_(1,ā)=0.

Every nonzero root relation contains one of these atoms. A nonempty current extension or an exceptional h_n extension supplies one immediately. If the common limiting extension V is nonempty, choose ā∈V and an n outside the finite exceptional set; the singleton at (h_n,ā) lies below the relation. There is no isolated atom at b.

A current-coordinate atom maps to zero at every future object. The atom at (h_n,ā) maps to δ_(1,ā) along h_n and to zero along every other h_m and along b. At s, δ_(1,ā) is an atom and its k-image is zero. Hence all these source atoms are strong with respect to every future target-domain relation. This proves full SL_rel at r.

### Strong Atomicity fails at the target

At type t, the target has four propositions P({1,k}). The nonzero proposition {k} is an atom, but

\[
k\cdot\{k\}=\{1,k\}.
\]

The target proposition {1} splits that image. Thus {k} is not a strong world, and as an atom it contains no other nonzero candidate. SL_t fails at s. Since s is accessible from r,

\[
\mathcal B,r\not\models\Box\mathrm{SL}_t.
\tag{4.2}
\]

The full target relation algebras remain atomic at every type. Together with the source calculation, this gives Box Atomicity_rel throughout the model.

## 5 Model B satisfies every current Barcan instance

The transport along each h_n is onto at every relational type. Given an arbitrary target entity d, choose d_n=d, d_∞=k·d, and d_m=d_∞ for m≠n. Idempotence verifies (4.1). Choose any root current extension. This constructs a preimage of d along h_n without imposing any condition on d. Individual transport is onto as well, because its domain is a singleton.

Fix any type σ and an admitted root predicate F:σt satisfying ∀x^σ Box Fx. At every h_n, every target x has a root preimage along h_n. Applying the premise to that preimage shows that the current target extension of h_nF is the entire D_s(σ).

The root predicate F has only finitely many exceptional h_n components. Choose n outside that finite set. The whole target entity h_nF equals bF, so the current extension of bF is also the entire D_s(σ). The original premise gives the corresponding universal truth at r by T. Thus ∀x Fx holds at r, at every h_n, and at b, proving Box ∀x Fx.

Consequently

\[
\mathcal B,r\models\mathrm{BF}_\sigma
\quad\text{for every admitted }\sigma,
\tag{5.1}
\]

including e. Notice that b need not be onto. Its lack of surjectivity cannot be detected by an admitted Barcan counterexample at r because every root predicate eventually agrees with its b-component along the surjective h_n arrows.

At s, BF_t fails by the usual full idempotent example. Let X:tt have current extension all four propositions and k-extension {0,1}. Every transported k·p is an endpoint, so ∀p Box Xp holds at s. But at k the newly quantified proposition {1} is not in that endpoint extension. Therefore Box ∀p Xp fails. Since s is accessible,

\[
\mathcal B,r\not\models\Box\mathrm{BF}_t.
\tag{5.2}
\]

This does not contradict (5.1): a target predicate can be lifted along any one h_n, but its lift need not satisfy the root Barcan antecedent along all the other arrows.


## Sources and integration review

Direct source: OpenAI Codex, prompted by Daniel Kodsi, *Strong worlds do not control modal domains*, 26 October 2026, §§2–5, unpaginated. The common profile semantics and both complete construction-specific arguments above are retained from that source; their ordinary independent integration review is dated 28 October 2026.

Background full-action semantics is Bacon and Dorr, *Classicism*, draft of 16 May 2023, Definition 3.19 and satisfaction clauses pp.55–57, and §3.5 pp.58–60. The fixed relational Strong Atomicity definitions are recorded in the map; the target singleton/idempotent calculations are reproved directly in §§3–5 above. The new restricted entrance hierarchies are the AI source's arguments, not attributed to those published background results.

The source positive theorem from current Strong Atomicity plus Rigid Comprehension entails necessary Strong Atomicity and necessary relational BF. Thus both model failures also refute full current Rigid Comprehension by existing closure; no extra primitive failure flag is needed. The first model's every-relational-type BF failure and the individual BF_e validity are recorded in the proof even though the native map uses schema nodes. Necessary strong worlds do not assert persistent nonzeroness of each world: the singleton worlds here may become zero, which still decides every target relation.

No human check or Lean certification is claimed. Validation of the candidate records does not verify these proofs.

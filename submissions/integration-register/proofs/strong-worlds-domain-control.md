# Strong worlds do not control modal domains

Research by OpenAI Codex, 26 October 2026. Direct source for the new arguments and constructions: `misc`, this report, §§2–8, unpaginated. Ordinary mathematics only.

## 1 Verdict and exact scope

**All three proposed implications are false.** Full relational Strong Leibniz alone over C implies neither propositional Barcan, nor Barcan at all relational types, nor necessary Strong Leibniz.

Two explicit models give stronger separations:

1. **Eventually stationary entrance to the full successor action** satisfies

```math
\mathrm C+\Box\mathrm{SL}_{\rm rel}+\neg\mathrm{BF}_t
```

   Indeed, every relational Barcan instance fails at the entrance, while BF at individuals holds necessarily. This refutes even necessary Strong Leibniz implying relational Barcan.
2. **Cofinite entrance to the full idempotent action** satisfies

```math
\mathrm C+\mathrm{SL}_{\rm rel}+\mathrm{BF}_{\rm all}
   +\Box\mathrm{Atomicity}_{\rm rel}
   +\neg\Box\mathrm{SL}_t+\neg\Box\mathrm{BF}_t
```

   Thus adding current Barcan at every type does not make Strong Leibniz necessary.

Here SL_rel is the full schema over every admitted type τ other than e. BF_all includes e; BF_rel excludes e. A boxed schema means the separately boxed closed instances. Neither construction assumes C5. All operations and domains use the fixed relational type system; there are no e-valued function types.

There is also a positive intermediate theorem. SL at any one relational type entails that, necessarily, every **actually instantiated** relation of that type contains a strong world. This includes the strengthening

```math
\mathrm{SL}_t\ \Longrightarrow\ \Box\mathrm{StrongActuality}
```

The possible-but-not-currently-instantiated case remains essential in the definition of SL. The second model separates the intermediate theorem from necessary SL.

## 2 Definitions and a profile semantics lemma

For τ=σ₁⋯σₙt, with n possibly zero, write 0_τ for bottom, ≤_τ for the Boolean entailment order, and

```math
\begin{aligned}
\mathrm{Dec}_\tau(W)
  &:=\forall Y^\tau\,(W\le_\tau Y\lor W\le_\tau\neg_\tau Y),\\
\mathrm{SWorld}_\tau(W)
  &:=(W\ne0_\tau)\land\Box\mathrm{Dec}_\tau(W),\\
\mathrm{SL}_\tau
  &:=\forall X^\tau\,(X\ne0_\tau\to
       \exists W^\tau(\mathrm{SWorld}_\tau(W)\land W\le_\tau X))
\end{aligned}
```

The universal quantifier in the boxed Dec clause ranges over the whole domain at the reached object. It is never restricted to transports of source entities.

We use ordinary full action-model intensions at a target object s, then put a carefully restricted domain at one new entrance object r. The construction of those restricted domains, including abstraction closure, is part of the proof.

### 2.1 The full target hierarchy

Let the target's endomorphism monoid be M. Its individual domain is a singleton, with trivial action. Define the relational domains recursively by

```math
D_s(\tau)=\mathcal P\left(M\times
       \prod_{i=1}^nD_s(\sigma_i)\right)
\tag{2.1}
```

For an empty argument tuple this is P(M), the proposition domain. Equivalently, F is an arbitrary profile m↦F_m, where F_m is a subset of the product of the target argument domains. These are sets at each finite type.

Transport is precomposition on the arrow coordinate:

```math
(m\cdot F)_u=F_{um}
\tag{2.2}
```

An application to assigned arguments is evaluated at u using the transported arguments u·a_i. Thus partial application has profile

```math
(Fa)_u(\bar b)=F_u(u\cdot a,\bar b)
\tag{2.3}
```

A bound variable newly quantified at an arrow ranges over the target's full domain. The Boolean operations are pointwise. Equality has the actual diagonal as its extension at every arrow; applying it to transported parameters gives the usual possibly coalescing identity propositions. Quantification at the identity uses all current target arguments, and its operation has the same profile at every arrow. These are the standard full action semantics.

In particular every logical constant is fixed by every monoid action. Structural induction gives naturality for every term T:

```math
m\cdot\llbracket T\rrbracket_s(\rho)
 =\llbracket T\rrbracket_s(m\cdot\rho)
\tag{2.4}
```

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

```math
k_mh_n=h_{m+n}
```

At s use the full hierarchy (2.1). Define the eventual-stationarity subset of each target relational domain by

```math
\mathrm{ES}_\tau
 :=\{b\in D_s(\tau):\exists N\ (S^{N+1}b=S^Nb)\}
\tag{3.1}
```

The integer N is external construction data. No object-language arithmetic or choice principle is assumed. At r put

```math
D_r(\tau)=
\mathcal P\left(\prod_iD_r(\sigma_i)\right)
\times\mathrm{ES}_\tau
\tag{3.2}
```

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

```math
\mathcal A,r\models\Box\mathrm{SL}_\tau
\quad\text{for every relational }\tau
\tag{3.3}
```

### A pure propositional Barcan counterexample

A root proposition is a bit ε for its truth at r together with a finite or cofinite subset B⊆N. At s, propositions are arbitrary subsets of N. Define the admitted, pure predicate

```math
P(p):=\Diamond\Box p\lor\Diamond\Box\neg p
\tag{3.4}
```

Every finite/cofinite B is eventually constantly false/true. Thus P(p) holds at r for every root p, and at every successor for its transported value. Hence

```math
\mathcal A,r\models\forall p\,\Box P(p)
```

At s take the proposition of even integers. Neither it nor its complement ever becomes necessary, so P is false of it. Consequently

```math
\mathcal A,r\not\models\Box\forall p\,P(p)
\tag{3.5}
```

This is a direct failure of BF_t with a pure definable predicate. It does not infer BF failure merely from nonsurjectivity of a transport.

### The failure extends to each relational quantified type

Fix a relational type τ. In the full target there is an admitted operation L_τ:ττ whose action is b↦Sb. Its raw profile is independent of the outer arrow coordinate: on an input b and remaining tuple ā it reads b's coordinate 1 at ā. Applying it at coordinate m therefore reads b at m+1. Thus L_τ itself is S-fixed.

Choose a root operation E_τ:ττ with target component L_τ and any current extension, for example empty. It is admitted by (3.2). Put

```math
P_\tau(Y):=\Diamond(E_\tau Y=Y)
\tag{3.6}
```

Every root Y has an eventually stationary target component. Therefore (3.6) holds at r and at every successor for every such transported Y: eventually the shift equals itself. This proves ∀Y Box P_τ(Y) at r.

In the full target, take Z with raw extension all tuples at even coordinates and no tuples at odd coordinates. It never becomes fixed by S. Therefore P_τ(Z) is false, and Box ∀Y P_τ(Y) fails at r. The type ττ is admitted because τ is relational. This supplies a direct BF_τ counterexample for every τ≠e.

BF_e holds necessarily: every individual domain is the same singleton and all individual transports are identity. At s, all relational transports are surjective because an arbitrary profile can be extended backwards by finitely many arbitrary coordinates; full action semantics then gives BF at every type there. The counterexample is specifically the restricted entrance.

## 4 Model B with a cofinite entrance to an idempotent action

Take M={1,k}, with k²=k≠1, and use the full target hierarchy (2.1). Add r with arrows

```math
h_n:r\to s\quad(n\in N),\qquad b:r\to s,
```

where kh_n=b and kb=b. There are no arrows s→r and only identity at r. Associativity follows from k²=k.

At a relational type τ, a root entity has an arbitrary current extension A and target data

```math
(d_\infty,(d_n)_{n\in N})
```

such that

```math
k\cdot d_\infty=d_\infty,
\qquad k\cdot d_n=d_\infty\ (\forall n),
\qquad d_n=d_\infty\text{ for all but finitely many }n
\tag{4.1}
```

Its images at b and h_n are d_∞ and d_n respectively. Equivalently, write a target relation as its two raw extensions (U,V). Then d_∞=(V,V), each d_n=(U_n,V), and U_n=V for all but finitely many n. The finite exceptional set is external construction data, with no common bound across entities.

### Closure and C

Logical constants have constant target profile and satisfy (4.1). Compatibility under k is preserved by term naturality. For a λ-term with finitely many free parameters, take the union of their finite exceptional sets. Outside it, the environments at h_n and b are identical; the target interpretations of the whole λ-term are therefore identical. At b the environment is k-fixed, so naturality makes the result k-fixed as well. Application is included in the same argument. All arbitrary current extensions needed for root abstraction are permitted. Section 2.2 therefore proves C.

### Full current Strong Leibniz

The root admits singleton atoms at a current root tuple, and at a coordinate (h_n,ā) with ā a target tuple. For the latter, take d_n=δ_(1,ā), all other d_m=0, and d_∞=0. This satisfies (4.1) because k·δ_(1,ā)=0.

Every nonzero root relation contains one of these atoms. A nonempty current extension or an exceptional h_n extension supplies one immediately. If the common limiting extension V is nonempty, choose ā∈V and an n outside the finite exceptional set; the singleton at (h_n,ā) lies below the relation. There is no isolated atom at b.

A current-coordinate atom maps to zero at every future object. The atom at (h_n,ā) maps to δ_(1,ā) along h_n and to zero along every other h_m and along b. At s, δ_(1,ā) is an atom and its k-image is zero. Hence all these source atoms are strong with respect to every future target-domain relation. This proves full SL_rel at r.

### Strong Leibniz fails at the target

At type t, the target has four propositions P({1,k}). The nonzero proposition {k} is an atom, but

```math
k\cdot\{k\}=\{1,k\}
```

The target proposition {1} splits that image. Thus {k} is not a strong world, and as an atom it contains no other nonzero candidate. SL_t fails at s. Since s is accessible from r,

```math
\mathcal B,r\not\models\Box\mathrm{SL}_t
\tag{4.2}
```

The full target relation algebras remain atomic at every type. Together with the source calculation, this gives Box Atomicity_rel throughout the model.

## 5 Model B satisfies every current Barcan instance

The transport along each h_n is onto at every relational type. Given an arbitrary target entity d, choose d_n=d, d_∞=k·d, and d_m=d_∞ for m≠n. Idempotence verifies (4.1). Choose any root current extension. This constructs a preimage of d along h_n without imposing any condition on d. Individual transport is onto as well, because its domain is a singleton.

Fix any type σ and an admitted root predicate F:σt satisfying ∀x^σ Box Fx. At every h_n, every target x has a root preimage along h_n. Applying the premise to that preimage shows that the current target extension of h_nF is the entire D_s(σ).

The root predicate F has only finitely many exceptional h_n components. Choose n outside that finite set. The whole target entity h_nF equals bF, so the current extension of bF is also the entire D_s(σ). The original premise gives the corresponding universal truth at r by T. Thus ∀x Fx holds at r, at every h_n, and at b, proving Box ∀x Fx.

Consequently

```math
\mathcal B,r\models\mathrm{BF}_\sigma
\quad\text{for every admitted }\sigma,
\tag{5.1}
```

including e. Notice that b need not be onto. Its lack of surjectivity cannot be detected by an admitted Barcan counterexample at r because every root predicate eventually agrees with its b-component along the surjective h_n arrows.

At s, BF_t fails by the usual full idempotent example. Let X:tt have current extension all four propositions and k-extension {0,1}. Every transported k·p is an endpoint, so ∀p Box Xp holds at s. But at k the newly quantified proposition {1} is not in that endpoint extension. Therefore Box ∀p Xp fails. Since s is accessible,

```math
\mathcal B,r\not\models\Box\mathrm{BF}_t
\tag{5.2}
```

This does not contradict (5.1): a target predicate can be lifted along any one h_n, but its lift need not satisfy the root Barcan antecedent along all the other arrows.

## 6 A positive theorem without comprehension

Fix a relational type τ=σ₁⋯σₙt, allowing n=0. Define the admitted relation

```math
C_\tau[\bar x]:=\exists W^\tau\,
   (\mathrm{SWorld}_\tau(W)\land W[\bar x])
\tag{6.1}
```

**Lemma.** Every current strong world W lies below C_τ.

Indeed Box Dec_τ(W) persists by 4. At any future point and tuple where W[x̄] holds, W is nonbottom there, and its persistent deciding clause makes it a strong world there. It itself witnesses C_τ[x̄]. This is necessary coextension in the required direction and hence W≤C_τ. Formally the argument uses the necessitated universally closed C theorem deriving nonbottom from an instance, together with 4 and CBF; it does not necessitate SL.

**Theorem.** SL_τ implies C_τ=Top_τ, hence

```math
\Box\forall\bar x\,\exists W^\tau\,
 (\mathrm{SWorld}_\tau(W)\land W[\bar x])
\tag{6.2}
```

If the complement of C_τ were nonbottom, SL_τ would supply a strong W below that complement. The lemma also gives W≤C_τ, contradicting W≠0. Thus C_τ=Top_τ. This is the dual Strong Leibniz argument and uses only the one type instance.

At τ=t, the tuple is empty and (6.2) is precisely necessary Strong Actuality. No Rigid Comprehension, BF, ND or choice principle is used.

More generally, at every accessible point an actually instantiated X has a strong world below it. Choose a tuple ā with X[ā], then a strong W with W[ā] by (6.2). W decides X at that point by T. The alternative W≤¬X contradicts their shared true instance, so W≤X. Consequently

```math
\mathrm{SL}_\tau\ \Longrightarrow\
\Box\forall X^\tau\left[
 (\exists\bar x\,X[\bar x])\to
 \exists W^\tau(\mathrm{SWorld}_\tau(W)\land W\le_\tau X)
\right]
\tag{6.3}
```

The antecedent in (6.3) is **current instantiation**, not X≠0. The latter permits X to have instances only later. At s in Model B, {k} is possible but currently false and has no strong subworld; every currently true proposition does have the strong subworld {1}. This verifies the precise boundary of the positive theorem.

## 7 What the examples explain

The first construction permits a current strong-world property to identify a complicated future proposition at one isolated time without admitting a current proposition representing that future proposition's entire temporal pattern. Such singleton properties vanish after that time. Their admission therefore does not supply the uniform representation required by BF. This is why full higher-type Strong Leibniz does not repair the propositional domain gap.

The second construction has enough surjective approaches to a limiting arrow to enforce every current Barcan instance. Nevertheless the limiting target has a new splitting of its false atom. All current strong atoms survive only as strong atoms or zero; they need not exhaust the target's strong-world requirements. Rigid Comprehension is precisely an additional route to a stable representing family, not something supplied by the mere existence of strong refinements.

These results preserve the known positive theorem

```math
\mathrm{SL}_{\rm rel}+\mathrm{RC}_{\rm rel}
\Longrightarrow
\Box\mathrm{SL}_{\rm rel}+\Box\mathrm{BF}_{\rm rel}
```

Both new source models therefore fail full current Rigid Comprehension. That conclusion follows from the independently established positive theorem and their displayed failures; it is not assumed in the constructions.

The new models are not the full-two-object-chain-new-individual model. Their individual domains are fixed singletons; the failures and the nonpersistence concern relational domains. In Model A BF_e actually holds necessarily, while BF_t fails. In Model B all current BF instances hold and boxed propositional BF fails.

## 8 Nontriviality and remaining obligations

The substantive new work is the construction of restricted entrance domains compatible with **all typed λ-abstractions and quantifiers**. A Boolean-algebra sketch alone would not establish a C model. Sections 2–5 give recursive domains, transports, closure, all-type strong atoms and direct Barcan witnesses or proofs. The limits are external finite-exception conditions, not assumptions of finiteness in the object language.

The necessary-Strong-Actuality observation is a short strengthening of the existing SL_t⇒Box Actuality proof: a strong world remains strong wherever it is true. Its all-type actual-instantiation version helps distinguish the two modal notions, but is much easier than constructing the separating models.

The broader questions with weaker comprehension assumptions are not classified here. The strong positive boundary with full Rigid Comprehension remains valid. No implication involving individuals is inferred from a relational-only theorem.

## 9 Sources and verification

- Bacon and Dorr, [Classicism](https://philpapers.org/archive/BACC-8.pdf), draft of 16 May 2023, Definition 3.19 and satisfaction clauses, pp. 55–57; full action models, §3.5, pp. 58–60. These supply the target profile semantics and its logical interpretation. The restricted entrance constructions above are new arguments here.
- The local [strong-world calculation for action models](../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/strong-worlds-one-object-action-models.md), especially the future-domain quantifier and idempotent sections, supplies the already established target failures. The successor-target singleton calculation is also explained there.
- Bacon, *A Philosophical Introduction to Higher-Order Logics*, 2024, §8.2, pp. 164–171, supplies the Strong Leibniz definitions and the RC boundary's historical setting. The book proof's documented gap is not reused as evidence.
- The merged [current SL plus RC propagation proof](../../../logical-maps/topics/classicism/writeups/strong-leibniz-and-rigid-comprehension-imply-necessary-strong-leibniz.md) and [bottom-cut proof](../../../logical-maps/topics/classicism/writeups/strong-leibniz-rigid-bottom-cut-integration.md) establish the positive boundary with unboxed premises.
- The recorded [SL_t⇒necessary Actuality](../../classicism-results-2026-10-24-v2/source/topics/classicism/results/strong-leibniz-t-implies-necessary-actuality.yaml), attributed to Cian Dorr, 26 September 2026, is the starting pattern for §6. The strengthened conclusion and its typed version are the arguments given here.

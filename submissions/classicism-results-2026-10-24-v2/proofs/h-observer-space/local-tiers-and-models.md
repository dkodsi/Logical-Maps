# Local separation tiers and models of H

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–6, unpaginated. The type system is the fixed relational system: no function type has output e.

Two distinctions hold over H. Propositional separation, even with every logical preservation clause and endpoint-valued observers, does not recover C or Functionality. Pointwise-identity conjunction separation also does not imply separation by observers preserving the whole conjunction operation. Both distinctions have models validating H's contextual beta and eta equations.

The source framework is the [canonical topic background](../../source/topics/classicism/background.md). For a direct check of H's rule list, the currently available [author PDF](https://andrew-bacon.github.io/papers/Classicism.pdf) is the **1 July 2022 draft**, Figure 2, printed p. 8: PC, UI, EG, Ref, LL, contextual beta/eta, MP, Gen and Inst. That older draft is used here only to check those rules; it is not relabelled as the 16 May 2023 draft used in the map's canonical source metadata.

## 1. Outer domains and admitted domains

The construction distinguishes outer domains A_σ, used to interpret lambda abstraction, from admitted domains D_σ, used for assignments and quantification.

Choose nonempty sets A_e and A_t. At every allowed arrow type put

```math
A_{\sigma\rho}:=A_\rho^{A_\sigma},\qquad\rho\ne e
```

Choose nonempty D_e⊆A_e and D_t⊆A_t. Define recursively

```math
D_{\sigma\rho}:=
\{f\in A_{\sigma\rho}:f[D_\sigma]\subseteq D_\rho\}
```

All terms are evaluated in the full outer function hierarchy. Application is actual function application, and λx^σ.M is the function on **all of A_σ** obtained by varying x. Logical constants are total outer functions chosen so that they belong to their admitted domains. Relational constants may be any elements of their admitted domains; individual constants must belong to D_e.

An admissible assignment sends each variable of type σ into D_σ. By induction, every term under such an assignment denotes an element of its admitted domain. The application case is the definition of D_{σρ}. In the lambda case, applying the outer abstraction to an admitted argument produces an admissible assignment for its body, so its result belongs to D_ρ. Terms with output e are variables or constants, since the type grammar permits no arrow ending in e.

Choose a truth map tr:D_t→{0,1}. On admitted inputs, interpret the logical operations so that

```math
\begin{aligned}
\mathrm{tr}(\neg p)&=1-\mathrm{tr}(p),\\
\mathrm{tr}(p\land q)&=\mathrm{tr}(p)\land\mathrm{tr}(q),\\
\mathrm{tr}(p\lor q)&=\mathrm{tr}(p)\lor\mathrm{tr}(q),\\
\mathrm{tr}(\forall_\sigma F)&=1
\quad\Longleftrightarrow\quad
\forall x\in D_\sigma\;\mathrm{tr}(Fx)=1,
\end{aligned}
```

with the analogous existential clause. Identity judgments are true exactly when their admitted arguments are the same outer-domain element. The examples below give explicit total interpretations meeting these requirements.

**H soundness.** PC and MP use the displayed ordinary truth conditions. UI and EG are sound because every term substituted for a quantified variable belongs to D_σ under every admissible assignment. Gen has its usual free-variable condition and ranges over D_σ. Inst takes P→Q to (∃v P)→Q when v is not free in Q: an existential witness belongs to D_σ, and the premise gives Q under that admissible assignment; the free-variable condition leaves Q unchanged. Actual outer equality gives Ref and LL. The ordinary outer function interpretation validates beta, eta and their contextual instances as identities, under all outer assignments. Semantic substitution and renaming hold in the same full function interpretation and support the conversion calculations. Nonempty D_e supplies the individual-existence requirement if presented separately.

Outer assignments need not satisfy H's truth conditions: their role is to define the outer functions denoted by abstractions. H validity is asserted under admissible assignments. In particular, equality of values at every admitted argument need not identify two outer functions. No rule inferring an abstraction identity from a universally quantified current identity has been added.

## 2. Propositional logical separation without C or Functionality

Take

```math
A_e=\{0,1\},\quad D_e=\{0\},\qquad
A_t=D_t=\{0,1\}
```

Truth is the ordinary Boolean value. In this example D_σ=A_σ for every relational σ. This follows by induction: every relational codomain already has its entire outer domain admitted, so every outer function into it is admitted. Only the individual domain is smaller than its outer domain.

Interpret negation, conjunction and disjunction by the ordinary Boolean operations. Set

```math
\forall_\sigma F=\bigwedge_{x\in D_\sigma}Fx,
\qquad
\exists_\sigma F=\bigvee_{x\in D_\sigma}Fx,
```

and let equality at σ return the Boolean value of actual identity in A_σ. These are total outer functions and admitted logical constants. Section 1 proves H soundness, including beta and eta.

There are exactly two propositions. The identity observer I(p)=p satisfies every full Boolean and quantifier operation identity, at every type, simply by outer function equality. It also satisfies every translated equality clause and full identity-fixing clause. It is factive, endpoint-valued, and fixes both endpoints.

Consequently **every propositional logical separation instance at every finite type list holds**: if all eligible observers agree on p,q, identity agrees on them, and two Boolean values agreeing in truth are equal. Adding any of the listed restrictions retains identity and preserves this argument.

Nevertheless Functionality at e,t fails. Choose the admitted outer predicates

```math
F(0)=F(1)=1,\qquad G(0)=1,\quad G(1)=0
```

Then ∀x^e(Fx=Gx) is true, since x ranges only over {0}, while F and G are distinct outer functions. Full typed separation at et also fails: at the only admitted argument they give the same proposition, so every observer agrees on their current instances.

C fails directly, not just by inference from that Functionality failure. H proves the universal-instantiation formula

```math
(\forall x^e\,Gx)\to Ga
```

Its abstraction over a, and the abstraction of ⊤, are identified by C's Logical Equivalence. In this model ∀x Gx=1, but the two outer abstractions differ at the hidden individual a=1: the displayed conditional is false there, while ⊤ is true. Thus an actual H Logical Equivalence instance fails.

This proves that propositional full logical separation over H does not recover C, even when every finite list is included and the observers are required to be factive, endpoint-valued and identity-fixing. It also proves that propositional Extensionality or the Fregean Axiom does not imply all-type Functionality over H. The full typed recovery theorem in [Typed separation and Classicism](typed-separation-and-classicism.md), §§2–4, requires its stated type scope.

## 3. Pointwise conjunction separation without whole-operation separation

This example uses one hidden proposition. Let

```math
D_t=\{0,u,v,1\}=\{(0,0),(0,1),(1,0),(1,1)\},
\qquad A_t=D_t\cup\{z\}
```

Truth reads the first coordinate on D_t. Take A_e=D_e to be a singleton and use the admitted-domain recursion of §1 at higher types.

On D_t, interpret conjunction m as coordinatewise meet, negation and disjunction coordinatewise in the usual way. Extend m to the hidden inputs by

```math
m(z,z)=u,\qquad m(z,0)=z,
```

and put m(a,b)=0 at every other pair involving z. Extend negation and disjunction arbitrarily on hidden inputs, for example by returning 0 whenever an input is z. Their admitted-input truth conditions remain correct, and all three logical constants are admitted.

For any F∈D_{σt}, let ∀_σF be the diagonal value (b,b), where b is the ordinary universal truth value of F on D_σ. Define ∃ similarly. For outer F not belonging to D_{σt}, define either quantifier to return 0. At every type let equality, on **all outer inputs**, return the diagonal Boolean value of actual equality. These interpretations are total and admitted. The fixed abbreviations give ⊤=1 and ⊥=0. Section 1 again proves full H soundness.

Write

```math
\begin{aligned}
M_{\rm mat}(E)&:\forall p,q\,[E(m(p,q))\leftrightarrow(Ep\land Eq)],\\
M_{\rm pt}(E)&:\forall p,q\,[E(m(p,q))=m(Ep,Eq)],\\
M_{\rm op}(E)&:(\lambda p,q.E(m(p,q)))=(\lambda p,q.m(Ep,Eq))
\end{aligned}
```

The first two quantifiers range over D_t. The third identity compares the whole outer functions and therefore also their values at hidden inputs.

### Pointwise-identity witnesses

For i=0,1 define E_i on D_t by

```math
E_i(b_0,b_1)=(b_i,b_i),
```

and set E_i(z)=0. These outer functions map D_t into D_t, so they are admitted observers. They preserve m at every admitted pair and jointly separate the four admitted propositions. Hence S[M_pt] holds, and so does S[M_mat].

The witnesses also fix both endpoints, have endpoint-valued outputs on every admitted proposition, and satisfy full FixEq_σ at every type. For the last claim, every outer identity judgment has value 0 or 1, and E_i fixes both, even when the identity's arguments are hidden. Thus all these further restrictions can be added to the pointwise separating class simultaneously.

### No whole-operation witness separates 0 from u

Let E be any admitted observer satisfying M_op. This says E is an endomorphism of the entire outer operation m. Its restriction maps D_t into D_t and preserves the diamond meet there.

There are two cases.

* If E(z)=d∈D_t, applying preservation to m(z,z)=u gives E(u)=m(d,d)=d. Preservation of m(z,0)=z gives m(d,E(0))=d. Preservation of m(0,u)=0 gives m(E(0),d)=E(0). The latter two are diamond-meet equations, so d=E(0). Thus E(u)=E(0).
* If E(z)=z, preservation of m(z,z)=u gives E(u)=u. Since 0≤u in the diamond, preservation gives E(0)≤u. Therefore E(0) is 0 or u. Both are false, as is E(u).

In both cases E(0) and E(u) agree in truth. But 0≠u. Thus S[M_op] fails. Restricting the whole-operation class further cannot supply a separating witness, so the failure remains with endpoint acceptance, endpoint rejection, endpoint fixing, endpoint-valued range and any finite list of full FixEq requirements.

We have proved the strict implication

```math
\boxed{\mathrm H+S[M_{\rm op}]
\ \Longrightarrow\ \mathrm H+S[M_{\rm pt}],
\qquad\text{with no converse}}
```

The same countermodel separates whole-operation separation from material separation. It does **not** separate material separation from pointwise-identity separation: both hold in it.

## 4. Material and pointwise qualifications can differ

The preceding model also distinguishes the two qualifications themselves. Define an admitted observer on D_t by

```math
E(b,c)=(b,b\lor c),
```

and extend it at z by E(z)=0. Its actual truth value equals that of its input, so M_mat(E) holds. It fixes 0 and 1. But for p=v and q=u,

```math
E(m(v,u))=E(0)=0,
\qquad
m(E(v),E(u))=m(1,u)=u
```

Hence M_pt(E) fails. This is a strict distinction between observer predicates, not a proof that their propositional separation theories differ. The latter implication remains unclassified here. Under the explicit local identity-bivalence assumptions in [the representation theorem](representation-under-identity-bivalence.md), principal tests give the stated positive equivalences instead.

For **full typed** separation, pointwise versus whole-operation requirements do not produce this gap: full typed separation yields Functionality, which identifies the composite operations from their pointwise identities. For the complete logical qualification, all three full typed separation theories coincide by H transport followed by C normalization. Those conclusions are compatible with every local distinction proved here.

## 5. A C model separates propositional and full typed Boolean separation too

The distinction in §2 is not merely a consequence of failure of C. The existing [full action model: two-object retract](../../source/topics/classicism/models/full-two-object-retract.yaml) is a C model in which propositional full-composite Boolean separation holds but Functionality at t,t fails.

The [saved observer proof](../observer-models.md), §2, gives admitted identity and coordinate-selection observers, proves their Boolean preservation at both objects, and proves their propositional separation. Here is a direct Functionality witness in the same model.

The objects W,V have arrows h:W→V and j:V→W with jh=id_W and hj=k≠id_V. Propositions at W have two coordinates (b,c); those at V have three (a,b,c). The transport
$`h_t(b,c)=(c,b,c)`$
has proper image I⊊D_t(V). Let G be the bottom predicate at type tt. Fullness admits a predicate F whose truth profile is false at every current pair (id_W,p), and is true at a future pair (h,a) precisely when a∉I. For every current p, the proposition Fp is bottom: its current coordinate is false, and its future coordinate is false because h_t(p)∈I. Thus ∀p(Fp=Gp) is true. Yet F≠G, because their truth profiles differ on some (h,a) with a∉I. This refutes Fun_{t,t}, and hence full typed Boolean separation by the general factorization theorem.

The source full-action construction supplies beta/eta and C soundness. This paragraph adds only the explicit Functionality witness; the new claim is not attributed to the published source.

## 6. Exact scope of the distinctions

| Claim | Verdict established here |
|---|---|
| Propositional full logical separation over H implies C | False, §2 |
| Propositional full logical separation over H implies Functionality | False, §2 |
| Propositional full Boolean separation plus C implies full typed Boolean separation | False, §5 |
| Propositional pointwise-M separation over H implies whole-operation-M separation | False, §3 |
| Material-M and pointwise-M are equivalent observer predicates over H | False, §4 |
| Propositional material-M separation implies pointwise-M separation over H | Not settled by these arguments |
| Full typed pointwise and whole-operation separation differ | They coincide by Functionality, under the stated general schema scope |
| The three complete logical separation theories differ at full typed scope | They coincide by the H recovery and normalization theorem |

The new countermodels are the explicit outer-domain constructions in §§1–4, direct source `misc`. The older action-model comparison retains its existing model record, published construction locator and separate observer proof. No unverified distinction is promoted to a non-implication.

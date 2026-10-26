# Why the endpoint core can identify individuals

OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`).

## 1. Construction

Let K be the full standard two-valued relational hierarchy on one individual *. Apply the proved arbitrary-C predecessor construction in [the arbitrary-C predecessor construction](classical-present-over-arbitrary-model.md) with current individuals $`D_{e}`$={a,b} and the constant map $`q_{e}`$(a)=$`q_{e}`$(b)=*.

For $`\tau=\sigma_1\cdots\sigma_nt`$ the resulting C-model R has

```math
D_\tau=\mathcal P(D_{\sigma_1}\times\cdots\times D_{\sigma_n})\times K_\tau.
```

and $`q_{\tau}`$ is second-coordinate projection. All $`q_{\tau}`$ are onto, including $`q_{e}`$. Propositions are the four pairs (ε,η) in 2 x 2. Current truth is ε. Application, lambda interpretation and quantification retain K's original second components, as in the cited construction.

There is an admitted operation E:tt whose current action is

```math
E(\epsilon,\eta)=(\eta,\eta).
```

and whose old K-component is the identity on 2. It is admitted because its output's old component η depends only on the input's old component.

## 2. Observer properties

E is endpoint-valued and has the whole identity E composed with E=E: both operations have the displayed idempotent current action and the same old component. Its whole Boolean identities follow in both coordinates from ordinary Boolean operations on 2.

For every admitted type σ and root predicate F, the current truth of $`Q_\sigma`$(E composed with F) is

```math
\forall x\in D_\sigma.\,q(F)(q_\sigma(x))\text{ is true in }K.
```

Surjectivity of $`q_{\sigma}`$ makes this equivalent to $`Q_\sigma^K`$(q(F)). That is exactly the current bit of E($`Q_\sigma`$ F). The old components agree as well, because q(E) is identity. Thus E commutes with every typed quantifier. This is a whole operation identity: both the current rows and the old components of the operations on F agree.

The example therefore satisfies bare C plus one endpoint-valued, whole-idempotent observer with all typed quantifier qualifications. It does not require any infinite conjunction inside the object language: the same displayed E has every externally specified finite qualification.

## 3. Why individuals must be identified

Actual equality of a and b is false. Its proposition has profile

```math
\delta_e(a,b)=(0,1).
```

because their current objects differ but their old images coincide. Consequently E(delta_e(a,b))=Top=(1,1).

Every normalized individual predicate is constant on {a,b}. Indeed the old predicate domain over {*} contains only its two constant truth tables, and normalization by E replaces a predicate's current table by the pullback of that old table. Hence no normalized predicate can distinguish a and b.

The classical core therefore has one individual, the common equivalence class of a and b under observed equality. Taking the two current objects as distinct core individuals would violate the desired literal Leibniz identity clause. This demonstrates why the generalized theorem must permit identification of individuals, rather than merely dropping C5 while keeping its same-individual-domain conclusion.

C5 genuinely fails in this example. The distinct root propositions (0,1) and Top become identical in K. Their equality proposition is not Bottom, so their actual distinctness is not necessary.

## 4. The normalized core

Define $`r_{e}`$=id externally, $`r_{t}`$=E and recursively

```math
r_{\sigma\tau}(f)(x)=r_\tau(f(r_\sigma(x))).
```

Since q(E) is identity, term preservation and β/η give $`q_{\tau}`$($`r_{\tau}`$ f)=$`q_{\tau}`$(f) at every relational type. At terminal truth, normalization reads the K component. It follows by induction through the arguments that $`r_{\tau}`$ f has current table

```math
(x_1,\ldots,x_n)\longmapsto\mathrm{truth}_K(q_\tau(f)[q_{\sigma_1}(x_1),\ldots,q_{\sigma_n}(x_n)]).
```

Its old component is $`q_{\tau}`$(f). Thus a normalized relational object is uniquely determined by its old component, and every old component is realized. Projection q gives a bijection between the normalized objects at every relational type and $`K_{\tau}`$. At e it gives the bijection only after the a~b quotient. These maps preserve application and the core logical operations. The resulting classical core is exactly K up to this canonical isomorphism.

This is a concrete model explaining the quotient in the new bare-C theorem. It does not establish the general theorem by itself; that argument is in [the general endpoint-core theorem](endpoint-classical-cores.md).

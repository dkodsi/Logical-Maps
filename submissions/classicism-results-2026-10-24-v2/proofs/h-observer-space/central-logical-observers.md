# Observers that commute with every logical observer

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new arguments: `misc`, this note, §§1–5, unpaginated.

Commuting with the logical operations is the usual qualification for an observer. Commuting with every qualified observer is a further, different restriction. Over C5, separation by these central observers is exactly Extensionality. The proof identifies the possible central observers under ordinary separation before deriving the collapse.

The C5 premise matters. A full two-point chain has central separation at every point and still has contingent propositions. More generally, among full models on finite rooted posets, central separation holds exactly on the singleton and the two-point chain. This gives a complete model-family classification, not a characterization of arbitrary H models.

## 1. The restriction and its scope

Fix a finite external qualification list Δ. Write $`\mathrm{Good}_\Delta`$ for the whole Boolean and listed quantifier identities in [Logical observer separation](../logical-observer-hierarchy.md), §1. Put I=λp.p, and define

```math
\mathrm{Cent}_\Delta(E):=
\mathrm{Good}_\Delta(E)\land
\forall G^{tt}\,[\mathrm{Good}_\Delta(G)\to E\circ G=G\circ E].
\tag{1}
```

Each composition equality is identity of the complete unary operations. The quantifier in (1) ranges over admitted observers, not external maps. A fixed Δ gives one finitary formula. The full separation theory uses the separate formulas for the finite lists and relational output types; it does not quantify over types or require one infinitary observer class.

Write CentreSep(τ,Δ) for separation at τ by the observers in (1), and CentreSep for its full schema. The identity observer is always central. Two central observers commute with each other, but the definition is stronger than asking for a chosen pairwise commuting separating family: each observer in (1) must commute with every $`\mathrm{Good}_\Delta`$ observer, including the Boolean patches used below.

Over C, whenever E and G are $`\mathrm{Good}_\Delta`$ and c is any admitted proposition, the term

```math
P_c(E,G)(p):=(c\land Ep)\lor(\neg c\land Gp)
\tag{2}
```

is $`\mathrm{Good}_\Delta`$. The two Boolean output regions prove the Boolean laws; fixed-guard distribution over the listed quantifiers proves their laws. The existing patching theorem supplies the whole composite identities. No current truth condition on c is needed.

## 2. Central observers are idempotent

Assume C and the Functionality needed to collect unary output identities. Every central observer E satisfies

```math
E\circ E=E.
\tag{3}
```

To prove this, fix p and form the admitted Good observer

```math
F_p(r):=(Ep\land Er)\lor(\neg Ep\land r).
\tag{4}
```

Centrality gives $`E(F_p p)=F_p(Ep)`$. Boolean simplification gives the two sides explicitly:

```math
E(F_pp)=E(Ep\lor p)=E^2p\lor Ep,
\qquad
F_p(Ep)=Ep\land E^2p.
\tag{5}
```

Equality of the union and intersection forces E²p=Ep. Functionality gives the whole identity (3). The observer $`F_p`$ is selected separately for each input in the argument; no choice function or uniform family premise is used.

Thus centrality already implies idempotence. The converse fails in general: the ordinary idempotent normalization of OS does not produce central observers.

## 3. The centre under C5 and ordinary separation

Assume C5, t∈Δ, and ordinary propositional separation $`S_{t,\Delta}`$. Let E be central. The [canonical kernel theorem](surjective-logical-observers.md), §2, supplies an admitted greatest kernel element k with

```math
Ek=0,
\qquad Ep=0\ \longleftrightarrow\ p\le k.
\tag{6}
```

Here and below 0,1 mean Bottom, Top. The kernel theorem requires t∈Δ; its equality guards are endpoint-valued under C5. It does not require E to be onto or injective.

**Theorem 1.** Every central E is either I or an endpoint-valued observer whose greatest kernel k is currently true. There is at most one central observer other than I.

**Proof.** For every $`\mathrm{Good}_\Delta`$ observer G, centrality and (6) give

```math
E(Gk)=G(Ek)=0,
\qquad Gk\le k.
\tag{7}
```

Suppose first that k is currently false. Then every Gk is false, while G0=0. Ordinary separation applied to k and 0 gives k=0. A Boolean observer with zero kernel is injective; its idempotence from §2 therefore gives E=I.

Suppose instead that k is currently true. For an arbitrary Good G, the patch

```math
F(r):=(k\land Gr)\lor(\neg k\land r)
\tag{8}
```

is Good. Since Ek=0, Boolean preservation gives E(Fr)=Er. Centrality E∘F=F∘E then gives

```math
k\land G(Er)=k\land Er.
\tag{9}
```

Because k is true, G(Er) and Er have the same current truth value. This holds for every Good G. If Er is true, all observers agree on Er and 1; if Er is false, they agree on Er and 0. Ordinary separation gives Er=1 or Er=0 accordingly. Thus E is endpoint-valued.

Finally, if E and F are endpoint-valued Good observers, endpoint fixing gives E∘F=F and F∘E=E. They commute only when E=F. This proves uniqueness of a possible nonidentity central observer. ∎

The theorem classifies the centre under ordinary separation; it does not assert that the nonidentity alternative is realized. In that alternative the observer sends a currently true proposition to Bottom. Nothing in the proof identifies current truth preservation with endpoint-valuedness.

## 4. Central separation is Extensionality over C5

**Theorem 2.** For each finite Δ containing t,

```math
\boxed{\mathrm{C5}+\mathrm{CentreSep}(t,\Delta)
\quad\longleftrightarrow\quad\mathrm{Extensionality}.}
\tag{10}
```

Consequently the same equivalence holds for full CentreSep, retaining C5 on the left.

**Proof.** Central separation implies ordinary separation, so Theorem 1 applies. Suppose a central E differs from I. Its greatest kernel k is true, and all central observers are I or E.

For any v≤k, we have Ev=0. If v is false, I and E agree on v and 0, so central separation gives v=0. If v is true, they agree on v and k, so central separation gives v=k. Thus k is a nonzero atom, and is currently true.

The established atom-observer correspondence over C5 gives the admitted principal endpoint observer

```math
H(p):=\Box(k\to p),
\tag{11}
```

qualified at every requested finite list. In particular Hk=1, whereas Ek=0. But E is central, so it commutes with H; two endpoint observers commute only when equal. This contradiction excludes E≠I.

Only identity is therefore central. Central separation becomes the propositional Fregean principle. C, already part of C5, upgrades it to full Extensionality by the recorded Fregean-to-Extensionality theorem. Equivalently one may use C5 Functionality after the propositional collapse.

Conversely, Extensionality gives C5 and makes every proposition an endpoint. Every Good observer fixes those endpoints and therefore is I by Functionality. Identity is central and supplies separation at every relational type. ∎

No Boolean Completeness, Zorn, Choice or finite observer bound is assumed in this proof. It constructs the true atom only inside the temporary nonidentity case and discharges that case. The optional central-separation hypothesis is not necessitated.

Since Rev and End each imply C5, the full-theory conjunctions give two further exact formulations, allowing separate witness families:

```math
\boxed{
\mathrm{CentreSep}+\mathrm{Rev}
\ \longleftrightarrow\ \mathrm{Extensionality}
\ \longleftrightarrow\ \mathrm{CentreSep}+\mathrm{End}.}
\tag{12}
```

## 5. Full finite rooted-poset models

Take a full action model on a finite rooted poset P, with singleton individuals. The [finite coordinate theorem](idempotent-native-box-observers.md), §§3–4, identifies all Boolean observers at its root o with inflationary coordinate maps f:P→P:

```math
x\le f(x),\qquad E_f(p)=f^{-1}[p].
\tag{13}
```

Every such coordinate observer is Good at every finite qualification list. Composition reverses the order of the coordinate maps, which leaves commutation unchanged. Consequently the centre at every Δ is exactly the centre of the monoid of all inflationary maps on P. No native-Box qualification is imposed here.

For x∈P, let $`g_x`$ move only o to x and fix every other point. It is inflationary. If a central f fixes o, commutation at o gives

```math
f(x)=f(g_x(o))=g_x(f(o))=x.
\tag{14}
```

Hence f=I. If f(o)=a≠o, the same calculation gives $`f(x)=g_x(a)=a`$ for every x. Thus f is constant, and inflationarity forces a to be a greatest element of P.

Conversely, identity is central, and if a greatest element $`1_P`$ exists the constant map to $`1_P`$ commutes with every inflationary map: each such map fixes $`1_P`$. We have proved the exact centre description

```math
\boxed{
Z(\mathrm{Infl}(P))=
\begin{cases}
\{I,\mathrm{const}_{1_P}\},&P\text{ has a greatest element},\\
\{I\},&P\text{ has none}.
\end{cases}}
\tag{15}
```

On a singleton the two displayed maps coincide. Otherwise the central read points at o are exactly o and, if it exists, $`1_P`$. Distinct propositions are subsets of P, so central separation holds precisely when those read points exhaust P. Current Functionality lifts this propositional calculation to every relational output type. Therefore

```math
\boxed{\mathrm{CentreSep}\text{ holds in the full finite rooted-poset model}
\quad\longleftrightarrow\quad
P\text{ is a singleton or a two-point chain}.}
\tag{16}
```

The two-point chain also has CentreSep at its only proper future cone, the singleton. It consequently supplies C+□CentreSep, with all BF and Functionality and their boxes, but not C5 or Extensionality. This shows why (10) keeps C5 explicit. The model even has internally finitely many propositions and Actuality; neither replaces C5 in (10).

For the reverse separation, use the full two-point S5 cluster. Its endpoint readers separate, so it has End and Rev; it has four propositions and fails Extensionality. By (10) it fails CentreSep. Equivalently all four maps on its two coordinates are admitted logical observers, and only identity is central. Thus CentreSep is incomparable with Rev and with End over H, while either conjunction in (12) is exactly Extensionality.

These finite model calculations do not assert an intrinsic H characterization of CentreSep, or a comparison with native-Box separation outside the displayed examples.

## 6. Sources

The centrality restriction, idempotence calculation, C5 centre classification, Extensionality characterization and finite rooted-poset centre calculation are new arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–5, unpaginated.

Boolean patching, the atom-to-endpoint-observer construction, and Rev/End implying C5 are in [Logical observer separation](../logical-observer-hierarchy.md), §§1, 3–5. The admitted kernel theorem is in [Surjective logical observers](surjective-logical-observers.md), §2; it holds for arbitrary Good observers before surjectivity is assumed. The propositional-to-full Extensionality implication is recorded as [Fregean implies Extensionality](../../source/topics/classicism/results/fregean-axiom-implies-extensionality-r.yaml).

The full action-model framework is Bacon and Dorr, *Classicism*, draft of 16 May 2023, §3.5, pp. 58–61, and Appendix D, pp. 73–74, as recorded in [Full action models](../../source/topics/classicism/groups/full-action-models.yaml). The finite-coordinate observer calculation used here is [Idempotent native-Box observers](idempotent-native-box-observers.md), §§3–4, unpaginated. The new centre verdicts do not change those constructions or their published attribution.

All type lists are external and finite, and all centrality and composition equations retain their whole-operation meaning.

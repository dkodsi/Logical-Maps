# Full cancellative monoid models with surjective and left-invertible observers

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the observer constructions and new model verdicts: `misc`, this note, §§1–6, unpaginated. The full action-model construction and existing comparison theorems are attributed in §7.

Every full action model of a cancellative monoid, with singleton individuals, has full logical separation by surjective observers. If the monoid also has a specified countably infinite sequence of distinct units, it has full logical separation by observers with admitted qualified left inverses. Both separation schemas hold separately necessarily.

The monoid ℤ×ℕ has these two properties but fails C5, and therefore fails reversible separation. In particular,

```math
\mathrm H+\Box\mathrm{SurjSep}+\Box\mathrm{SplitMono}
\ \not\Longrightarrow\ \mathrm{Rev},
\tag{1}
```

even with C and necessary BF as additional premises. The inverse equations below hold at all future inputs as identities of whole admitted operations. The proof never turns current surjectivity into an admitted section.

## 1. The full action model and the separation conventions

Let M be a set-sized monoid, with unit 1. Regard it as a category with one object. Write composition multiplicatively, with the rightmost arrow traversed first: after an arrow r, a further arrow h gives the composite hr. Assume both cancellation laws:

```math
ab=ac\ \Longrightarrow\ b=c,
\qquad
ba=ca\ \Longrightarrow\ b=c
\tag{2}
```

Give the sole object one individual and use the full relational action-model domains. Thus every intension at every admitted relational type is present. A relational intension R of type σ₁⋯σₖt is specified by its truth profile R(h,x₁,…,xₖ), for every h∈M and every argument tuple at the sole object. Its transport is

```math
(\rho_r R)(h,\bar x)=R(hr,\bar x)
\tag{3}
```

Arguments are transported when an intension is applied. In particular, propositions are exactly subsets of M, current truth is membership of 1, and

```math
\rho_r p=\{h:hr\in p\},
\qquad
\top=M,\quad\bot=\varnothing
\tag{4}
```

The full action construction supplies C in the fixed relational type system. The monoid elements are semantic arrows, not terms of an additional individual-to-individual function type.

Right cancellation makes every type transport onto. At a relational type, given a desired profile Y, prescribe the preimage profile X by $`X(hr,\bar x)=Y(h,\bar x)`$, and assign arbitrary truth values at coordinates outside M r. Right cancellation makes this prescription unambiguous; fullness admits X. At type e the unique map on the singleton is onto. Hence the full-model Barcan criterion gives BF and Functionality at the sole object, and necessary BF and necessary Functionality as well.

Fix any finite external type list Δ. Good_Δ means full Boolean composite preservation, full universal and existential composite preservation at the types in Δ, and the usual translated equality clauses. Over C the translated equality clauses follow from the Boolean qualification. They are not assertions that an observer fixes identity propositions.

SurjSep is separation by Good_Δ observers E satisfying the current internal sentence ∀q∃p(Ep=q). SplitMono is separation by Good_Δ observers E for which some admitted Good_Δ observer F satisfies F∘E=I, where I:=λp.p. Both use material agreement of observed propositions. At a relational output type τ, the agreement also universally quantifies over the argument tuple of τ. The full schemas range over every relational τ and finite Δ. A boxed schema means the separate boxes of its closed instances; there is no object-language type quantifier or infinitary qualification conjunction.

## 2. Arbitrary observation profiles are fully qualified

Let a:M→M be any externally specified function. Fullness admits the observer E_a with profile

```math
E_a(m,q)\quad\Longleftrightarrow\quad a(m)\in q
\tag{5}
```

Here q is an arbitrary proposition at the target of m, which is again the sole object. Application and (4) give

```math
E_a(p)=\{m:a(m)m\in p\}
\tag{6}
```

More generally, transport E_a along r and apply it to an arbitrary future input q. At a further coordinate h the resulting proposition has truth value

```math
h\in (\rho_r E_a)(q)
\quad\Longleftrightarrow\quad
a(hr)h\in q
\tag{7}
```

The distinction between (5), (6) and (7) matters: (5) defines the whole admitted observer, and (7) controls its action on inputs not necessarily transported from an earlier stage.

Every E_a is Good_Δ for every finite Δ. Boolean preservation follows because every individual truth test in (5) is evaluation at an arrow and Boolean operations are pointwise. For the universal law, fix any future coordinate m and any admitted F of type σt there. Write b=a(m). The truth of E_a(∀_σF) at that coordinate is

```math
\forall y\in D_\sigma\quad F(b,y)\text{ is true}
\tag{8}
```

The truth of ∀_σ(λx.E_a(Fx)) there is

```math
\forall x\in D_\sigma\quad
F\bigl(b,\rho_\sigma(b)x\bigr)\text{ is true}
\tag{9}
```

These agree because ρ_σ(b) is onto. Replacing both universal quantifiers by existential ones proves the existential law. The same comparison applies after arbitrary transport r, using a(mr) in place of a(m). Thus the comparisons cover every future coordinate and every input there: they prove the full identities between the composite λF operations. The Boolean laws have the same full-profile scope. The translated equality qualification then follows from the stated C theorem.

No injectivity of ρ_σ(b) is required. In particular this argument does not presume C5, and does not assert that E_a preserves or reflects actual equality.

## 3. Left translations give surjective separation

For b∈M choose the constant assignment a(m)=b, and write its observer as S_b. Then

```math
S_b(p)=\{m:bm\in p\}
\tag{10}
```

Given q⊆M, define p=bq:={bm:m∈q}. Left cancellation gives S_b(p)=q. This proves the current internal surjectivity sentence for S_b. The argument selects an admitted proposition p for each q; it does not select an admitted inverse operation.

The profile (5) of S_b is constant in its arrow coordinate, so ρ_r S_b=S_b for every r. Its surjectivity therefore also holds after every transport. Section 2 gives its full Good_Δ qualification for every requested finite list.

If p≠q, choose b∈M at which their memberships differ. At the actual coordinate 1, S_b reads precisely that membership, so S_b p and S_b q differ in current truth. These observers separate propositions. For a relational output type, Functionality supplies an argument tuple at which distinct relations give distinct proposition objects, and the same construction separates those values. Thus the model satisfies full typed SurjSep. The distinct uses of cancellation are explicit: right cancellation gave onto type transports and quantifier preservation; left cancellation made (10) onto.

## 4. An infinite sequence of units gives qualified left inverses

Assume in addition that a specific external sequence of pairwise distinct units has been supplied:

```math
u_0=1,u_1,u_2,\ldots
\tag{11}
```

This is a hypothesis about the model construction. It is not an internally admitted enumeration or an invocation of object-language Choice. Put

```math
\alpha_n=u_{n+1}u_n^{-1}
\tag{12}
```

For each b∈M define an observation assignment a_b, and define a single assignment c independent of b, as follows:

```math
a_b(z)=
\begin{cases}
b,&z=u_0,\\
\alpha_n^{-1},&z=u_{n+1},\\
1,&z\notin\{u_0,u_1,\ldots\},
\end{cases}
\qquad
c(z)=
\begin{cases}
\alpha_n,&z=u_n,\\
1,&z\notin\{u_0,u_1,\ldots\}
\end{cases}
\tag{13}
```

The cases are disjoint because the units are pairwise distinct. Let E_b:=E_{a_b} and F:=E_c. Fullness admits both profiles, including their countably many cases. Section 2 makes both observers Good_Δ for the same arbitrary finite list Δ.

For every z∈M,

```math
a_b\bigl(c(z)z\bigr)c(z)=1
\tag{14}
```

If z=u_n, then c(z)z=α_nu_n=u_{n+1}, so the left side is α_n^{-1}α_n. If z lies outside the displayed sequence, both factors are 1. The exceptional observation b at u_0 is never encountered in this composition.

Equation (14) proves an identity of whole operations. To check this without restricting to current inputs, transport E_b and F along arbitrary r, take an arbitrary q at that future stage, and inspect a further coordinate h. Applying (7) twice gives

```math
\begin{aligned}
h\in (\rho_r F)\bigl((\rho_r E_b)(q)\bigr)
&\Longleftrightarrow
c(hr)h\in (\rho_r E_b)(q)\\
&\Longleftrightarrow
a_b\bigl(c(hr)hr\bigr)c(hr)h\in q\\
&\Longleftrightarrow h\in q
\end{aligned}
\tag{15}
```

The last step is (14) at z=hr. Thus F∘E_b=I as a full admitted-operation identity. No commutativity has been used. No necessity assertion has been inferred merely from a current pointwise equation.

At the actual coordinate, a_b(1)=b, so E_b p is true exactly when b∈p. Consequently the E_b separate all propositions, using this same qualified left inverse F. Functionality again lifts the conclusion to every relational output type. The full SplitMono schema holds.

The construction also supplies the one-pair kernel condition from [Left-inverse separation](left-inverse-separation-decomposition.md). Let w={1}. Then w is true, while Fw=Bottom: the coordinate map z↦c(z)z sends u_n to u_{n+1} and fixes the complement of the sequence, and therefore never takes the value 1. The admitted witnesses E_1,F,w satisfy K_Δ for every finite Δ. This is an additional description of the explicit witnesses, not an extra assumption needed for the separating argument.

## 5. Necessity and the monoid ℤ×ℕ

The separation instances just proved are closed pure formulas once the output type and finite qualification list have been fixed externally. In a one-object action model, naturality of any closed pure term P gives ρ_r P=P for every arrow r: its interpretation at the target is its interpretation at that same sole object. In particular, if the closed proposition P is true, it is true at every arrow. Equivalently one may repeat the foregoing existence proofs at every target object, since there is only one. Thus every instance of SurjSep and, under (11), every instance of SplitMono is separately necessary. This argument permits witnesses to be chosen anew at the target; it does not claim that transporting a particular E_b leaves its distinguishing behavior unchanged.

Now take the additive cancellative monoid

```math
M=\mathbb Z\times\mathbb N,
\qquad 1_M=(0,0),
\qquad u_n=(n,0)
\tag{16}
```

Its units are the pairs (z,0), so (11) holds and α_n=(1,0). The constructions above establish C, necessary BF, separately necessary full SurjSep and separately necessary full SplitMono.

Let w={(0,0)} and let v=(0,1). The admitted proposition w differs from Bottom but

```math
\rho_v w=\varnothing
\tag{17}
```

Thus distinct propositions become identical, so ND_t fails and C5 fails. The established full-H theorem Rev⇒C5 now gives failure of Rev. This proves (1), in the stronger model profile

```math
\boxed{
\mathrm C+\Box\mathrm{BF}
+\Box\mathrm{SurjSep}+\Box\mathrm{SplitMono}
+\neg\mathrm{C5}+\neg\mathrm{Rev}
}
\tag{18}
```

The same conclusion holds for any cancellative monoid satisfying (11) and containing a nonunit v. A nonunit in a cancellative monoid has no left inverse: if av=1, then (va)v=v=1v and right cancellation gives va=1 as well. Hence no h satisfies hv=1, and ρ_v{1}=Bottom. The explicit monoid (16) is a concrete instance of this family.

## 6. The exact comparison settled

Over H, full reversible separation entails both full surjective separation and full qualified left-inverse separation. A qualified two-sided inverse witnesses each requirement. The converse fails by (18), even if both proposed weakening schemas are separately boxed.

The conjunction is strictly stronger than each factor. The [omega-chain model](omega-chain-surjective-observers.md) has separately necessary SurjSep but fails SplitMono. Conversely, the [finite-block symmetry model](finite-block-symmetry-left-inverse.md), §§1–6, has C5 and separately necessary SplitMono but fails Rev. Over C5, [surjective separation is equivalent to Rev](surjective-logical-observers.md), so that model fails SurjSep. Each comparison retains the full typed, finite-list scope proved in its cited note.

Consequently there are strict implications

```math
\mathrm{Rev}
\ \Longrightarrow\
\bigl(\mathrm{SurjSep}\land\mathrm{SplitMono}\bigr)
\ \Longrightarrow\ \mathrm{SurjSep},\ \mathrm{SplitMono}
\tag{19}
```

The last two principles remain incomparable. This determines the conjunction comparison; it does not claim that the displayed conjunction is a least stronger observer qualification or that every upper comparison has been classified.

## 7. Sources

The general observation profiles, the cancellative-monoid constructions, the arbitrary-future inverse calculation and the new ℤ×ℕ verdict are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–6, unpaginated.

The semantic framework is Bacon and Dorr, *Classicism*, draft of 16 May 2023, §3.5, pp. 58–61; Appendix D, pp. 73–74, as recorded in [Full action models](../../source/topics/classicism/groups/full-action-models.yaml). The all-type surjective-transport criterion for BF is Proposition 3.24(ii), recorded in [Full epic Barcan](../../source/topics/classicism/arguments/full-epic-barcan.yaml). Those sources supply the full action-model construction and its background properties; the new observer and separation verdicts are proved here and are not attributed to the paper.

The qualification and separation conventions, and Rev⇒C5, are in [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md), §§1 and 4. The qualified inverse orientations are stated in [Qualified right-inverse separation](split-inverse-logical-observers.md), §1. The one-pair kernel condition and its same-profile normalization are in [Left-inverse separation](left-inverse-separation-decomposition.md), §§1–2. The comparison models and the C5 surjective theorem retain their linked proofs and scopes.

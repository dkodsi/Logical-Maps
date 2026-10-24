# Full three-object fork: all Barcan instances without binary families

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: misc, this note, §§1–5, unpaginated.

## 1. Construction and evaluation point

Take the category with objects r,l,h, identity arrows, and exactly two nonidentity arrows

```math
\alpha:r\longrightarrow l,\qquad \beta:r\longrightarrow h.
```

Both l and h are terminal along their respective branches: there are no further nonidentity arrows. Use singleton individuals at every object and the full action construction in the fixed relational type system. Evaluate at the identity of r.

This is the same general full action construction used by the recorded [two-object chain](../../source/topics/classicism/models/full-two-object-chain.yaml); the source reference for that construction is Bacon–Dorr, *Classicism*, draft of 16 May 2023, §3.5, pp. 59 and 61. The fork-specific calculations below are new arguments attributed to misc.

At the root,

```math
D_t(r)=\mathcal P\{1_r,\alpha,\beta\},
```

and each leaf has the two-element proposition domain. Proposition transport takes the corresponding leaf bit. The full function-type domains consist of the natural families of functions between the recursively constructed domains; at a leaf these are ordinary full function spaces. This standard full action construction is a C model, hence an H model.

## 2. Joint transport surjectivity at every type

For every admitted type τ, the paired map

```math
(\alpha_\tau,\beta_\tau):D_\tau(r)
 \longrightarrow D_\tau(l)\times D_\tau(h)
```

has an explicit section sτ.

At e, all three domains are singletons. At t, given two leaf truth values, set the root proposition's α and β bits to those values and its 1r bit to false.

For a function type σρ, suppose sρ is already defined. Given leaf functions f_l and f_h, retain them as the two leaf components and define the root component by

```math
f_r(x):=s_\rho\bigl(f_l(\alpha_\sigma x),
                         f_h(\beta_\sigma x)\bigr).
```

The section equations for sρ give

```math
\alpha_\rho(f_r(x))=f_l(\alpha_\sigma x),\qquad
\beta_\rho(f_r(x))=f_h(\beta_\sigma x).
```

Thus these components form an admitted natural family in the full model, whose transports are the prescribed f_l,f_h. This defines sσρ. Induction on types proves the claim; it requires no choice of a family of arbitrary preimages.

In particular every arrow transports every type surjectively. Consequently every BF instance holds at every object. Directly, if ∀x^σ□Fx holds at r, then for every root x and every arrow γ out of r the transported F is true of γσx. Surjectivity makes these transported x cover the entire σ-domain at the target of γ. Therefore F is universally true at every target, which is □∀x^σFx. At leaves the same reasoning is immediate. Hence the model satisfies all BF instances and all their boxed forms.

The same surjectivity verifies Functionality at every type. If two root natural function families agree on every root input, naturality and surjectivity force agreement of their leaf components on every leaf input as well; their complete families are identical. Leaf Functionality is ordinary function extensionality.

## 3. No nonconstant endpoint-valued family, even without designated inputs

Let F:σt be any admitted root family whose every root output equals Top or Bottom as a proposition object. Write f_l,f_h for its leaf components, taking values in {0,1}.

For arbitrary leaf inputs u∈Dσ(l), v∈Dσ(h), joint surjectivity gives a root x with ασx=u and βσx=v. Since Fx is one of the two root endpoints, its two leaf bits agree. Naturality therefore gives

```math
f_l(u)=f_h(v)
\qquad\text{for every independent pair }u,v.
```

Both leaf domains are nonempty, so f_l and f_h are the same constant c. Every root output Fx is an endpoint with leaf bit c, hence is that same endpoint. Thus F is constant.

It follows that **no admitted family at any type σ has range exactly {Top,Bottom}**. In particular there is no endpoint selector fixing Top and Bottom, but the conclusion is stronger: there is no nonconstant endpoint-valued family with its two values attained at arbitrary, undesignated inputs.

Consequently BinaryRangeσ(B) from [Quantifier-generated lattices](quantifier-generated-lattices.md) fails for every σ. Specializing any proposed constructor to p=Top and q=Bottom would supply the impossible family above. Even the weaker pointwise-existence assertion ∀p,q∃F with exact binary range fails; this is not merely a failure of uniform choice of the constructor.

## 4. The C bridge between designated and undesignated ranges

For clarity, there is also a general argument over C that avoids conflating the two definitions. Suppose an admitted F:tt is endpoint-valued, F(a)=Top and F(b)=Bottom, with no conditions on F(Top) or F(Bottom). Define

```math
B(p):=F\bigl((p\land a)\lor(\neg p\land b)\bigr).
```

C's Boolean identities give B(Top)=F(a)=Top and B(Bottom)=F(b)=Bottom. Every output remains an endpoint because F is endpoint-valued on every proposition input. Thus any such undesignated nonconstant F yields a designated endpoint selector. This proof uses the admitted witnesses a,b as parameters; it does not require F to preserve any logical operation.

The fork also fails modal .2 directly. The root proposition whose α bit is true and β bit is false becomes Top at l and Bottom at h. Hence ◇□p holds at r while □◇p fails there. This agrees with the C equivalence between .2 and endpoint selectors proved in [Modal selectors](../modal-selectors-and-quantifier-reduction.md), §1; the independent argument in §3 proves the stronger all-type absence claim without relying on that equivalence.

## 5. Consequence for universal-only separation over H

Over C, the proved [meet/quantifier characterization](../meet-quantifier-separation.md), §4, gives for every finite external type list Δ:

```math
\mathrm{BF}_\Delta
\ \leftrightarrow\ S[A\land Q_\Delta]
\ \leftrightarrow\ S[A\land M\land Q_\Delta].
```

The qualifications use full composite operation identities; Top fixing may replace acceptance in that theorem. Section 2 therefore makes the fork satisfy every such universal-only separation instance, even the conjunction-preserving strengthening. Its Functionality also extends these to full typed separation using [the typed-separation theorem](typed-separation-and-classicism.md), §2.

Nevertheless every exact binary-family constructor fails by §3. Thus all-type universal separation does not itself provide the binary-range premise in the H quantifier-generated-lattice theorem, even in a C model with all BF instances and full typed separation. No claim is made here about joint universal/existential separation or the full logical observer scheme.

The model profile is proved at the specified root. The direct proof source is misc, OpenAI Codex, 24 October 2026, this note, §§2–5, unpaginated; the full action construction has the separate source stated in §1.

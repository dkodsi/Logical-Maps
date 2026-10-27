# CH and analysis separate ordinary from reversible observers

25 October 2026. Ordinary mathematical research by OpenAI Codex. Direct source for the generic-evaluation construction and its observer verification: `misc`, the linked proof and audits, unpaginated. The underlying Boolean-valued construction and reversible pure-truth theorem retain their separate attribution. No native records or formal certificates are changed.

**The two branches are settled: Rev propagates CH and analysis; C5 + OS does not.** The negative examples even admit separation by observers with qualified left inverses (SplitMono), hence also native-Box-preserving separation. They use ordinary relative consistency assumptions on ZFC, not a countable transitive model assumption.

| Assumptions | CH and first-order analytical truth |
|---|---|
| C5 + OS | Current truth need not be necessary |
| C5 + SplitMono, hence also BoxSep | Current truth still need not be necessary |
| Rev | Current truth is necessary; full Rev already supplies C5 |

Here analytical sentences use the real field together with its natural-numbers predicate. Realhood uses completeness for **nonempty** bounded admitted subproperties. For a carrier type $`\sigma`$, the precise assertion is

```math
U_{\sigma,\varphi}:=\forall\mathfrak R\,
  (\mathrm{Real}_\sigma(\mathfrak R)\to\varphi(\mathfrak R)),
\qquad U_{\sigma,\varphi}\to\Box U_{\sigma,\varphi}.
```

## Why Rev succeeds

The existing theorem Rev implies No Pure Contingency applies directly: after expanding the definitions, each $`U_{\sigma,\varphi}`$ is a closed pure sentence. All its field data, including its natural-numbers predicate, are bound variables. A reversible observer and its admitted inverse induce mutually inverse transformations at every type occurring in the sentence. Conjugation fixes the logical operations and transports every quantified domain bijectively, so the observer fixes the sentence itself. Separation then makes a true sentence identical to Top.

Thus Rev gives both signs of propagation, for CH and for every finite first- or second-order analytical sentence. Categoricity supplies the corresponding native non-contingency principles. No actual-existence hypothesis is needed for this positive argument. See [the full reversible proof](rev-analysis.md).

## Why C5 + OS fails

The decisive change to the previous Boolean-valued model is its **truth evaluation**. Work inside a countable model $`M`$ of the indicated ZFC theory. Take

```math
B=2\times A,
```

where $`A`$ is an internally complete atomless forcing algebra. Use the internally full typed function domains of $`M`$, but declare $`(\epsilon,b)`$ true when $`b`$ belongs to an externally chosen $`M`$-generic ultrafilter $`G`$ on $`A`$. The isolated atom $`a=(1,0)`$ remains possible and is currently false.

Genericity preserves precisely the joins and meets of the admitted, internally coded families. This gives ordinary actual quantifier semantics; it does not postulate an ultrafilter complete for arbitrary external families. Defined identity is crisp, and therefore C5 holds.

Weak homogeneity supplies enough internal Boolean automorphisms to make every nonzero atomless component true under some admitted observer. A further admitted observer handles the isolated-atom component. All these observers preserve the whole Boolean and quantifier operations, not merely their current truth values. This proves full current OS.

For the forcings used below, the isolated-atom component can even be handled by an injective observer with a qualified admitted left inverse. Choose a nonzero basic condition $`c\notin G`$ and an internal complete isomorphism $`h:A\to A\mathbin{\upharpoonright}c`$. Put

```math
\begin{aligned}
E(\epsilon,b)&=(\epsilon,\epsilon\neg c\vee h(b)),\\
F(\epsilon,d)&=(\epsilon,h^{-1}(d\wedge c)).
\end{aligned}
```

Then $`F\circ E=I`$, both operations are qualified, and $`E(a)`$ is currently true because $`\neg c\in G`$. Together with the automorphism observers, this proves current SplitMono. It does not give two-sided inverses: every Boolean automorphism fixes the unique atom $`a`$, so reversible observers cannot distinguish that false, nonzero proposition from Bottom.

The full construction and admission proof are in [the generic-point countermodel](os-analysis-model.md), with independent audits of [generic quantifiers and qualified left inverses](os-analysis-positive.md) and [forcing and carrier capacity](generic-observer-model-audit.md).

## The mathematical disagreements

The existing extensional forcing-transfer lemma identifies the Boolean value of universal analytical truth with

```math
\llbracket U_{t,\varphi}\rrbracket
 =\bigl(\mathbf 1_{M\models\varphi(\mathbb R)},
         \|\varphi(\mathbb R)\|_A^M\bigr).
```

There is a real-structure tuple of value Top, so the examples have actual real structures and no vacuity is involved. The proposition type $`t`$ has sufficient carrier capacity in each construction.

* **CH true but not necessary.** Start with $`M\models\mathrm{ZFC}+\neg\mathrm{CH}`$. Force with countable partial functions from $`\omega_1`$ to $`\kappa=(2^{\aleph_0})^M`$. This homogeneous countably closed forcing collapses the old continuum to $`\omega_1`$, adds no reals, and forces CH. Thus $`U_{t,\mathrm{CH}}`$ has value $`(0,1)`$: true at the generic evaluation and not necessary.
* **Negated CH true but not necessary.** Start with $`M\models\mathrm{ZFC}+V=L`$ and add $`\omega_2`$ Cohen reals. Then $`U_{t,\neg\mathrm{CH}}`$ has value $`(0,1)`$, while ground-model CH occupies the isolated atom.
* **First-order analysis true but not necessary.** In the same Cohen example, take the finite first-order analytical sentence $`\psi`$ expressing the existence of a nonconstructible real. Its field-language coding uses the natural-numbers predicate. The ground satisfies its negation and forcing satisfies $`\psi`$, so $`U_{t,\psi}`$ again has value $`(0,1)`$.

In each case the opposite universal assertion has value $`(1,0)`$. Both boxes are false, so the examples refute the relevant native non-contingency principle as well as current-to-necessary propagation. The displayed models also retain necessary BF and necessary Relational Choice.

## Status and boundaries

The Rev implication is an application of an existing observer theorem. The generic truth evaluation, its exact quantifier check, and the resulting OS/SplitMono countermodels are the new arguments of this investigation. Independent ordinary proof audits support the construction; no historical novelty or machine verification is claimed.

The exact metatheory is a countable model of each specified ZFC theory plus an external generic filter, which exists by countability. The construction works for nonstandard, ill-founded models as well. Standard relative consistency results for CH and its negation therefore give these countermodels assuming Con(ZFC).

Only **current** OS and SplitMono are asserted. The isolated-atom evaluation still fails OS qualified at $`t`$, so necessary OS fails. The examples do not resolve the different question obtained by replacing OS with its separately boxed schema.

This result supersedes the C5 + OS gap left in [the earlier mathematical propagation note](mathematical-propagation.md) and [CH/analysis audit](ch-analysis-audit.md). No compilation is required.

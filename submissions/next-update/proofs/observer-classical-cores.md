# Logical retractions determine whole typed cores

Over C5, an idempotent logical observer determines a C5 Henkin model at every relational type. Its individuals are unchanged and its propositions form the observer's image. Observers with the same image give canonically isomorphic pointed models. Functional Choice and Boolean Completeness descend instancewise, and commuting retractions give intersections of cores.

The [endpoint theorem over bare C](endpoint-classical-cores.md) removes C5 for one endpoint observer with all typed quantifier laws; its whole idempotence follows from those laws. The [mathematical inheritance](observer-core-mathematics.md) and [recovery theorems](observer-core-recovery.md) develop the C5 construction below.

## 1. Assumptions and normalization

Let $`M`$ be a pointed general C5 model. C5 includes ☐ND at every type; its established BF and Functionality consequences give an actual-function presentation. Write $`D_\sigma`$ for its domains, with $`D_t`$ a Boolean algebra and current truth given by its distinguished ultrafilter. Admitted quantified predicates have Boolean infima and suprema with the ordinary current truth clauses. Identity is Top for identical objects and Bottom otherwise.

Let $`E:tt`$ preserve the Boolean operations and the proposition quantifier as whole operations, and satisfy $`E\circ E=E`$. The established [C5 quantifier reduction](../../classicism-results-2026-10-24-v2/proofs/modal-selectors-and-quantifier-reduction.md#4-over-c5-q_t-supplies-every-quantifier) gives this same observer every typed quantifier law.

Define recursively

```math
r_e(x)=x,\qquad r_t(p)=E(p),\qquad
r_{\sigma\tau}(f)=\lambda x^\sigma\, .\,r_\tau\bigl(f(r_\sigma(x))\bigr).
```

The individual identity is external notation: when $`\sigma=e`$, use $`x`$ directly. No operation of type $`ee`$ is introduced. All relational normalizations are admitted lambda terms. Induction gives $`r_\sigma^2=r_\sigma`$. Put

```math
D_\sigma^E=\{x\in D_\sigma:r_\sigma(x)=x\}.
```

These domains are nonempty and definable. A fixed arrow $`f`$ satisfies

```math
r_\tau\circ f=f,\qquad f\circ r_\sigma=f.
```

Indeed, apply idempotence to either side of $`f=r_\tau\circ f\circ r_\sigma`$. It follows that fixed arrows take fixed inputs to fixed outputs and are determined by their restrictions to fixed inputs. They therefore form an actual-function subset of $`(D_\tau^E)^{D_\sigma^E}`$.

At every relational type, normalization is a Boolean endomorphism for the pointwise operations. This follows by induction from Boolean preservation by $`E`$. Thus the fixed domains have the original endpoints and their inherited Boolean order.

## 2. The core is a C5 model

Interpret a logical constant $`c`$ in the core by $`r_{\mathrm{type}(c)}(c)`$, restricted to fixed arguments. Boolean operations are their original restrictions to $`\mathrm{Im}(E)`$.

For a fixed predicate $`F`$, we have $`E\circ F=F`$ and $`F\circ r_\sigma=F`$. Hence

```math
E(Q_\sigma F)=Q_\sigma(E\circ F)=Q_\sigma F.
```

The range of $`F`$ on all original inputs equals its range on fixed inputs. Its original infimum is consequently fixed and is precisely the core universal value. The same range equality and the ambient quantifier truth clause give the required current truth clause. Existential quantification is dual.

For fixed $`a`$, the admitted predicate $`x\mapsto\delta_\sigma(r_\sigma(x),a)`$ is fixed: it is invariant under normalization of its input and has endpoint outputs. It distinguishes $`a`$ from every other fixed object. Thus Leibniz equality computed using core predicates is crisp identity on the core domains.

For lambda closure, translate terms recursively by normalizing variables, projecting constants, preserving application, and abstracting the translated bodies. Induction shows that each translated body takes fixed values and is invariant under normalization of its arguments. The resulting abstraction is therefore a fixed arrow and computes the core interpretation on fixed assignments. All these expressions are admitted ambient terms. Beta and eta follow from their actual-function interpretation.

The Boolean and quantifier clauses validate H and its algebraic theorem identities. If H proves an equivalence, the corresponding core proposition denotations agree under every assignment; actual-function extensionality then identifies their abstractions. This verifies C's original theoremhood restriction. Crisp equality gives ND and its box at every type. The resulting pointed C5 model $`M_E`$ has individual domain $`D_e`$, proposition algebra $`\mathrm{Im}(E)`$, and current truth inherited on that image.

## 3. Same image, canonical isomorphism

Suppose $`E,F`$ are logical retractions with the same proposition image. Each fixes that image, so

```math
E\circ F=F,\qquad F\circ E=E.
```

Induction through the normalization formula gives

```math
r_\sigma^E r_\sigma^F r_\sigma^E=r_\sigma^E,
\qquad r_\sigma^F r_\sigma^E r_\sigma^F=r_\sigma^F,
```

where juxtaposition in these equations denotes composition. At an arrow, the triple on the input occurs in reverse order; its palindromic form gives the same induction hypothesis.

Define $`\Phi_\sigma(x)=r_\sigma^F(x)`$ on $`D_\sigma^E`$. These equations give inverse $`r_\sigma^E`$. The maps are identity on individuals and on the common proposition image. For fixed $`f,x`$ in the E-core,

```math
\begin{aligned}
\Phi_{\sigma\tau}(f)(\Phi_\sigma(x))
&=r_\tau^F\bigl(f(r_\sigma^F(x))\bigr)\\
&=r_\tau^F\bigl(f(r_\sigma^E r_\sigma^F r_\sigma^E(x))\bigr)\\
&=r_\tau^F(f(x))=\Phi_\tau(f(x)).
\end{aligned}
```

The second step uses input invariance of $`f`$ and fixedness of $`x`$. Thus application is preserved. A predicate and its image have the same proposition-value range, giving preservation of quantifiers. Boolean operations, identity, abstraction and current truth are preserved as well.

These are isomorphisms of the pure logical cores, also preserving individual constants. For a relational named constant c, an expanded isomorphism additionally requires $`\Phi(r^E(c))=r^F(c)`$; equality of the proposition images alone does not ensure this.

These pointed logical isomorphisms compose coherently. Any two such maps fixing the base domains and preserving application agree by induction through actual-function types. In particular, the isomorphism from one core to a third equals the composite through any second core with that image.

More generally the equations $`EFE=E`$ and $`FEF=F`$ suffice for an unpointed logical isomorphism, using $`F`$ as the isomorphism between proposition images. It need not preserve current truth. The pointed assertion retains the same-image hypothesis.

Every endpoint-valued logical observer fixes both endpoints and is idempotent, with image $`\{\bot,\top\}`$. Consequently all such observers in a given C5 model determine one classical two-valued Henkin core, up to these canonical isomorphisms. The core need not be full standard.

## 4. Choice and completeness descend

Suppose the ambient model satisfies Functional Choice at $`\sigma,\tau`$. A serial core relation, viewed as an ambient normalized relation, is invariant under normalization of both arguments. Its core seriality implies ambient seriality: for ambient $`x`$, use a core witness for $`r_\sigma(x)`$. Ambient Functional Choice supplies $`f`$. Then $`g=r_{\sigma\tau}(f)`$ is a core selector, since on a core input $`x`$,

```math
R[x,g(x)]=R[x,r_\tau(f(x))]=R[x,f(x)].
```

This uses invariance of the relation, without applying an observer to a merely true Choice assertion.

Suppose the ambient model satisfies Boolean Completeness at relational $`\tau`$. For a core family $`P`$, take the ambient predicate

```math
P'(x)=(r_\tau(x)=x)\land P(x).
```

Its current instances are exactly the selected core objects. Let $`y`$ be their ambient greatest lower bound. Then $`z=r_\tau(y)`$ is still a lower bound, because normalization is monotone and fixes every family member. Any core lower bound $`v`$ satisfies $`v\le y`$, hence $`v=r_\tau(v)\le z`$. The inherited order is the core Boolean order, so $`z`$ is its infimum. Both inheritance results concern the same current instances; no premise is necessitated.

## 5. Intersections and the limitation on truth transfer

If $`E,F`$ commute, their composite is a logical retraction. Induction gives

```math
r_\sigma^E r_\sigma^F=r_\sigma^F r_\sigma^E=r_\sigma^{EF},
\qquad D_\sigma^{EF}=D_\sigma^E\cap D_\sigma^F.
```

The intersection, with the projected operations, is again a C5 core.

Normalization does not preserve arbitrary ambient application. If $`Ep\ne p`$ and $`H(q)=(q=p)`$, crisp equality gives

```math
E(H(p))=\top,\qquad r_{tt}(H)(E(p))=E(H(E(p)))=\bot.
```

Accordingly this is not an elementary-submodel theorem or an invariance theorem for arbitrary original sentences. The interpretation translates terms recursively through the entire hierarchy. Restricting only the outputs would omit the necessary input invariance.

## Sources and contribution

Whole typed cores, canonical comparison, inheritance and intersections: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`), `general-observer-principles/structure.txt`, §§2–8, unpaginated; [source manifest](../evidence/source-manifest.json).

The existing C5 ⇒ BF step is attributed to Prior and Lemmon in Bacon–Dorr, *Classicism*, draft of 16 May 2023, Proposition 2.3, p. 22 (`necessary-nd-implies-bf`); BF ⇒ Functionality is Bacon–Dorr, Proposition 2.1 n. 27, pp. 20–21 (`barcan-r-implies-functionality-r`). The C5 quantifier reduction is linked above. Earlier Boolean-image results are inputs to the comparison, not newly claimed here.

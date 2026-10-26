# Classical cores from endpoint retractions over C

OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`).

## 1. Main theorem and qualification

Let M be any general model of the fixed C, with native actual identity in its usual identity-quotient presentation. No BF, Functionality, ND or C5 assumption is made. Suppose one admitted E:tt satisfies:

- **(B) Boolean laws:** the whole Boolean-preservation identities.
- **(Q) Quantifier laws:** the whole $`Q_\sigma`$ identity at each admitted type.
- **(V) Endpoints:** every $`Ep`$ is Top or Bottom.

There is a canonical classical, two-valued, extensional Henkin model obtained by recursively normalizing all relational types and quotienting the individuals by E-observed identity. Functional Choice and Boolean Completeness descend instance by instance. Any two such observers produce canonically isomorphic pointed models, with the same individual quotient. The canonicity assertion concerns the pure logical cores (and expansions by individually named constants). Arbitrary relational signature constants require the compatibility condition stated at the end of Section 6.

Here (Q) qualifies one observer through every type. It is not an illicit object-language quantifier over types or an infinite conjunction concealed in one formula. Every finite fragment of the construction uses finitely many of these laws. A separation schema with a potentially different witness for each finite list is not itself being assumed to furnish one simultaneous witness in the original model.

**Derived idempotence (I).** Boolean preservation and the quantifier law at t already give the whole identity $`E\circ E=E`$. Put

```math
d_E:=\forall p^t.\,(Ep\leftrightarrow p).
```

Whole preservation gives

```math
E(d_E)=\forall p^t.\,(E(Ep)\leftrightarrow Ep).
```

Every Ep is an endpoint fixed by E, so the right side is currently true. The left side is itself an endpoint, hence equals Top. The universal coextension assertion is therefore necessary; C's Intensionality and β/η yield the whole identity E∘E=E. No optional premise is necessitated and no ambient Functionality is used. The canonicity argument below separately establishes its whole-operation comparison identities.

This improves the endpoint case of the [C5 core construction](observer-classical-cores.md) by removing C5 altogether. The old arbitrary-Boolean-image theorem remains under its stated C5 hypothesis. The present theorem does not claim that all Boolean images enjoy this stronger bare-C conclusion.

## 2. Normalizers without Functionality

Use $`r_{e}`$=id externally; no forbidden ee object is introduced. Put

```math
r_t=E,\qquad r_{\sigma\tau}(f)=\lambda x.\,r_\tau(f(r_\sigma(x))).\tag{2.1}
```

At an e input omit the external $`r_{e}`$. Every relational normalizer is an admitted lambda term. Whole β/η identities and congruence give, inductively from (I),

```math
r_\sigma\circ r_\sigma=r_\sigma.\tag{2.2}
```

as a whole operation identity. At the arrow step the composite rewrites to $`r_{\tau}`$ $`r_{\tau}`$ f $`r_{\sigma}`$ $`r_{\sigma}`$; replace the two whole composites by their inductive identities. This is equational rewriting under lambda, not inference of function identity from merely pointwise agreement.

Write $`S_{\sigma}`$=Fix($`r_{\sigma}`$), with $`S_{e}`$=$`D_{e}`$. Every fixed set is nonempty. An object f in $`S_{\sigma\tau}`$ satisfies the whole identities

```math
r_\tau\circ f=f,\qquad f\circ r_\sigma=f.\tag{2.3}
```

Indeed f=$`r_{\tau}`$ f $`r_{\sigma}`$; postcompose by $`r_{\tau}`$ or precompose by $`r_{\sigma}`$ and use (2.2). Consequently fixed functions take fixed inputs to fixed outputs and ignore input normalization.

In flattened form $`\tau=\sigma_1\cdots\sigma_nt`$, a fixed relation f has the whole terminal-output identity and all input-invariance identities

```math
\begin{aligned}f&=\lambda\bar x.\,E(f[\bar x]),\\f&=\lambda\bar x.\,f[r_{\sigma_1}(x_1),\ldots,r_{\sigma_n}(x_n)].\end{aligned}\tag{2.4}
```

These follow by unrolling (2.1), applying idempotence at each input and at t, and rewriting whole composites. All terminal values of f are endpoints by (V). Boolean operations preserve fixed objects, by (B).

## 3. Extensionality inside the fixed hierarchy

If an admitted predicate H:σ t satisfies $`E\circ H=H`$ as a whole identity, then (Q) gives E($`Q_\sigma`$ H)=$`Q_\sigma`$ H. Hence $`Q_\sigma`$ H is an endpoint. If H is true of every original input, the original quantifier truth clause says $`Q_\sigma`$ H is true; its being an endpoint now gives

```math
Q_\sigma H=\top.\tag{3.1}
```

There is no optional necessitation here. The actual universal is an endpoint and actually true. Iterating the whole quantifier identities gives the same conclusion for any finite tuple of input types.

**Extensionality lemma.** If f,g belong to $`S_{\tau}`$, where $`\tau=\sigma_1\cdots\sigma_nt`$, and f[xbar],g[xbar] have the same actual truth value at every tuple of fixed arguments, then f=g in M.

Proof. By input invariance, the truth agreement holds for every tuple of original arguments: replace each argument by its normalization. Put H=lambda xbar.(f[xbar] iff g[xbar]). Boolean preservation and the whole terminal-output identities (2.4) give $`E\circ H=H`$ at terminal output as a whole identity. Its universal closure is true and E-fixed by (Q), and therefore Top by (V). C's Intensionality, applied to this genuinely necessary universal equivalence, identifies f and g. For n=0 both objects are endpoints, so their truth agreement already identifies them. QED.

In particular fixed arrow objects are determined by their values on fixed inputs. Ambient operations need not have this property. This is the step that replaces the original theorem's appeal to C5 -> BF -> Functionality.

## 4. Observed identity and the individual quotient

For any original objects a,b of type σ, put

```math
a\mathrel{\approx_E}b\quad\Longleftrightarrow\quad E(\delta_\sigma(a,b))=\top.\tag{4.1}
```

The Boolean and $`Q_{\sigma t}`$ laws, applied to the defining Leibniz formula, give the exact actual-truth criterion

```math
a\mathrel{\approx_E}b\quad\Longleftrightarrow\quad\forall P^{\sigma t}.\,(E(Pa)\leftrightarrow E(Pb)).\tag{4.2}
```

This is an equivalence relation. When a,b are fixed, normalizing P gives

```math
\begin{gathered}P^{\prime}=r_{\sigma t}(P)=E\circ P\circ r_\sigma,\\P^{\prime}a=E(Pa),\qquad P^{\prime}b=E(Pb).\end{gathered}\tag{4.3}
```

Every P' is fixed, and every fixed predicate occurs among these. Thus on fixed objects approx_E is exactly indistinguishability by fixed predicates.

At a relational type, this equivalence is literal EQUALITY on $`S_{\sigma}`$. If a≠b there, the Extensionality Lemma supplies a fixed terminal tuple at which their truth values differ. Normalize the evaluation predicate x |-> x[tuple]. It is a fixed σ t predicate, and its values on a,b are their original endpoint values at that tuple. It separates them.

At e, in contrast, approx_E may identify different individuals. Define the core individual domain to be $`D_{e}`$/approx_E. Retain each relational domain $`S_{\tau}`$, identifying its objects with their induced actual functions on the core input domains.

Application is well defined on individual classes. For f in $`S_{e\tau}`$, if $`a\approx_E b`$, every fixed terminal evaluation of f(a),f(b) agrees: x |-> f(x)[tuple] is a fixed et predicate, by (2.4). The Extensionality Lemma therefore gives f(a)=f(b). At nonindividual inputs no further quotient is needed. The same lemma shows that different fixed arrow objects induce different functions on the resulting core domains.

Only the individual quotient is required in this normalized construction. The quotient of the entire original hierarchy by (4.1) would be a different construction; it need not turn its original proposition domain into 2.

## 5. Logic, lambda closure and the C gate

Interpret a logical or signature constant c by r_type(c)(c), with its restriction to the core inputs; an individual constant is interpreted by its approx_E class. The proposition domain is exactly {Bottom,Top}.

Boolean operations have their ordinary two-valued meanings. If F is a fixed σ t predicate, $`Q_\sigma`$ F is E-fixed by (Q). Its actual truth is universal truth over the original domain, which equals universal truth over the normalized domain by input invariance, and over the individual quotient where appropriate by (4.2). Thus the projected quantifier is exactly the core's ordinary universal quantifier. Existential quantifiers follow by Boolean duality. This also proves that projected Q evaluates F as $`Q_\sigma`$ F itself.

For lambda closure, recursively translate core terms into original terms: normalize each relational variable, replace constants by their projected constants, preserve application, and abstract the translated body. The inductive output is fixed and invariant under normalizing every free input. Its abstraction therefore satisfies (2.3) as a whole term identity and belongs to the appropriate $`S_{\sigma\tau}`$. Equational β/η and congruence justify this structural induction; ambient Functionality is not inserted. Individual representatives are harmless because every fixed arrow respects approx_E as proved in Section 4.

The fixed predicates distinguish exactly the core objects, by Section 4. So derived Leibniz identity in this two-valued structure is ordinary literal identity. We have constructed an extensional, two-valued Henkin model with the correct Boolean, quantifier, application and lambda clauses. It validates H. An H-equivalence has the same truth value at every core assignment; actual-function extensionality of these core domains then identifies the corresponding abstractions. This verifies C's exact Logical Equivalence gate, without treating an equivalence derived from optional observer premises as an H-theorem in the original model.

**Theorem 5.1.** The resulting core is a classical two-valued extensional Henkin model of C, hence of C5 and the full Extensionality schema.

No external fullness of its function domains is asserted.

## 6. Canonicity over C

First, any two endpoint-valued Boolean/all-Q observers E,F agree on the relation (4.1), even on arbitrary original objects and without assuming whole idempotence for this particular observation. Suppose E(delta(a,b)) is Top. By (4.2), E(Pa) and E(Pb) agree for every admitted P. Substitute F o P. Since F's values are endpoints and E fixes endpoints, this gives F(Pa)=F(Pb) for every P. The F version of (4.2) gives F(delta(a,b))=Top. The reverse implication is symmetric. Since both observed identity values are endpoints, they are equal.

Thus every eligible retraction has the same individual quotient.

Now let E,F satisfy all four qualifications of Section 1. Crucially we can prove the whole mutual triple identities without upgrading any arbitrary pointwise equality:

```math
E\circ F\circ E=E,\qquad F\circ E\circ F=F.\tag{6.1}
```

Indeed EFE is $`r_{tt}^E`$(F), so is E-normalized. E is also E-normalized by whole idempotence. On the two E-fixed arguments Bottom and Top, both operations are identity because F fixes endpoints. The Extensionality Lemma inside the E-fixed hierarchy gives EFE=E as a whole operation identity. Exchange E,F for the other equation.

Equational induction through (2.1) now gives

```math
\begin{aligned}r_\sigma^E r_\sigma^F r_\sigma^E&=r_\sigma^E,\\r_\sigma^F r_\sigma^E r_\sigma^F&=r_\sigma^F.\end{aligned}\tag{6.2}
```

Define Phi_sigma(x)=$`r_{\sigma}^F`$(x) on the E-fixed relational domain. At e use the identity on the common quotient. Equations (6.2) give inverse $`r_{\sigma}^E`$. The maps are identity on the endpoint proposition domain.

They preserve application: for E-fixed f,x, using (2.3) and (6.2),

```math
\begin{aligned}\Phi(f)(\Phi(x))&=r_\tau^F(f(r_\sigma^F(x)))\\&=r_\tau^F(f(r_\sigma^E r_\sigma^F r_\sigma^E(x)))\\&=r_\tau^F(f(x))=\Phi(f(x)).\end{aligned}\tag{6.3}
```

At individual input use the shared quotient; the calculation is just the external identity normalization. Bijection of argument domains and identity at t preserve all quantifiers, Booleans and current truth. Thus Φ is a pointed logical isomorphism. These isomorphisms compose coherently: an application-preserving map fixing e and t is unique by induction through the core's actual function types.

**Theorem 6.1.** Every fully qualified endpoint logical retraction determines the same pure classical Henkin core, up to canonical coherent isomorphism.

No whole EF=F or FE=E is assumed or needed. The whole triple equations are proved by the new internal extensionality argument.

Individual constants are also preserved, since their core interpretations are their classes in the common individual quotient. Arbitrary relational signature constants need not be preserved. Already a proposition constant c may have E(c)≠F(c), whereas Phi_t is identity. Each normalized expansion in Section 5 exists, but its isomorphism to the other expanded core requires $`\Phi(r^E(c))=r^F(c)`$ for every named relational constant. Jointly fixed constants are one sufficient case. No observer-independent truth claim for arbitrary relationally expanded theories is made.

## 7. Functional Choice and Boolean Completeness descend

Functional Choice descends instancewise exactly as in the C5 argument. For a core serial R, its original normalized relation ignores normalized inputs and outputs. Core seriality therefore gives original current seriality. An ambient selecting operation f exists by the given FC instance. Its normalization g=$`r_{\sigma\tau}`$(f) is a core operation, and for a fixed input x,

```math
R(x,g(x))=R(x,r_\tau(f(x)))=R(x,f(x)).\tag{7.1}
```

This is the same proposition. Individual classes are respected by the core operations. No observer is applied to an arbitrary merely true selector assertion.

For Boolean Completeness at relational τ, $`r_{\tau}`$ is a Boolean endomorphism and therefore monotone for the original algebraic order; the proof is by equational induction using whole (B). The order on its fixed domain is precisely the core Boolean order. For example, core pointwise entailment between fixed relations gives the corresponding whole identity by the Extensionality Lemma, and the converse is immediate.

For a core family P use the original predicate $`P^{\prime}(x):=(r_\tau(x)=x)\land P(x)`$. Its current instances are exactly the fixed core members of P. Let y be their ambient GLB, supplied by ambient BC. Then $`r_{\tau}`$(y) is a lower bound, by monotonicity and fixedness of every selected member. Every fixed competing lower bound v is also an ambient lower bound, so v≤y and hence v=$`r_{\tau}`$(v)≤$`r_{\tau}`$(y). This is the core GLB.

These are current, instance-local inheritance theorems. Neither optional premise was necessitated. No unrestricted truth-transfer theorem follows.

## 8. Why the individual quotient is needed

Take the full coherent two-stage model with current individuals {a,b} mapping onto a singleton classical future, both sent to *. At t the current propositions are pairs (p0,p1), with actual truth p0. At every relational type admit all coherent current functions/future objects. Every transport $`q_{\sigma}`$ is onto: inductively choose coherent current lifts of each future operation; all required current functions are admitted in the full model.

The terminal reader E(p0,p1)=(p1,p1), with future identity component, is an admitted Boolean endpoint observer and is whole idempotent. It preserves every $`Q_\sigma`$ as a whole operation: at the current component surjectivity of $`q_{\sigma}`$ makes quantification over all current images equal quantification over the future domain; at the future component both operations are identical.

Yet delta_e(a,b)=(0,1), so a≠b currently but their possible future identity holds. In particular C5 fails. E(delta_e(a,b))=(1,1), and the core's individual domain has one member. Thus the new hypotheses really permit models outside C5, and retaining all the original individuals would be false. This example has BF; no independence from BF is claimed.

## 9. Scope

Over C, a fully qualified endpoint logical retraction gives a canonical classical Henkin core. Its individual quotient is independent of the observer, and its canonical isomorphisms do not require ambient Functionality. Functional Choice and Boolean Completeness descend. The usual C5 endpoint theorem is recovered because C5 makes observed identities literal, so its individual quotient is trivial.

Full standardness requires the additional completeness condition characterized below.

Quotienting the entire original hierarchy by observed identity does not suffice to classicalize propositions. In a C5 model delta_sigma(a,b) is already an endpoint for every original a,b, so any Boolean observer leaves all those equality values unchanged. Quotienting by observed identity would therefore leave the entire original proposition domain intact. Recursive normalization before taking the quotient is essential.

## Sources

The earlier [C5 core construction](observer-classical-cores.md) supplies the normalization design. [Logical-observer qualifications](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/observer-lattice.md) and the [fixed framework](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/topics/classicism/background.md) fix the Boolean, quantifier and Intensionality clauses. The two-stage example is expanded in [Why the endpoint core can identify individuals](endpoint-core-individual-quotient.md). The [full-standardness criterion](observer-core-mathematics.md#2-full-standardness-and-external-completeness) requires an additional external completeness condition.

The diagonal idempotence argument is OpenAI Codex, prompted by Daniel Kodsi, *Endpoint observers are automatically whole-idempotent*, 25 October 2026, §§1–2, unpaginated (`misc`).

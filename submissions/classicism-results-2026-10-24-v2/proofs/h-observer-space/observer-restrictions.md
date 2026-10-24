# Observer restrictions over H

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–7, unpaginated. The results below are ordinary proofs over H.

Restrictions on observer truth, number and output range have different effects. Factivity alone collapses the false propositions; material negation preservation turns it into complete truth-correctness. One separating observer collapses propositions to the two truth values, whereas a finite family gives an exact finite cardinal bound. In the identity-collapse branch, explicit observers already have two outputs and are idempotent.

## 1. Notation and type scope

Use the fixed relational language and the usual fixed abbreviations T for Top and B for Bottom. H proves T true, B false and T distinct from B. For E of type tt put

$$
\begin{aligned}
A(E)&:=ET,& Z(E)&:=\neg EB,\\
\mathrm{Fact}(E)&:=\forall p\,(Ep\to p),&
\mathrm{Infl}(E)&:=\forall p\,(p\to Ep),\\
\mathrm{Correct}(E)&:=\forall p\,(Ep\leftrightarrow p),&
N_{\rm mat}(E)&:=\forall p\,[E(\neg p)\leftrightarrow\neg Ep].
\end{aligned}
$$

Inflationarity here concerns ordinary truth implication; it is not an order relation between proposition objects. Factivity is likewise truth reflection. The two endpoint clauses A,Z assert acceptance and rejection, not output identities.

For a qualification K(E), write

$$
S[K]:=\forall p,q\left[
p=q\leftrightarrow\forall E\bigl(K(E)\to(Ep\leftrightarrow Eq)\bigr)
\right].
$$

The relational instance Sep_tau[K], for tau=sigma_1...sigma_n t, tests E(X[arguments]) and E(Y[arguments]) at every current argument tuple. FullSep[K] is the schema at every relational type. The [general H lifting theorem](typed-separation-and-classicism.md), §2, gives

$$
\mathrm{FullSep}[K]
\quad\leftrightarrow\quad
S[K]+\mathrm{Functionality}.
$$

Functionality is the explicit schema from pointwise identity to identity of functions with relational codomain. It is not a background rule in the arguments below.

Define the two one-sided truth collapses

$$
\mathrm{NC}:=\forall p\,(\neg p\to p=B),\qquad
\mathrm{PC}:=\forall p\,(p\to p=T).
$$

The Fregean Axiom FA says materially equivalent propositions are identical. Over H,

$$
\mathrm{FA}\quad\leftrightarrow\quad \mathrm{NC}\land\mathrm{PC}.
$$

Indeed false propositions then all equal B and true propositions all equal T. Conversely FA identifies a false proposition with B and a true proposition with T.

## 2. Factivity and inflationarity have exact one-sided effects

**Theorem 1.** Over H,

$$
\boxed{S[\mathrm{Fact}]
\ \leftrightarrow\
S[A\land Z\land\mathrm{Fact}]
\ \leftrightarrow\ \mathrm{NC},}
$$

$$
\boxed{S[\mathrm{Infl}]
\ \leftrightarrow\
S[A\land Z\land\mathrm{Infl}]
\ \leftrightarrow\ \mathrm{PC}.}
$$

Either or both endpoint truth conditions may also be imposed separately, with the same respective characterization.

### Factivity

If p is false, every factive observer rejects p and B. Separation therefore gives p=B. This proves necessity of NC for unrestricted factive separation; restricting the qualified class only strengthens separation, so it proves necessity for the endpoint-restricted versions as well.

Conversely assume NC. The identity observer I(r):=r satisfies A, Z and Fact, and distinguishes propositions with different truth values. Distinct propositions with the same truth value must therefore both be true.

Let p,q be distinct true propositions. At least one differs from T; take such a proposition as a and use the admitted term

$$
F_a(r):=r\land(r\ne a).
$$

This is factive by its truth clause. It rejects B, and it accepts T because a differs from T. At a it is false, whereas at the other member of p,q it is true. Hence these endpoint-qualified factive tests separate every distinct pair, proving the strongest displayed version. No conjunction identity, identity bivalence or admission of an external function is used.

### Inflationarity

If p is true, every inflationary observer accepts p and T. Separation gives p=T, proving PC.

Conversely assume PC. Identity again distinguishes different-truth pairs. A distinct same-truth pair must now be false. Choose a member a different from B and use

$$
G_a(r):=r\lor(r=a).
$$

This is inflationary by its truth clause. It accepts T and rejects B because a differs from B. It accepts a and rejects the other false member of the pair. Thus A,Z-qualified inflationary tests separate.

The witnesses prove the converses even with both endpoint truth conditions, while every intermediate class lies between the endpoint-restricted and unrestricted classes. This proves all stated variants. ∎

**Typed consequence.** Full typed factive separation, with any of these endpoint truth choices, is exactly NC plus Functionality. The inflationary analogue is exactly PC plus Functionality. Neither package is thereby identified with full Extensionality.

The distinction is witnessed by finite full-function H models. Take three proposition objects, two true and one false, with truth-correct primitives, singleton individuals and all admitted function spaces full. Choose a designated true T and the unique false B as the outputs of the primitive logical operations according to their ordinary truth conditions. Equality has output T for identity and B otherwise. The fixed Top and Bottom abbreviations then have the designated values. NC and all Functionality instances hold, but PC fails at the second true proposition. Theorem 1 therefore gives full typed factive separation with both endpoint truth conditions while Extensionality fails. Dually, one true and two false proposition objects give PC plus Functionality without NC. These are ordinary full-function H models; no C soundness claim is made.

## 3. Negation converts either one-sided condition into correctness

**Lemma.** Over H,

$$
\mathrm{Fact}(E)\land N_{\rm mat}(E)
\ \longrightarrow\ \mathrm{Correct}(E),
$$

$$
\mathrm{Infl}(E)\land N_{\rm mat}(E)
\ \longrightarrow\ \mathrm{Correct}(E).
$$

For the first implication, apply factivity to neg p. Negation preservation turns the result into neg Ep implies neg p; contraposition gives p implies Ep. For the second, apply inflationarity to neg p and contrapose to obtain Ep implies p. These are truth-level arguments only.

More generally, suppose H proves K(I) and proves that every K-observer is Correct. Then, at each fixed relational type tau,

$$
\boxed{\mathrm{Sep}_{\tau}[K]
\quad\leftrightarrow\quad
\mathrm{Extensionality}_{\tau}.}
$$

If two relations are coextensive, truth-correct observers agree on all their values, so separation identifies them. Conversely agreement under all qualified observers includes agreement under identity, which is coextension; Extensionality identifies the relations.

Apply this to factivity plus material negation preservation, inflationarity plus material negation preservation, or factivity plus inflationarity. The same result holds if material negation preservation is replaced by pointwise or full-operation negation preservation, since those imply its truth law and identity satisfies all three versions in H. Additional qualifications may be retained whenever H proves them of identity.

At t this is exactly FA. Passing from the t instance to full Extensionality requires the explicit Functionality schema over H. No C-based upgrade from propositional Fregean to all relational types is used.

Thus adding both endpoint truth conditions to factivity leaves the one-sided collapse NC, while adding negation preservation gives complete truth-correctness and hence Extensionality through separation. These are distinct mechanisms.

## 4. One observer: a separating subfamily versus a unique qualified class

For a particular observer E write

$$
\mathrm{OneSep}(E):=
\forall p,q\,[p=q\leftrightarrow(Ep\leftrightarrow Eq)].
$$

This says that the singleton family containing E separates propositions. It does not say E is the only observer satisfying some independently specified qualification.

**Lemma.** Over H, OneSep(E) implies FA.

Since T differs from B, OneSep forces ET and EB to have opposite truth values. For every p, ordinary bivalence makes Ep agree with exactly one of ET,EB. OneSep therefore identifies p with T or B. The ordinary truth of p determines which: equality with T makes p true and equality with B makes p false. Hence NC and PC, equivalently FA.

Conversely FA makes identity a singleton separating family. Therefore, whenever H proves K(I),

$$
\boxed{\exists E\,[K(E)\land\mathrm{OneSep}(E)]
\quad\leftrightarrow\quad\mathrm{FA}.}
$$

This does not imply that the entire qualified class is a singleton. For example, with no qualification, both identity and negation remain distinct observers even when FA holds.

Now define the different assertion

$$
\mathrm{AtMostOne}[K]:=
\forall E,F\,[(K(E)\land K(F))\to E=F].
$$

**Theorem 2.** For arbitrary K, over H,

$$
S[K]+\mathrm{AtMostOne}[K]\ \longrightarrow\ \mathrm{FA},
$$

$$
\mathrm{FullSep}[K]+\mathrm{AtMostOne}[K]
\ \longrightarrow\ \mathrm{Extensionality}.
$$

Separation of T and B ensures some eligible observer exists and distinguishes them: otherwise every eligible observer would agree on T,B. At-most-one makes every eligible observer identical to this witness E. Thus S[K] becomes OneSep(E), and the lemma gives FA. Full typed separation additionally gives Functionality, which lifts propositional identity under material coextension to identity of arbitrary relations.

For an exact converse, suppose H proves K(I) and K(E) implies A(E) and Z(E). Then

$$
\boxed{
\mathrm{FullSep}[K]+\exists!E\,K(E)
\quad\leftrightarrow\quad
\mathrm{Extensionality}.}
$$

The existential uniqueness can equivalently be replaced by AtMostOne[K], since separation already supplies existence.

For the converse, Extensionality includes FA, so every p is T or B. Endpoint acceptance/rejection then makes every qualified E truth-correct. FA turns this into pointwise identity Ep=p, and Functionality at tt identifies E with I. Thus identity is the unique qualified observer. It also supplies full typed separation by Extensionality itself. These qualification conditions apply, in particular, to any standard preservation package with A,Z for which identity is admitted.

The role of uniqueness is therefore precise: a single separating subfamily is enough for the collapse, but uniqueness of the entire qualified class is a separate additional assertion whose converse needs restrictions on that class.

## 5. A fixed finite observer family gives a finite cardinal bound

Fix an external natural number n at least one. Define separation by a specified list E_1,...,E_n by

$$
\forall p,q\left[
p=q\leftrightarrow
\bigwedge_{i=1}^{n}(E_i p\leftrightarrow E_i q)
\right].
$$

Its truth-profile vector assigns to each proposition one of the 2^n Boolean patterns and distinguishes different propositions. Consequently it entails the finite sentence asserting that there are at most 2^n proposition objects:

$$
\mathrm{AtMost}_{2^n}(t):=
\forall p_0,\ldots,p_{2^n}\,
\bigvee_{0\le i<j\le 2^n}(p_i=p_j).
$$

The proof is the ordinary finite pigeonhole argument, expanded into a finite H truth-case argument. It does not identify observer outputs as proposition objects with Boolean numbers.

The same bound follows from S[K] if all qualified observers are among an explicitly given list of n observers. Indeed agreement under that list implies agreement under every qualified observer, so S[K] gives the required injectivity. Conversely, no assertion that an arbitrary preservation qualification admits such a list follows merely from the cardinal bound.

There is an exact converse when no observer qualification is imposed:

$$
\boxed{
\exists E_1,\ldots,E_n\ \text{whose listed truth profiles separate}
\quad\leftrightarrow\quad
\mathrm{AtMost}_{2^n}(t).}
$$

To prove it, the finite cardinal bound supplies a finite enumeration by k distinct objects a_1,...,a_k with k at most 2^n. This is finite classical reasoning in H: successively choose an unlisted object if one exists; exceeding 2^n distinct choices contradicts the bound. Equivalently, use the resulting finite disjunction of existential enumeration formulas for k=1,...,2^n. No choice schema is required.

Assign the enumerated objects distinct n-bit patterns. For each coordinate i, use the admitted term

$$
E_i(r):=\bigvee_{\substack{1\le j\le k\\
                         \text{bit }i\text{ of }j\text{'s code is }1}}
                   (r=a_j).
$$

An empty disjunction means the fixed false B. H truth conditions make these profiles exactly the chosen codes, so they separate. No pointwise or full-operation preservation is asserted for these coding observers.

All n, k, finite conjunctions and finite disjunctions in this section are externally fixed finite syntactic constructions. This result does not replace an internally formulated Frege-finiteness principle by external finiteness, and it does not concern finite image size of each observer.

## 6. Binary range and idempotence in the identity-collapse branch

Retain the notation and theorem of [Identity-fixing observers and identity collapse over H](identity-collapse.md): z:=(T=B), IC_t collapses each true propositional identity judgment to T and each false one to z. Define

$$
\mathrm{Range}_{T,z}(E):=
\forall r\,(Er=T\lor Er=z),
$$

$$
\mathrm{Idem}^{\rm pt}(E):=
\forall r\,E(Er)=Er,\qquad
\mathrm{Idem}^{\rm op}(E):=
(\lambda r.E(Er))=E.
$$

Under IC_t, the separating witnesses in that note are

$$
E_0(r):=(r=T),\qquad
E_a(r):=((r=T)=((r=a)=z))
\quad(a\ne T,\ a\ne z).
$$

Their exact output calculations show that their images lie in {T,z} and that they fix both T,z. They are therefore pointwise idempotent. Hence, for either Q equal to CorrectEq_t or to FixEq_t^pt,

$$
\boxed{
S[A\land Q\land\mathrm{Range}_{T,z}
                  \land\mathrm{Idem}^{\rm pt}]
\quad\leftrightarrow\quad \mathrm{IC}_t.}
$$

Forward, discard the two extra restrictions and apply the identity-collapse theorem. Backward, its same admitted witnesses already satisfy both extra clauses. Either extra clause can also be imposed alone.

Full typed separation with the strong equality-fixing qualification and the full idempotence identity is correspondingly equivalent to IC_t plus Functionality. The reverse uses Fun_(t,t) to upgrade pointwise idempotence and the two stated binary Functionality instances to upgrade equality fixing. The forward uses the general typed theorem and the identity-collapse necessity argument.

The two outputs are T and z, not necessarily the fixed T and B. These observers have explicitly at most two outputs; no internal finiteness interpretation is needed. Their normalization does not assert reversibility, which is a different restriction.

## 7. Sources and scope

The direct source for the original arguments in §§2–6 is this note (`misc`, OpenAI Codex, 24 October 2026, unpaginated). The one-sided converse witnesses, singleton arguments and fixed finite cardinal characterization are proved here. The identity-collapse normalization uses the explicit witnesses in the linked companion note.

The general typed lifting theorem is in [Typed separation and the recovery of Classicism over H](typed-separation-and-classicism.md), §2. The earlier complete-logical qualification factivity result is in [Logical-observer hierarchy](../logical-observer-hierarchy.md), §2; the present proofs isolate which hypotheses already suffice over H. The fixed framework and type scope are given in [Background](../../source/topics/classicism/background.md).

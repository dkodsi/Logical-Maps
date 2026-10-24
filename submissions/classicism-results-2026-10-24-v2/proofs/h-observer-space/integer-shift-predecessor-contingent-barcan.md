# Integer-shift predecessor: surjective separation with contingent Barcan

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new construction and observer verdicts: `misc`, this note, §§1–7, unpaginated. The ideally-full action-model framework and the earlier root extension are attributed in §8.

**Full surjective logical observer separation does not imply necessary BF.** The model below satisfies

```math
\boxed{\mathrm C+\mathrm{SurjSep}+\mathrm{BF}
\quad\text{and}\quad\neg\Box\mathrm{BF}_\sigma
\text{ for every admitted type }\sigma.}
\tag{1}
```

In particular the failures include e, t, and every higher relational type. The positive SurjSep verdict has every relational output type and every finite external qualification list. All witnesses preserve the full composite Boolean and listed quantifier operations, not just their current truth tables.

The construction adds an integer-translation coordinate to the finite-pinning ℕ/singleton all-maps model. Translation charts supply onto logical observers with kernel elements accepted at any prescribed evaluation arrow. A full root truth-profile extension then pairs these onto tails with the separating truth readers. The old smaller object still has non-surjective higher-type transports and refutes BF.

## 1. The integer-decorated category and its domains

Take two objects

```math
X=\mathbb N\times\mathbb Z,
\qquad Y=\{*\}\times\mathbb Z.
\tag{2}
```

Write X₀=ℕ and Y₀={*}. For W,Z∈{X,Y}, the arrows W→Z are exactly

```math
(f,k):(a,n)\longmapsto(f(a),n+k),
\qquad f:W_0\to Z_0,\quad k\in\mathbb Z.
\tag{3}
```

All functions f of the displayed source and target are allowed. Composition is

```math
(g,l)\circ(f,k)=(g\circ f,k+l),
\tag{4}
```

and identities are (id,0). Thus these sets and maps form a category. Call k the **tag** of the arrow. For each object Z, let u_Z=(id_{Z₀},1); this is an invertible arrow with inverse tag −1.

Use the ideally-full action model over this category with the ideal of finite subsets at both objects and no additional symmetry restriction. Individuals are the elements of the displayed base objects, acted on by (3). At a relational type, admitted intensions are exactly the profiles pinned by some finite subset of their source object. A pin P means that, for parallel arrows h,h′ agreeing on P, the profile has the same value on h,h′ when its future argument tuple is held fixed. Transport is right precomposition, and commutes with application and the logical interpretation.

The [finite-pinning framework](../../source/topics/classicism/groups/finite-support-two-object.yaml) applies to any category of sets and functions with finite ideals, not only to a category containing all functions between its objects. The arrows (3) meet its hypotheses: identities and composition are present, images of finite sets are finite, and the ideals are closed under finite unions. The general ideally-full construction therefore supplies the recursive domains, lambda abstraction and C soundness. Denote this old model by B. We do not replace these domains with arbitrary function sets at X.

At Y, however, a single point pins **every** outgoing profile. For a fixed target, the image of (*,0) under (f,k) determines both f(*) and k, hence determines the whole arrow. Consequently any profile on outgoing arrows from Y and arbitrary future argument tuples is admitted there, at every relational type. This limited fullness fact will be used for the failure of BF.

## 2. Split epimorphisms approximate every finite pin at X

Let h:X→Z and let P⊆X be finite. If Z=Y, h is already split epic: any arrow choosing a first coordinate in ℕ and having the opposite tag is a section.

If Z=X, write h=(f,k). There are only finitely many first coordinates a occurring in P. Extend the restriction of f to those coordinates to an onto map g:ℕ→ℕ, and put b=(g,k). Such an extension is obtained by assigning every natural-number output somewhere in the infinite remaining input set. Then b agrees with h on P. Choosing a section s₀ of g, for example its least-preimage section, makes s=(s₀,−k) an arrow with b∘s=id_X.

Thus, for every h and P, there is a split epimorphism b with the same target and the same values on P. Functoriality gives

```math
\rho_\sigma(b)\rho_\sigma(s)=I
\tag{5}
```

at every admitted type σ. In particular every selected b acts onto at every type, including higher relational types.

This implies current BF at X directly. Let F:σt at X satisfy F(x)=Top for every current x, and choose a finite pin P for its entire profile. Given any outgoing h:X→Z and arbitrary y∈D_σ(Z), choose b agreeing with h on P as above and lift y through ρ_σ(b), say y=ρ_σ(b)x. Necessity of F(x) gives F(b,y) true. Pinning gives F(h,y) true. Since h,y were arbitrary, ∀_σF=Top. This proves BF_σ at X for every σ.

C+BF supplies all current Functionality instances at X. Equivalently, the same approximation argument compares two predicate profiles on arbitrary future arguments after lifting them through b. No BF claim is made at Y.

The split epimorphisms also distinguish all proposition pairs at X. Distinct proposition intensions disagree at some outgoing h. Apply the preceding approximation with the union of their two finite pins; the resulting b retains the disagreement. This will supply the root's truth readers.

## 3. Translation charts give onto observers and prescribed kernel coordinates

Fix any outgoing arrow b:X→Z, with tag k. It need not be invertible or split epic for this section. For integers j≥0 define

```math
C_j=\{h:X\to Z:\mathrm{tag}(h)=k+j\}.
\tag{6}
```

These disjoint charts share the pin {(0,0)}. Their target and tag determine membership; agreeing on that single point determines the tag. Postcomposition by u_Z sends C_j onto C_{j+1}. Let c_b be the proposition C₀, false on all other arrows. It is admitted, and b∈c_b.

For an arbitrary outgoing h:X→W choose observation arrows from W as follows:

```math
s_h=
\begin{cases}
u_Z,&h\in\bigcup_{j\ge0}C_j,\\
\mathrm{id}_W,&\text{otherwise},
\end{cases}
\qquad
r_h=
\begin{cases}
u_Z^{-1},&h\in\bigcup_{j\ge1}C_j,\\
\mathrm{id}_W,&\text{otherwise}.
\end{cases}
\tag{7}
```

Define the entire tt profiles

```math
S_b(h,q)\Longleftrightarrow s_h\in q,
\qquad R_b(h,q)\Longleftrightarrow r_h\in q,
\tag{8}
```

where q is any proposition at W. Both profiles have the same one-point pin; no uniform bound on the number of external cases is required. Ideal fullness admits S_b,R_b.

For every h,

```math
r_{s_hh}s_h=\mathrm{id}_{\mathrm{target}(h)}.
\tag{9}
```

On C_j the first observation shifts to C_{j+1}, where the second observation shifts back. Outside the charts both observations are identities and the coordinate remains outside. For arbitrary future l:X→W, arbitrary q at W, and further arrow a:W→V, the application formula therefore gives

```math
\begin{aligned}
a\in(\rho(l)S_b)((\rho(l)R_b)q)
&\Longleftrightarrow r_{s_{al}al}s_{al}a\in q\\
&\Longleftrightarrow a\in q.
\end{aligned}
\tag{10}
```

Thus S_b∘R_b=I as a whole operation. In particular S_b is currently onto. Also

```math
h\in S_bc_b\quad\Longleftrightarrow\quad s_hh\in C_0,
```

which never occurs: the charts move to their successors and their complement remains outside. Hence

```math
S_b\circ R_b=I,\qquad S_bc_b=\bot,\qquad b\in c_b.
\tag{11}
```

All selected observation arrows in (7) are invertible. Evaluation along such an arrow commutes with Boolean operations and, because its action on every type is onto, with universal and existential quantification. Applying this calculation at every future coordinate and every future predicate verifies the **full composite** identities for S_b and R_b. Translated equality clauses follow from Boolean qualification over C. Both observers are therefore Good_Δ for every finite Δ. The same witnesses work for all those lists as a fact about this model; no infinitary object-language qualification is introduced.

These are prescribed-coordinate kernel pairs, not necessarily currently true-kernel pairs: c_b need not contain the identity of X. Exactly the fact b∈c_b will be used below.

## 4. A future point where every BF instance fails

Fix h:Y→X with first component selecting 0 and tag 0. Its individual action has image {0}×ℤ, so it misses, for example, q_e=(1,0).

Its action on propositions is also not onto. Let q₀ be the proposition at X consisting of the self-arrows (g,m) with g(1)=0, and no arrows X→Y. This is pinned by {(1,0)}, hence admitted. Choose self-arrows a,a′ at X, both with tag 0, whose first maps agree at 0 but differ as follows:

```math
g(0)=g'(0)=0,\qquad g(1)=1,\qquad g'(1)=0.
\tag{12}
```

Then a∘h=a′∘h, but q₀ has different truth at a,a′. Every transported proposition ρ_t(h)p has equal truth at a,a′, because its values are p(ah) and p(a′h). Thus

```math
q_0\notin\mathrm{Im}\rho_t(h).
\tag{13}
```

There is a missing object at every higher relational type as well. For τ=σ₁⋯σ_nt, let q_τ be the admitted constant relation λx₁⋯x_n.q₀ at X; for n=0 this is q₀ itself. Suppose q_τ=ρ_τ(h)A for some A at Y. Choose one argument a_i of each σ_i at Y, using nonemptiness of the type domains. Apply the assumed identity to their transported tuple. Naturality and beta yield

```math
q_0=\rho_t(h)\bigl(A[a_1,\ldots,a_n]\bigr),
```

contradicting (13). Hence ρ_τ(h) is not onto at every relational type τ. This argument needs no extensional identification of arbitrary relations.

Now fix any admitted type σ, with q_σ outside the image as above. At Y define a predicate F_σ of type σt by the following entire truth profile, for every outgoing l:Y→W and x∈D_σ(W):

```math
F_\sigma(l,x)\text{ is false exactly when }l=h\text{ and }x=q_\sigma.
\tag{14}
```

The one-point fullness fact from §1 admits this profile. For every current p∈D_σ(Y), application at a future l evaluates (14) on ρ_σ(l)p. It is always true: the only possible exception is l=h, where q_σ is outside the image. Thus F_σ(p)=Top for every current p. But at h, the quantified proposition ∀_σF_σ is false, because its domain includes q_σ. Therefore

```math
Y\models\forall p^\sigma\,\Box F_\sigma p
\quad\text{and}\quad
Y\not\models\Box\forall p^\sigma\,F_\sigma p.
\tag{15}
```

BF_σ fails at Y, for every σ. The predicates (14) are individually admitted profiles; no internal choice of a family over types is asserted. The failures at e and t already suffice for the main comparison, while (13) and the constant-relation argument supply the exact stronger scope.

## 5. The full root truth-profile predecessor

Adjoin a new predecessor * over X by the established [root truth-profile construction](root-truth-profile-surjective-separation.md), §3. Recall its recursive domains:

```math
A_e=B_e(X),\qquad
A_{\sigma_1\cdots\sigma_nt}
=\{0,1\}^{\prod_i A_{\sigma_i}}\times B_{\sigma_1\cdots\sigma_nt}(X).
\tag{16}
```

Projection π onto the second component is onto at every type. Root truth is the first bit; application sections the first truth function and applies the old tail to projected arguments. Lambda abstraction is the actual root truth function of its body paired with the old abstraction under the projected assignment. Boolean operations, quantifiers and equality have their ordinary current truth clauses in the first component and their old interpretations in the second. The new arrows to an old Z are b∘i, with action ρ(b)π. No old domains or arrows are altered.

For clarity, C soundness of this construction requires only that B is a C model, not that all of its old arrows act onto. Contextual beta/eta hold componentwise. H-equivalent formula bodies have equal root truth functions for every root assignment and equal old abstractions by B's C, so their pairs are identical; this verifies C's actual Logical Equivalence schema. The root admits precisely the arbitrary first truth functions in (16), paired with allowed old tails, so the lambda construction has no additional admission obligation.

Current BF at X from §2 suffices for current BF at the new root. If each current F(x) is Top, its first values are all true and its old values are Top on the image of π. Projection is onto, so old BF at X makes the old universal Top as well. The root universal is therefore Top. Current Functionality similarly follows from onto argument projections and old Functionality at X, or from C+BF. It is not necessary to assume BF or Functionality at the old target Y; indeed BF fails there by §4.

## 6. Surjective separators at every finite list and output type

Use only the split epimorphisms b:X→Z from §2 as separating evaluation arrows. For each such b take S_b,R_b,c_b from §3 and define the root observer

```math
E_b=(v_b,S_b),\qquad
v_b(p):=[b\in\pi_t p].
\tag{17}
```

It is admitted by (16), and

```math
E_b(p)=\bigl(v_b(p),S_b(\pi_t p)\bigr).
\tag{18}
```

Its root Boolean laws are evaluation laws. At a quantifier type σ, the root truth of E_b(∀_σF), for arbitrary F=(f,g), quantifies over every object at Z. The root truth of ∀x E_b(Fx) quantifies over the image of ρ_σ(b)π_σ. These coincide because both π_σ and ρ_σ(b) are onto. The existential calculation is identical with ∃. The old components of the composites agree by the whole laws for S_b. Thus the complete composite lambda operations are identical as pairs in (16), proving Good_Δ(E_b) for every finite Δ. No reflection of equality by b or π is assumed; C supplies the translated equality clauses.

For any desired root output (ε,q), with ε∈{0,1} and q an old proposition at X, put

```math
z=(\neg c_b\land R_bq)\lor\varepsilon c_b,
\tag{19}
```

where εc_b is c_b for ε=1 and Bottom for ε=0. Equation (11) and Boolean preservation give S_bz=q. Since b∈c_b, the truth of z at b is ε. Hence the admitted input (0,z) satisfies E_b(0,z)=(ε,q). This proves current surjectivity, without an admitted root inverse premise.

The root identity observer is also onto and Good at every list. It distinguishes different first bits. Different old tails disagree at some outgoing h, and §2 supplies a split epimorphism b preserving that disagreement; E_b then distinguishes the root propositions. Thus propositional SurjSep holds for every finite Δ.

For a relational output, a difference of root truth functions is detected by a root argument tuple and identity. A difference of old relation tails is detected by old Functionality at X on an old tuple; lift that tuple through π and apply one of the E_b to its differing proposition values. This proves full relational SurjSep, at each finite list, with exactly the same finite qualification used at propositional scope. Alternatively use the established typed factorization with current Functionality.

## 7. The modal consequence and its limits

The old object Y is accessible from the new root, by any arrow X→Y following i. Its domains and interpretations remain unchanged. Formula (15) therefore refutes □BF_σ at the root for every σ. Combining §§5–6 proves (1).

The individual onto-persistence theorem is unaffected. Over C+BF_t, each current admitted onto observer satisfies □Onto(E). In the present construction the old S_b even has the whole right inverse R_b throughout the future model. Neither fact makes separation persistent or forces BF at the future object.

Since full OS implies all BF, necessary OS would imply necessary BF at each type. Thus this model also fails necessary OS and necessary SurjSep, although those nonimplications already have the separate fixed/free-symmetry root model. Its new verdict is the failure of necessary BF, with exact type scope. C5 fails as well, since C5 implies necessary BF; the C5 equivalence between SurjSep and Rev is not challenged.

The reusable construction has two independent ingredients. Finite-pin approximation by split epimorphisms gives current BF/Functionality and enough all-type evaluation readers at X. The integer tag supplies prescribed-coordinate kernel pairs without imposing surjectivity on every old arrow. The root extension combines the readers with those onto tails. The admitted old arrows from Y to X remain non-surjective at every type, and are precisely where BF fails.

No converse from an arbitrary unqualified onto map, no necessary separation hypothesis, and no infinitary qualification are used. The positive separation is the full typed finite-list schema over H, in a model of C. All negative verdicts are mathematical model arguments, not missing arrows in a computed map.

## 8. Sources

The integer-decorated category, tag-chart kernels, higher-type missing-image witnesses and their combination with the root extension are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–7, unpaginated.

The ideally-full finite-pinning framework is Bacon and Dorr, *Classicism*, draft of 16 May 2023, Appendix D, Definitions D.1–D.3 and Proposition D.4, pp. 73–74, as recorded in [Finitely pinned action models on two objects](../../source/topics/classicism/groups/finite-support-two-object.yaml). The source's ℕ/singleton all-maps model and its contingent-Barcan verdict are recorded at [Finite-support action model: N and singleton, all maps](../../source/topics/classicism/models/finite-support-two-object-all-maps.yaml), Appendix D, p. 79. The present category changes that source construction by adding the visible integer coordinate; its new verdicts are not attributed to the paper.

The split-epimorphism approximation and arbitrary-type observer calculation build on [Logical separation with contingent Barcan](logical-separation-with-contingent-barcan.md), §§2–5. The all-future chart calculation is the same admitted-profile method used in [Fixed-point symmetry](fixed-point-symmetry-left-inverse-separation.md), §§2–4, now with the visible integer tag and no symmetry group. The complete recursive predecessor and current-surjectivity argument are [Root truth-profile extension](root-truth-profile-surjective-separation.md), §§3–5, following [Two upper observer models](../observer-lattice-models.md), §2. The earlier model's necessary BF assumption is not imported; §2 above establishes exactly the current BF needed at the selected old source.

For the final typed lift see [Typed separation and Classicism](typed-separation-and-classicism.md), §2, and [BF implies Functionality](../../source/topics/classicism/results/barcan-r-implies-functionality-r.yaml). The individual persistence result is [Surjective separation without persistence](root-truth-profile-surjective-separation.md), §1.

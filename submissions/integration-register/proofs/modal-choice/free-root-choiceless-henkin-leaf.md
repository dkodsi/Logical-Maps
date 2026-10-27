# Free root over a choiceless Henkin leaf

26 October 2026. Ordinary mathematical construction and verification
by OpenAI Codex. Direct source for this combination and its verdicts:
`misc`, this note, §§1–7, unpaginated. The underlying choiceless Henkin
model and coalesced-root construction have the sources listed in §8.
No independent review, human verification, Lean certification, or
literature-priority claim is made.

## 1. Statement and metatheory

There is an explicit countermodel in ordinary ZFC to

```math
C+RC_{\rm all}+IC_{\rm all}\ \Longrightarrow\ MRC_{\rm all}
\tag{1}
```

Its distinguished root satisfies the stronger package

```math
RC_{\rm all}+\Box IC_{\rm all}+\Box BF_{\rm all}
+\Box OS_{\rm full}+\Box BC_t+\mathrm{Actuality},
\tag{2}
```

but fails MRC at the pair of individual types (e,e). In particular it
also fails □RC_all and Modal Well-Ordering. Current TC_all holds as
well. The failure of (1) therefore survives adding current Transversal
Choice, full logical observer separation, and propositional Boolean
Completeness.

Work in external ZFC. Take the explicit classical extensional
Henkin model H from [Independently swappable pairs](finite-support-pairs-henkin-leaf.md),
§§1–4: the individuals are fixed labels and pairs of options, and
every admitted relation has finite support under independent pair
swaps. The invariant relation U sends each label to its pair, and
has no admitted functional subrelation. The linked note checks
every typed domain, abstraction and quantifier, and strict LE.
This supplies the leaf directly, without an assumption that a
set-sized model of ZF exists. External Choice is available at the
root; the leaf's admitted relations still lack a selector for U.

The first version used the existing ZF-without-Choice Henkin model
as a conditional input. That alternative remains valid with its
own stated hypothesis; the explicit finite-support leaf removes
the extra model-existence assumption from the present separation.

Treat H as a terminal one-world model. Its proposition domain is 2,
and Box there is truth. Therefore H satisfies IC at every type:
given any inhabited admitted property F, choose one instance a and
use its admitted haecceity λx(x=a). This is a separate existential
choice for a fixed F, not an admitted uniform choice function for all
F. H also satisfies every BF instance and full OS, using identity as
observer, because its relational domains are extensional.

## 2. The two-world typed model

Adjoin a new root r with one arrow to H. There are only the identity
arrows and this one additional arrow. Write D_σ(H) for the leaf
domains. At the root let D_e(r)=D_e(H), with identity transport.
For every relational type τ=σ₁…σₙt, including n=0, set

```math
D_\tau(r)=
\mathcal P^V\!\left(\prod_{j=1}^{n}D_{\sigma_j}(r)\right)
\times D_\tau(H)
\tag{3}
```

The empty product has one element, so D_t(r)=2×2. Types are defined
by their usual finite structural recursion: the argument types in
(3) are proper subtypes. No individual-valued function type is added.

A root relation is a pair (A,a), where A is its arbitrary actual
extension in the external metatheory and a is an admitted leaf
relation. Its transport π_τ is the second projection. Every π_τ is
onto: pair any leaf relation with the empty root extension. Individual
transport is onto as well.

Application takes sections of A and applies a to the projected
argument. Thus, for a curried relation f and an argument x,

```math
\pi_\tau(fx)=(\pi_{\sigma\tau}f)(\pi_\sigma x)
\tag{4}
```

Abstraction has the actual extension of its body as its first
component and the leaf abstraction of its projected parameters as
its second component. Boolean operations act coordinatewise on
propositions. A quantified formula is true in the first coordinate
exactly according to ordinary quantification over the root domain;
its second coordinate is its interpretation in H. For propositions,
write (ε,b), with actual truth ε.

Equality at every type has first coordinate literal equality of the
root entities and second coordinate equality of their projections.
At the individual type the projections are identity. This is the
one-leaf specialization of the existing unrestricted coalesced-root
construction; the restricted Henkin leaf is preserved at every type.

## 3. Verification of C and of native necessity

The root and the leaf satisfy the ordinary H truth clauses. Equality
is actual equality of the corresponding entities at each evaluation,
so reflexivity and substitution hold. Onto projections make the leaf
coordinate of each root quantified formula agree with the leaf's
own quantification. Application and abstraction satisfy the typed
conversion laws by their definitions.

For the strict Logical Equivalence rule, suppose an equivalence is
an H theorem. Its two abstractions have identical actual extensions
at the root. Their leaf abstractions are identical in H, which is a
C model. Formula (3) therefore makes the root abstractions identical
as entities. The same identity holds at the leaf. This checks the
rule only for H theorems; no equivalence using an optional choice
premise is used in this argument. Thus the construction is a C model.

Top is (1,1), and the definition Box p=(p=Top) gives

```math
\Box(\epsilon,b)=(\epsilon\land b,b)
\tag{5}
```

Consequently a boxed formula is true at the root exactly when it is
true at both evaluations, with the appropriate domains at each.
Algebraic entailment between propositions is coordinatewise. Between
root relations it is inclusion of actual extensions together with
leaf entailment: the unconditional Boolean join identity is evaluated
componentwise in (3). This includes relations of every finite arity.

The construction is not C5. For example, (1,0) is distinct from Bottom
at the root but transports to Bottom at the leaf.

## 4. Current Relational and Transversal Choice

Fix any serial root relation R:στt. Its current extension is an
ordinary serial relation on the external sets D_σ(r),D_τ(r). External
Choice supplies a functional subrelation A of that extension. Pair A
with the empty relation at the leaf. By (3) this is an admitted root
relation S. It is currently total and functional and is a current
subrelation of R. In fact the empty leaf component also gives S≤R.
This proves every current RC instance, including individual outputs.

The same argument proves TC_all. Given any current equivalence
relation at a type, externally select one member of each current
class and use that set as the free current extension of an admitted
predicate, with empty leaf component. No leaf choice graph has been
added: every transported relation still belongs to H.

## 5. Intensional Choice holds necessarily

Fix a type σ and a root F:σt such that □∃x Fx. Formula (5) says that
its actual extension A is nonempty and its leaf property F_H is
inhabited in H. Choose a∈A and b∈D_σ(H) with F_H(b). Let

```math
G=(\{a\},H_b),\qquad H_b:=\lambda x^\sigma(x=b)	ext{ in H}
\tag{6}
```

This pair belongs to D_σt(r), whether or not π_σ(a)=b. Its current
extension is the singleton {a}; its leaf extension is the singleton
{b}. Both are contained in the corresponding extensions of F, so
G≤F. Both evaluations satisfy unique instantiation of G. Hence
□∃!x Gx holds at the root.

This proves IC_σ at r. It holds at H by §1, and therefore □IC_σ
holds at r by (5). The proof applies separately to every original
type, with no uniform choice over types and no added type quantifier.

The independence of the two singleton components in (6) is allowed:
Intensional Choice asks for a necessarily unique instance of a
property; it does not require that instance to be the transport of
the root's unique instance. The property itself transports correctly.

## 6. The necessarily serial relation without a selector

Let U∈D_eet(H) be the serial leaf relation without an admitted
functional subrelation. Let R at the root have universal current
extension D_e(r)×D_e(r) and leaf component U. This is admitted by
(3). Both components are serial, so □Serial(R) holds at r.

Suppose MRC_(e,e) supplied S≤R with □Functional(S). Its leaf
component S_H is, by construction, an admitted relation in H.
The necessary functionality makes S_H total and functional in H;
the algebraic bound S≤R makes S_H a subrelation of U. This contradicts
the defining failure of Choice in H. Therefore

```math
r\models RC_{\rm all}+\Box IC_{\rm all}
+\neg MRC_{e,e}
\tag{7}
```

Since H fails RC, the root fails □RC. Modal Well-Ordering fails at
least at e as well: the leaf component of a necessarily wellordering
root relation would wellorder D_e(H), and selecting the least U-output
by an admitted lambda formula would be a functional subrelation of
U in H. This also follows from the existing MWO⇒MRC implication.

## 7. Additional verified structure

**Boxed BF.** Suppose every current x satisfies □Fx. Then F is true
of every root x and its leaf component is true of every projected x.
Since π_σ is onto, it is true of every leaf argument. Thus □∀x Fx.
BF holds at r, and it holds at the terminal leaf, so every closed BF
instance is necessary.

**Actuality and boxed BC_t.** The root-only proposition (1,0) entails
every current truth and witnesses Actuality. The proposition algebras
are the finite Boolean algebras 2×2 and 2. Every represented family
therefore has a Boolean join and meet at each evaluation; □BC_t holds.
Vicinity follows from Actuality. No all-type BC verdict is inferred.

**Full necessary OS.** Identity and the admitted leaf reader

```math
E_\ell(\epsilon,b)=(b,b)
\tag{8}
```

separate propositions. The reader's leaf component is identity. Its
Boolean whole-operation identities are immediate; its quantifier
whole-operation identities hold at the root because every projection
is onto and at the leaf because it is identity. The translated
equality reflexivity and substitution clauses hold by equality
substitution in H. Thus the reader is qualified at every specified
finite type list, without an infinitary qualification assertion.

Different root relations have either different current extensions,
separated by identity at a current tuple, or different leaf entities.
In the latter case leaf extensionality supplies a leaf tuple where
they differ; lift it through the onto projections and use the reader.
This proves full typed OS. At the leaf identity supplies full OS, so
the separately boxed schema holds as well. The argument is precisely
the previously verified one-leaf observer construction; it does not
use Choice in the leaf.

These extra verdicts sharpen (7). They do not refute either existing
RC⇒TC or completeness+choice⇒Actuality target: TC and Actuality
both hold at this root.

## 8. Sources and status

- Explicit classical finite-support Henkin component:
  [Independently swappable pairs](finite-support-pairs-henkin-leaf.md),
  §§1–4, OpenAI Codex, 26 October 2026, `misc`, unpaginated.
- The original alternative choiceless Henkin component: Bacon and Dorr,
  *Classicism*, draft of 16 May 2023, §2.3, note 46, p. 32;
  [existing model record](../../../classicism-results-2026-10-24-v2/source/topics/classicism/models/henkin-without-relational-choice.yaml).
- The coalesced-root construction: Bacon and Dorr, *Classicism*,
  Appendix E, Definition E.2, pp. 80–83;
  [construction and free-root RC argument](../../../classicism-results-2026-10-24-v2/source/topics/classicism/groups/coalesced-sums.yaml).
- The explicit one-leaf domain formula and full observer verification:
  [CH and first-order-analysis propagation audit](../observer-analysis/ch-analysis-audit.md),
  §4, unpaginated. That note uses a different leaf; this construction
  replaces it by the explicitly constructed finite-support Henkin model.
- New RC+IC/Modalized-RC separation and its direct verification:
  this note, §§1–7, OpenAI Codex, 26 October 2026, `misc`, unpaginated.

This is an ordinary mathematical ZFC countermodel, not a new
native model record or a formal certificate. The key checks are the
restricted leaf domains in (3), the two independent singleton
components in (6), and the projection contradiction in §6.

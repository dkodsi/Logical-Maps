# Relational Choice alone: the ordinary-union fixed-point obstruction

22 October 2026. OpenAI Codex research subagent. New scratch arguments, no database edits and no Lean claim. The full RC⇒TC question remains unresolved here.

## 1. Exact existing evidence

The local unresolved write-up `topics/classicism/writeups/relational-choice-r-implies-transversal-choice-r.md` identifies the coextension/identity gap, records the equivalence of Transversal Choice with Relational Choice plus Transversal, and explains why the recorded symmetric full hierarchies do not separate RC from TC.

A proved-only `scripts.pmap.load_topic` / `Engine` query was run with RC in the queried premises, not the background. It reports no RC⇒TC derivation and no recorded RC/TC separator. RC⇒Boolean Completeness and RC⇒Actuality both have recorded countermodels (for example `finite-support-permutations` occurs in both lists). These are statements about the current records, not literature independence claims.

The separate audit `/tmp/classicism-research/audit-bare-c-bourbaki-witt.md` verifies bare-C Bourbaki–Witt for represented progressive functional graphs on a genuinely antisymmetric chain-complete order. Replacing algebraic order by actual inclusion removes genuine antisymmetry.

## 2. A precise equivalence blocking the most natural repair

Fix σ, put ρ:=σt, and write

    F ⊑ G  :⇔  ∀x(Fx→Gx),
    F ≡ G  :⇔  ∀x(Fx↔Gx).

These are actual inclusion and actual coextension. Unlike algebraic Boolean order, ⊑ is generally only a preorder on the ρ-entities.

For a family C of type ρt define its material union

    μ_C := λx ∃F(CF ∧ Fx).

Every C has ⊑-suprema, and its suprema are exactly the properties actually coextensive with μ_C. This assertion is bare-C ordinary reasoning, with no identity of coextensive codes inferred.

Define **Extensional Chain-Supremum Selection at σ** to say that there is a represented graph T of type (ρt)ρt satisfying:

1. For every actual ⊑-chain C, there is exactly one F with T(C,F), and this F is a ⊑-supremum of C. Here a chain only needs comparability; using a definition demanding entity-antisymmetry would change this principle, as discussed below.
2. If C,D are actually coextensive chain predicates, then T(C,F) iff T(D,F), for every F.

Then, in bare C,

    Extensional Chain-Supremum Selection at σ  ⇔  Transversal at σ.

Here Transversal at σ is the map’s principle asserting an admitted property containing exactly one σ-property from each actual coextension class.

### Forward proof

For F of type ρ put

    C_F := λG^ρ (G ≡ F).

Its instances are pairwise coextensive, hence comparable in the actual-inclusion preorder. It is inhabited by F. Its supremum properties are exactly the coextensions of F: any upper bound includes F, and F itself is an upper bound; mutual inclusion characterizes its suprema.

Define

    K(F,Y) := T(C_F,Y).

For each F there is exactly one Y with K(F,Y), and Y≡F. If F≡G, then C_F and C_G are actually coextensive. The required invariance of T therefore makes K(F,Y) iff K(G,Y). Thus K is a graph choosing one entity per actual coextension class.

Finally put

    A(Y) := ∃F K(F,Y).

Every coextension class meets A, by totality of K. If A(Y), A(Z), and Y≡Z, choose F,G with K(F,Y), K(G,Z). Since Y≡F and Z≡G, we have F≡G. Invariance gives K(F,Z), and functionality at F gives Y=Z. Hence A is a transversal of actual coextension.

All constructions are admitted lambda terms. No output operation K of type ρρ is assumed; K is relational throughout.

### Reverse proof

Let A of type ρt be a transversal of actual coextension. Put

    T(C,F) := A(F) ∧ ∀x(Fx ↔ ∃G(CG ∧ Gx)).

Every family C, not only a chain, has exactly one such F, namely the A-representative of μ_C. It is a supremum under actual inclusion. If C,D are actually coextensive, their material unions are actually coextensive, and the displayed formula immediately gives T(C,F) iff T(D,F). This establishes the reverse implication without RC.

### The chain-definition qualification

The map’s `TotalOrder` definition includes antisymmetry with respect to identity. C_F usually fails that clause, because it contains distinct coextensive codes. The forward proof therefore concerns comparable families in the actual-inclusion **preorder**, the natural family class when one says that material unions make the ordinary partial-transversal preorder chain-complete.

If one restricts to entity-antisymmetric chain predicates instead, this particular reduction does not establish the equivalence. It still establishes the exact obstruction for the more generous comparable-chain completion, and the ordinary-union strategy cannot silently move between these two meanings of “chain.” A separate proof would be needed to obtain the required extensional selector on identity-antisymmetric chains from RC alone.

## 3. Why uniqueness of a functional graph does not repair supremum choice

An actual-inclusion supremum s of C is unique only modulo ≡. If s and t are different codes with s≡t, functionality of a graph f gives no relation between f(s) and f(t). Even actual equivalence of their output extensions is not supplied. Therefore

    T(C,y):=∃s(Sup_⊑(C,s)∧f(s,y))

need not be functional, nor functional modulo ≡. RC could select a functional subrelation of this T, but the selection may distinguish two actually coextensive predicates C,D. Repeating RC changes the chosen code level and does not itself enforce invariance.

The equality `s=t` obtained from genuine algebraic antisymmetry is exactly what makes the RC+BC proof’s composition work. The current obstruction does not prove that every alternative RC-only argument fails.

## 4. Saturation does not immediately descend a graph to the quotient

Given a progressive functional S on property codes, one can define

    S^sat(F,G) := ∃F′G′(F′≡F ∧ G′≡G ∧ S(F′,G′)).

This formula is invariant under replacement of either argument by an actual coextension. It need not be single-valued even modulo coextension: different coextensive F′ may have selected strict extensions with different actual members. A proof using S^sat as an operation on the extension quotient therefore needs an additional congruence argument.

Likewise, taking the material union of all S-images of coextensions of F gives a canonical output **extension**, but for partial transversals it may add two different representatives from the same previously missed equivalence class. Taking their intersection avoids this collision but need not be strict or even add a representative. Neither operation preserves the required strict-progress property by the assumptions alone.

## 5. Status

The extensional chain-supremum selector equivalence is a precise new obstruction, subject to the explicit comparability-versus-identity-antisymmetry distinction. It is not a countermodel to RC⇒TC. No C-Henkin construction satisfying all-type RC while failing TC has been produced in this note.

## 6. A quotient-compatible Bourbaki–Witt theorem in bare C

The loss of identity-antisymmetry is not by itself fatal. It can be replaced by compatibility of the graph with preorder equivalence, with no quotient type constructed.

Let P be an admitted property and ≤ a represented preorder on P. Write

    x∼y := P(x)∧P(y)∧x≤y∧y≤x,
    x<y := P(x)∧P(y)∧x≤y∧¬(y≤x).

Assume every admitted comparable property C⊆P, including the empty property, has a supremum in P. Suppose a represented relation f on P satisfies:

* totality: every x∈P has an f-output in P;
* output uniqueness modulo ∼: f(x,y) and f(x,z) imply y∼z;
* congruence: x∼x′, f(x,y), and f(x′,y′) imply y∼y′;
* progressivity: f(x,y) implies x≤y.

Then there exist x,y∈P with f(x,y) and x∼y.

This is an internal bare-C theorem. It uses comparable families, not the map’s narrower identity-antisymmetric chains. It does not assert that arbitrary represented preorders satisfying the map’s narrower chain-completeness clause satisfy this version.

### Proof by saturated f-chains

A property C⊆P is **saturated** when Cx and x∼y imply Cy. Call C an f-chain if:

1. it is saturated and totally preordered by ≤;
2. every admitted nonempty subproperty X⊆C has a member x with no strict predecessor in X (equivalently, x≤y for all y∈X);
3. each x∈C is a supremum in P of

       Im_f(Pred(C,x)) := λz∃y(Cy∧y<x∧f(y,z)).

All are ordinary formulas. A saturated equivalence class of a least P-element is an f-chain; existence of such an element follows from empty-family completeness.

For any two f-chains C,D define I as the property of common members whose strict predecessor properties in C and D are actually coextensive. Preorder equivalence preserves strict-order comparisons. Together with saturation of C,D, this makes I saturated. The same argument as in the antisymmetric proof makes I an initial segment of C and D.

If both C\I and D\I are nonempty, choose least members c,d. Their predecessor properties each have extension I, so the represented f-images are coextensive. Both c and d are suprema of this same actual family, so c∼d. Since C,D are saturated, c and d both lie in C∩D. Strict-order invariance under c∼d, and their identical predecessor extensions, now put c in I, contradiction. Thus C or D is an initial segment of the other.

The admitted union A of all f-chains is saturated, comparable, and internally well-founded: for a nonempty admitted X⊆A, take x∈X, an f-chain C containing x, and a least member m of X∩C; initial-segment comparability shows m≤z for every z∈X. The predecessor extension of any x∈A is already its predecessor extension in an f-chain containing it. Therefore its defining f-image supremum property transfers, so A is an f-chain.

Let u be a supremum of A. If u∉A, then A has no greatest equivalence class: any greatest member a would satisfy a∼u, and saturation would give u∈A. For each x∈A there is y∈A with x<y. Every f-output z of x lies below y by condition 3 at y, hence below u. Conversely each x lies below every f-output of x, so every upper bound of Im_f(A) is an upper bound of A. Thus u is a supremum of Im_f(A). Adjoin the full ∼-class of u to A. Old predecessor properties are unchanged; the new members all have predecessor property A, and all are equivalent suprema of Im_f(A). The enlarged property is an f-chain, contradicting u∉A.

So u∈A. Choose v with f(u,v). If u<v, then v is a supremum of Im_f(A): for x<u, condition 3 at u puts all outputs of x below u≤v; for x∼u, congruence puts all outputs of x in the class of v; and v itself belongs to the image. Adjoining the full ∼-class of v now produces a larger f-chain, contradicting that u upper-bounds A. Progressivity therefore gives u∼v. QED.

No identity between coextensive predicate codes was used. The replacement for the identity step is saturation plus order equivalence, and the congruence hypothesis is used critically in the final image bound for x∼u.

## 7. Application to ordinary partial transversals

For an actual equivalence R on σ, take P to be the properties F with at most one actual member in each R-cell. Order P by actual inclusion. P is saturated under actual coextension. Every represented comparable family has a supremum given by its material union, still in P: if the union contains two R-related elements, they lie in two chain members, one includes the other, and uniqueness in the larger member identifies the elements.

Every nonfull F∈P has an actual strict extension by adjoining one element from a missed cell. Therefore a total progressive graph on P that is strict at nonfull inputs and **respects actual coextension modulo actual coextension** yields an R-transversal by §6.

This isolates a sufficient repair of the RC-only argument:

    Choose a progressive graph whose output extension depends only on the input extension.

Ordinary RC gives a graph functional with respect to entity identity. It does not establish the displayed compatibility. Saturating an arbitrary RC graph fails for the reason in §4: different coextensive inputs may have outputs with different extensions.

## 8. A precise choice normal form equivalent to Transversal Choice

Define extension-compatible relational selection on property types as follows. For arbitrary σ,τ, and any represented relation U between σ-properties and τ-properties which is serial and invariant under actual coextension in each argument, there is a represented subrelation S⊆U which is total, has outputs unique modulo actual coextension, and respects actual coextension of inputs modulo actual coextension of outputs.

Transversal Choice implies this principle: take transversals of the input and output coextension equivalences; on input representatives use ordinary Relational Choice, which TC implies; replace each chosen output by its output representative, and extend the resulting graph to the corresponding actual coextension classes. All these extensions are represented by existential quantification, with no operation canonicalizers needed.

Conversely, this principle implies Transversal Choice. Given R, define U(F,G) by exhaustive cases on the actual partial-transversal P:

* if P(F) and F is not full, require P(G) and F strictly included in G;
* otherwise require G coextensive with F.

This relation on σ-properties is serial by adjoining a missed-cell element or leaving the input extension unchanged. It is invariant under coextension of either argument. A selected compatible S stays in P on P-inputs, is progressive, and is strict on nonfull inputs. Section 6, applied as in §7, gives a fixed equivalence class, hence a full transversal.

Thus the displayed property-type selection principle is equivalent to TC over C. This gives a normal form for exactly what a successful RC-only fixed-point argument would need to derive. It is not itself a derivation from RC.

## 9. Hostile audit of the semilinear shear no-go

I independently read `/tmp/classicism-research/rc-alone-shear-obstruction.md` and checked its full argument. It passes under its stated assumptions.

* The exactness of N_h uses that H is the actual standard rational line Qh. For a noninteger nonnegative rational qh, finitely removing qh,(q−1)h,… down past zero gives a forward-closed property containing 0 and omitting qh. This works regardless of later additions to higher-type domains.
* The finite predicate T_m^x contains the first m+1 iteration pairs and every pair whose first coordinate is above mh. It is closed under simultaneous +h,+x, and at mh isolates mx exactly. No unrestricted recursion theorem or function with individual output is used.
* N_h and the paired ancestry relation therefore define rational scalar multiplication uniformly. The finite-span predicate is an admitted lambda term.
* The important action hypothesis is about seed **relation entities**, not merely their actual extensions: the shears must be automorphisms of the whole intensional structure fixing addition, order, H, h, and c as entities. Only with that hypothesis does equivariance ensure that Span_A is fixed as an entity. The no-go’s §1 does explicitly state this stronger hypothesis; if a prospective construction supplied only root-level relational automorphisms, that transfer would remain unproved.
* For the stated shear group, fixing finite A exactly means annihilating W=span_Q(v0,v(A)). Finite-dimensional linear separation gives Fix(G_A)=W⊕Q=span_Q(h,c,A). Infinite dimension ensures a nonempty complement.
* A functional selector S with finite support A must select from that complement at a G_A-fixed predicate code. Its selected output is then fixed by all G_A, contradiction.

Thus the no-go does not need full symmetric powersets, ideal fullness, BC, or optional modal principles. It rules out the specified finite-support shear family, not all definable-Skolem or Henkin constructions.

## 10. A weaker compatibility condition, but no new RC implication

In §7, full output congruence can be weakened as follows. Suppose a represented progressive functional graph f on ordinary partial transversals has this property:

    For coextensive F,F′, the union of any f-output of F
    with any f-output of F′ is still a partial transversal.

For F define the admitted property

    H_F(x) := ∃F′G(F′≡F ∧ f(F′,G) ∧ Gx).

Pairwise compatibility makes H_F a partial transversal: any two potentially conflicting members have witnesses in two such outputs, and the compatibility condition identifies them. H_F includes F by progressivity. If F is not full and f is strict there, H_F strictly includes F. Finally F≡F′ makes H_F and H_F′ actually coextensive. Thus the graph of this lambda operation, considered only modulo coextension, satisfies the quotient-compatible fixed-point theorem and yields a full transversal.

This is a weaker, more local sufficient condition than output congruence. It is not known here to follow from RC. The raw RC graph can pick different elements of one missed cell for two coextensive input codes, violating the condition. Canonicalizing finite ambiguity is already covered by the earlier finite-cell rigidification argument; I found no independent RC-derived condition handling arbitrary infinite ambiguity.

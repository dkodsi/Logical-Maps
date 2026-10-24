# Relational Choice alone: a definable-Skolem seed and the higher-type obstruction

OpenAI GPT-6, 22 October 2026. Research note, not a countermodel or proof of separation. No records were edited.

## Status

**Subsequent hostile check: the large-dimensional shear seed in §3 is also ruled out under its stated closure assumptions.** The `bc_partial_selectors` agent supplied the paired-ancestral argument recorded in the addendum below. The earlier sections are retained to show exactly why the candidate fails.

The ordinary first-order distinction between definable Skolem functions and coextension-invariant definable choice is a useful analogy for Relational Choice versus Transversal Choice. It is not by itself a model of C. Below is a concrete first-order seed and two failed attempts to preserve its no-transversal property under higher-order closure. The finite-support invariant in §3 prevents transversals but also prevents Relational Choice, as the addendum proves.

The narrow proved-only local Engine query with premise `relational-choice-r` found no entailment, exclusion, or separating model for `transversal-choice-r` or `transversal-r`. It did find many models separating Relational Choice from Boolean Completeness and from Actuality, so neither can simply be inferred to close the gap.

## 1. Explicit first-order seed

Let M be a divisible ordered abelian group with a proper nonzero convex subgroup H, with named constants h>0 in H and c>H. Use rational scalar multiplication as a definitional expansion. Let

E(x,y) iff x-y belongs to H.

For example M=V⊕Q in lexicographic order, H={0}⊕Q, h=(0,1), c=(v₀,0), where V is a nonzero ordered Q-vector space and v₀>0.

The following direct elimination/choice algorithm applies in the elementary semilinear language (+,<,H,h,c).

After normalizing linear terms and splitting negated atoms, any quantifier-free condition on one variable y is a finite union of finite intersections of sets of the following forms, with parameter-definable a:

- a point {a}, or an ordinary open/closed upper/lower ray at a;
- the coset a+H;
- the strict quotient ray below a+H;
- the strict quotient ray above a+H.

Each such set is convex. A nonempty finite intersection of convex subsets of a linear order is the intersection of two members of the family (allow the same member twice): retain a strongest left boundary and a strongest right boundary. Its nonemptiness and a selected point can be computed from the finitely many parameter comparisons. Representative recipes are:

- Two compatible ordinary bounds: choose an included endpoint if one works, otherwise their midpoint; for an unbounded ray use its endpoint plus/minus h.
- Two compatible H-cosets: use the first center.
- A coset a+H and an ordinary upper bound b: if b is in the coset, use b-h; if b is above that coset, use a; otherwise the intersection is empty. Reverse signs for a lower bound.
- A coset and a quotient ray: the whole coset is contained or disjoint, so use its center when contained.
- Quotient lower ray below a+H and quotient upper ray above b+H: the intersection is nonempty exactly when a-b is positive and outside H; then (a+b)/2 works.
- Two quotient lower rays: min(a,b)-c works; two upper rays: max(a,b)+c works.
- A quotient lower ray at a and an ordinary lower bound b have nonempty intersection exactly when a-b is positive outside H; use (a+b)/2. A quotient lower ray and an ordinary upper bound have the universal witness min(a,b)-c. Reverse signs for the other mixed cases.
- A point constraint: test the point against the other constraint.

Endpoint variants are handled by testing the endpoint first. Each recipe has a finite definable case split and can default to 0 when the pair is empty. For a whole conjunction, form the finite list of pair-candidates and choose the first one satisfying every conjunct. The two-boundary observation ensures that at least one works when the conjunction is nonempty. For a disjunction, choose the first disjunct with a working candidate.

This proves, at once, elimination of one existential quantifier from a quantifier-free formula and a definable Skolem function for it. Iteration gives quantifier elimination and definable Skolem functions for every first-order formula; tuple outputs can be selected one coordinate at a time.

Every first-order definable unary set is a finite union of convex sets by this normalization. No E-transversal is first-order definable, even with parameters. Indeed a convex subset containing two distinct points contains two points in the same H-coset: if its endpoints are already in one coset, use them; otherwise adding a sufficiently small positive element of H to the smaller endpoint stays strictly below the larger endpoint. So each convex piece of a transversal has at most one point. A finite union of such pieces is finite, while M/H is an infinite nonzero divisible ordered group.

Thus this is a concrete first-order model with definable Skolem functions and no definable E-transversal.

### Source check and caveat

This distinction is the topic of Laskowski–Shaw, *Definable choice for a class of weakly o-minimal theories*, arXiv:1505.02147v3, Definitions 1.1–1.2 and §5 (https://arxiv.org/pdf/1505.02147). Shaw's 2008 dissertation, *Weakly o-minimal structures and Skolem functions*, §3.1, Theorem 3.1.1, pp. 43–50, addresses the elementary convex-subgroup case (https://api.drum.lib.umd.edu/server/api/core/bitstreams/15dbaf45-a412-4123-972e-fe9c5088f8a9/content). The algorithm above is written independently: the dissertation's displayed pairwise case analysis contains apparent sign/translation errors, so those displayed formulas should not be copied unchecked. Ealy–Maříková, *Quantifier elimination for o-minimal structures expanded by a valuational cut*, 17 August 2022, p. 2 n. 1, also flags a gap in the broader Laskowski–Shaw general theorem (https://kgrc.univie.ac.at/fileadmin/user_upload/p_kgrc/Valuation_Theory/QE_for_o_minimal_structures.pdf). The elementary linear algorithm above does not appeal to that broader theorem.

## 2. Why Q² is an inadequate higher-order seed

Taking V=Q makes the group particularly explicit, but full higher-order quantifier/comprehension closure destroys the first-order no-selector argument.

For a positive parameter a define the ancestral condition

N_a(x) := ∀P^(et) [(P0 ∧ ∀y(Py→P(y+a))) → Px].

All standard nonnegative integer multiples of a satisfy it by ordinary external finite induction, for any interpretation of the predicate domain. If that domain contains all first-order definable subsets, then for a=c=(1,0), every other x can be excluded by an admitted forward-closed set containing 0. If x<0, use the nonnegative ray. Otherwise take an integer m larger than x's first coordinate and remove the finite list x,x-c,...,x-mc from the nonnegative ray. None of those points is 0 when x is not an integer multiple of c, and the resulting set is closed under addition by c. Hence N_c defines exactly {nc:n∈N}.

Higher-order lambda closure must therefore add a discrete predicate absent from the initial weakly o-minimal structure. Similar ancestral commensurability defines the rational line Qc; in Q²/H this is a full transversal. The crucial defect is not ordinary Skolem choice but the impredicative closure already needed for C. Consequently, a proof that all initial predicate extensions are first-order definable is not stable under the proposed construction.

## 3. The proposed no-selector invariant (subsequently ruled out for RC)

Use instead M=V⊕Q with V of infinite Q-dimension, say V=R as an ordered Q-vector space. The additive shears

g_f(v,q)=(v,q+f(v)),

for Q-linear maps f:V→Q, preserve the order, the subgroup H, addition, and h. Requiring f(v₀)=0 makes them fix c. If finitely many additional individual parameters are fixed, require f to vanish on the span of their V-coordinates as well.

If v lies outside that finite-dimensional span, a Q-linear f vanishing on the span but nonzero at v exists. The shear preserves the coset {v}×Q and moves every point in it. Hence no subset invariant under all such parameter-fixing shears can contain exactly one point from every coset.

This yields a stable target invariant for a Henkin construction:

> Every admissible entity has a finite support in the underlying group; all C operations and quantified domains are equivariant; therefore the extension of every admissible unary predicate has finite support. Such a predicate cannot be an E-transversal.

Unlike weak o-minimality, equivariance under parameter-fixing automorphisms survives arbitrary lambda abstraction and quantification over an invariant domain. The higher domains must still be specified, however. Using the full hereditarily symmetric hierarchy is not an option: the local write-up `relational-choice-r-implies-transversal-choice-r.md` proves that such a hierarchy cannot separate these principles.

## 4. The exact missing Skolem lemma

Let G_A be the subgroup fixing a finite support A. Suppose U is an admissible relation with support A and actual seriality. To adjoin a functional selector with support A, it is sufficient that for every current input x there be some y in the U-fiber fixed by the stabilizer (G_A)_x. External choice of one such y for each G_A-orbit of inputs then extends equivariantly to a selector graph. (A separate equivariant intension-lifting operation must place that graph in the admitted relational domain.)

This is a real sufficient condition, not a consequence yet proved for the candidate. Its obstruction is precise: an admissible nonempty predicate F may have a larger stabilizer than any selected presentation by parameters, while that larger stabilizer fixes no member of F's actual extension. Ordinary definable Skolem functions from a parameter tuple only give a witness fixed by that tuple's stabilizer, which can be strictly smaller. One needs a presentation/support theorem for *intensional* predicate codes, and one must preserve it after adding the selectors and after all higher-type quantifier closure.

The proposed strategy is therefore:

1. Give predicate intensions noncanonical presentations carrying their actual parameters, so λz E(x,z) and λz E(x',z) stay distinct when x and x' are merely actually E-equivalent.
2. Quotient only by identities genuinely required by H Logical Equivalence and the C laws, never by actual coextension.
3. Prove that the resulting code objects have enough recoverable finite support that every serial definable fiber has a stabilizer-fixed witness.
4. Adjoin an equivariant selector graph and show that the same invariant survives all newly admitted formulas and higher quantifiers.

The first-order seed verifies only the parameter-wise choice part of step 3. It does not verify the intensional presentation theorem, uniform higher-type choice, or the induction in step 4.

## 5. Why a vacuous transfer theorem is not progress

A statement saying “if a typed intensional Henkin hierarchy validates H, Logical Equivalence, every formula's lambda denotation, all quantifiers, and all required choice relations, then it is a C+Relational Choice model” merely repackages the desired construction. To be useful, a transfer result must instead start with an independently constructed object, for example the first-order semilinear structure plus explicit syntactic code sorts, and prove the higher-type closure and support-witness properties.

The dangerous jump is from an external operation selecting one witness from each definable family to a *single admitted higher-type relation* selecting uniformly from every predicate code. There are infinitely many formula shapes, and actual code equality is intensional. A family of first-order Skolem recipes indexed externally by formulas does not automatically give that single relation.

A finite-fragment compactness approach would likewise need an explicit finite-fragment model with all relevant lambda/quantifier axioms and the full universal no-transversal assertion. Finite propositional domains cannot serve: they introduce actual atoms/Actuality, after which Relational Choice yields Transversal Choice. No such fragment construction is supplied here.

## Conclusion

The concrete semilinear seed shows that ordinary first-order choice from presentations need not identify presentations of the same cell. Its finite-support higher-order continuation is ruled out: the shear invariant prevents both transversals and the required uniform property chooser. There is no verified C countermodel and no settlement of Relational Choice alone ⇒ Transversal Choice. The separate note `rc-alone-large-support-audit.md` isolates what remains unproved when supports are enlarged.


## Addendum: the enlarged shear seed is ruled out too

Independent obstruction found by `/root/bc_partial_selectors`, confirmed in discussion with this audit agent on 22 October 2026. The candidate assumptions include the addition graph, H, h,c, and all first-order definable predicates on finite tuples.

Because H=Qh, the ancestral N_h selects exactly the standard natural multiples nh: H itself excludes points outside H, and finite-removal forward-closed predicates within the nonnegative part of H exclude all noninteger multiples.

For any a, define the paired ancestral relation M_a(u,v) as the least relation, by universal quantification over binary predicates, containing (0,0) and closed under (u,v)↦(u+h,v+a). At u=nh for standard n, finite induction gives M_a(nh,na). If z≠na, exclude (nh,z) with a first-order predicate consisting of the nonnegative first-coordinate half-space minus the finite backwards list (nh−kh,z−ka), 0≤k≤n. That predicate contains (0,0), is closed under the paired successor, and excludes (nh,z). Therefore M_a(nh,z) iff z=na.

This makes rational multiplication and finite Q-linear span definable by higher-order C formulas. In particular, for the finite individual support A of a proposed uniform membership chooser S, the set

L_A = span_Q(h,c,A)

is an admitted predicate, and its defining intension is fixed by G_A. In the proposed shear model L_A is exactly the pointwise fixed set of G_A: f must vanish on the finite-dimensional span of the V-coordinates of c,A; every remaining rational second coordinate is already generated by h.

Thus F_A := M \ L_A is an admitted G_A-invariant intension with a nonempty actual extension, but none of its actual instances is fixed by G_A. If S has support A and is a functional chooser for nonempty predicates, functionality at F_A forces its selected value to be fixed by G_A. Contradiction.

This is a direct higher-order witness to failure of Relational Choice in the candidate. The obstruction is stronger than failure of weak o-minimality and applies even when V has arbitrarily large dimension. A replacement seed would have to avoid the definability of the support stabilizer's fixed set, rather than merely increasing quotient dimension. No replacement construction has been established here.

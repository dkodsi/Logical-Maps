# Pointwise reversible separation and the scope of necessity

26 October 2026. Ordinary mathematical research in the fixed relational theory C.
Direct source of the arguments developed here: `misc`, this note, unpaginated.
These are ordinary proofs, not new native database records or formal certificates.

## 1. Definitions and main conclusions

All observer variables have type tt. All variables p,q,u,v below have type t.
Put

```math
\begin{aligned}
M_{\rm pt}(E)&:=\forall u\,v\,[E(u\land v)=Eu\land Ev],\\
I_{\rm pt}(E)&:=\forall u\,[E(Eu)=u],\\
K_{\rm pt}(E)&:=M_{\rm pt}(E)\land I_{\rm pt}(E),\\
D(p,q)&:=\exists E^{tt}[K_{\rm pt}(E)\land\neg(Ep\leftrightarrow Eq)],\\
S_{\rm pt}&:=\forall p\,q\,[(\forall E^{tt}\, .\,K_{\rm pt}(E)\to(Ep\leftrightarrow Eq))\to p=q].
\end{aligned}
```

Pointwise preservation uses actual identity, not material biconditional.
The corresponding whole laws are identities of the lambda operations:

```math
\begin{aligned}
M_{\rm op}(E)&:=(\lambda u\,v.E(u\land v))=(\lambda u\,v.Eu\land Ev),\\
I_{\rm op}(E)&:=(\lambda u.E(Eu))=(\lambda u.u).
\end{aligned}
```

Rev retains the full typed, finite-qualification schema of the
[observer hierarchy](../../classicism-results-2026-10-24-v2/proofs/logical-observer-hierarchy.md),
sections 1 and 4. The principal new scope reduction is

```math
\boxed{
\begin{aligned}
\mathrm{Rev}
&\longleftrightarrow\Box S_{\rm pt}\\
&\longleftrightarrow\forall p\,q\,\Box[p\ne q\to D(p,q)]\\
&\longleftrightarrow\forall p\,q\,[p\ne q\to\Box D(p,q)].
\end{aligned}}
\tag{1}
```

Equivalently, only one proposition parameter is needed:

```math
\boxed{\mathrm{Rev}\longleftrightarrow
\forall p\,[p\ne\bot\to
\Box\exists E^{tt}(K_{\rm pt}(E)\land Ep)].}
\tag{2}
```

The outer quantifier tests only current propositions. The observer may vary
at different accessible points. Neither BF nor C5 is assumed in these equivalences.

Changing that witness scope gives a much stronger principle:

```math
\boxed{\mathrm{Extensionality}\longleftrightarrow
\forall p\,[(\forall E^{tt}\, .\,
\neg\Box(K_{\rm pt}(E)\land Ep))\to p=\bot].}
\tag{3}
```

Thus the difference between a locally available observer at every point and
one observer working necessarily is substantive.

Further work below gives an exact atomic characterization (section 8), a
classification of all four qualification choices in full action models
(section 9), and a weaker observer criterion for C5 (section 10).

## 2. Whole conjunction-preserving involutions already preserve quantifiers

This supplies the positive baseline and repairs the earlier audit's unnecessary
restriction to separation at tt. For each admitted type sigma define

```math
c(b)=\lambda x^\sigma.b,\quad
L_E(F)=\lambda x^\sigma.E(Fx),\quad
Q(F)=\forall x^\sigma Fx.
```

C proves the entailment-order adjunction

```math
c(b)\le F\ \longleftrightarrow\ b\le Q(F).
\tag{4}
```

Indeed the two sides are respectively equivalent to
$`\Box\forall x(b\to Fx)`$ and $`\Box(b\to\forall xFx)`$.
The intervening distribution is an unconditional H theorem. This is the
constant-predicate adjunction, not the stronger claim that Q takes the infimum
of all currently admitted values of F.

Assume the whole meet and involution laws of E. Substitution of those
identities into lambda contexts, followed by beta and eta, proves the whole
meet and involution laws for L_E, and $`L_Ec=cE`$. This is equality congruence;
no application of Logical Equivalence under an optional hypothesis is used.
Both E and L_E are therefore order automorphisms. For all b,F,

```math
\begin{aligned}
b\le Q(L_EF)
&\longleftrightarrow c(b)\le L_EF
\longleftrightarrow L_Ec(b)\le F\\
&\longleftrightarrow c(Eb)\le F
\longleftrightarrow Eb\le QF
\longleftrightarrow b\le E(QF).
\end{aligned}
```

Antisymmetry gives $`Q(L_EF)=E(QF)`$. To obtain the whole quantifier-operation
identity, first discharge E's qualification and universally close this C
theorem. Necessitate that theorem and instantiate E under the box using CBF.
The finite qualification is a conjunction of identities, so NI makes it
necessary. Hence the pointwise result holds under $`\Box\forall F`$, and
Intensionality identifies the whole operations. The same argument upgrades
Boolean preservation; existential preservation follows by duality.

It follows that propositional separation by whole meet-preserving involutions
is equivalent over C to Rev. In the forward direction such separation yields
BF at each type: if every Fx is Top, every eligible observer accepts QF;
separation from Top identifies QF with Top. BF gives Functionality and lifts
separation to relational outputs. The converse uses involutive normalization
in the existing observer hierarchy, section 4.

## 3. Identity reflection and one-sided reflection of universal identity laws

Under K_pt(E), E is a Boolean order automorphism of the currently quantified
propositions. Pointwise involution supplies both injectivity and surjectivity;
pointwise meet preservation and order reflection then give preservation of
Top, Bottom, negation and the remaining Boolean operations as output identities.

For entities a,b of any fixed admitted type sigma,

```math
K_{\rm pt}(E)\ \longrightarrow\ [E(a=b)\leftrightarrow a=b].
\tag{5}
```

To prove the nontrivial direction, apply E to the unconditional Leibniz
substitution theorem with the admitted predicate $`P(z)=E(a=z)`$.
Boolean preservation yields
$`E(a=b)\to(E(Pa)\to E(Pb))`$.
Pointwise involution rewrites E(Pa) to a=a and E(Pb) to a=b.
The reverse direction follows by substitution and ETop=Top.

Consequently S_pt implies ND at every admitted type. If a and b are distinct,
every eligible E rejects both a=b and Bottom. Separation identifies these
propositions, so a=b is Bottom and its negation is necessary.

More generally, let u be a universally quantified formula whose matrix is a
Boolean combination of identity judgments. The terms inside the identities
may be complex. Then

```math
K_{\rm pt}(E)\longrightarrow(Eu\to u).
\tag{6}
```

For each current argument tuple, universal instantiation gives u entailment
below its matrix. Apply the Boolean order automorphism E. Equation (5) and
Boolean preservation make the image of that matrix agree with it in truth.
Thus Eu forces every matrix instance; generalization proves u. This is
one-sided reflection, not a claim of quantifier preservation.

In particular put

```math
n:=\forall x^t\forall y^t\,[x\ne y\to\Box(x\ne y)].
\tag{7}
```

Since $`\Box(x\ne y)`$ is the identity judgment
$`(\neg(x=y)=\top)`$, equation (6) gives $`En\to n`$.
The formula n is one closed proposition, not a schema over types.

## 4. Proof of the modal scope reduction

Assume $`T:=\forall p\,q\,\Box[p\ne q\to D(p,q)]`$.
T gives current S_pt by modal reflexivity, and section 3 therefore gives ND_t. Thus n is true,
so n is nonbottom. Applying ND_t to n and Bottom gives
$`\Box(n\ne\bot)`$.

Use T at the single old pair n,Bottom. Since every eligible observer fixes
Bottom, this gives

```math
\Box\exists E\,[K_{\rm pt}(E)\land En].
```

Necessitate the unconditional, universally closed reflection theorem (6),
specialized to n. It follows that $`\Box n`$, i.e. boxed ND_t. The recorded
type-reduction theorem gives C5. C5 supplies Functionality, which turns both
current pointwise qualification laws into whole-operation identities. Current
S_pt now gives Rev by section 2.

Conversely, Rev implies its separately boxed schema by the established
observer-hierarchy proof. Since it implies S_pt by a finite derivation, it
implies $`\Box S_{\rm pt}`$. CBF gives T. This also proves the first two
equivalences in (1), without assuming BF in their forward direction.

Either parameterwise formulation in (1) gives current S_pt and hence ND_t.
Current inequalities therefore persist, proving the last equivalence. For
currently identical parameters, NI makes the boxed conditional vacuous.

Equation (2) follows using q=Bottom in one direction and the Boolean symmetric
difference of p,q in the other. The same proof works directly: its T-consequence
gives current S_pt; the single instance p=n supplies the boxed acceptance needed
above. The variant with $`\forall p\,\Box[p\ne\bot\to\exists E(K_{\rm pt}(E)\land Ep)]`$
is equivalent as well.

Only the n-instance needs persistence once current S_pt is assumed. In particular,

```math
\mathrm{Rev}\longleftrightarrow
S_{\rm pt}\land\Box\exists E(K_{\rm pt}(E)\land En).
\tag{8}
```

All these parameterwise modal characterizations remain equivalent if either
pointwise qualification is strengthened to its whole-operation version: Rev
supplies the strongest witnesses, and the weakest version already implies Rev.

There is also an exact unboxed bridge:

```math
\mathrm{Rev}\longleftrightarrow S_{\rm pt}\land\mathrm{BF}_t.
\tag{9}
```

S_pt gives ND_t; the recorded ND_t plus BF_t theorem gives boxed ND_t and
therefore C5. Functionality then upgrades the qualifications and section 2
applies. Conversely Rev supplies both S_pt and BF_t. Thus BF_t is precisely
the missing additional premise for the current pointwise formulation.

## 5. A fixed necessary witness forces Extensionality

Assume the right side of (3), and let p be nonbottom. Its witness satisfies
K_pt(E) currently and $`\Box Ep`$, hence $`Ep=\top`$. Since E fixes Top and
is injective, p=Top. Every nonbottom proposition is therefore Top, which is
the Fregean Axiom. Over C this gives full Extensionality.

Conversely, under Fregean every nonbottom p is Top. The identity observer
qualifies necessarily by C alone and accepts p necessarily by NI. This proves
(3). In fact the weaker fixed-witness demand
$`\forall p[p\ne\bot\to\exists E(K_{\rm pt}(E)\land\Box Ep)]`$
already forces the same collapse.

The two-parameter version with a fixed E and necessarily differing outputs
also gives Fregean, by taking q=Bottom. These are witness-scope distinctions,
not failures of the parameterwise modal equivalences in section 4.

## 6. Sharp current and recurrent counterexamples

Use the full two-object retract category with jh=1_r and hj=k distinct from
1_s, evaluated at r. Root propositions are pairs, target propositions triples,
with transports

```math
H(a,b)=(b,a,b),\quad J(x,y,z)=(y,z),\quad K(x,y,z)=(z,y,z).
```

The raw observer profiles f_r(a,b)=b and f_h(x,y,z)=x XOR y XOR z induce

```math
E_r(a,b)=(b,a),\qquad E_h(x,y,z)=(x\mathbin\oplus y\mathbin\oplus z,z,y).
```

Both actions square to identity and are compatible with H,J,K, so whole
involutivity holds. The root action preserves conjunction pointwise. Identity
and E separate all four root propositions. Whole conjunction preservation
fails at s, for example on 100 and 010.

For the other hybrid, choose raw f_h(x,y,z)=y instead. The target action is
$`B(x,y,z)=(y,z,y)`$: it preserves meet everywhere, while $`B^2=K\ne I`$.
Thus whole meet preservation and only current pointwise involution also suffice
for separation at r. Both-pointwise separation follows from either example.

BF_t fails directly: the admitted predicate A has universal root extension
and raw h-extension $`x=z`$. Every current p has Ap=Top because Hp satisfies
that equation. But at h the newly quantified proposition 100 fails A. Hence
$`\forall p\Box Ap`$ and $`\neg\Box\forall p Ap`$.

This proves all three negative entries in the whole/pointwise 2-by-2 table.
The whole/whole entry is positive by section 2. Necessitating just one
pointwise qualification law yields exactly its whole version by Intensionality,
so the two hybrid counterexamples apply to that attempted repair as well.

Moreover $`S_{\rm pt}\land\Box\Diamond S_{\rm pt}`$ holds at r: every reachable
point can return to r, where S_pt holds. Yet Rev fails. Recurrent availability
of pointwise separation is therefore insufficient.

By contrast, $`S_{\rm pt}\land\Diamond\mathrm{Rev}`$ is equivalent to Rev.
S_pt gives ND_t, hence the current modal-5 schema. Rev implies its necessity;
thus possible Rev gives possibly necessary Rev, and modal 5 yields necessary
Rev. Here Rev can be represented by the single whole-law propositional sentence
of section 2. Bare possible Rev, even necessarily possible Rev, is insufficient:
the full one-way two-object chain has a terminal Fregean object satisfying Rev
while the root fails ND_t.

## 7. Relation to the choice and infinity package

The earlier suggestion that a bridge from boxed Functional Choice to Rev
remained to be found was mistaken. Existing proved records give

```math
\Box\mathrm{FC}\Rightarrow\Box\mathrm{Plenitude}
\Rightarrow\mathrm{C5}+\mathrm{Atomicity}
\Rightarrow\mathrm{Rev}.
```

The final implication is the existing atom-swap construction. Infinity is
not needed. A proved-only Engine query with no optional background confirmed
the recorded intermediate implications; this is not a new database theorem.

The distinction from current Functional Choice remains substantive. The
[model lane](pointwise-models.md) extends the retract by a countably infinite group
and fixed infinite individuals. It proves

```math
C+\mathrm{FC}+\Box I_e+\Box I_t+S_{\rm pt}+\neg\mathrm{Rev},
```

where I_e,I_t are the genuine quantified infinity axioms. The countermodel is
an ordinary full action construction in external ZFC. Current FC and infinity
therefore do not replace the modal requirement in (1).

Strict Forcing Possibilism is relatively independent of C plus boxed FC and these infinity axioms by
the countable-S5 and larger-S5 models in the
[ordinary-proof handoff](../../classicism-results-2026-10-24-v2/proofs/forcing-possibilism.md),
sections 2–3. Rev consequently holds on both sides. The new characterizations
do not reverse that result or supply an inconsistency argument for strict FP.

## 8. One atom forces the entire atomic package

Write OneAtom for the existence of a Boolean atom among propositions.
The [atomic proof](pointwise-atomicity.md), sections 2–4, establishes over C

```math
\boxed{S_{\rm pt}\land\mathrm{OneAtom}
\ \longleftrightarrow\
ND_t\land\mathrm{Atomicity}_t.}
\tag{12}
```

Actuality means that there is a true atom. Both right-hand premises are
current; no BF or Functionality is assumed. By [Atomicity and Vicinity](atomicity-vicinity-actuality.md), they imply Actuality. For the forward implication,
separation sends any atom to a true atom w. For any nonzero d, another
qualifying involution E makes Ed true. Then w≤Ed, and the atom Ew lies below
d. Conversely ND makes principal evaluations at current atoms endpoint-valued.
The admitted swap of an atom below d with a true atom is a pointwise
meet-preserving involution accepting d.

Consequently, under S_pt, OneAtom, Atomicity_t, and Actuality are equivalent.
There can be no mixture of an atomic part and a nonzero atomless part.
Combining this with Rev implies C5 and the established C5/Plenitude bridge
gives the further corollary

```math
\boxed{\mathrm{Rev}\land\mathrm{OneAtom}
\ \longleftrightarrow\ \Box\mathrm{Plenitude}.}
\tag{13}
```

For (13), Rev and OneAtom give current Atomicity_t by (12). C5 supplies BF,
which lifts Atomicity_t to relational Atomicity, and the recorded theorem
then gives necessary Plenitude. Conversely necessary Plenitude gives C5 and
Atomicity; the established atom-swap argument supplies Rev. The historical
C5/Plenitude equivalence is not new; the single-atom reduction is the corollary.

The atomic note also gives a verified counterexample to weakening (12): the
existing finite-support sections-and-projection model satisfies current ND
and necessary Actuality but fails Atomicity and S_pt.

## 9. Exact classification throughout the full action models

The [full-action proof](pointwise-action-characterization.md) replaces the isolated
retract calculations with the following complete classification at an
evaluation object R:

| Conjunction law | Involution law | Exact condition on every arrow out of R |
| --- | --- | --- |
| Whole | Whole | Invertible |
| Pointwise | Whole | Has a left inverse |
| Whole | Pointwise | Has a left inverse |
| Pointwise | Pointwise | Has a left inverse |

The first condition is Rev. The second condition is current ND_t in these
full models. This is a model-class theorem; ND_t is not sufficient for S_pt
in arbitrary C models, as the counterexample in section 8 shows.

For each split arrow h with jh=1, an explicit raw observer swaps the root atoms
1 and h. A three-coordinate xor correction makes it involutive on every
successor's entire proposition domain, even when hj differs from 1. A second
coordinate-selection construction instead makes the conjunction law whole.
Neither construction needs a coherent family of retractions or metatheoretic
choice. When both laws are whole, all outgoing arrows must be invertible.

Current Plenitude has the same left-inverse criterion in full models. In the
usual choice metatheory, so does current Functional Choice. In particular the
existing double-retraction model has current FC and Plenitude despite its
failure of coherent retractions, BF, Rev, and Strong Actuality.

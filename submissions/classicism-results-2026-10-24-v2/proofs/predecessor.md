# Pure Maximalism forbids numerical predecessor operations

Original mathematical argument, direct source misc; unpaginated.

For a fixed admitted counting type σ, put ν=(σt)t and let 0, S and N be
the repository's Frege zero, successor and impredicative natural-number
property. Define

```math
\mathrm{PredOp}_\sigma :=
\exists f^{\nu\nu}\,\forall n^\nu\,(Nn\to f(Sn)=n).
```

There is no condition on f(0). The operation type is admitted because ν is
relational. The conclusion is the unboxed negation of this sentence.

## The object-language argument

Suppose a and b are numbers and f satisfies the predecessor law. Then
f(Sa)=a and f(Sb)=b. Necessity of Identity makes each identity necessary.
The following implication is a bare logical theorem:

```math
f(Sa)=a\to f(Sb)=b\to\neg(Sa=Sb\land a\ne b).
```

Necessitate this theorem and apply K twice. The result is
□¬(Sa=Sb∧a≠b), contradicting ◇(Sa=Sb∧a≠b).
This step never necessitates the optional predecessor assumption or its
universal law. Every fixed finite numeral is a number already in C.

## A closed pure collision for each counting type

Use the full one-world Henkin interpretation with one individual. Its
proposition domain has two elements extensionally, and all function spaces
over finite domains with finite codomains are finite. Mutual recursion on
types therefore proves that every type, including ν, has a finite domain.

Externally define a_0=0 and a_(n+1)=S(a_n). Let O be the subtype of values
equal to a_n for some external natural n. O is finite, contains zero, and is
closed under S. If S restricted to O were injective, it would be surjective.
Then zero would be a successor. This is impossible: zero holds of the empty
property, whereas every successor fails there.

There are therefore external natural indices i,j with a_(i+1)=a_(j+1)
and a_i≠a_j. Their finite numeral terms define a closed pure sentence

```math
\psi_{\sigma,i,j}:=
(\overline{i+1}_\sigma=\overline{j+1}_\sigma)
\land(\bar i_\sigma\ne\bar j_\sigma).
```

This exact sentence holds in the interpretation. C soundness certifies its
consistency with C. Pure Max therefore entails ◇ψ. The object-language
argument above contradicts PredOp. No model, consistency, Infinity, or
noncollapse premise remains in the principal conclusion.

O need not equal the model's entire internal numerical domain. Only its
explicit numeral witnesses are used. The existential choice of i,j is in
the metatheory; the Max instance itself is a single finite sentence.

At σ=e, the model calculation is especially direct: 2=3 because both
cardinalities count no properties, while 1≠2 because 1 counts the universal
singleton property. A separate certificate retains this explicit instance.

## The graph and Plenitude

Define the represented relation on all of ν:

```math
U(x,y):=
[Nx\land x\ne0\land Ny\land x=Sy]
\lor[(\neg Nx\lor x=0)\land y=0].
```

C proves every number is zero or a successor of a number. Thus U is total
even without noncollapse. Under Iσ (equivalently I*σ), it is single-valued:
two numerical predecessors agree by successor injectivity, and the default
case has output zero. Any operation realizing U would satisfy PredOp.
Plenitude at (ν,ν) would supply such an operation.

The stronger final graph certificate is restricted to **σ=e**. Its
noncollapse premise is discharged as follows. The full Nat interpretation
satisfies quantified Infinity_e: induction on finite cardinalities shows
they count only externally finite subsets, and Nat itself is infinite.
The certified C implication Infinity_e→I*_e makes I*_e consistent. Pure Max
then gives ◇I*_e, which is precisely I_e. Combining this with the certified
no-predecessor result proves that the displayed U is total and unique but
has no realizing operation, and refutes the unboxed (ν_e,ν_e) Plenitude
instance. The proof does not assume actual Infinity_e under Max.

The graph result at every counting type requires an all-type Max→Iσ
certificate beyond the e-instance supplied here. Do not silently attribute
that stronger scope to these graph declarations. The all-type
no-predecessor theorem does not depend on that extra result.

Direct source: `research/2026-10-22/notes/relational-coding-recursion-20261022.md`
§38, original research (`misc`), unpaginated. The finite-orbit presentation
is a new proof organization of its finite-model argument. The Nat-model
Infinity proof follows the existing `axiomOfInfinityE_holds_nat` proof in
`Classicism/Results/Consistency/Consistency.lean`. A local AI auditor reviewed
the source and scope; no human verification or published attribution is claimed.

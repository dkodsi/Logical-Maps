# Infinitary formation, named exhaustion and arithmetic

Original mathematical argument, direct source misc; unpaginated.

## 1. Framework and object language versus metalanguage

Keep C's relational types: e, t and σ→τ only when τ≠e. Keep the original
H-theoremhood gate on Logical Equivalence. In particular, none of the extra
semantic truths introduced below is automatically a new instance of that
gate. NI is a theorem of C; BF and ND are not silently assumed. Set-sized
models and the external constructions below are understood in ZFC.

For every relational type τ and every external set I, consider the instance

```math
\forall(a_i^\tau)_{i\in I}\left[
 \bigwedge_{i\in I}\mathrm{Atom}_\tau(a_i)
 \to\exists b^\tau\left(
   \bigwedge_{i\in I}a_i\le_\tau b\ \land
   \forall c^\tau\left(
     \bigwedge_{i\in I}a_i\le_\tau c\to b\le_\tau c
   \right)\right)\right].
\tag{AJ}_{\tau,I}
```

Here order and atoms are the existing C definitions. There is no added world
sort. The choices of τ and I index the scheme in the **metalanguage**. Once
infinitary conjunctions and the indicated simultaneous quantifier block are
admitted, each displayed instance is an **object-language sentence**. For
countable I, that quantifier block requires the analogue of
$`L_{\omega_1,\omega_1}`$, not just $`L_{\omega_1,\omega}`$. Alternatively,
use an open formula with externally many free variables, required under every
external assignment. Closed instances substituting named terms cover only
named families and do not suffice for all external joins.

Three resource choices must remain separate:

| Resource | What it supplies |
|---|---|
| Infinitary assertions | Formulas or satisfaction conditions; they need not denote admitted propositions. |
| Infinitary term and λ formation | Actual entities in the quantified domains, with compositional truth and transport clauses. |
| Infinitary inference | Proof trees with specified rules; soundness and completeness are additional questions. |

Over the **principal-world general Gallin representation of CC**, all
external atom joins at every relational type are equivalent to external
fullness. Here CC includes boxed Functional Choice and the quantified Frege
infinities; this is not a claim about bare C. To see the nontrivial direction,
write the represented universe at type τ as the set of world–argument points.
The singleton at $`(w,\bar a)`$ is represented by
$`\lambda\bar x.(\delta_w\land\bar x=\bar a)`$.
For an arbitrary external set S of such points, join its singleton atoms.
The join includes S. If it included a point z outside S, subtracting the
represented singleton z would give a strictly smaller upper bound for every
singleton in S. Thus the join is precisely S. The converse follows by taking
unions in the full powerset hierarchy.

This is a semantic characterization. Countable joins, or joins below one
fixed cardinal bound, do not supply every external subset. The elementary
submodel construction in [the Gallin note, §7](full-gallin.md)
gives the precise bounded counterexample. Moreover,
[the join-calculus note](atomic-join-calculus.md)
proves incompleteness for the ordinary uniformly absolute set-coded proof
implementation. The semantic scheme does not supply its missing
model-existence theorem.

## 2. Finite named exhaustion is already recorded

Fix a finitary signature Σ with exactly u<ω individual constant symbols.
Its relational signature may be any set; it need not be finite. For u≥1,
write the individual names as $`c_1,\ldots,c_u`$. The recorded theorem is

```math
\mathrm{SP}_\Sigma\vdash
\begin{cases}
\forall x^e\forall y^e\;x=y,&u=0,\\
U_\Sigma:=\forall x^e\bigvee_{i=1}^{u}x=c_i,&u\ge1
\end{cases}
\tag{FNE}
```

This is an externally indexed schema of ordinary finitary object sentences.
Standing nonemptiness makes the zero-name case a singleton. For u≥1,
signature Max makes distinct individual-name symbols unequal, so the actual
e-domain has exactly u elements. Altogether its size is exactly max(1,u).
These are **actual individual-domain** assertions, not boxed exhaustion or
exhaustion at higher types.

The proof has two separate parts. First, the closed-Σ-profile root has the
names themselves as root individuals and uses components separating the
C(Σ)-non-theorems. Arbitrary actual extensions paired with closed-term
profiles supply relational domains and λ closure. The root therefore
satisfies Max(C(Σ))+UΣ. Every term has finitely many free parameters even
when the relational signature is infinite, so the profile substitution proof
still applies. With no individual names, use the singleton-marker root.

Second, if UΣ fails at a, the admitted proposition
$`q=\bigwedge_{i=1}^{u}a\ne c_i`$ is true. NI implies
$`\Diamond q\to a\ne c_i`$ for every i: an actual identity with ci would
persist and preclude q. Thus
$`\Box(\Diamond q\to\neg U_\Sigma)`$. The true q witnesses
$`\Box_{\ne}\neg U_\Sigma`$, proving
$`\Diamond_{\ne}U_\Sigma\to U_\Sigma`$. Eligibility supplies the
antecedent as an SP instance. The zero-name case uses a counterpair a≠b in
place of the finite list.

Useful object-language corollaries, with all other free variables universally
closed, are

```math
\forall x\,\varphi(x)\leftrightarrow\bigwedge_{i=1}^{u}\varphi(c_i),
\qquad
\exists x\,\varphi(x)\leftrightarrow\bigvee_{i=1}^{u}\varphi(c_i)
```

The theorem is in
[the signature audit, §10](../source/research/2026-10-22/notes/audit-signature-to-pure-sp-20261022.md)
and the frozen submission under **SP-INDIVIDUAL-CARDINALITY**
(`MAIN-RESULTS.json`) and **principles.27** (`CATALOG.json`). The full finite
theorem has not been Lean certified. The existing
`StrongPossibilityConsequencesSchemas.lean` checks monism reflection and
`pureSP_monism` **assuming** the relevant Max-consistency premise; it does
not build the profile model or prove all finite-name instances.

## 3. Countable names: one formation clause proves reflection

Fix exactly the individual-name symbols $`c_0,c_1,\ldots`$. Admit one
distinguished definitional predicate

```math
d_\Sigma:=\lambda x^e.\bigwedge_{n<\omega}x\ne c_n,
\qquad E_\Sigma:=\neg\exists x^e\,d_\Sigma x
\tag{D}
```

Its truth clause is required at **every evaluation point**. Equivalently,
use ordinary finitary syntax with one symbol d of type et whose interpretation
is constrained by that clause. It is not an arbitrary extra nonlogical
constant. E then means
$`\forall x^e\bigvee_{n<\omega}x=c_n`$. This is a restricted formation
resource: it does not admit all countable abstractions. An external assertion
of all inequalities without an admitted d(a) proposition is insufficient for
the following argument.

**Reflection theorem.** Under (D) and C,

```math
\Diamond_{\ne}E_\Sigma\longrightarrow E_\Sigma
\tag{R}
```

For each n, d(a) implies a≠cn. If a=cn, NI gives □(a=cn), so ◇d(a) is
impossible. Hence ◇d(a) implies every a≠cn, and the stipulated clause
assembles these conclusions into d(a). Therefore
$`\Diamond d(a)\to d(a)\to\neg E_\Sigma`$. This argument holds at
every point, giving $`\Box(\Diamond d(a)\to\neg E_\Sigma)`$.
If ¬E holds actually, choose an actual a with d(a). The admitted proposition
q=d(a) witnesses

```math
\exists q^t\,[q\land\Box(\Diamond q\to\neg E_\Sigma)]
=\Box_{\ne}\neg E_\Sigma
```

Contraposition gives (R). No optional BF or ND is used.

For a syntactic proof, explicitly provide the projections d(a)→a≠cn,
contextual countable introduction from every $`F\to a\ne c_n`$ to
$`F\to d(a)`$, and theorem necessitation for the enriched calculus. The
boxed line comes from a theorem, not from necessitating an optional premise.
If one first universally closes it, CBF (already a theorem of C) permits
specializing the necessarily universal statement to an actual a.

E by itself says **at most countably many** individuals. It says exactly
countably infinitely many only together with pairwise distinctness of these
names. Crucially, (R) alone does not establish the needed SP eligibility:

```math
\mathrm{Con}\bigl(\mathrm{Max}(T)+E_\Sigma\bigr)
\tag{Eligibility}
```

Consistency of T, or even of T+E, is not enough. The reference theory T must
be specified. For an unspecified $`C_\infty(\Sigma)`$, the countable SP
claim remains conditional on this separate obligation.

## 4. A restricted semantic reference with a proved eligibility bridge

The following is a new adaptation of the recorded profile construction.
Let Ld be **finitary** C(Σ) syntax plus the constrained symbol d in (D).
Let Kd be the class of set-sized action models of C satisfying its countable
truth clause at every object. Define
$`T_d:=\mathrm{Th}(\mathcal K_d),`$
the set of finite Ld sentences valid at all points of all Kd models. This is
an explicit, potentially noneffective **semantic reference theory**. It does
not mean a theory deciding every sentence, and it asserts no completeness
of an infinitary proof calculus. Keep Logical Equivalence restricted to the
original H-theorems in Ld. Theoremhood in Td is validity, equivalently
derivability from all these validities using the sound C rules.

Write Max(Td) for Td together with s≠t for each same-type closed-term
identity s=t not in Td. Define SP(Td) using the corresponding
Max(Td)-consistency side condition. The usual finitary C metarules remain
available. We prove

```math
\mathrm{Con}(\mathrm{Max}(T_d)+E_\Sigma),
\qquad \mathrm{SP}(T_d)\vdash E_\Sigma
\tag{SNE}
```

**Separating components.** For every closed identity absent from Td, choose
a Kd model and a point refuting it. There are set-many finite Ld identities.
In ZFC a set of witnesses can be chosen: first bound the least ranks of
witness codes by Replacement, then use Choice in the resulting set. Retain
each entire component and all its objects and arrows. We may also explicitly
include the two full one-world models with individual domains ω and
ω∪{*}, with cn=n and d respectively empty and {*}. Both satisfy (D).

**Root and action.** Add an object o with individual domain the symbols
$`\{c_n:n<\omega\}`$. For each component object V, add o→V sending cn
to its interpretation at V. Compose this arrow with V→V′ as o→V′.
Constant coherence guarantees compatibility. Arrows may merge names;
injectivity would add an unwarranted ND requirement.

At relational type $`\tau=\tau_1\cdots\tau_k t`$, define

```math
D_\tau(o)=\mathcal P\!\left(\prod_{i=1}^{k}D_{\tau_i}(o)\right)
\times B_\tau,
```

where Bτ consists of profiles of **closed Ld terms**, with equality of
profiles meaning equality of denotations at every component object. A root
pair (A,bT) is sent to the component denotation of T. Term naturality in the
components makes these maps compose. Profiles contain entity values, not
just actual truth values. Since every component object and arrow is retained,
their extension data determine those intensions, as in the existing audit.
Interpret each individual constant by its root symbol. Interpret each other
relational constant r of Σ by any actual root extension, for example the
empty one, paired with its own closed-term profile br. The constrained d is
handled separately below.

**Closure.** For a finite term M with root parameters p1,…,pm, choose closed
profile representatives T1,…,Tm and substitute them simultaneously. This
produces another finite Ld term. In an abstraction, leave its bound variables
symbolic: use $`\lambda y.M(y,T_1,\ldots,T_m)`$. The actual coordinate is
the unrestricted root extension of this abstraction; its profile is the
displayed closed term. Application and βη agree in both coordinates.
Quantification at a component uses that component's **whole original
domain**, not merely the image of the root domain. Boolean, equality and
quantifier objects have their usual root extensions and closed profiles.
These clauses validate H. For an H-theorem equivalence, the root extensions
agree by H soundness and the profiles agree by component Logical Equivalence.
This verifies the original gate without extending it to arbitrary Td truths.

**The new predicate.** Interpret d at o by the empty actual extension paired
with its own closed-term profile. Every root individual is a name, so (D)
holds at o; it holds in the unchanged components by their selection. Its
naturality comes from the full d-profile, not from transporting its empty
actual extension alone. For a transported root name cj, d(cj) is false in
every component, but an unnamed component individual can still satisfy d.
Thus the graft belongs to Kd. This establishes all Td truths at the root by
the definition of Td, with no circular appeal to Td-completeness.

**Max and exhaustion.** Every identity absent from Td fails in a selected
component, so its two root profiles differ at relational types. The only
closed e-terms are names, and distinct name symbols are distinct root
individuals. The root therefore satisfies every Max disequality. Its
individuals are exactly the names, so E holds. This is a
model of Max(Td)+E and proves eligibility. In particular, the finite sentence
$`\forall x\,\Box(\Diamond d(x)\to\exists y\,d(y))`$ is valid throughout
Kd by the argument in §3, so it belongs to Td. It supplies reflection (R)
by ordinary finite reasoning; no unprovided finitary rule assembles the
countable inequalities. The eligible SP instance ◇≠E now gives E.

SP entails every Max disequality s≠t: the constructed Max model makes that
disequality eligible, ◇≠(s≠t) implies ◇(s≠t), and NI reflects the latter
to s≠t. Distinct symbols cn,cm can be interpreted distinctly in the full ω
model, so cn=cm is absent from Td. Thus SP(Td) entails **exactly** countably
many actual individuals. This
entailment makes no claim that SP(Td) itself is consistent.

**The conclusion is not built into Td.** The full ω+{*} model refutes E,
so Td does not contain E. At the graft, the closed proposition ¬E has a
nonzero profile (the added ω+{*} component witnesses it), giving ◇¬E.
More generally, the closed identity (¬E)=⊥ is absent from Td, so Max(Td)
itself entails ◇¬E. The constructed root therefore satisfies
Max(Td)+E+¬□E. SP(Td) entails actual exhaustion and its failure of
necessity, again without a consistency claim for SP.

For a syntactic reference T, the same separation construction applies if T
is sound for Kd and **complete for closed identities** relative to Kd.
That is the separation obligation used in the construction. It is substantial:
in this globally specified model class, validity of a sentence A implies
validity of A=⊤, so identity completeness also supplies closed-sentence
completeness and the needed reflection theorem. No such calculus has been
established here for an unspecified C∞. Changing the reference from original C to Td is part of the
proposal and must remain explicit. Omitting the numeral abstraction of §5
avoids that particular obstruction; it does not by itself prove compatibility
of (D) with original Max.

## 5. Other useful infinitary shortcuts and their limits

### One pure abstraction standardizes Frege arithmetic

At the cardinality type $`\nu=(et)t`$, let νn denote the existing finite
numeral term $`\mathrm{Suc}_e^n0_e`$. Admit just

```math
P:=\lambda Z^\nu.\bigvee_{n<\omega}Z=\nu_n
\tag{Num}
```

with its pointwise clauses everywhere. P contains zero and is successor
closed. Impredicative finite-cardinality numberhood N is consequently
contained in P; ordinary finite induction proves the converse. At any point
satisfying $`I_e=\Diamond I_e^*`$, an accessible I* point separates all
finite numerals. NI pulls their distinctness back, so N at the original
point is precisely standard ω.

No full relation domain is needed to get standard addition and multiplication.
At standard m,n, the finite relation

```math
R_{m,n}(i,j)=
\bigvee_{k=0}^{n}(i=\nu_k\land j=\nu_{m+k})
\ \lor\ \bigwedge_{k=0}^{n}i\ne\nu_k
```

contains the initial pair, is closed under the addition recursion, and
excludes every wrong endpoint at first coordinate νn. The unrestricted tail
ensures closure. Replacing νm+k by νm·k gives the multiplication analogue,
using the already verified addition relation. Induction on finite arithmetic
syntax now gives standard truth at every I point. Each arithmetical A
therefore satisfies

```math
\Box(I_e\to A)\ \lor\ \Box(I_e\to\neg A)
```

This contradicts **original finitary Max**, whose reference theory C is
recursively enumerable and consistent with I. A Rosser-independent arithmetic
sentence over C+I gives both C-consistent I∧A and I∧¬A; original Max
makes both possible. The recorded incompatibility is
[`possibility-and-necessity-of-arithmetic-incompatible`](../source/topics/classicism/results/possibility-and-necessity-of-arithmetic-incompatible.yaml),
from Goodsell, *Arithmetic is Necessary*, draft 5 June 2024, §6, Theorem 11
and note 14, pp. 24–26. A proved-only Engine query on precisely
`distinctness-schema-r` and `necessity-of-arithmetic` returns that proof of
false. The reduction to the one term (Num) is the new local argument in
[the abstraction note, §12](../source/research/2026-10-22/notes/quotient-abstraction-lane.md),
not a claim attributed to Goodsell. The cited incompatibility record has
Lean status `stated`; the one-term reduction is an ordinary local proof
without Lean certification.

Thus general countable λ formation is not an innocuous addition to original
Max. It includes (Num). The restricted naming predicate d has type et,
whereas (Num) is a property of cardinality objects; (D) does not automatically
provide (Num). Replacing original C in the Max side condition with a stronger
reference theory is a different theory, as §4 explicitly does.

With the **whole** countable infinitary λ language, every external
$`S\subseteq\omega^k`$ is represented on standard numeral tuples by
$`\lambda\bar z.\bigvee_{\bar n\in S}\bigwedge_i z_i=\nu_{n_i}`$.
This gives full second-order arithmetic there. An alternative is an ω-rule
on intrinsic N together with enriched theorem necessitation: truth induction
then derives each true arithmetic sentence under I and hence its necessary
conditional. That is a new proof rule, unsound for unrestricted original
Henkin models; it is not merely a shorter finitary C proof.

### Unbounded parameter formation supplies Actuality and Atomicity

Suppose every external set-indexed parameter conjunction and its λ
abstraction denotes an admitted object, with ordinary pointwise truth clauses
and coherent transport at all reachable points.
At an actual point w, conjoin all its true propositions. The resulting a is
true at w and algebraically entails every proposition true there. This is an
Actuality witness.

For Atomicity at any relational type, take a nonbottom R and an accessible
point/tuple where R is true. For every root relation Y, select Y or ¬Y
according to its truth at that point/tuple, and λ-abstract their conjunction.
It gives a nonbottom a≤R. For each root Y, either a≤Y or a≤¬Y.
If z≤a, the first alternative for Y=z gives z=a; the second gives z=⊥.
Thus a is an atom. Applying this at every point yields boxed Atomicity.
These two arguments use no optional BF or ND. They require an external
family ranging over the **entire** relevant root domain; arbitrary bounded
closure does not suffice.

With C5, the recorded implication from Atomicity to boxed Plenitude yields
the full constant-domain intensional S5 representation. Propositions are
$`\mathcal P(W)`$, not merely two truth values; actual Extensionality is
not asserted. ZFC then supplies boxed Functional Choice in the full
hierarchy. Over ZF the relevant external choice remains an additional
assumption. Details are in the abstraction note, §§8 and 11.

For every fixed infinite regular κ, the support construction in that note,
§10.3, is closed under parameter formations of size <κ yet fails Actuality
and Atomicity. It uses coordinates I=κ×2, worlds $`\mathcal P(I)`$, and
the full group Sym(I); admitted objects have supports of size <κ. Unions of
<κ supports remain small.
At a balanced world A, neither A nor its complement is small, so its singleton
world proposition is not supported, although supported coordinate
propositions separate worlds. The invariant proposition consisting of all
balanced worlds is nonzero and has no singleton atom beneath it. This
separates fixed-bound closure from the unbounded conclusions above.

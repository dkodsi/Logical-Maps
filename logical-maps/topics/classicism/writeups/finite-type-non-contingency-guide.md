# Two finite-type non-contingency principles

FTN and FTAN extend arithmetic and analytical necessitism by iterating the
same rigid-power construction. Each finite height gives a
separate sentence; neither collects an infinite hierarchy into one object.

| Principle | When an instance applies | What it supplies |
| --- | --- | --- |
| [[finite-type-necessitism]] (FTN) | The canonical arithmetic at the source type is necessarily genuine | Rigid represented powers of the canonical numbers, through each specified finite height |
| [[finite-type-analytic-necessitism]] (FTAN) | A real-number structure is possible at a host type | A rigid, necessarily real structure at that same host type, with represented powers through each specified finite height |

## What a represented power adds

For a carrier \(X\), put \(\mathsf P(X)=\{A:\operatorname{Rigid}(A)\land A\le X\}\),
where inclusion is necessary inclusion. Requiring this canonical family to
be a represented power says that the family is rigid and that, at every
possibility, every admitted predicate on \(X\) agrees there with a member.
A rigid \(X\) alone does not ensure this fullness.

FTN iterates this operation from the numbers: subsets of numbers, families
of those subsets, and so on. FTAN starts from a returned real carrier.
The real carrier stays at the original host type; its powers occupy their
native higher predicate types.

## Four proved connections and what they add

1. **Necessary Rigid Comprehension + current Rigid Power → FTN.**
   This identifies familiar sufficient assumptions: boxed comprehension
   supplies necessary fullness, and current Rigid Power fixes each successive
   family. Rigid Power need not be boxed.
   [Proof](necessary-rigid-comprehension-and-rigid-power-imply-finite-type-necessitism.md).
2. **FTN → Arithmetic Necessitism.**
   The first represented power already fixes its number carrier, under the
   same arithmetic guard.
   [Proof](finite-type-necessitism-implies-arithmetic-necessitism.md).
3. **FTN + Analytic Necessitism → FTAN.**
   This strengthens the source paper's UFTN + AN bridge: UFTN additionally
   asserts necessarily genuine arithmetic at \(e\), but that extra assumption
   is unnecessary. An activated AN instance supplies a fixed real field;
   its number substructure activates FTN. The resulting finite powers
   transfer to that same real field.
   [Proof](finite-type-necessitism-and-analytic-necessitism-imply-finite-type-analytic-necessitism.md).
4. **FTAN → Second-Order Analytic Necessitism (SOAN).**
   Finite tuple coding converts sufficiently many unary power levels into
   represented relations of each requested finite arity.
   [Proof](finite-type-analytic-necessitism-implies-second-order-analytic-necessitism.md).

The last connection gives Necessity of Second-Order Analysis and
Non-contingency of CH through the existing SOAN implications.
SOAN supplies relations on reals; FTAN additionally supplies higher
families of relations.

## Why the same carrier type matters

Even with an active arithmetic guard, FTN does not imply AN as the map
defines it. FTN builds a fixed real field at a suitable higher type.
AN requires one at the **same type at which a real field was possible**.

The source's full paired-profile model makes this distinction concrete.
Its root has one individual; its terminal point has continuum many.
Relational objects at the root are all pairs of current and terminal
profiles, and transport takes the terminal profile. A carrier projecting
bijectively to its terminal carrier is fixed; paired subsets and their
images supply its full rigid powers at every finite height.

The canonical numbers have distinct numeral profiles and project
bijectively to the terminal numbers. This verifies FTN at every activated
source and an active arithmetic guard at \(e\), hence UFTN. Yet a real
field at individual type is possible only terminally: none fits on the
root singleton. AN fails at \(e\), while the fixed reference continuum
remains available at a higher relational type. [1, §7.]

Thus the obstruction persists even when genuine arithmetic exists.
FTN + AN → FTAN retains original-host realization as a premise.

## The reference variant and its arithmetic bridge

Change AN's consequent so that the fixed real field need not occupy the
original host. For each fixed counting source \(\sigma\), put
\(\rho_\sigma=((\sigma t)t)t\). The source's **Reference Analytic
Necessitism**, written here \(\mathrm{AN}^{\mathrm{ref}(\sigma)}\), is
the schema, for every specified target host \(\tau\),

\[
\Diamond\exists\mathfrak R\,\operatorname{Real}_\tau(\mathfrak R)
\ \to\
\exists\mathfrak R\,[\operatorname{RigidStr}(\mathfrak R)
             \land\Box\operatorname{Real}_{\rho_\sigma}(\mathfrak R)].
\]

The source calls this RANA; its second-order version, SRANA, also supplies
the represented relations required by SOAN on the reference field.

The exact proved bridge is

\[
\boxed{\mathrm{FTN}+\Box I^*_\sigma
       \ \Longrightarrow\ \mathrm{SRANA}_{\rho_\sigma}
       \ \Longrightarrow\ \mathrm{AN}^{\mathrm{ref}(\sigma)}.}
\]

Under the guard, Dedekind cuts of rational codes in the first full rigid
power form a fixed necessarily-real field. Unions of admitted bounded
families of cuts have representatives by fullness, proving completeness.
Higher powers, restricted to this field and finite tuple codes, supply
the represented relations. The construction already supplies the
reference without needing the possible-real antecedent. [1, §4.]

RANA implies Necessity of Analysis. SRANA implies Necessity of Second-Order
Analysis and Non-contingency of CH: truth is stable on the full fixed
reference and transfers by categoricity to genuine real structures at
other types. This does not require a fixed realization at each such type.

The arithmetic premise is **\(\Box I^*_\sigma\)** at one specified source.
It must not be replaced by the map's weaker \(I_\sigma=\Diamond I^*_\sigma\).
Types remain schema parameters; there is no quantifier over types.
UFTN includes the required guard at \(e\). Bare guarded FTN does not:
complete-component coalesced roots satisfy FTN vacuously while analytical
truth principles fail. See [the model arguments](finite-type-model-verdicts.md).

## SOAN with failure of Arithmetic Necessitism

The [[symmetric-cohen-arithmetic-growth]] model has active
\(\Box I^*_e\) but a number carrier that is not inextensible, so Arithmetic
Necessitism fails. No real structure is possible at any admitted host.
Therefore every possible-real antecedent is false: **FTAN, SOAN and AN
all hold**, while FTN fails.

More generally, relative to a specified failed Arithmetic Necessitism
instance, **AN, SOAN, FTAN and the all-type absence of possible real
structures are equivalent**. Any possible field together with AN would
give a fixed Peano reference. That reference fixes the offending
canonical numbers under their active arithmetic guard, a contradiction.
Conversely, no possible fields makes all three analytic schemas vacuous.
Their analytical-truth and CH consequences can therefore hold while
structural Arithmetic Necessitism fails.

In the Cohen model, the necessary arithmetic guard and no-possible-reals
result also imply **necessary failure of Transversal at \((et)t\)** and
**necessary failure of Actuality**. Current genuine arithmetic plus that
Transversal instance gives a real field at \(((et)t)t\); necessitating
this closed conditional proves the first failure, and Actuality implies
Transversal. No possible reals alone would not suffice. See the
[full consequences](symmetric-cohen-arithmetic-growth-consequences.md) and
[finite-type verdict](symmetric-cohen-arithmetic-growth-finite-types.md).
This does not identify failure of Arithmetic Necessitism with failure of
the distinct Necessity of Arithmetic principle.

The model [[stitched-countably-closed-subset]] separates FTN from necessary
Rigid Comprehension + AN: a new subset of an unchanged first power defeats
the next rigid power. This explains the extra Rigid Power premise in the
positive generator.

## Sources

1. GPT-6 Astra, prompted by Daniel Kodsi, *Finite-Type Necessitism and Analytic
   Non-Contingency*, 30 October 2026, §3, Proposition 5, pp. 4–6; §4,
   Proposition 7, Theorem 8 and “Reference formulations,” pp. 6–8; §7,
   “Fixed mathematics and a changing available carrier” and the arithmetic
   separation, accompanying unpaginated Markdown version. The source uses
   SANA for the map's SOAN.
2. OpenAI Codex, prompted by Daniel Kodsi, *Simple generators for finite-type
   mathematical non-contingency*, 29 October 2026, §§1–3, and *Finite-type
   necessitism: a stronger comparison and simpler bridges*, 29 October 2026,
   §§3–4, both unpaginated. The linked proofs reproduce the generator and
   strengthened FTN + AN bridge with their precise assumptions.
3. GPT-6 Astra, prompted by Daniel Kodsi, *Symmetric Cohen model: arithmetic
   growth*, 29 October 2026, §§7.2–7.4, and *Finite-type consequences*,
   29 October 2026, §5, both unpaginated. The NoReal supplement supplies the
   additional Transversal and Actuality consequences with their guards.

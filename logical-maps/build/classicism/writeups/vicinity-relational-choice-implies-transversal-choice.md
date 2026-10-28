# Vicinity and Relational Choice give Transversal Choice

For every fixed type \(\sigma\), including \(e\), C proves
\[
\operatorname{Vicinity}+RC_{\sigma t,\sigma}\ \Longrightarrow\ TC_\sigma.
\tag{1}
\]
Thus full RC, TC, Well-Ordering and Zorn coincide over C plus Vicinity.
Unboxed ND_t suffices through its existing implication to Vicinity.
No completeness or Actuality premise is used. We first prove the C5 lemma,
then interpret it on a true Vicinity region without shrinking the carrier
on which the transversal is required.

## 1. Normalize the equivalence and partial transversals

Fix a current equivalence \(R\) on \(\sigma\), and let \(\rho=\sigma t\).
Define its uniform equivalence closure
\[
Q(x,y):=\forall P^{\sigma\sigma t}
 ((\operatorname{Equiv}(P)\land R\subseteq P)\to(Px)y),
\qquad (SA)x:=\exists y((Qx)y\land Ay).
\]
H proves, for arbitrary \(R\), that \(Q\) is an equivalence and contains
\(R\). Since the current \(R\) is an equivalence, \(Q\) and \(R\)
currently agree. The unconditional equivalence laws give literal C
saturation identities: \(S0=0\), \(S1=1\), \(SS=S\),
\(A\le SA\), \(S(A\lor B)=SA\lor SB\), and
\(S(A\land SB)=SA\land SB\). Saturation also commutes with admitted
existential unions. No optional equivalence enters Logical Equivalence.

Call \(B\) *strictly local* when
\[
P(B):=(\lambda A.B\land S(B\land A))=(\lambda A.B\land A).
\]
This is one identity, so C5 makes its value an endpoint. It implies that
\(B\) is a current partial transversal: apply locality with a singleton
to any two related members. Conversely the term
\[
N(D)x:=Dx\land\forall y((Dy\land(Qx)y)\to y=x)
\]
is strictly local by an unconditional H uniqueness proof and Logical
Equivalence. If \(D\) currently has a singleton extension, \(N(D)\)
has that same extension. Strict locality is hereditary under algebraic
subobjects.

## 2. Choice supplies a progressive operation

Set \(\operatorname{Full}(B):=\forall x(SB)x\). The relation
\(U(B,a):=\operatorname{Full}(B)\lor\neg(SB)a\) is currently serial:
use any object when Full holds and a missed object otherwise. The single
instance \(RC_{\rho,\sigma}\) gives a current functional subrelation
\(K\) of \(U\), total on \(B\). Put
\[
K_B:=\lambda x.(KB)x,\qquad
f(B):=B\lor(N(K_B)\land\neg SB).
\]
This is an admitted \(\rho\rho\) operation even when \(\sigma=e\).
It has \(B\le f(B)\). If \(B\) is local, write
\(D=N(K_B)\land\neg SB\). Then \(D\) is local and
\(SD\le\neg SB\); a complement of an S-fixed object is S-fixed.
Expanding the locality expression for \(B\lor D\), the two cross terms
vanish and the diagonal terms are \(B\land A\) and \(D\land A\).
Thus \(f\) preserves locality. C5 Functionality collects these value
identities into the displayed whole-operation identity.

If \(B\) misses a cell, its unique current K-output \(a\) satisfies
\(\neg(SB)a\). The singleton property \(K_B\) is preserved currently
by \(N\), so \(f(B)a\) and \(\neg Ba\). Hence \(f(B)\ne B\).
It remains to find a fixed point among local objects.

## 3. C5 supplies exactly the joins the canonical chain needs

Under C5, identity predicates and their quantified Boolean combinations
are endpoint-valued. For any family code \(X^{\rho t}\), write
\(\widehat X(B):=\Box XB\); this is endpoint-valued. Only such families
are used below. BF makes the admitted existential their actual algebraic
join, not merely a material union.

If an endpoint-valued family \(X\) consists of a chain of local objects,
its join \(J_X(x):=\exists B(XB\land Bx)\) is local. To see this,
expand \(J_X\land S(J_X\land A)\). For any two members \(B,D\),
comparability and locality imply \(B\land S(D\land A)\le A\).
These bounds collect across the two admitted existential indices by BF;
zero membership coefficients contribute zero. This gives the desired
locality inequality; the reverse is saturation's unit law. Functionality
packages it as P(J_X). The empty join is zero. No arbitrary current family
has been rigidified and Boolean Completeness has not been assumed.

Use endpoint-valued family codes to define an f-chain as a chain in P
well-ordered against all admitted endpoint subfamilies, with every member
\(b\) the algebraic supremum in P of
\(\{f(a):a<b\text{ in the chain}\}\). All clauses are formulas in
identities, so the predicate of f-chain codes is endpoint-valued.
The singleton zero is an f-chain.

Two f-chains agree up to an initial segment and one extends the other.
Indeed form their common initial segment of elements with the same strict
predecessors. If both remainders were nonempty, their least elements
would have exactly that common predecessor family; their defining
supremum property makes them equal, a contradiction. Every difference
and predecessor family here is an admitted endpoint predicate.

Let A be the admitted existential union of all f-chains. It is again an
endpoint-valued f-chain. Comparison gives linearity and the predecessor
condition. For well-foundedness, choose any element of an admitted
nonempty subfamily and a chain containing it. The least element of the
subfamily's intersection with that chain is globally least by comparison.
Let \(u=J_A\), which exists and is local by the preceding join lemma.

If \(u\notin A\), A has no greatest member. For each \(a\in A\) choose
a later \(b\in A\); conformity gives \(f(a)\le b\le u\). Since
\(a\le f(a)\), u is also the supremum of f[A]. Appending u gives another
admitted endpoint f-chain, contrary to the definition of A. Thus
\(u\in A\). If \(u<f(u)\), appending f(u) again gives an f-chain:
f(u) is the greatest member of f[A]. This contradicts u being an upper
bound of A. Hence \(f(u)=u\), and §2 forces Full(u). Locality and Full
make u an R-transversal. This proves the C5 lemma without Zorn or BC.

## 4. Rebase the Vicinity interpretation before taking its support

The [existing supported-interpretation theorem](vicinity-relational-choice-implies-transversal-choice.html#supported-interpretation),
§§2–5, supplies from Vicinity a true proposition s that decides current
identities and collects every typed algebraic bound below s. Its hereditary
retractions give a concrete C5 interpretation and preserve strict Logical
Equivalence by a finite positive-identity guard, without ambient BF or
Functionality. Those sections use Vicinity alone; their RC/completeness
application occurs later.

Use that construction with a fresh source individual sort \(e_0\)
interpreted as the **entire original \(\sigma\) carrier**, and source
\(t_0\) as original t. Recursively translate source arrow types. This
respects the restriction on individual-valued functions: source arrow
codomains are never \(e_0\). Set \(j_{e_0}\) to identity substitution,
\(j_{t_0}(p)=s\land p\), and
\(j_{\alpha\beta}(F)=\lambda x.j_\beta(F(j_\alpha x))\).
The identity substitution convention does not introduce an ee operation.
The cited proof is parametric in the original types and applies unchanged.
Even if two source sorts translate to the same original type, keep their
separately specified domains and retractions distinct.

The interpreted individual domain is therefore all original \(\sigma\),
and its property domain is the image of \(j(X)=\lambda a.s\land Xa\).
For a supported serial relation U from that property domain to individuals,
apply original \(RC_{\sigma t,\sigma}\) to
\(V(X,a):=U(jX,a)\). A selected relation K retracts to
\(L(X,a):=s\land K(jX,a)\). On fixed inputs its current membership
and equality of outputs agree with the original ones, so it witnesses
the required source RC instance.

Original \(R\) becomes \(R^s(a,b):=s\land R(a,b)\), with exactly the
same current equivalence classes. The C5 lemma supplies a source
transversal. It is an actual admitted original property of \(\sigma\),
and the source individual domain contains every original object. Hence
it is the desired original transversal. No quotient representatives or
descent across coextensive codes are selected.

## 5. Consequences and exact modal scope

Necessitating the discharged theorem (1) gives
\(\Box\operatorname{Vicinity}+\Box RC\to\Box TC\).
Together with MRC-to-boxed-MRC, the existing boxed TC-to-boxed Well-Ordering
arrow and Dorr's boxed Well-Ordering-plus-IC theorem, this also yields
\(\Box\operatorname{Vicinity}+MRC\to\) Modal Well-Ordering. No duplicate
records for these longer derived paths are needed.

The bare-C conjecture RC → TC remains open. The type-t result uses
\(RC_{tt,t}\), not \(RC_{t,t}\). The proof does not obtain Vicinity
from RC or Actuality without further premises.

## Sources and review

Direct sources: OpenAI Codex, prompted by Daniel Kodsi, *Strict local sections, crisp chains, and
Relational Choice*, 25 October 2026, §§1–4; *The observer machinery and
the remaining RC–TC gap*, 25 October 2026, §§1–2; and *Vicinity suffices
for Relational Choice to imply Transversal Choice*, 26 October 2026,
§§1–5; all unpaginated. The common-core construction retains Christopher
Sun's attribution in the linked existing proof. This consolidated
referee-oriented argument was independently read and checked on
28 October 2026. Ordinary AI review; no human or Lean certification.


<a id="supported-interpretation"></a>

## Appendix: supported interpretation from Vicinity

The supporting proof below retains its original internal section numbering.

This note supplies the supported C5 interpretation used in the Transversal Choice proof; it asserts no additional database result.

## 2. One core controls all admitted quantifiers

Choose a true Vicinity witness w. Put

\[
A_w:=\forall r^t\,(r\to w\le\Diamond r),\qquad s:=w\land A_w.
\]

Both w and A_w, hence s, are currently true. For every fixed admitted argument type σ and every admitted F:σt,

\[
\bigl[\forall x^\sigma\,(s\le F(x))\bigr]
\ \Longrightarrow\ s\le\forall x^\sigma F(x).
\tag{3}
\]

Here and below the conclusion is an algebraic bound, not just a material implication.

For the proof let T:=∀x(s≤F(x)) be currently true. Vicinity gives
w≤◇(w∧T). Work at any accessible evaluation v where s is true. Suppose that an x available there satisfies ¬F(x). At v the A_w conjunct applies to the proposition s∧¬F(x), which is true there, and gives

\[
w\le\Diamond(s\land\neg F(x)).
\]

The bound w≤◇(w∧T) obtained at the original evaluation persists to v. Since w holds at v, there is an accessible u where w∧T holds. The parameter x is available at u; this uses only the converse-Barcan direction. T supplies □(s→F(x)) at u. The bound obtained at v also persists to u, and w there gives ◇(s∧¬F(x)), a contradiction. Thus every x at every accessible s-evaluation satisfies F(x), proving (3).

This is an ordinary S4/CBF derivation expressed by evaluations. No Barcan premise, completeness, choice, or necessitation of an optional premise is involved. The same argument applies at every evaluation satisfying s, since w∧A_w holds there again. Its mechanism is the one used in Sun's recorded Vicinity argument; its all-type formulation here makes the required quantifier scope explicit.

For every current identity E=(a=b), at any type, s decides E according to its current truth. If E is true, NI gives E=1. If E is false, Vicinity gives w≤◇¬E. NI makes E persistent, so ◇¬E=¬E. Consequently

\[
s\land E=\begin{cases}s,&a=b,\\0,&a\ne b.\end{cases}
\tag{4}
\]

Induction on finite formulas, using (3) at universal quantifiers and a current witness for a false universal, extends this decision property to formulas built from identities by Boolean operations and typed quantifiers. Arbitrary atomic membership assertions are not included in that claim.

There is also an exact range-bound consequence. For any admitted f:σt,

\[
s\land\exists x^\sigma f(x)
=\bigvee_{x\text{ current}}\bigl(s\land f(x)\bigr).
\tag{5}
\]

The right side means the actual algebraic least upper bound of the displayed range; (5) establishes its existence without BC. Instantiation gives each upper-bound inequality. If b bounds every s∧f(x), then s≤(f(x)→b) for every current x. Equation (3) collects these bounds into s≤∀x(f(x)→b), which gives the converse inequality. The relative meet statement is dual. An index predicate decided on s may be inserted: nonmembers then contribute 0, while current members contribute their full s-restricted values.

## 3. Concrete supported domains

Define hereditary retractions by

\[
j_e(x):=x,\qquad j_t(p):=s\land p,\qquad
j_{\sigma\tau}(F):=\lambda x^\sigma\,j_\tau(F(j_\sigma x)).
\tag{6}
\]

The e-case is a substitution convention, **not** a term of the forbidden type ee. All other displayed retractions have admitted types. Whenever an argument type is e, the corresponding occurrence of j_e simply erases.

These are idempotent as whole operations. At t this is the Boolean identity s∧(s∧p)=s∧p, also under abstraction. Inductively, β-expansion of j_(στ)(j_(στ)F) gives

\[
\lambda x\,j_\tau\bigl(j_\tau(F(j_\sigma(j_\sigma x)))\bigr).
\]

The already established lower-type whole identities reduce this to j_(στ)F. The same reduction under the outer F-abstraction proves whole-operation idempotence at the new type. All replacements are substitutions of entity identities in terms; there is no appeal to Functionality or to Logical Equivalence under an optional premise.

Set

\[
D_\tau(x):=(j_\tau x=x),
\]

with D_e(x):=(x=x). Each domain is inhabited and is exactly the image of j_τ. If F and x are fixed in their respective types, β and the fixedness identities give F(x)=j_τ(F(x)), so application restricts to these domains. In particular D_t is exactly [0,s]. The predicates D_τ are identity predicates and are decided on s by (4).

In the supported interpretation, use these concrete carriers and restricted application. At t use 0 and s as the endpoints, ordinary meet and join, and relative complement p↦s∧¬p. On fixed arguments equality is

\[
\operatorname{eq}_s(x,y):=s\land(x=y).
\tag{7}
\]

Its admitted unrestricted relation is s∧(j_σx=j_σy). Current truth of (7) is precisely literal equality of the fixed entities, since s is true.

Interpret an abstraction by evaluating its body on projected arguments and retracting its output. Quantifiers for a supported predicate F may be written

\[
\exists_s x\,F(x):=s\land\exists x\,F(j_\sigma x),\qquad
\forall_s x\,F(x):=s\land\forall x\,F(j_\sigma x).
\tag{8}
\]

The image description shows that their current truth is exactly quantification over D_σ. Equation (5) shows that their proposition values are the actual joins and meets in [0,s] of the corresponding fixed-domain range values. Quantifier operations and the displayed logical operations are themselves projected to their appropriate higher domains. β, idempotence and the Boolean identities give exactly the clauses above on fixed arguments.

## 4. Preserving H and the strict Logical Equivalence rule

The retraction interpretation preserves H by ordinary relativization to the images of idempotent maps. The required details matter because C's Logical Equivalence rule applies only to H-theorem equivalences.

Translate every variable occurrence through its j, use (7) for equality, (8) for quantification, and retract abstractions as in §3. For any finite H derivation, let E be the finite conjunction of the whole retraction identities and logical-constant identities needed in its translation. If supported parameters are left unprojected, include their fixedness identities as well. These are all **positive identities**. There is no Vicinity, quantifier-bound lemma, completeness, choice, or other optional material premise in E.

Under E and s the usual H proof translates as follows. Identity and substitution concern actual equality of projected entities. Application stays in the projected domains. β uses j²=j on the argument and output, and η uses the same whole identity at the abstraction's type. Universal instantiation uses the projected instance jx; existential introduction uses that same available term. Generalization and elimination range over all images, precisely as in (8). The propositional rules use the ordinary Boolean clauses on an evaluation where s is true. These checks give induction on the H derivation. Every translated proposition is s-supported under E, so outside s two such matrices are both false.

In particular, if H proves Φ↔Ψ, the preceding translation gives the **old-H theorem**

\[
(E\land\Phi^s)\ \longleftrightarrow\ (E\land\Psi^s).
\tag{9}
\]

Apply old Logical Equivalence to (9), including the required abstraction variables. Each conjunct of E is a true identity in C and hence literally 1 by NI; therefore E=1. Substitution of this entity identity, and the unconditional Boolean identities under abstraction, removes E from the resulting abstraction identity. Retraction preserves that identity. This is precisely Logical Equivalence in the supported interpretation.

This argument does not substitute current semantic coextension for entity identity. Nor does it feed an equivalence proved from Vicinity into Logical Equivalence: only the H theorem (9) enters the rule, and its explicit guard is subsequently removed by identity substitution. Together with the preceding H checks it establishes a concrete interpretation of C.

## 5. The supported interpretation satisfies C5

For each pair of current fixed entities, (4) makes its relative equality either 0 or s. If the entities are distinct, their relative inequality is literally s, so it is relatively necessary: its identity to the relative top s is true and its relative box has value s. Equal pairs have zero inequality antecedent.

Thus every current instance of the ND matrix has relative value s. Equation (5) and its meet dual make the universal closure over the fixed domains literally s as well. Its relative box is consequently s. This proves **boxed all-type ND** in the interpretation, which is C5; it proves more than current unboxed ND there.

No assertion that the original unrelativized structure satisfies C5, ND, BF, or Functionality has been made. The new necessity operator is identity to s within the supported propositional domain, rather than original identity to 1.


Source: OpenAI Codex, prompted by Daniel Kodsi, Vicinity, Relational Choice and propositional completeness imply Actuality, 25 October 2026, §§2–5, unpaginated.

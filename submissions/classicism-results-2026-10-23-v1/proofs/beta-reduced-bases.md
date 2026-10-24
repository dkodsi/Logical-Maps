# Reduced beta bases and their limits

**Scope correction:** The later [beta identity audit](beta-eta.md) supersedes this note's historical H0 assessment. Bacon–Dorr report the H0 result positively; the reduced unary-beta countermodel is narrower. Current Lean coverage is in the [evidence index](../evidence/RESULT-INDEX.md#beta-eta-conversion).

Original mathematical argument, direct source misc; unpaginated.

Beta/eta recovery from saturated beta equivalence and Intensionality
Ordinary independent mathematical audit, 23 October 2026.
Original argument: misc. No Lean derivation or literature-novelty claim.

VERDICT

The proposed basis suffices to recover all beta/eta conversions in the fixed
relational grammar e,t,sigma->tau (tau relational). No separate modal K, T,
Barcan, Choice, Infinity, or actual extensionality principle is needed for this
recovery. This is a simple sufficient basis, not a proved absolutely minimal
or irredundant axiomatization.

INDEPENDENT BASE

Use raw typed lambda terms, capture-avoiding substitution and alpha-renaming,
with ordinary typed predicate logic and equality. Application is congruent
under equality. Quantifier binders have their ordinary introduction and
substitution/elimination rules independently of lambda conversion.

Add theorem-only necessitation and the following LOGICAL axiom schemata:

I_tau: Box(forall ybar, A[ybar] <-> B[ybar]) -> A=B,
       for every relational tau = (types of ybar)->t, including tau=t.

B_sat: ((lambda x.M) a)[ybar] <-> M[a/x][ybar],
       for EVERY relational output type tau of M; ybar fully applies tau
       down to t, and is fresh for the redex and its contractum.

Schemata allow arbitrary well-typed terms and parameters. Open theorems can
be universally generalized. Necessitation applies only after all relevant
universal generalizations, with no undischarged proof hypotheses. The I_tau
instances are part of the chosen logical base, not optional local premises.

RECOVERY

1. Beta identity. Generalize B_sat over ybar, then necessitate. Apply I_tau:
       (lambda x.M) a = M[a/x].
   Empty ybar gives the propositional case. This is one application of
   all-type Intensionality, not iteration of actual extensionality.

2. Eta identity. For F:sigma->tau and x not free in F, instantiate B_sat with
   M=F x and a fresh z. Generalize over z AND the remaining tail ybar, then
   necessitate and apply I_(sigma->tau):
       lambda x.F x = F.
   Do not replace Box(forall z,ybar, ...) by forall z,ybar, Box(...).

3. Theorem-level abstraction congruence. Suppose M=N is a logical theorem,
   with x possibly free. Equality congruence gives agreement after applying
   the tail arguments. The beta identities from step 1 then give, for fresh z,
       ((lambda x.M) z)[ybar] <-> ((lambda x.N) z)[ybar].
   Generalize over z,ybar, necessitate, and apply I_(sigma->tau). Therefore
       lambda x.M = lambda x.N.
   This does not infer abstraction equality from an arbitrary local
   hypothesis M=N containing x.

4. Context closure. Equality substitution handles application contexts;
   step 3 handles abstraction contexts. Induct on the term context, then use
   equality reflexivity/symmetry/transitivity. Every beta/eta-convertible pair
   is provably identical. At formula type, ordinary equality substitution
   consequently transfers derivations from any unchanged optional premises.
   The conversion identity itself was proved without those premises.

WHY THE SCOPE OF B_sat MATTERS

Only proposition-bodied beta equivalence is insufficient, even with every
I_tau. Counterinterpretation: take full extensional typed function domains
over two truth values and nonempty individuals, with Box interpreted as the
identity on truth values. Interpret truth-output abstraction normally, but
interpret every abstraction whose body has non-propositional relational
type as the constant-zero function of its required type. Primitive logical
binders and equality retain their usual interpretations. All I_tau hold,
and truth-output beta holds. Higher-output beta fails, for instance for
(lambda x.F) a with a nonzero relational F; corresponding higher eta fails.
Thus truth-level beta must cover the fully applied HIGHER-OUTPUT redex too.

This counterexample concerns ONLY unary proposition-bodied beta. It is NOT
a counterexample to the tuple beta schema in Bacon-Dorr's H0 (Classicism,
July 2022 draft, p. 7 n. 7), which permits
       (lambda vbar.P)[Abar] <-> P[Abar/vbar]
for arbitrary tuples and truth-valued P. The counterinterpretation fails
that schema when tuples have length at least two. The tuple schema gives
long eta expansion lambda ybar.F[ybar]=F by Gen, Nec and I_tau; the present
audit does not establish whether it alone also recovers arbitrary-body beta
and contextual lambda congruence without further assumptions. The sufficient
basis audited above deliberately uses B_sat, not an asserted identification
of B_sat with H0's tuple schema.

WHY PROPOSITIONAL INTENSIONALITY ALONE IS INSUFFICIENT

Even all beta identities do not force eta from I_t alone. Use truth values
{0,1}, Box=id, and recursively let each function domain consist of pairs
(g,i), where g is a function on the preceding domains and i is 0 or 1.
Application forgets i; lambda abstraction assigns tag 0. Beta identities
hold exactly, and I_t holds. But lambda x.F x has tag 0, and therefore differs
from F when F has tag 1. All-type Intensionality excludes this duplicate
representation. This is a counterinterpretation of the reduced proposed
base, not a claimed model of C with its existing eta rule.

A STILL SMALLER CONVERSION-ONLY PRESENTATION

For recovering conversions one may replace I_tau plus necessitation by the
single theorem-level rule: from a theorem forall ybar(A[ybar]<->B[ybar]),
infer A=B. Together with B_sat and ordinary predicate/equality logic this
repeats all four steps without mentioning Box. This identifies the part of
Intensionality actually used; no equivalence of entire ambient theories or
irredundancy theorem is claimed here.

CURRENT LEAN CODE DOES NOT ESTABLISH THIS ELIMINATION

Classicism/Syntax/Conversion.lean makes Beta.intro and Eta.intro primitive,
then defines their contextual equivalence closure Conv.
Classicism/Syntax/Derivation.lean:213 has the primitive Derivable.conv rule.
Its allE_beta helpers use Conv.beta; its substEq proof at lines 475-502 uses
Conv.eta at the two ends. The shallow layer likewise admits kernel
beta/eta conversion through rfl (Classicism/Equivalence.lean:42).
Classicism/Modal.lean:110-135 proves Intensionality and modalized
functionality inside that already conversion-bearing framework.

An independent Lean certification would need a separate raw-syntax calculus
without those conversion constructors. In particular, it must not reuse
allE_beta, substEq, or a shallow definitional beta/eta step as evidence that
the removed conversions have been derived. No such certification was run
for this audit.

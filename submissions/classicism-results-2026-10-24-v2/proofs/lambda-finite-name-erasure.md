# Conservative elimination of finitely supported names

Original research by OpenAI Codex, prompted by Daniel Kodsi, 23 October 2026; direct source `misc`, cited unpaginated sections. No claim of human verification or literature priority.

1. Exact theorem and fixed calculus

Let C be an arbitrary typed signature. Let L(C;T) be the concrete
lambda-free calculus of ModalComprehensionConcreteCalculus.lean, with
additional global axioms drawn from a set T of CLOSED C-formulas. Such an
axiom can be used in any variable context by weakening its empty context.
The fixed rules include implication and iff logic, equality/application
substitution, genuine quantifier binders with eigenvariable rules, normal
K, necessitation ONLY from an empty list of local hypotheses, all-relational-
type Intensionality INCLUDING type t, and finite-body strong comprehension.
All global axioms remain eligible for necessitation. Local hypotheses are
represented by a separate finite list, never by enlarging T.

Let N be a typed family of fresh names. Each n has a relational type k_n
and an independent closed finite body A_n : Body C [] k_n. In C+N give n
exactly the global defining axiom

  D_n(n) := Box diagram(A_n,n).

Here diagram saturates the relation and universally binds the finite body
spine; it is the existing UniformRepresents formula. The old body is
embedded in the enlarged signature. No object-level distinctness between
different names, choice function, or other axiom is added.

THEOREM. For every finite variable context Gamma, finite list Delta of
C-formulas in Gamma, and C-formula P in Gamma,

  L(C+N; T + {D_n(n) : n in N}); Gamma; Delta |- P
       iff
  L(C;T); Gamma; Delta |- P.

The forward direction is proved below. The reverse direction is the
ordinary typed signature inclusion, by induction on the actual rules.
The theorem also applies to the explicitly stipulated classical base:
replace its open DNE schema and e-existence axiom by their two equivalent
closed axioms, apply this theorem, and translate back. The equivalence is
proved in ModalFiniteClassicalDefinitions.lean by UI, Gen and an actual
global-axiom replacement induction, at arbitrary Gamma and Delta.

2. The fixed named families meet the hypotheses

ModalUniformCombinators.lean defines I, K, S, C and W by finite Body
constructors. Their saturated matrices are, respectively,

  x[ybar];  a[ybar];  (f x)(g x)[ybar];
  (f a)b[ybar];  (f a)a[ybar],

with the displayed input variables bound in the order specified there and
the remaining relational output saturated by Body.ofTerm. More explicitly
C has arguments f,b,a and body (f a)b; W has arguments f,a and body (f a)a.
Their bodies contain no named constants at all. Taking Gamma=[] gives
A_n; taking any other Gamma is exactly its weakening. S requires its
intermediate type to be relational. C and W allow arbitrary input types,
including e and schematic Ty.var indices. No e-returning arrow occurs.
The NamedAxiom instances in RelationalBracketInterpretation.lean are the
weakenings of these closed D_n(n), not extra combinator equations.

Primitive logical-operation names can be treated in precisely the same
way, using the calculus's own operations in their defining matrices:
conjunction(p,q), disjunction(p,q), neg(p), equality_sigma(x,y),
forall x.Fx, and exists x.Fx. In the displayed classical presentation,
negation/conjunction/disjunction are the existing implication/falsity
abbreviations; falsity is the binder formula forall p:t.p. For the seven
type-indexed source operations, use these fully expanded finite matrices:
constant relation p; neg(F[ybar]); conjunction(F[ybar],G[ybar]);
disjunction(F[ybar],G[ybar]); forall ybar.(F[ybar] iff G[ybar]);
Box(F[ybar]); and forall ybar.(F[ybar] implies G[ybar]), respectively.
All inputs, and output-tail variables when present, are bound in the
finite Body. These bodies use primitive binders/connectives, not other
new logical or combinator names. Every named type is relational.

This is an ordinary construction of eligible definitions. It does NOT
assert that the current opaque Atoms in RelationalLambdaCompilation.lean
already carry these definitions: that file deliberately leaves them
opaque. For its current NamedAxiom(Atoms Sig), take all Atoms Sig as the
old signature C and erase only the added combinator names. To erase logical
atoms too, first supply their displayed SC definitions and the required
logical-operation interpretation. Erasure alone supplies no such meanings,
delta laws, or whole-C proof translation.

3. Finite support of an actual derivation

Take a derivation pi of the left-hand sequent. Its inductive proof tree is
finite. Every object term, formula, context list, and admitted finite Body
occurring as a node parameter is finite syntax. Collect the typed new-name
labels occurring in ALL of those objects, at every node. In particular
include all intermediate conclusions and local hypotheses (also hypotheses
introduced by weakening), UI arguments, existential witnesses, equality-
substitution matrices and both substituted terms, every argument to an
equality rule, Intensionality's relations, and every comprehension Body.
Counting only the final sequent or the names of invoked global axioms is
insufficient: a witness or substitution matrix can contain a name that
disappears from a resulting formula.

The union F is finite. All original C-constants are retained, so their
equality need not be decidable and their set need not be finite. New
combinator/logical labels and their finite type indices have decidable
equality, giving a concrete duplicate-free enumeration of F. For the
ordinary theorem only finiteness and an enumeration are needed. Proofs
of membership or of the weakening side condition are not additional
object formulas: their finite lists are included, and their logical
membership claims will be transported below.

Each used definition contributes its own name to F. Its body contributes
no further new name, by independence. Thus adding the definitions of every
name in F introduces no dependency closure. Names occurring merely as
terms, with no cited defining axiom, may also receive their definitions;
the original derivation remains valid in this stronger finite extension.

4. Restricting syntax without a default for unused constants

Define the finite-support signature at type tau as

  C_F(tau) = C(tau) + {n : N(tau) | the typed label n belongs to F}.

It has a total inclusion j into C+N. A term t of C+N whose new-name support
is contained in F has a restriction t|F in C_F: retain variables and old
constants, attach the available membership proof to each new constant,
and recurse through every constructor. Restrict a Body by recursing through
its atom and bind constructors. Membership-proof choices do not change
the resulting mathematical syntax. Inclusion recovers the original term.
There is NO map from unused names into C_F and NO chosen default term.

Structural induction proves the required coherence equations: restriction
commutes with application, equality, primitive logical operations, box,
renaming, weakening, capture-avoiding substitution and instantiation. For
substitution, require support inclusion for both the substituted expression
and every substitution image actually used; in the rules at issue the
finite matrix, witness/argument and identity variables suffice. One need
not assign terms to every unused variable or every unused constant of the
whole infinite signature. Under a binder the new bound variable is kept
and the existing map is lifted, so capture is impossible.

Induction on relational type proves coext restriction. Induction on Body
proves diagram restriction and then

  (Body.code A)|F = Body.code(A|F).

The representative bound by Body.code is a variable, so this step inserts
no new name. These equations are proved from the syntax constructors, not
from an assumed preservation-of-proofs property.

5. Restricting every actual proof rule

Induct on pi, using one common F containing the support of the whole tree.
Restriction keeps Gamma unchanged and restricts Delta entry by entry.

Hypothesis membership and weakening transport along the restriction of
their finite lists. An old global axiom remains the same old axiom; a
named global instance becomes the defining instance of its retained
name, since its closed body is unchanged and restriction commutes with
weakening. Implication introduction/elimination, iff introduction and its
two eliminations, and truth introduction are the same instances after
restriction. Equality reflexivity/symmetry/transitivity, application
congruence, eqRight and eqTruth are preserved immediately. eqSubst is
preserved by the actual matrix/instantiation equation from Section 4.

For allI, the branch hypotheses remain exactly the weakened image of the
concluding hypotheses. For allE and exI, restrict the explicitly included
argument/witness and use the instantiation equation. For exE, the branch
context remains P|F :: weaken(Delta|F), its conclusion remains weaken(q|F),
and the eigenvariable is the same bound variable as before. No new object
or constant is required to serve as that eigenvariable.

For Nec the source premise has local context [], and its restricted
premise still has local context []; apply Nec to it. No premise from a
nonempty local context is promoted to a theorem. K is preserved by box
and implication coherence. Intensionality is preserved by coext
coherence at its unchanged relational type. For comprehension, apply the
actual SC constructor to A|F; the body-code equation gives exactly the
restricted conclusion. This checks all constructors of the concrete
Derives relation, including the proof-syntax parameters most easily
omitted from a support calculation.

Consequently pi restricts to a genuine derivation over C_F with only the
finite family of definitions in F. If the initial classical presentation
uses open DNE instances, restrict their proposition arguments too, then
replace these instances by UI proofs from closed universal DNE. This
retains empty local hypotheses in the axiom replacements and hence in Nec.

6. Identification with a finite DefinitionTower

Enumerate F as n_1,...,n_m with their actual relational types k_1,...,k_m.
Starting at (C,T), repeatedly extend the current signature by FreshConst
at k_i and add representationDefinition of the embedded closed body A_i.
This is an actual DefinitionTower: each A_i is available already over C,
so in particular it is available over every preceding stage. The theorem
would also allow finite acyclic dependent bodies ordered beforehand, but
independence makes that extra analysis unnecessary here.

The final signature is type-preservingly isomorphic to C_F. Send an old
c to its repeated old embedding, and send n_i to the fresh constructor
introduced at stage i followed by later old embeddings. The inverse is
defined by cases on this FINITE iterated signature. These are total
signature maps between the two restricted signatures. They do not extend
to a total interpretation of unused symbols in C+N. The maps send every
definition to exactly its corresponding tower definition. Applying the
same syntax/rule induction transports the finite derivation to the tower.

For a closed old-language conclusion, DefinitionTower.conservative in
ModalFiniteDefinitions.lean now applies literally, over arbitrary old
closed global theory T. Its source proves each naming step by guarded
induction, actual fresh-constant replacement, SC existence and existential
elimination; it is not a field assuming conservativity. Erasing the last
name first keeps all earlier definitions as global Nec-eligible axioms.
After m steps the conclusion is derived in the original theory.

7. Open local sequents: direct erasure works

Closing and reopening is NOT mathematically necessary. Here is the direct
one-name argument at arbitrary Gamma, which then iterates last-to-first.
Write g=D_n(c), a CLOSED boxed definition. Guarded proof induction gives

  old theory in signature C+c; Gamma; g^Gamma,Delta |- P,

and discharging just that guard gives Delta |- g^Gamma -> P. The sole
delicate induction step is Nec. Its original premise has no local
hypotheses. The induction hypothesis gives g^Gamma |- Q; discharge g,
necessitate the resulting theorem g^Gamma -> Q, and use K together with
the theorem g^Gamma -> Box(g^Gamma). The latter follows from modal 4,
already derived in this calculus, because g is boxed. Thus Nec yields
g^Gamma |- Box Q. Old globals are retained; Delta is never necessitated.
The allI/exE steps use that weakening a closed guard equals its lift to
the enlarged context. These are the same guarded-induction cases already
present in concrete_guarded_over.

Replace c by a fresh variable h of type k_n at the FRONT of Gamma, shifting
all old variables and fixing every old constant. The old global axioms
are closed, so they survive unchanged under this replacement. The actual
proof transport preserves the empty context at Nec. The result is

  old theory; k_n::Gamma; weaken(Delta) |- E(h) -> weaken(P),

where E(h) is exactly Body.code of A_n weakened to Gamma. This identity
is the capture-avoiding closed-definition/instantiation calculation used
by replaceFresh_inst_embedOld, now with arbitrary Gamma. SC for that
weakened body supplies old theory; Gamma; [] |- exists h.E(h). Weaken
this theorem to Delta. In its existential-elimination branch, assume E(h)
beside weaken(Delta), apply the displayed implication, and conclude
weaken(P). ExE therefore gives old theory; Gamma; Delta |- P. Its
eigenvariable condition holds exactly: h occurs in neither old Delta nor
old P, whose syntax has merely been shifted. No closed inhabitant of
k_n or of any type in Gamma is needed. No BF, choice or generalization
of a local premise occurs. Repeat for the finite tower.

This proves the stated open-sequent theorem directly. The general-Gamma
guard and fresh-transport lemmas already exist in source, but the current
representation_name_conservative_over and DefinitionTower.conservative
theorem HEADERS restrict their boundary to Gamma=[]. This note's direct
open version is an ordinary generalization, not a claim that those Lean
headers have already been generalized or compiled.

8. Using the existing closed-boundary tower theorem instead

For literal reuse of that theorem, there is a second complete route.
Starting with the extended open sequent, discharge its premises using

  discharge([],P)=P,
  discharge(q::Delta,P)=discharge(Delta,q -> P).

Then use Gen repeatedly to universally bind Gamma, innermost variable
first. This produces a theorem of one CLOSED OLD-LANGUAGE sentence Q.
No optional premise has become a global axiom; each was discharged by
implication introduction. The forward close_sequent source theorem
already works for arbitrary global Ax. Restrict its finite proof, identify
the finite tower, and apply DefinitionTower.conservative to Q with an
empty local list.

To recover the open sequent in L(C;T), successively rename the current
proof into a context with one fresh variable and apply UI at that variable.
Renaming preserves T because every axiom is a weakening of a closed
sentence: renaming one weakening is exactly another weakening. The proof
renaming induction preserves every rule, including SC and empty-context
Nec. After all variables are reopened, reapply Delta in the reverse order
of its discharge by implication elimination and hypothesis weakening.
This is exactly the construction of ModalSequentClosure, extended in the
ordinary argument from the empty theory to closed T. Its currently saved
reopen_theorem is base-scoped; the required closed-T renaming extension is
the explicit elementary argument just given, not an implicit appeal to a
stronger Lean theorem. For ClassicalAxioms use the two closed-axiom
equivalence before and after the argument.

Thus closing/reopening is a convenient way to use the current theorem
signature, not a substantive condition of finite-name conservativity.
The earlier plan's statement that open sequents "must" be closed should
be read as an implementation route, not a mathematical necessity.

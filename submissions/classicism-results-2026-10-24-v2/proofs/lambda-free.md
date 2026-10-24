# Reconstructing Classicism without primitive abstraction

Original mathematical argument, direct source misc; unpaginated.

1. Exact lambda-free base

Use classical many-sorted applicative logic in the fixed relational types:
e and t, and sigma->tau only when tau is not e. Include application, typed
identity, propositional connectives, object quantifier BINDERS, and a modal
operator B:tt, written BOX. Initially there is no lambda binder.

Identity has ordinary typed reflexivity and capture-avoiding Leibniz
replacement in formulas, and its resulting symmetry, transitivity and
application congruence rules, including congruence at the primitive
equality/connective operators and B. Thus equality can be substituted
through an application of B. These assumptions concern the lambda-free
language; they do not assume congruence under a lambda binder.
If BOX is instead a formula connective, its equality congruence must be
stated separately. Normal K alone does not silently supply it.

Use logical generalization and universal instantiation, modal K, and
necessitation of THEOREMS with the usual assumption restriction. Include
Intensionality at each relational type tau=rho_1...rho_k t, including k=0:

  forall X,Y:tau,
    [BOX forall ybar, (X[ybar] IFF Y[ybar])] -> X=Y.             (I_tau)

Assume strong modal comprehension, uniformly for every finite tuple:

  exists R:sigmabar t, BOX forall xbar, (R[xbar] IFF A).        (SC)

R is not free in A. Other free object parameters are allowed and universally
closed in the schema. Types and finite type tuples are metalinguistic
parameters. The schemas are uniform under adding ordinary signature
constants and replacing them by fresh object variables. Reference-theory-
sensitive schemata such as Max are outside the conservativity argument.

All admitted sorts are inhabited as in ordinary many-sorted H. No operation
returning e, object-language type quantifier, choice operator or lambda
context-congruence rule is assumed. For an especially simple presentation
one may include S4 explicitly; Section 3 derives its T and 4 from the stated
equality and nullary Intensionality assumptions.

2. Unrestricted globally necessitable epsilon collapses modality

Suppose an unrestricted binder epsilon p:t.Phi is available, and its witness
axioms are theorems eligible for necessitation. Define

  c(r) := epsilon p:t . ((r AND p=top) OR (NOT r AND p=bottom)).

The predicate is always inhabited, by top when r and bottom when not r.
The witness axiom therefore gives the theorem

  E(r): (r AND c(r)=top) OR (NOT r AND c(r)=bottom).

Generalize r and necessitate, then use boxed universal instantiation, to
obtain BOX E(r). Under r, E(r) gives c(r)=top. NI (Section 3) gives
BOX(c(r)=top). The unconditional logical implication
E(r) AND c(r)=top -> r uses only top!=bottom. Necessitate it and use K to
obtain BOX r. The other case likewise yields NOT r -> BOX NOT r. Thus

  forall r, (r -> BOX r) AND (NOT r -> BOX NOT r).

Already the first half is modal collapse. With nullary Intensionality it
implies the Fregean Axiom and the usual extensional collapse. The chosen
sort is t: restricting unrestricted epsilon to relational output sorts does
not avoid this example. The reconstruction below therefore does not use it.

3. NI, T and persistence are available without lambda

From x=y, equality/application congruence gives (x=x)=(x=y), and then
BOX(x=x)=BOX(x=y). Necessitation of reflexivity gives BOX(x=x), hence
BOX(x=y). This is NI at every admitted type, without binder congruence.

Nullary I and K give BOX p -> p=top: necessitate the logical implication
p -> (p IFF top), apply K and then I_t. Conversely p=top permits substitution
into B, while BOX top is a theorem. Hence the base proves

  BOX p IFF p=top.                                            (BoxId)

T follows because p=top implies p. For 4, BOX p gives p=top; NI gives
BOX(p=top). Necessitate the unconditional theorem p=top -> BOX p and apply
K to obtain BOX BOX p. No optional premise has been necessitated.

Every defining condition D(h)=BOX U(h) is consequently persistent:

  forall h, D(h) -> BOX D(h).                                  (StableD)

4. A closed unique representation captures all parameters at once

Let M:tau depend on x:sigma and free parameters pbar:pibar. The abstraction
is admitted only when tau is relational. Write tau=rhobar t, choose fresh
output variables ybar, and put

  Htype := pibar -> sigma -> tau,
  D_M(H) := BOX forall pbar,x,ybar,
                   (H[pbar,x,ybar] IFF M[ybar]).

SC applied ONCE to (pbar,x,ybar) proves exists H D_M(H). The condition is
closed except for H: every free object parameter has been captured.
Htype is admitted because its final output is t.

If D_M(H) and D_M(J), a necessitated unconditional logical implication,
combined by K with the two boxed premises, gives
BOX forall pbar,x,ybar (H[pbar,x,ybar] IFF J[pbar,x,ybar]).
I_Htype gives H=J. Thus the old theory proves exists-unique H D_M(H),
and Section 3 gives StableD for this condition.

This does not select a function from forall pbar exists-unique R. Uniform
comprehension over the parameters has directly supplied the whole H.

5. Conservative introduction of the closed name

Add a fresh constant c_M:Htype with defining axiom D_M(c_M). This extension
is conservative for OLD-LANGUAGE sentences even though its new axiom may be
necessitated. The following argument establishes the modal point explicitly.

Take a finite extended derivation of an old-language sentence A. Replace
c_M everywhere by a variable h fresh for the entire proof. Inductively
derive in the OLD theory D_M(h)->B(h) for each translated line B(h).

* Old axioms remain instances by signature/parameter uniformity. The new
  defining axiom becomes D_M(h), whose guarded implication is tautological.
* Modus ponens is preserved by propositional logic.
* Generalization is preserved: the guard is closed except for fresh h,
  which is not among the variables generalized in the original proof.
* For necessitation, the induction hypothesis D_M(h)->B(h) is an OLD-theory
  theorem with no open assumptions. Necessitate it. K gives
  BOX D_M(h)->BOX B(h); StableD gives D_M(h)->BOX B(h), as required.
  If only closed sentences may be necessitated, universally close the
  induction hypothesis first and then use boxed universal instantiation.

At the final line h is absent from A. Generalize h and use the old theorem
exists h D_M(h) to conclude A. This proves conservativity. Existence and
StableD suffice for proof elimination; uniqueness makes the definition
canonical and independent of the selected name.

The proof applies to the explicit uniform base of Section 1, not to Max
or an unrestricted epsilon calculus. Successive definitions are handled
one at a time; a finite proof uses finitely many names, which can be
eliminated in reverse introduction order.

6. Definition of abstraction and beta/eta identities

Define lambda x.M as the abbreviation c_M[pbar]. For any admissible
argument a:sigma, boxed universal instantiation of D_M(c_M) yields

  BOX forall ybar, (c_M[pbar,a,ybar] IFF M[a/x][ybar]).

I_tau gives the literal beta identity

  (lambda x.M) a = M[a/x].

The output-tail quantifiers stay INSIDE the box; no BF is used. For tau=t
the tail is empty and I_t applies. Output e remains forbidden by the grammar.

For F:sigma->tau and x not free in F, the definition of lambda x.(F x)
already gives BOX forall x,ybar of its coextension with F. I_(sigma->tau)
therefore gives the literal eta identity lambda x.(F x)=F.

Only a persistently and uniquely determined representation is named.
One can display this as a restricted description binder iota R.D_M(R),
implemented by the closed-H construction. It is not epsilon for arbitrary
predicates. Primitive beta/eta computation is not assumed: the displayed
equations have been proved as identities.

7. Correct scope of abstraction conversion and nested definitions

If M=N is a THEOREM with its displayed variables free, application/equality
reasoning gives M[ybar] IFF N[ybar]. Generalize the relevant arguments
before necessitating. Combine this boxed theorem with the two defining
equations and apply typed Intensionality to obtain lambda x.M=lambda x.N.

This is theorem-level abstraction conversion. It is NOT a rule lifting
arbitrary equalities under optional assumptions into lambda identities.
Persistent guards can justify additional conditional lifts; current
pointwise equality alone must not replace boxed coextension.

Nested abstractions are translated from proper subterms outward. Each
stage uses SC in the preceding conservative signature extension. Earlier
constants do not magically expand into terms of the original lambda-free
language: their removal is by the guarded proof-elimination argument.
Usual fresh-variable and capture-avoiding substitution conventions apply.

For coherence under alpha-renaming, parameter reordering or substitution,
use the boxed defining equations: instantiate the irrelevant or reordered
parameter positions and obtain boxed coextension over precisely the same
remaining bound arguments. Typed Intensionality identifies the resulting
relations. This does not assume syntactic epsilon extensionality or a
primitive lambda congruence rule. In particular, substituting a term for a
free parameter of c_M[pbar] and independently forming the description of
the substituted body produce the same relation by this argument.

8. Uniqueness for pointwise representation

For a separate comparison, consider pointwise representation:

  exists R, forall xbar, BOX(R[xbar] IFF A).                    (WC)

Over C, uniqueness of WC witnesses at unary input type sigma is exactly
BF_sigma. Even uniqueness for A=top suffices: under forall x BOX Fx, F and
the constant-top relation both represent top pointwise. Their identity
gives BOX forall x Fx. Conversely BF yields boxed universal agreement of
any two witnesses; Intensionality then gives their identity.

This is the same local strength as Functionality_(sigma,t), already recorded
via Functionality -> Tractarianism -> BF and BF -> Functionality. The
empty tuple is trivial; finite tuples use the corresponding BF instances.

9. Quantifier binders have closed operator representatives

For each fixed admitted sigma, apply SC to the single variable F:sigma t
and the lambda-FREE formula forall x:sigma, F x. It gives

  exists Q:(sigma t)t, BOX forall F:sigma t,
    (Q F IFF forall x:sigma, F x).                             (D_forall)

The defining condition is closed, persistent by 4, and uniquely specifies Q:
combine two such boxed definitions and apply I_((sigma t)t). Section 5
therefore permits a conservative closed name Q_sigma. Similarly, SC on the
formula exists x:sigma, F x gives a unique persistent closed representative
E_sigma:(sigma t)t of the existential binder. Neither construction uses a
lambda term or assumes that primitive quantification means application to
a lambda abstraction.

Let L=lambda x.A, with any other parameters retained. Its already established
strong defining equation gives BOX forall x (L x IFF A). Logical reasoning
under that box gives both

  BOX [(forall x,L x) IFF (forall x,A)],
  BOX [(exists x,L x) IFF (exists x,A)].

Boxed universal instantiation of D_forall at F=L gives
BOX [Q_sigma L IFF forall x,L x]; the existential definition similarly gives
BOX [E_sigma L IFF exists x,L x]. Combine the corresponding boxed
biconditionals by K and apply I_t. The resulting literal identities are

  Q_sigma (lambda x.A) = (forall x:sigma,A),
  E_sigma (lambda x.A) = (exists x:sigma,A).

All object variables are generalized before any needed necessitation, or
remain within the existing boxes. No BF instance moves a quantifier across
a box. This works also for sigma=e; both newly named operators return t.
It represents the primitive binders by closed operators in the conservative
extension. It does NOT eliminate the binders from the starting language,
SC, the defining axioms or the underlying proof rules. A completely
binder-free presentation would require a separate syntax and proof audit.

10. Equivalence with the fixed Classicism under translation

Let L be exactly the lambda-free theory of Section 1, and let L+ be its
conservative closed naming extension from Sections 4--7 and 9. The fixed
comparison theory is C from topic.yaml and background.md: the smallest
H-theory containing Logical Equivalence, in the relational type grammar.
For a fixed ordinary signature, these presentations have the same theorems
under the translations below. This is an ordinary proof transformation,
not an assertion that their raw syntaxes are literally identical.

From C to L+. Translate application and identity directly, each abstraction
by its closed representation from Section 6, and H's quantifier constants
by Q_sigma and E_sigma from Section 9. Translate a quantified expression
equivalently by the primitive binder; Section 9 proves literal agreement
with its operator-on-abstraction expression. The logical constants retain
their standard interpretations. Nested abstraction is translated from
proper subterms outward; Section 7 supplies substitution coherence.

These interpretations recover H. Its classical logical, quantifier,
identity, instantiation and generalization rules have their stipulated
counterparts in L+. Its beta and eta identities follow from Section 6,
and their contextual instances from application congruence, logical binder
congruence and the theorem-level abstraction conversion of Section 7.
In particular, this recovery does not replace H's quantifier constants by
unexplained binder notation: Section 9 supplies that missing bridge.

Now suppose H proves A IFF A'. Its translated H derivation gives an
unconditional L+ theorem. Generalize the variables zbar to be abstracted
before applying necessitation. The defining equations for the two
abstractions, normal modal reasoning and I_(type(zbar)t) then give

  (lambda zbar.A)^translation = (lambda zbar.A')^translation.

More generally, unconditional material agreement of fully applied
relations yields their identity by this same Gen, Nec and Intensionality
argument. In particular every required Logical Equivalence instance is
proved, with its H-theoremhood side condition respected. Since L+ recovers
H and Logical Equivalence, every C theorem has a translated L+ proof.

The primitive modal operator introduces no additional term-level freedom.
Write J for the reconstructed lambda p.(p=top). Section 3's unconditional
BoxId theorem and beta give B p IFF J p. Generalize p, necessitate and
apply I_tt to obtain the literal operator identity

  B = lambda p.(p=top).

Thus the primitive modal operator can be eliminated even where it occurs
as an argument or other unsaturated term. Agreement merely at the level
of displayed boxed formulas would not by itself have supplied this fact.

From L and L+ to C. Interpret B as C's defined operator
lambda p.(p=top), and interpret the primitive binders by the usual H
quantifier expressions. C proves the stipulated lambda-free logical and
equality rules, K, theorem-only necessitation and all-type Intensionality
(Classicism, draft 16 May 2023, section 1.5, pp. 16--19; also the map's
intensionality-r and modalized-fregean records). It proves SC directly:
for A with displayed tuple xbar, take R=lambda xbar.A. Beta is an
unconditional theorem; generalize xbar, necessitate, and introduce the
existential witness to obtain the stated strong comprehension instance.
All other parameters remain arbitrary. No choice principle is needed.

Each additional closed name c_M is translated by the closed C term
lambda pbar,x,ybar.M[ybar], with earlier names already translated.
Its defining axiom translates to a C theorem by beta, generalization and
necessitation. Likewise Q_sigma translates to lambda F.forall x.F x,
and E_sigma to lambda F.exists x.F x. Hence every L+ proof translates
back into a C proof. The translations back and forth agree on compound
terms by the proved beta/eta, quantifier and modal-operator identities and
substitution coherence. Relational terms can also be compared directly
by their boxed fully applied agreement and typed Intensionality; terms
of type e are unchanged variables or signature constants.

Consequently, if A is a C formula and A* its translation into L+, then

  C proves A  if and only if  L+ proves A*.

For an original lambda-free formula P, L+ proves P if and only if L
proves P by Section 5, so the comparison is with a conservative naming
extension of L, not with an extra comprehension or choice assumption.

Optional premises. Both translations also preserve local deductions:
for a set Gamma of optional formulas, translated term by term,

  Gamma proves_C A  if and only if  Gamma* proves_L+ A*.

Here the underlying modal and Logical Equivalence rules keep their usual
theoremhood restrictions. A necessitation step is translated only when
its premise is independently a theorem of the base theory or its
conservative naming extension; no member of Gamma is thereby necessitated.
The Logical Equivalence step uses the fixed H-theoremhood side condition,
not equivalence derivable from Gamma. The proof translations preserve
these distinctions. This is not a claim that declaring arbitrary optional
premises to be new globally necessitable axioms preserves local strength.

The comparison covers the fixed relational syntax and ordinary uniform
signature constants. It does not identify arbitrary enrichments or
signature- and reference-theory-sensitive Max schemata under a change of
language. Such a transfer needs a separate audit of their side conditions.

Scope of this audit

The conservative-name argument, abstraction and quantifier reconstruction,
and Section 10's equivalence with the fixed C are ordinary metatheoretic
proofs for the explicitly stipulated presentations and translations. No
minimal-axiom theorem, unrestricted-choice conservativity, syntax-level
Lean certificate or equivalence with arbitrary enriched formulations is
claimed. Existing C counterparts support the reverse translation, not
hidden lambda assumptions in the lambda-free base. Repository validation
is separate from proof verification.

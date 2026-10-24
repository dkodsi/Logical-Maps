# Lambda-free reconstruction of Classicism

Original research by OpenAI Codex, prompted by Daniel Kodsi, 23 October 2026; direct source `misc`, cited unpaginated sections. No claim of human verification or literature priority.

1. EXACT CLAIM AND EXACT BASE

Use the paper's fixed types: e and t, and sigma -> rho only when rho is
relational, hence ends in t. All type parameters below are schematic; every
instance has a finite type and a finite derivation. There is no e -> e type.
Let Sigma be any ordinary typed signature. Names need not denote distinct
objects. Purity-sensitive or reference-theory-sensitive additional schemas
are not transported by the theorem below.

Let B(Sigma) be the following lambda-free presentation. Terms have variables,
ordinary constants, application, typed equality, top, propositional formula
constructors, and object universal/existential BINDERS. They also have a
first-class constant b:t->t; write Box p for b(p). There is no lambda-term
constructor or conversion rule. The classical logic and equality rules are
the ordinary ones for this syntax, with existence at e; all local hypotheses
are tracked. Implication, biconditional, top and the binders can be taken as
the concrete primitive constructors in ModalComprehensionConcreteSyntax.
Falsity is forall p:t.p, negation is implication to falsity, and uniform DNE
gives the classical fragment. Relational inhabitation follows from SC.

Add K, theorem-only necessitation, and these two uniform schemata:

  I_rho: Box coext_rho(X,Y) -> X=Y.

Here coext_t(p,q) is p iff q, and
coext_(sigma->rho)(F,G) is forall x:sigma.coext_rho(Fx,Gx).

  SC: exists R:tau_1...tau_n t,
        Box forall x_1...x_n (R[x_1,...,x_n] iff A).

The finite tuple may be empty. A is admitted lambda-free syntax, R is not
free in A, and other free parameters are permitted. Schemata are uniform
under ordinary constant extension and replacement of constants by fresh
variables. Equality permits Leibniz substitution into admitted formulas and
application congruence, in particular through b. All schematic logical
axioms are global, while optional premises remain local. No choice axiom,
Barcan axiom, primitive lambda congruence, or unrestricted description binder
is included.

Let C(Sigma) be the repository's fixed Classicism, in its actual elimination
presentation: classical higher-order logic with beta/eta/delta conversion
and the contextual Subst rule whose equivalence premises are derivations in
the logical theory alone. In particular, optional local premises cannot
enter those equivalence premises.

Define j from B terms to C terms by the evident applicative/logical
translation, translating primitive binders by quantifier-on-abstraction and
translating the constant b to lambda p.(p=top_C).

THEOREM. For every finite old B-context Delta and old B-formula p, with any
free object variables,

  Delta |- B p    iff    j(Delta) |- C j(p).

Moreover every C term admits a lambda-free translation in a conservative
extension of B by explicitly defined relational constants. This translation
preserves all beta/eta/delta conversions as literal object identities and
preserves C's full derivation rules. The two translations round-trip up to
provable object identity. Thus B supplies a conservative presentation of C
after adding the reconstructed notation for abstraction and logical objects.
This does not assert literal equality of the two raw syntaxes.

The proof below identifies the finite named extension and every delicate
rule. The companion logical-operator and name-erasure proofs supply their
expanded construction details. Compiler acceptance of the implementing Lean
files remains a separate matter.

2. FOUR BASIC LEMMAS INSIDE B

(a) Necessity of identity. From a=b, equality substitution gives
(a=a)=(a=b), hence b(a=a)=b(a=b) by application congruence. Necessitation of
reflexivity supplies b(a=a). Substitution gives Box(a=b). This is a proof
under the displayed equality hypothesis, not necessitation of that hypothesis.

(b) Box p iff p=top. Necessitate the logical theorem p -> (p iff top),
use K under Box p, and apply I_t. Conversely substitute p=top through b
and use the theorem Box top. Consequently T holds. To derive 4, use
Box p -> p=top, (a), and the necessitation of the unconditional implication
(p=top) -> Box p. Thus every defining condition D(h)=Box U(h) is stable:

  |- D(h) -> Box D(h).

(c) Theorem equivalence gives theorem identity. If P|-Q and Q|-P, with
no additional local hypotheses, discharge P and Q and obtain |- P iff Q.
Necessitate and apply I_t. The same observation upgrades every unconditional
classical equivalence between alternative definitions to literal identity.

(d) Theorem zeta. If |- Fx=Gx, where x is a fresh variable, ordinary
equality gives theorem coext_rho(Fx,Gx). Generalize x, then necessitate,
then apply I_(sigma->rho). This proves |- F=G. There is no corresponding
rule from a merely local hypothesis Fx=Gx. This restriction is retained
every time zeta is used below.

The ordinary quantifier rules also give theorem binder congruence: from
|- P=Q in the context containing x, derive the universal and existential
equivalences, then use (c) to identify forall x.P with forall x.Q, and
exists x.P with exists x.Q. No quantifier is moved across a modal box.

3. ONE UNIFORM DEFINITION GIVES LITERAL APPLICATION LAWS

Suppose M is an admitted term of relational type rho, in variables ubar.
Saturate rho by a fresh output tuple ybar and use SC on the single formula
M[ybar]. This gives a representative H of type type(ubar)->rho satisfying

  D(H) := Box forall ubar,ybar (H[ubar,ybar] iff M[ybar]).

All the displayed variables are bound, so D is closed apart from H when
M has no other free parameters. For any admitted argument tuple abar,
boxed universal instantiation gives

  Box coext_rho(H[abar], M[abar/ubar]).

Here boxed UI is derived by necessitating the ordinary UI theorem and using
K. I_rho gives the literal identity

  H[abar] = M[abar/ubar].

No Barcan principle or function selecting pointwise witnesses is used.
The same argument covers a formula-valued body containing primitive binders.
SC proves existence of H, and section 2(b) proves stability of D(H).
Two representatives satisfy boxed coextension and hence are identical by I.

4. A FIXED TYPED APPLICATIVE BASIS

Introduce, when needed, names with the following closed defining bodies:

  I_rho x = x
  K_(sigma,rho) a x = a
  S_(sigma,nu,rho) f g x = (f x)(g x),     nu relational
  C_(sigma,tau,rho) f a x = (f x)a,        sigma,tau arbitrary
  W_(sigma,rho) f x = (f x)x.

Application in these displayed equations is explicitly left-grouped.
Their types and boxed definitions are given in relational-bracket-abstraction.txt
and ModalUniformCombinators. Every output type is relational. Each defining
body uses variables and application only; it contains no other new name.
Section 3 derives each equation from its own SC definition.

For an applicative body M:rho with distinguished variable x:sigma, define
[x]M structurally: x goes to I; another variable or constant goes to K M;
an application f a with relational a goes to S([x]f)([x]a). A term of
nonrelational type can only be a variable or constant. For an application
with such an argument use W([x]f) when a=x, and C([x]f)a otherwise, removing
the unused x from the latter argument. This construction never needs e->e.

Induction on M gives ([x]M)a = M[a/x], using exactly the five equations and
application congruence. Renaming commutes literally with the algorithm.
In particular ([x]M)x=M in the fresh-x context. Section 2(d) therefore gives
abstraction congruence for equality THEOREMS of bodies, and eta:

  |- M=N  implies  |- [x]M=[x]N;
  |- x (`Fx`)=F when x is absent from F.

Substitution does not in general commute literally with the algorithm.
Let s substitute terms for its old free variables, and let s+ fix x. Both
(x (`M s+`))x and (([x]M)s)x have theorem identity with M s+: the first by
fresh-argument beta, the second by substituting s+ into that beta theorem.
The five-law equality calculus is substitution-closed by direct induction
on its constructors. Apply theorem zeta to obtain

  |- x (`M s+`) = ([x]M)s.

This is object identity and is the exact coherence needed by the compiler.

5. LOGICAL OBJECTS AND THE TERM COMPILER

Give the six primitive C logical-object families their own independent SC
definitions: and, or, not, forall_sigma, exists_sigma, equality_sigma.
Their defining bodies are the corresponding B formula constructors or
classical definitions. For example:

  D(Q_sigma) = Box forall F:sigma->t
                     (Q_sigma F iff forall x:sigma.Fx).
  D(Eq_sigma) = Box forall x,y:sigma
                     ((Eq_sigma x)y iff x=y).

All are closed definitions of relational objects, including when sigma=e.
Section 3 gives literal application identities for every admitted argument.
The seven type-indexed operation families are independently represented by
their fully applied pointwise formulas. Coextension and inclusion bind the
output tuple; constant/negation/and/or/box return the pointwise relation.
These bodies use primitive B syntax, not the newly named logical objects.
Their exact definitions and delta proof are in the companion
logical-operator-reconstruction-proof.txt.

Define k on all C terms: preserve variables and ordinary signature constants,
translate each logical object to its fixed name, preserve application, and
translate lambda x.M as [x]k(M). This is an actual structural compiler,
independent of any proof or choice of a witness for a particular lambda.

Term induction, section 4, and the defining application laws give:
  - literal renaming compatibility;
  - substitution compatibility up to theorem object identity;
  - literal object identities for beta and eta;
  - object identities for every delta generator.

In particular, the substitution induction does not presume the claim at
an abstraction. Given a source substitution s, write ks for its componentwise
translation. The induction hypothesis for its body is the THEOREM

  k(M[s+]) = k(M)[(ks)+].

Apply theorem abstraction congruence to this identity. Then section 4's
bracket/substitution identity identifies the right-hand abstraction with
([x]k(M))[ks]. These are exactly the two translations required in the lambda
case. Variable, constant and application cases use reflexivity/congruence.
Combining this result with bracket beta gives the translated source beta
identity for EVERY admitted argument, including one that contains lambdas.
For source eta, use literal renaming coherence before bracket eta. Thus
the proof handles capture and substitution of complex terms explicitly.

For delta, unfold the finite type once on each side, apply the literal
operator laws to fresh arguments, use the lower-type identity where needed,
and apply theorem zeta to those arguments in reverse order. The proposition-
valued coext/inclusion cases also use theorem binder congruence. This is
induction on a finite relational type, not an appeal to extensionality under
local hypotheses. Application and theorem abstraction congruence then lift
each conversion generator to any term position. Symmetry/transitivity give
the full beta/eta/delta conversion relation as theorem object identities.

6. TRANSPORT OF EVERY C DERIVATION RULE

Work in B with the explicit global defining axioms D. Statements in this
section are under D, and only D and the logical base may enter theoremhood.
For every C derivation Delta|-p, prove k(Delta)|-k(p) by induction on its
actual derivation tree. Term-identity and logical-object lemmas used here
have no local premises.

Hypothesis/weakening: application of k to the same list preserves membership
and weakening. The only C logical axiom, existence at e, translates by the
quantifier/equality laws to B's explicit existence theorem. No proper
optional axiom is added to the global necessitable theory.

Propositional rules: replace applications of the named and/or/not objects
by their defining formula values, use the classical B rule, then replace
back. These are equality substitutions, so the current local premises are
preserved. This covers conjunction introduction/elimination, disjunction
introduction/cases, negation introduction/explosion, and excluded middle.

Universal elimination: k(forall_sigma F) is Q_sigma k(F), literally equal
to forall x.k(F)x. Instantiate at k(a) to get k(F)k(a). F need not be a
syntactic abstraction. Existential introduction is the corresponding
argument with the named existential operator.

Universal introduction: by the induction hypothesis derive k(M) with a
fresh x and weakened k(Delta). Generalize to forall x.k(M). The theorem
beta identity k(lambda x.M)x=k(M), binder congruence, and the Q application
law identify this conclusion with k(forall x.M). Renaming coherence keeps
the hypotheses precisely the required weakened list. None of them is
necessitated.

Existential elimination: its translated major premise is equivalent by the
E law to exists x.k(F)x. Its minor proof has hypotheses k(F)x and weakened
k(Delta), and concludes the weakened k(r). Thus the actual B existential-
elimination rule applies, with the original freshness condition preserved.

Reflexivity/Leibniz: the equality-object law identifies the translated
identity formula with primitive B identity. Reflexivity is immediate.
For Leibniz, apply ordinary B equality substitution to the admitted formula
k(F)x. Its instance at k(a) or k(b) is the translated application required.

Conversion: every conversion identity was proved with no local premises in
section 5. Substitute that identity into the already translated derivation
of the formula. This permits arbitrary current Delta but does not use it
to prove the conversion identity.

Contextual Subst: this is the important remaining case. The source rule has
P|-Q and Q|-P in its logical subtheory, and Delta|-H[P], where H is a
one-hole term context that may pass under binders. The first two derivations
are proper subtrees, so induction translates them to

  k(P) |- k(Q),     k(Q) |- k(P)

under D and the B logical base alone. Discharge the single premises,
necessitate the resulting theorem biconditional, and apply I_t to obtain
the THEOREM k(P)=k(Q). The main Delta is absent from this derivation.

Induct on H to prove the theorem k(H[P])=k(H[Q]). At the hole use this
identity. At either application position use equality congruence. At a
lambda layer apply section 4's theorem abstraction congruence. P and Q may
mention variables bound above the hole: the relevant identity is then a
theorem in that larger variable context, and zeta generalizes the variable
when leaving its binder. There are still no local formula premises.
Finally equality substitution transfers the translated main derivation
from k(H[P]) to k(H[Q]). This exactly respects the source rule's restriction.

These exhaust the actual Derivable constructors in Syntax/Derivation.lean.
Thus C proofs, not merely its separate axiom statements or conversion
terms, have been transported.

7. THE OTHER DIRECTION DOES NOT ASSUME THIS RECONSTRUCTION

The map j is sound for B directly inside C. Its classical/equality rules
are the ordinary C rules; its source primitive binders are quantified lambda
expressions in the target, where lambda is already allowed.

Theorem equivalence in C gives proposition identity by Subst in the hole
p=hole. Hence if C proves p, it proves p=top_C, establishing necessitation.
K follows by equality substitution: under p=top_C and (p->q)=top_C,
the theorem (top_C->q)=q identifies q with top_C.

Here is also a direct C derivation of theorem abstraction congruence, used
in this direction without importing I from B. If |- M=N at relational
output rho, fully apply both terms to a fresh output tuple ybar. Equality
substitution gives M[ybar] iff N[ybar] as a THEOREM. Their two one-premise
derivations therefore license source Subst under the context

  (lambda x,ybar.M[ybar]) = (lambda x,ybar.HOLE),

starting from reflexivity. Eta-convert the output tuple on both sides.
This yields (lambda x.M)=(lambda x.N). Repeating the same construction
with no outer x gives theorem zeta from |- Fx=Gx: abstract fresh x and
eta-convert. Every Subst equivalence premise is in C's logical theory;
no local hypothesis or named global definition is used in that step.

For all-type I, put r=coext_rho(a,b). Let mask_rho(r,a) be the pointwise
intersection of the proposition r with a, written in C with lambdas.
There are unconditional C theorems

  mask_rho(r,a)=mask_rho(r,b),
  mask_rho(top_C,a)=a,   mask_rho(top_C,b)=b.

For the first, apply a and b to the full fresh output tuple ybar. Universal
instantiation of r gives a[ybar] iff b[ybar], so r and a[ybar] and
r and b[ybar] are interderivable without further hypotheses. Apply
Logical Equivalence to these two propositions and the just-proved theorem
abstraction congruence successively to ybar. The resulting identity is
the displayed mask identity at the whole relational type. The second and
third identities use (top and a[ybar]) iff a[ybar] and eta in the same way.
Under Box r, r=top_C. Ordinary equality substitution into the mask expression
therefore gives a=b. Crucially the abstraction equalities were theorems
before the local r=top_C was used. This proves I without assuming local
pointwise extensionality.

For an SC instance, the target C term lambda xbar.j(A) is a witness.
Beta, logical generalization, theorem necessitation and existential
introduction prove its exact boxed defining condition. Other parameters
remain arbitrary. This also proves C soundness for every later independent
name definition, by mapping the name to that closed target lambda witness.
Call this extension j+.

Thus every B+D derivation translates into a C derivation independently of
the reverse proof in section 6. The explicit Lean forward files implement
this direction. Their final acceptance is recorded separately in
lambda-free-reconstruction-final-acceptance.json.

8. ROUND TRIPS, INCLUDING UNSATURATED b

For each B term M, prove the theorem k(j(M))=M in B+D. Variables, original
constants and application follow directly or by congruence. The top,
implication and biconditional cases use the logical-object laws and the
unconditional classical equivalences between the chosen presentations;
section 2(c) makes those identities. The equality case uses Eq's law.

For a primitive binder, k(j(forall x.P)) is Q_sigma([x]k(j(P))). Its Q law
identifies this with forall x.([x]k(j(P)))x. Fresh-argument beta and the
induction hypothesis identify the body with P. Theorem binder congruence
gives the desired identity. The existential case is the same with E.

The constant b itself needs an operator identity, since it may appear as an
argument without being applied. Its round trip is p (`p=top`), up to the
already proved logical-operation and top identities. Beta gives its value
p=top at a fresh p. Section 2(b) says b(p) iff p=top as a B theorem; section
2(c) upgrades this to b(p)=(p=top). Theorem zeta gives the operator identity

  b = p (`p=top`).

Hence the induction covers b in every term position, not just boxed formulas.

Conversely, j+(k(M))=M is a C theorem for every C term. At logical constants
use their explicit lambda witnesses and the same logical-operation laws;
at variables/original constants/application the induction is immediate.
At lambda x.N, transported fresh-argument beta and the induction hypothesis
give equality of applications to fresh x; C theorem zeta gives equality of
the abstracted terms. Type-indexed logical constants follow by the same
finite-type induction as their delta laws. These are object identities,
not a claimed normalization algorithm.

9. FINITENESS AND CONSERVATIVE ERASURE

Any completed translated derivation mentions finitely many names. Include
constants in every intermediate formula, hypothesis, quantifier witness,
Leibniz matrix, comprehension body and auxiliary derivation. Each defining
body uses no other new names, so the finite set requires no further name
dependencies. Restrict the proof to that actual finite signature; this is
structural restriction of the same finite derivation, not a total map
assigning nonexistent old closed terms to unused symbols.

Each retained name c:rho has a defining axiom D(c)=Box U(c), where the old
theory proves exists h.D(h) by SC and D(h)->Box D(h) by 4. It can be erased
from an OLD-LANGUAGE local sequent Delta|-p as follows. Replace c by a
fresh variable h throughout the finite proof. Guard every line with D(h).
All ordinary rules preserve this guard, as do old uniform axioms. For Nec,
the original premise has no local hypotheses; the induction gives
D(h)|-q. Discharge D(h), necessitate D(h)->q, then use K and stability to
derive D(h)|-Box q. Thus no local member of Delta has been necessitated.

At the end obtain D(h),Delta|-p, with h absent from Delta and p. Apply
existential elimination to the old theorem exists h.D(h). This yields
Delta|-p in the old theory. Freshness also preserves every eigenvariable
condition. The argument applies relative to the remaining old global
definitions, so erase the finite names one at a time. It works directly
for open sequents; closing all free parameters is an optional formalization
route rather than an additional mathematical assumption.

See finite-name-erasure-proof.txt for the complete rule audit. Implementation
status updated 23 October 2026: the Lean finite tower and finite-support
restriction bridge, together with the complete dependency chain and final
equivalence, passed in run 20261023T220419627357Z-81c98662. The separate
acceptance receipt supplies the machine evidence; this text supplies the
ordinary mathematical argument.

10. CONCLUSION OF THE THEOREM AND ITS LIMITS

If Delta|-B p, section 7 gives j(Delta)|-C j(p).
If j(Delta)|-C j(p), section 6 gives k(j(Delta))|-B+D k(j(p)).
Use section 8's theorem identities to obtain Delta|-B+D p. This is an
old B-language boundary sequent. Section 9 erases its finitely many names,
giving Delta|-B p. This proves the claimed exact equivalence.

For arbitrary C terms/formulas, sections 5--8 give the conservative named
presentation and the two round trips. Every contextual beta/eta/delta
conversion is an actual identity theorem in that presentation. Primitive
lambda syntax and its conversion rules are therefore recoverable rather
than assumptions of B.

No minimal-axiom theorem is claimed. The quantified binders are retained in
the starting base; this is lambda-free, not wholly binder-free. Neither
Choice, Infinity, BF, nor optional local premises have entered the base.
There is no claim that Maximalism or other language-sensitive schemata
survive this change of presentation without a separate side-condition audit.
The theorem establishes mathematical proof transformations. The full Lean
implementation and both final leaves are accepted, with exact current-source
evidence in lambda-free-reconstruction-final-acceptance.json.

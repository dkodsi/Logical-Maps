# Reconstructing logical operators and their identities

Original research by OpenAI Codex, prompted by Daniel Kodsi, 23 October 2026; direct source `misc`, cited unpaginated sections. No claim of human verification or literature priority.

1. The exact proof tools

For a relational type rho = sigma1->...->sigman->t, write zbar_rho for a
fresh tuple z1:sigma1,...,zn:sigman, and X[zbar] for full application in
that order. At rho=t the tuple is empty and X[zbar]=X. Every displayed
coextension below is the literal recursive source formula

  X equiv_rho Y := forall zbar_rho (X[zbar] <-> Y[zbar]).

The following are derived in the stipulated base; none is a new axiom of
this note.

(a) T, 4, necessity of identity, and BoxId:

  Bp -> p;  Bp -> B(Bp);  a=b -> B(a=b);
  Bp <-> (p=top).

The representation-core derivations establish these using only the stated
lambda-free rules. In particular BoxId is available before reconstruction
of a lambda term for B.

(b) Boxed universal instantiation. From B(forall x A) infer B(A[a/x]).
Proof: ordinary UI proves (forall x A)->A[a/x] with no local hypotheses.
Necessitate that theorem, then apply K. Iterate for a finite tuple. This
never changes forall x B A into B forall x A; no BF is being used.

(c) Theorem agreement gives identity. If L_F proves M equiv_rho N with no
local hypotheses, apply Nec and I_rho to obtain M=N. In particular a
THEOREM P<->Q gives P=Q by Nec and I_t. For an identity between operators,
first prove their fully applied agreement, GENERALIZE EVERY ARGUMENT of
their entire relational type, then apply Nec and Intensionality. This is
theorem-level comparison, not pointwise extensionality under assumptions.

(d) A boxed SC definition yields literal terminal application laws. Suppose

  D_O := B forall ubar,zbar (O[ubar,zbar] <-> Phi(ubar,zbar)).

Boxed UI specializes the input and output arguments; I_t gives
O[abar,bbar]=Phi(abar,bbar). If Phi is the full application of an existing
relation-valued term M(ubar), keep the OUTPUT tuple quantified, specialize
only ubar, and apply I_rho. This gives O[abar]=M(abar) at relational output
rho. Retaining the tuple inside the original box is essential.

(e) Primitive quantifier congruence is ordinary logic. From the theorem
forall x (P(x)<->Q(x)), ordinary Gen/UI and existential rules prove both

  (forall x P(x)) <-> (forall x Q(x)),
  (exists x P(x)) <-> (exists x Q(x)).

These are theorem-level biconditionals and hence identities by (c).
Alternatively necessitate the ordinary conditional congruence theorem
and use K with an already boxed universal agreement. Both routes preserve
the quantifiers inside the relevant box and require no BF.

Nec in these arguments acts only on theorems of L_F. The closed defining
axioms are GLOBAL axioms of this explicitly specified naming extension,
not arbitrary optional premises. Their conservativity is justified below.
If one wants all necessitation premises to be closed sentences, first
generalize the remaining free parameters, necessitate, and use boxed UI
back at those parameters. No step requires necessitating local premises.

2. Closed, independent SC definitions of all logical constants

Use only the following lambda-free abbreviations:

  0 := forall r:t.r;
  n(p) := p -> 0;
  a(p,q) := n(p -> n(q));
  v(p,q) := n(p) -> q.

Here 0 is a formula, not an additional constant symbol. UI from 0 gives
any formula. In classical L, n,a,v have the usual negation, conjunction,
and disjunction rules. For example a(p,q) is the negation of p->n(q):
from p and q its introduction follows immediately; from a(p,q), an
assumption n(p) makes p->n(q) derivable by ex-falso, yielding n(n(p)),
then p by DNE. An assumption n(q) similarly makes p->n(q) derivable,
yielding q by DNE. Thus no primitive conjunction is assumed here.

For each entry in the following list introduce ONE new typed name O with
the displayed closed boxed definition. All listed variables are bound by
the displayed outer universal quantifiers; tail tuples are expanded as
actual finite binder spines. Bound variables inside a matrix are fresh.

Propositional and ordinary typed logical operators:

  N:t->t
    D_N := B forall p (N p <-> n(p)).

  A:t->t->t
    D_A := B forall p,q (A p q <-> a(p,q)).

  V:t->t->t
    D_V := B forall p,q (V p q <-> v(p,q)).

  Q_sigma:(sigma->t)->t
    D_Q := B forall F (Q_sigma F <-> forall x:sigma (F x)).

  E_sigma:(sigma->t)->t
    D_E := B forall F (E_sigma F <-> exists x:sigma (F x)).

  J_sigma:sigma->sigma->t
    D_J := B forall x,y (J_sigma x y <-> x=y).

The seven relational operators, for rho with output tuple zbar_rho:

  U_rho:t->rho                         [constR]
    D_U := B forall p,zbar (U_rho p[zbar] <-> p).

  N_rho:rho->rho                       [negR]
    D_NR := B forall X,zbar (N_rho X[zbar] <-> n(X[zbar])).

  A_rho:rho->rho->rho                  [andR]
    D_AR := B forall X,Y,zbar
      (A_rho X Y[zbar] <-> a(X[zbar],Y[zbar])).

  V_rho:rho->rho->rho                  [orR]
    D_VR := B forall X,Y,zbar
      (V_rho X Y[zbar] <-> v(X[zbar],Y[zbar])).

  H_rho:rho->rho->t                    [coextR]
    D_H := B forall X,Y
      (H_rho X Y <-> forall zbar (X[zbar] <-> Y[zbar])).

  Z_rho:rho->rho                       [boxR]
    D_Z := B forall X,zbar (Z_rho X[zbar] <-> (X[zbar]=top)).

  L_rho:rho->rho->t                    [inclR]
    D_L := B forall X,Y
      (L_rho X Y <-> forall zbar (X[zbar] -> Y[zbar])).

In this list expression O X Y[zbar] means ((O X) Y) followed by the whole
output tuple; it does not mean O X (Y[zbar]). At rho=t, each tail tuple is
empty, so the same definitions apply without a special nullary premise.

Every right-hand matrix uses ONLY original L primitives, variables and
application. There is no occurrence of ANY of the newly named operators,
including lower-type names. For instance H_(sigma->rho) is defined using
forall z,zbar directly, not using H_rho. Z uses original typed equality
and top, not another new box operator. Thus these are independent closed
SC definitions, not circular or recursively dependent existence claims.
Their types all end in t. Q_sigma, E_sigma and J_sigma are admissible also
when sigma=e or Ty.var(i); no sigma->sigma map is required.

Existence: apply the actual finite-body SC schema to the matrix in each
row and its listed outer variables. The result is exists O D_O.
Uniqueness: two witnesses have boxed coextension at the whole type of O;
normal boxed reasoning combines their definitions and typed I identifies
them. Stability: D_O is already a box, so 4 gives D_O -> B D_O.
The established conservative stable-naming argument therefore permits
each closed name. Only a finite set is needed for any specified finite
term/proof; no simultaneous global selection of representatives is used.

By 1(d), every row immediately gives its LITERAL terminal application
identity. In particular:

  N p = n(p), A p q = a(p,q), V p q = v(p,q);
  Q_sigma F = (forall x F x), E_sigma F = (exists x F x);
  J_sigma x y = (x=y);
  H_rho X Y = (forall zbar (X[zbar]<->Y[zbar]));
  L_rho X Y = (forall zbar (X[zbar]->Y[zbar]));
  Z_rho X[zbar] = (X[zbar]=top).

The last identity also agrees with B(X[zbar]): BoxId is a THEOREM, so
1(c) gives Bp=(p=top), not just a material biconditional. No unsaturated
operator identity is inferred directly from current pointwise agreement.

3. The fixed bracket compiler is sound in this extension

Use the typed I/K/S/C/W basis and the exact structural algorithm in
relational-bracket-abstraction.txt and RelationalBracketAbstraction.lean.
For clarity, I is indexed only by a relational type; S's intermediate
type is relational; C and W allow arbitrary input types. Their independent
SC bodies are, respectively, the full terminal saturations of

  I x = x;
  K u x = u;
  S f g x = f x (g x);
  C f u x = f x u;
  W f x = f x x.

For example the S definition is a single box over all f,g,x AND the full
output tuple ybar of its relational result: its matrix compares
S f g x[ybar] with (f x (g x))[ybar]. There is no previous combinator in
that matrix. Section 1(d), retaining ybar inside the box, gives the stated
relation-valued application equality. The other four cases are identical
instances of that argument. Their existence and conservative naming are
therefore the same actual SC/stability construction as in Section 2.

Interpret the independent applicative syntax homomorphically in L_F:
variables and old constants keep their meanings, basis constants become
these fixed names, and application stays application. Induction on the
generated Equal proof relation gives a literal source identity: refl,
symm, trans and app use ordinary object equality rules, and its five
special law constructors use the just-derived SC application identities.
This is an explicit constructor-by-constructor argument, not an assumed
arbitrary proof-preservation interface or an extensional semantic model.

Consequently structural bracket abstraction has the object beta law

  ([x]M) b = M[b/x]                                        (beta-bracket)

for every applicative M of relational output and admitted argument b.
The ordinary proof is the actual structural induction: I for x, K for
an independent atom, S for application at relational intermediate type,
and W/C for a nonrelational argument that is respectively x or an
independent variable/constant. Those are all nonrelational cases, since
application cannot produce e or Ty.var(i). The argument also allows
substituting arbitrary admitted source terms for remaining variables:
each of the five source laws holds at those terms, and ordinary
application congruence carries the same induction through.

This does not claim literal syntax commutation of bracket with arbitrary
substitutions. Such substitutions can turn an atom into an application.
The required beta-bracket law is a theorem of OBJECT identity, which is
all the uses below need. Eta and general abstraction coherence are not
axioms of this equational fragment; later uses must derive them via
theorem-level Gen/Nec/Intensionality in L_F.

There is one elementary SYNTAX coherence fact needed when the argument
is the fresh bound variable itself. For an outer-variable renaming r,
bracket commutes literally with its lift:

  x (`rename(lift r,M`)) = rename(r,[x]M).

Proof by the same structural cases: lift r preserves the zero variable,
maps every older variable succ(v) to succ(r(v)), and fixes constants.
Consequently the I/K branch and the S/C/W branch selection are preserved;
application and the fixed typed constants commute with renaming, and the
recursive assertions finish each application case. In particular no
renaming can turn an older variable into the newly abstracted variable.
This fact is specific to RENAMING and does not assert the false analogous
syntax identity for arbitrary term substitution.

Take r to insert a fresh variable of type sigma in the outer context.
Apply beta-bracket to rename(lift r,M) at that fresh variable. The left
side is ([x]M) weakened into the new context, applied to its zero variable;
the right side is M itself. The latter syntax equation is checked on
variables (zero returns zero; succ(v) returns succ(v)), constants and
application. Thus the fresh-variable beta law used below is justified:

  ([x]M)^weaken x = M.

Define tr on Cterm: preserve variables, old typed constants and
application; map the thirteen families of logical constant constructors
to Section 2's corresponding names; map lambda x.M to [x]tr(M).
Translate inner lambdas first. The result is an applicative source term,
so every bracket call is within its actual syntactic domain.

4. Two elementary bridges needed by delta and the round trip

Propositional normalization. For arbitrary source propositions p,q,
the literal application laws and classical L prove these THEOREMS:

  V (N p) q = (p -> q);                                  (Imp)
  A (V (N p) q) (V (N q) p) = (p <-> q);                 (Iff)
  V p (N p) = top.                                      (Top)

Here is the identity justification, to exclude a hidden Fregean step.
The left side of Imp has the literal normal form n(n(p))->q. That is
materially equivalent to p->q: one direction uses p->n(n(p)), the other
uses DNE. Discharge all proof assumptions to obtain the theorem of
biconditional, then Nec and I_t give its identity. Iff follows similarly
from the derived conjunction rules and primitive iff introduction and
elimination. For Top, V p (N p) has normal form n(p)->n(p), which is a
theorem; top is also a theorem. Their biconditional is therefore a
theorem, and again Nec/I_t yields literal identity. No premise about the
truth value of the arbitrary p or q has been retained or necessitated.

Binder application. If M:t is an applicative expression with variable
x:sigma, put F=[x]M. Then

  Q_sigma F = (forall x M),
  E_sigma F = (exists x M).                              (Quant)

Proof: beta-bracket at the fresh variable gives F x=M as a theorem with
x free. Equality gives material equivalence, and Gen gives
forall x(F x<->M). Ordinary universal/existential congruence gives
(forall x F x)<->(forall x M) and its existential counterpart. Combine
with the literal Q/E application laws. These biconditionals are theorems,
so Nec/I_t give the displayed identities. Equivalently the entire
argument can be performed inside the box using 1(b) and 1(e).

The lemma invokes bracket only on APPLICATIVE M. It does not pretend that
the bracket algorithm accepts a formula with primitive binder nodes.
In the applications below M is always a translated Cterm and hence
applicative. Its comparison with a primitive source binder is precisely
what the resulting identity establishes.

5. Compatibility with every actual Term.unfoldR equation

Claim: if Term.unfoldR(O_rho)=some U in the actual C syntax, then

  L_F proves tr(O_rho) = tr(U)                           (Delta)

at the WHOLE operator type, including partial applications. A finite F
contains the names and combinators used on both sides. To prove the
claim, fully apply both sides to fresh variables, use beta-bracket and
the stated application laws, and compare their terminal matrices.
GENERALIZE ALL arguments, then Nec/I at the whole operator type. The
following checks give the exact matrices for every case.

constR:
  At t the unfolding is lambda p.p; both sides applied to p give p.
  At sigma->rho it is lambda p,z.constR_rho p. After further application
  to ybar_rho, beta-bracket and D_U give p on both sides.

negR:
  At t the unfolding is not; both independent names N_t and N give n(p).
  At sigma->rho it is lambda X,z.negR_rho(X z). On the full remaining
  output tuple ybar, both sides give n(X[z,ybar]).

andR and orR:
  At t the unfoldings are and and or, respectively; their independent
  names have the identical a(p,q) and v(p,q) matrices.
  At sigma->rho the unfoldings are lambda X,Y,z.
  andR_rho(X z)(Y z) and its or analogue. After ybar, the two matrices
  are a(X[z,ybar],Y[z,ybar]) and v(X[z,ybar],Y[z,ybar]).

coextR:
  At t the unfolding is lambda p,q.iff_C(p,q). By (Iff), its translation
  applied to p,q has value p<->q, exactly the H_t matrix.
  At sigma->rho the actual unfolding is
    lambda X,Y. forall z:sigma (coextR_rho(X z)(Y z)).
  Its translation is compiled with Q_sigma and a bracketed z-body.
  (Quant), followed by the H_rho application identity and ordinary
  universal congruence, gives exactly
    forall z:sigma forall ybar_rho
      (X[z,ybar] <-> Y[z,ybar]).
  This is the independent H_(sigma->rho) matrix. Here X,Y are the
  outer operator arguments; z,ybar are already bound INSIDE the matrix.
  They must not be treated as additional output arguments of H.

boxR:
  At t the unfolding is lambda p.eq_C(p,top_C). Its translated top_C is
  V R (N R), where R is the translation of forall r:t.r. By (Top) this
  is literally source top, without needing any assumption about R.
  The J_t application identity therefore makes the body (p=top),
  exactly the Z_t matrix.
  At sigma->rho the unfolding is lambda X,z.boxR_rho(X z). After the
  output tuple ybar, both sides give (X[z,ybar]=top).

inclR:
  At t the unfolding is lambda p,q.imp_C(p,q). By (Imp) its translated
  body is p->q, exactly the L_t matrix.
  At sigma->rho the actual unfolding is
    lambda X,Y. forall z:sigma (inclR_rho(X z)(Y z)).
  (Quant) and the L_rho application law give exactly
    forall z:sigma forall ybar_rho (X[z,ybar] -> Y[z,ybar]),
  the independent L_(sigma->rho) matrix.

These are all seven unfoldR branches, both base and arrow cases. Their
agreement proofs have no local hypotheses. Thus the final Gen/Nec/I step
is legitimate and proves whole-operator identities, rather than silently
upgrading pointwise or material agreement. Neither the coextR nor inclR
case interchanges a quantifier and a box. These checks concern each
fixed finite type expression, including arbitrary nonrelational input
types; they make no claim of object-level quantification over types.

6. The actual lambda-free boundary: tr(toC(u)) = u

Let toC be exactly ModalConcreteToCSyntax.toC. In particular it sends
source top/imp/iff/eq to the C abbreviations in Section 0, source B to
lambda p.eq_C(p,top_C), and source binders to the actual operator applied
to a C lambda. This is important: toC(B p) is initially a beta redex,
not literally the C syntax box(toC p).

Theorem. For every original L term u:sigma in any finite variable
context, a finite naming extension L_F proves the OBJECT identity

  tr(toC(u)) = u.                                        (RoundTrip)

At nonrelational types the term is a variable or old constant, and the
claim is literal preservation. At relational types prove the assertion
by induction on the actual source term constructor. Embed old typed
constants in the constructed C signature and send them back to those
same constants; the Sigma packaging used in code creates no new objects.

Variables and constants: reflexivity, using inverse de Bruijn-variable
maps. Application: the two induction identities plus ordinary application
congruence. There is no pointwise inference in this case.

Source top: its translated C expansion is V R (N R), for the applicative
R=tr(forall r:t.r). The identity (Top) gives exactly source top. This
argument does not rely on a previously established top round trip.

Source implication: its expansion translates to V (N tr(toC p))
tr(toC q). The induction identities replace its arguments by p,q;
(Imp) gives p->q, the actual source primitive.

Source biconditional: similarly use the two translated implication
subterms, their normalization, and (Iff). This gives the source primitive
p<->q as a literal identity, not merely its truth equivalence.

Source typed equality a=b: its expansion translates to
J_sigma tr(toC a) tr(toC b). Application congruence replaces the two
arguments by a,b, and D_J's literal law gives the source equality
formula (a=b). This works for e and Ty.var(i), as well as relational
types.

Source B AS AN UNSATURATED OPERATOR: write
  R_B := [p] (J_t p tr(top_C)).
This is precisely tr(toC(B)). Beta-bracket, (Top), and the J_t law give
the THEOREM R_B p=(p=top), with p arbitrary. BoxId is the theorem
Bp<->(p=top); therefore ordinary equality elimination proves the theorem
R_B p<->Bp. Generalize p, necessitate that universal theorem, and apply
I_(t->t). The conclusion is
  R_B = B.
Thus the boundary works when B appears as an argument or any unsaturated
subterm. Agreement only for displayed boxed formulas would not suffice.

Source forall x:sigma P: put M=tr(toC(P)), an applicative expression in
the extended variable context x:sigma. By the inductive hypothesis
M=P is an L_F theorem in that context. The exact translated C expression
is Q_sigma([x]M). By (Quant) this is (forall x M). Ordinary quantifier
congruence applied to the induction identity, followed by theorem-level
Nec/I_t, identifies it with the source (forall x P). Equivalently Gen
the material equivalence induced by M=P and use the boxed version of
the same argument. The free-variable side condition holds because the
induction proof has no local hypotheses.

Source exists x:sigma P: exactly the same argument using E_sigma and
existential congruence proves its identity with (exists x P).

This exhausts every source constructor. The proof admits arbitrary
remaining parameters and names in the old signature; it neither assumes
they are denotationally distinct nor requires their rigidity. Object
equality substitution into admitted formula matrices licenses use of
these theorem identities in any local sequent. The local hypotheses
themselves are not used in any necessitation or generalization step.

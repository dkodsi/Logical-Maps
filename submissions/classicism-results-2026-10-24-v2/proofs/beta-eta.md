# Beta identity and contextual beta eta conversion

Original mathematical argument, direct source misc; unpaginated.

EXACT POSITIVE RESULT

On raw typed lambda syntax, assume equality reflexivity/symmetry/transitivity,
application congruence, beta IDENTITY at every admitted relational output, and
the following THEOREM-level rule (call it zeta_=):

  from a proof of (F x)=(G x) with x fresh for F,G and no proof hypotheses,
  infer F=G.

Then all contextual beta/eta conversions are provable identities. Equality
substitution at formula type consequently gives contextual beta/eta equivalence
and transfers derivations from unchanged optional premises. This is a sufficient
basis, not a necessity or minimum-strength theorem.

Proof of eta: beta gives ((lambda x.F x) z)=F z for a fresh z; apply zeta_=.
Proof of lambda congruence: from the theorem M=N with x possibly free, beta
gives ((lambda x.M) z)=M[z/x] and ((lambda x.N) z)=N[z/x]. Rename the given
theorem to z, compose these identities, and apply zeta_=. Induct through term
contexts using this derived lambda congruence and ordinary application
congruence, then take reflexive/symmetric/transitive closure.

ORDINARY BRIDGES TO zeta_= (DISTINCT FROM THE LEAN CERTIFICATE)

1. Actual Functionality: universally generalize the fresh-variable identity
   and apply (forall x,Fx=Gx)->F=G at its function type. No modal rule and no
   propositional Intensionality are needed.

2. Modalized Functionality: generalize first, apply theorem-only necessitation,
   then Box(forall x,Fx=Gx)->F=G.

3. All-type Intensionality: from the identity Fx=Gx derive fully applied truth
   agreement by equality substitution; generalize over x and every remaining
   argument; necessitate that whole closure; apply Intensionality at the type
   of F,G. No actual extensionality or Barcan exchange is used.

For routes 2 and 3, the proof being necessitated must be a logical theorem of
the chosen base. One cannot silently lift a result depending on optional local
assumptions. A conversion basis treating the relevant schemas as logical axioms
must state that necessitation policy explicitly. Predicate quantification must
also be available independently of lambda beta conversion in an elimination
claim about the lambda calculus.

WHAT BETA IDENTITY ALONE DOES AND DOES NOT SETTLE HERE

Ordinary capture-avoiding equality substitution permits replacement into
application contexts and into binder contexts that do not capture free
variables of the replaced terms. It does not by itself state the rule taking
a theorem M(x)=N(x) to lambda x.M(x)=lambda x.N(x).

For x fresh for M,N, even the apparent binder step is obtainable from beta and
application congruence: apply lambda z.lambda x.z to the identity M=N and
contract both outer beta redexes. Any proposed countermodel must respect this.
Accordingly a naive term model that simply forbids rewriting beneath all lambdas
is not, without further argument, a model of ordinary capture-avoiding equality.

This audit supplies no valid independence countermodel for beta identity alone
plus the full intended equality calculus, and therefore does NOT claim that
zeta_= is necessary. The exact beta-alone question is left unresolved here.

PRIMARY-SOURCE CORRECTION TO THE EARLIER CHECKPOINT

Bacon and Dorr, Classicism, July 2022 draft, section 1.4 footnote 16, printed
p.14 (PDF page index 13), explicitly reports that closing the H0 of footnote 7
under zeta-Equivalence gives Classicism, including full beta and eta:
https://andrew-bacon.github.io/papers/Classicism.pdf

That source's zeta-Equivalence is the theorem rule from FULLY SATURATED
MATERIAL agreement F[vbar]<->G[vbar] to F=G. It is not the identity-premise
zeta_= rule used in this file's independent certificate. H0's beta is a
tuple formula schema, not merely unary proposition-bodied beta. The earlier
unary-beta counterinterpretation does not refute H0. Recovery from H0 plus
the source's rule is source-reported positive, not a literature-open question;
the earlier checkpoint recorded only the limit of our then-supplied proof.

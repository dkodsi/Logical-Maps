# Barcan and Actuality do not imply observer separation

Original mathematical argument, direct source misc; unpaginated.

1. EXACT CONCLUSION

The reverse asked about is FALSE:

  C + BF at every type  does not entail OS.

In fact the recorded symmetric-qualitative-contrast model satisfies C5,
boxed BF at every type, and Actuality, but refutes Boolean observer separation
S_B alone. Hence it refutes OS(t,Delta) for EVERY finite Delta, even empty.
The failure is at propositions; no issue about higher-type Functionality
or quantifier commutation is needed to produce it.

OS, Good_Delta and S_B retain their exact definitions from the companion
notes. In particular Bool(E) requires literal preservation of top, bottom,
negation, meet and join; the observer itself is an internally admitted
entity E:t->t. We are not adjoining arbitrary external maps of the Boolean
algebra to the higher-type domain.

2. THE EXISTING C MODEL

Use symmetric-qualitative-contrast, at W_0. Both W_0 and W_1 are copies of
N, and every bijection between any pair of them is an arrow. Composition
is ordinary function composition. A proposition at W_i is a finitely pinned
set of arrows out of W_i, with this additional condition: if it contains
h:W_i->W_0, it contains every g h for a permutation g:W_0->W_0. There is
no corresponding symmetry constraint on arrows into W_1. Higher functional
domains contain the finitely pinned applicative profiles over these domains.
The interpretation of any nonlogical relational constants can be top.

This is the source's C model, not a new claim that an arbitrary restricted
function hierarchy satisfies C. Every arrow is invertible. Its action at
every type is therefore bijective, proving BF and ND at every object, hence
boxed BF and boxed ND. In the map's notation this includes C5. Actuality
holds at W_0: the proposition A of all arrows W_0->W_0 is the least true
proposition. These are established model facts, independently checked by
reading the construction and the proved-only Engine with empty background.

For a current proposition p write v(p)=1 iff id_W0 belongs to p. Every
p's W_0-target component is either all arrows W_0->W_0 or empty, by the
symmetry condition. Consequently

  v(g_t p)=v(p)                                                    (1)

for every permutation g:W_0->W_0, since g_t p={h:h g belongs to p}.
This does not say g_t p=p: its W_1-target component can change.

3. FINITE PINNING MAKES EVERY ADMITTED OBSERVER LOCALLY INVARIANT

Let E:t->t be ANY admitted operator, and let the finite set S pin it down.
If g:W_0->W_0 fixes S pointwise, then

  g_tt E=E.                                                       (2)

This is exactly the definition of pinning, applied to g and id_W0, which
agree on S. Transport preserves application, so for every current p,

  g_t(Ep)=(g_tt E)(g_t p)=E(g_t p).

Apply v and use (1), this time on the output proposition Ep. We obtain

  v(E(g_t p))=v(Ep)                                               (3)

for every p whenever g fixes S. This is an actual-truth invariance statement;
no assertion that E fixes all its input propositions has been used.

4. ONE NONBOTTOM PROPOSITION THAT NO BOOLEAN OBSERVER CAN SEE

Let d be the proposition consisting of ALL arrows W_0->W_1. It is admitted:
it is pinned by the empty set, and its W_0-target component is empty, so the
symmetry requirement is vacuous. It is nonempty, hence d!=bottom.

Fix a Bool(E) observer and a finite S pinning it. Choose distinct a,b outside
S. With the ordinary numerical order on the labelled copy W_1, put

  r={h:W_0->W_1 : h(a)<h(b)}.

This too is admitted: it is pinned by {a,b}, and contains no W_0-target arrow.
Let g be the transposition of a,b in W_0. It fixes S, and its action on r is

  g_t r = d AND NOT r.                                            (4)

Indeed (h g)(a)=h(b) and (h g)(b)=h(a). Since h is a bijection and a!=b,
exactly one of h(a)<h(b) and h(b)<h(a) holds. For arrows into W_0, both sides
of (4) are false. Thus (4) is an identity of admitted propositions.

Now suppose v(Ed)=1. Equation (3), identity (4), and E's Boolean laws give

  v(Er)
    = v(E(g_t r))
    = v(E(d AND NOT r))
    = v(Ed) AND NOT v(Er)
    = NOT v(Er),

an impossibility. Therefore v(Ed)=0 for EVERY admitted Bool(E).
Also E(bottom)=bottom, so v(E(bottom))=0. All qualifying observers thus
agree in truth on d and bottom although d!=bottom. This refutes S_B.

Good_Delta is a subclass of Bool for every finite Delta. Accordingly all
Good_Delta observers also agree on d and bottom, and OS(t,Delta) fails.
The argument needs only material Boolean preservation and false bottom;
requiring literal identities, as the original schema does, cannot evade it.
The finite support S may depend on E; the same proposition d works for all E,
while the auxiliary r and transposition are chosen after E is fixed.

5. A SECOND ROUTE THROUGH BIVALENT EVALUATION

This corroborates the separation using a general internal theorem.
Define ordinary correct bivalent evaluation by

  BE(B): forall p [(p -> Bp=top) AND (NOT p -> Bp=bottom)].

Lemma (over C). If BE(B) exists and composite Boolean/quantifier separation holds for the single list {t}, then
Atomicity_t holds. No boxed form of these hypotheses is assumed.

Proof. BE(B) makes B coextensive with truth, locally endpoint-
valued, and Boolean-preserving-preserving, by ordinary classical case
analysis at each input. Given nonbottom d, composite separation distinguishes d from bottom:
choose an observer E satisfying the Boolean and universal composite identities with Ed true. Put
F(p):=B(Ep). Then F is Boolean-preserving, is locally endpoint-valued, and
Fd is true. Because B is coextensive with truth, F and E agree
in actual truth at every input. Thus F has the following truth agreement at the universal quantifier:
for each current X:tt, its quantifier law is equivalent in truth to E's.

Put w:=forall p(Fp->p). Its acceptance follows from the quantifier law:

  Fw IFF forall p F(Fp->p)
     IFF forall p (F(Fp)->Fp).

Every current Fp is top or bottom and F fixes those endpoints, so F(Fp)=Fp.
Thus Fw is true. Since F(bottom)=bottom, w!=bottom.
For any current p, necessary universal instantiation gives
w<=(Fp->p). If Fp=top, substitution gives w<=p. If Fp=bottom, literal
negation preservation gives F(NOT p)=top, so w<=NOT p. Thus the nonbottom
w decides every current proposition and is an atom. Since Fd is true and
F is endpoint-valued, Fd=top and w<=d. Every nonbottom d has an atom below it.
All uses of necessary UI are instances of an unconditional C theorem; no
conditional equivalence or optional premise is necessitated.

In the qualitative-contrast model BE exists explicitly. Let A be the
actual atom of all W_0-target arrows and take B(p)=BOX(A->p). If p is true,
it contains the entire W_0-target component and Bp=top. If p is false, it
omits that entire component; from every arrow one can return to W_0, so
Bp=bottom. This verifies BE directly on proposition profiles.

Atomicity_t fails directly: every nonempty q<=d is pinned by a finite S.
Choose h in q and a fresh n outside S. The proposition
q AND {k:W_0->W_1 : k(n)=h(n)} is nonempty and properly below q: a
permutation agreeing with h on S can send n to another unused value.
It is admitted and pinned by S union {n}. Hence d has no atom below it.
The lemma therefore independently refutes composite separation at {t} and OS in this model.
Section 4 proves the stronger result that S_B already fails, without Q.

The resulting implication is used in [Logical Observers, section 6](logical-observers.md#6-the-exact-case-with-c5-and-actuality), where the converse is established under C5.

6. CONSEQUENCES FOR THE EARLIER STATUS

Both arrows in the previously proved bounds are now STRICT:

  C + Atomicity_t + BOX BF(all types)  ->  H + OS  ->  C + BF(all types).

Strictness of the left arrow: the finite-support permutation model satisfies
OS but is atomless. Strictness of the right arrow: the qualitative-contrast
model here satisfies even C5+Actuality+boxed BF but fails OS.

This also settles the earlier separate question C->S_B negatively. The
obstruction is internal admissibility: the actual-truth pullbacks of admitted
Boolean operators need not separate the Boolean algebra. Externally one can
write Boolean evaluation maps, but the maps that would observe d cannot
have the finite-pinning and symmetry properties required of the tt domain.

No new model YAML or existing human proof is changed. These are new verdicts
about a published construction and a new ordinary proof, not recorded database
independence certificates or a claim of literature novelty.

SOURCE LOCATORS AND CURRENT CHECKS

Underlying model: topics/classicism/models/symmetric-qualitative-contrast.yaml,
Bacon-Dorr Classicism, draft of 16 May 2023, Appendix D p.79 final construction.
Group context: topics/classicism/groups/symmetric-ideally-full.yaml.
Directly checked primary source: author-hosted draft dated 1 July 2022,
Appendix D final construction, printed pp.77-78 (PDF indices 76-77):
https://andrew-bacon.github.io/papers/Classicism.pdf . The source supplies
C soundness and the model, not the new operator nonseparation argument.
Definition D.1 (printed p.73 in that draft) supplies the transport formulation
of pinning used in (2). These page schemes are not interchanged.

A proved-only Engine query, background=(), restricted to this model, confirms
barcan-r, gallin-extensional-comprehension-r, necessary-distinctness-necessary-r
and actuality hold, and atomicity-t fails. The BF and C5 claims also have
the direct invertible-arrow proof in section 2. All new observer claims are
proved on the page above rather than inferred from an absent database arrow.

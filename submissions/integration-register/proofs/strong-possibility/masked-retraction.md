# A pure proper retraction on numerical predicates

25 October 2026. Original ordinary mathematical proof by OpenAI Codex
and parallel research agents. Direct source: `misc`, this note, sections
1–4. The fixed theory is pure finitary relational C; T=Max(C). No human
or Lean verification is claimed.

There are explicit closed pure operations F,G at the counting type
rho=nu_(et) such that C proves G composed with F is the identity, and
T proves F composed with G is not the identity. Indeed F is injective
and omits the top predicate in every Max model. Thus direct finiteness
at this counting type is already refuted by Max; it is not an
independent H-clopen sentence and does not resolve unrestricted SP.

## 1. Types and the guarded arithmetic facts

Put nu=nu_e=(et)t and rho=nu t=((et)t)t=nu_(et). Let 0, S and N be
the Frege zero, successor, and natural-number property at e. Put
I=I_e=diamond I*_e, the usual numerical noncollapse proposition.
All operation types below end in t and are admitted relational types.

The existing arithmetic development gives the following C theorems:

* N0 and, for every x, Nx implies N(Sx);
* every number is zero or a successor of a number;
* under I, successor on numbers is injective and zero is not a
  numerical successor.

These are the guarded Peano facts used in
[predecessor-proof.md](../../../classicism-results-2026-10-24-v2/proofs/predecessor.md),
including its equivalence of I with the stated noncollapse condition.
Pure Max proves I_e; actual Infinity_e is not assumed.

Define the following closed pure predicates and operations, where X:rho
and x,y:nu:

    A(y) := I and Ny,
    c_0(y) := I and y=0,

    (QX)(y) := I and Ny and
                  exists x (Nx and Xx and y=Sx),
    (PX)(y) := I and Ny and X(Sy),

    F(X) := QX or (not A and X),
    G(X) := PX or (not A and X).

All Boolean operations in the last two lines are pointwise at rho.
These displayed definitions abbreviate lambda terms. In particular
P,Q,F,G:rho rho. Q uses a relational image; no operation selecting
a numerical predecessor is assumed or constructed.

## 2. The two unconditional operation identities

For arbitrary X and y, expansion gives

    (P(QX))(y)
      iff I and Ny and N(Sy) and
          exists x (Nx and Xx and Sy=Sx).

If I and Ny hold, successor closure supplies N(Sy), and guarded
successor injectivity identifies the displayed x with y. The reverse
implication takes x=y. If I and Ny do not both hold, both sides of the
following equivalence are false. Thus C proves, with no optional
premise,

    (P(QX))(y) iff A(y) and Xy.                             (1)

Likewise expansion of Q(PX) gives

    (Q(PX))(y)
      iff I and Ny and
          exists x (Nx and X(Sx) and y=Sx).

Under I and Ny, a numerical predecessor exists exactly when y is not
zero. The displayed equality then substitutes Xy for X(Sx). Hence C
proves the unconditional equivalence

    (Q(PX))(y) iff A(y) and y!=0 and Xy.                     (2)

Both P and Q take values below A and annihilate not A and X. For P,
I and Ny imply A(Sy) by numerical successor closure. For Q, its own
I and Nx guard excludes the not A(x) disjunct. They distribute over
the binary disjunctions used here. Expanding F and G and using
(1)–(2) therefore gives C theorems

    (G(FX))(y) iff Xy,
    (F(GX))(y) iff Xy and not c_0(y).                       (3)

The second equation uses N0, so that on I the exceptional numerical
zero is exactly the support of c_0. Off A both composites leave X
unchanged.

All equivalences in (1)–(3) are C theorems with I retained inside the
formulas. Necessitate these whole theorems and apply C's intensionality
and lambda/eta rules, or its derived Modalized Functionality after the
pointwise proposition identities. This gives genuine entity identities,
not merely actual coextension:

    G composed with F = id_rho,
    F composed with G = lambda X. (X and not c_0).           (4)

This inference never necessitates an optional assumption I. The C
Modalized Functionality theorem is recorded as
[classicism-implies-modalized-functionality-r.yaml](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/classicism-implies-modalized-functionality-r.yaml).

## 3. Max makes the retraction proper

The same expansions give unconditional C identities

    G(top_rho)=top_rho,
    F(top_rho)=not c_0.                                    (5)

Under I, c_0(0) is actually true. Thus c_0 is not bottom and not c_0
is not top. Since T proves I, equations (4)–(5) show in every Max model
that F composed with G is not the identity.

More concretely, G composed with F=id makes F injective on actual
rho-entities: apply G to an equation FX=FY. If some X satisfied
FX=top, applying G and using (5) would give X=top. But then
FX=F(top)=not c_0 differs from top. Consequently top is outside F's
actual range. This establishes actual Dedekind infinitude as well as
the finite mixed identity diagram

    exists f,g:rho rho
        (g composed with f=id and f composed with g!=id).   (6)

The witnesses F,G are closed pure terms. In particular (6) is not a
candidate for a Max-independent complementary existential pair.

This does not conflict with the no-predecessor theorem for the original
Frege number entities. The new operations act on numerical predicates.
They shift an I-supported predicate and preserve the complementary
part of its input. Recovering an original numerical entity from an
actually unique numerical predicate is a different operation, which
the no-predecessor theorem still excludes.

## 4. What the mask does and does not provide

Because I=diamond I*, ordinary S4 gives diamond I=I. The mask is not
ordinary-box fixed in Max. A full finite singleton C model refutes I;
therefore C does not prove I. Pure Max consequently proves not box I,
while also proving I. In particular it refutes I=box I.

There is a general limitation on replacing I by a stronger closed pure
central mask. Suppose C proves both J<->box J and J<->diamond J for
a closed pure J. If C proved neither J nor not J, both sides would be
C-consistent, so pure Max would give diamond J and diamond not J.
The first fixed-point equivalence gives box J from J; by Boolean duality
it also gives diamond not J<->not J. The second gives diamond J<->J.
Thus Max would prove both J and not J, contrary to its existing genuine
models. Hence C decides J. Necessitation makes J identically top or
identically bottom according to that decision.

Accordingly a closed pure C-provably ordinary-central mask cannot supply
a nontrivial uniform pasting device. This differs from the H-clopen
identity gates in the earlier positive fragment theorem. Those gates
need not be fixed by ordinary box and diamond.

Status: positive ordinary mathematical proof, with all optional arithmetic
conditions retained in the defining terms. No full SP conclusion, database
record, or Lean certificate is asserted.

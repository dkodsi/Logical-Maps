# Diagonal characters and stable atoms

Original mathematical argument, direct source misc; unpaginated.

1. Precise formulas

All objects quantified below are admitted objects of the fixed relational
language. E has type tt; p,q,a,w have type t. Put

  w_E := forall p:t, (E p -> p),
  B(E) := forall p:t, (E p = top OR E p = bottom),
  N(E) := forall p:t, E(not p) = not(E p),
  D(E) := E bottom = bottom AND B(E) AND N(E) AND E(w_E).

Every equality here is literal identity. The final conjunct E(w_E) asserts
truth only. It is not initially boxed or asserted identical with top. Under
B(E), however, that truth entails E(w_E)=top.

The original, longer character formula additionally asserts E top=top and
forall p,q E(p AND q)=(E p AND E q). The proof below shows it equivalent to
D(E) over C. It is a single finite formula, not a schema of preservation of
all quantifiers.

A stable atom means Atom_t(a) AND BOX DIAMOND a, where DIAMOND a abbreviates
a!=bottom. Atomhood here is local. Stability of being nonbottom is not
stability of atomhood at future points with new propositions.

2. From a diagonal character to a stable atom

Assume D(E), and put w=w_E.

First, w is necessarily nonbottom. By B(E) and E(w), E(w)=top. Together with
E(bottom)=bottom, this implies w!=bottom. More strongly, Necessity of
Identity makes both displayed output identities necessary. At any accessible
point, w=bottom would therefore force top=bottom by substitution. Necessitate
this closed C implication and apply normality to the two necessary identities.
The result is BOX(w!=bottom), namely BOX DIAMOND w. This step does not use ND.

For any fixed current p, if E p=top, then BOX(E p). Universal instantiation
gives the C theorem w -> (E p -> p); its necessitation, together with BOX(E p),
gives BOX(w -> p), hence w<=p. There is no quantifier movement through BOX:
the universal formula is part of w itself, and the instantiated implication
is a C theorem with E,p free.

If E p=bottom, N(E) gives E(not p)=top, so the same argument gives w<=not p.
Thus each current proposition p is decided by w. Since w!=bottom, this is
the standard Boolean-algebra characterization of Atom(w): a nonbottom proper
part z<=w cannot satisfy w<=not z, and the alternative w<=z makes z=w.

We have proved

  D(E) -> Atom(w_E) AND BOX DIAMOND(w_E).

It also follows that, for every current p,

  E p IFF w_E<=p.

The accepted case was proved above. In the rejected case w<=not p, so w<=p
would make the nonbottom w bottom.

The literal pointwise identity is stronger, but also follows:

  forall p:t, E p = (w_E<=p).                         (1)

If E p=top, then w<=p; since algebraic entailment is an identity proposition,
Necessity of Identity makes (w<=p)=top. If E p=bottom, we know w<=not p and
BOX(w!=bottom). Necessity of Identity makes the first of these necessary.
Necessitate the closed Boolean theorem

  (w<=not p AND w!=bottom) -> not(w<=p).

Normality yields BOX not(w<=p), hence (w<=p)=bottom. Comparing endpoints
gives (1). Merely using the material biconditional would not justify (1).

3. The canonical operator of a stable atom

Let Atom(a) and BOX DIAMOND a, and define the admitted lambda term

  E_a(p) := BOX(a -> p).

In C the order proposition a<=p and BOX(a->p) are identically equivalent
expressions: their equivalence is a C theorem without optional hypotheses,
so Equivalence applies to that equivalence. We may use either expression
for E_a throughout this section.

Atomhood gives, for each current p, a<=p or a<=not p. In the first case E_a(p)
is true and its identity form is necessary, so E_a(p)=top. In the second
case, necessary nonbottomness of a and the necessary order identity give
BOX not(a<=p), hence E_a(p)=bottom. Thus B(E_a).

Top is necessarily entailed, so E_a(top)=top. Stable nonbottomness excludes
necessary impossibility of a at every accessible point, so E_a(bottom)=bottom.

Conjunction preservation is already a C identity for every a, with no atom
assumption:

  BOX(a -> (p AND q))
    = BOX((a -> p) AND (a -> q))
    = BOX(a -> p) AND BOX(a -> q).

For negation, split on the two atom-deciding alternatives. If a<=p, stable
nonbottomness makes E_a(not p)=bottom, while E_a(p)=top. If a<=not p, the
opposite identities hold. Consequently E_a(not p)=not(E_a(p)) for each
current p. No optional universal assertion has been boxed.

The diagonal identity is unconditional in C:

  w_(E_a) = a.                                      (2)

Indeed, a implies forall p(BOX(a->p)->p) by T, while the reverse follows by
instantiating p=a and using the C theorem BOX(a->a). This is a C-provable
biconditional with a free, so Equivalence yields (2) without importing an
atom or stability hypothesis. Substitution in the C theorem E_a(a) now gives
E_a(w_(E_a)). Therefore E_a satisfies D and the original longer formula.

Combining (1) with these canonical identities proves that every D(E) also
preserves conjunction pointwise. Its top preservation follows already from
bottom preservation and N(E). Thus the shorter and longer character formulas
are equivalent over C.

4. Exact separation equivalence

Define the single finite formula

  SepD := forall p,q:t,
    [p=q IFF forall E:tt, (D(E) -> (E p IFF E q))].

Equivalently, every distinct p,q have a D-character whose outputs differ
in current truth. The equivalence uses ordinary classical quantifier logic;
it does not require an admitted operation selecting a character for every pair.

THEOREM, over C:

  SepD IFF (ND_t AND Atomicity_t).

Forward, necessary distinctness: if p!=q, choose a separating E. B(E) makes
the two values opposite endpoints. NI preserves their endpoint identities.
At any accessible point p=q would identify those outputs and force
top=bottom. Thus BOX(p!=q), exactly ND_t.

Forward, Atomicity: if p!=bottom, separate p from bottom by E. Since E(bottom)
is bottom, separation forces E p true. Section 2 supplies the atom w_E<=p.
This is Atomicity_t, and it actually supplies a necessarily nonbottom atom
under each current nonbottom proposition.

Reverse: assume local ND_t and Atomicity_t, and let p!=q. Their Boolean
symmetric difference

  d := (p AND not q) OR (q AND not p)

is nonbottom. Atomicity gives an atom a<=d. ND_t, applied to a!=bottom,
gives BOX DIAMOND a. Hence the explicit E_a satisfies D by section 3.
An atom below a binary join lies below one disjunct, so a<=(p AND not q) or
a<=(q AND not p). In the first case E_a(p) is true and E_a(q) false; in the
second case the truth values are reversed. Thus E_a separates p and q.
The direction p=q implies agreement of all characters is substitution.

5. Modal and identity boundaries

- No BF instance is used. The only universal instantiation under a box
  comes from necessitating a closed logical theorem; no local universal
  premise is changed into a boxed universal premise.
- The assumptions and conclusion are the two local type-t instances.
  No conclusion of C5, boxed ND, boxed Atomicity, or full-schema Atomicity
  is being silently added.
- E need not evaluate actual truth: its stable atom need not currently be
  true. Diagonal acceptance is not the much stronger requirement that E
  agrees with current truth on every proposition.
- Equation (1) is a universal family of current pointwise identities. It
  does not establish E = E_(w_E) as an identity between operations. That
  upgrade would need additional functionality or modal-domain reasoning.
- Atom(w_E) is local, whereas w_E!=bottom is necessary. Do not replace this
  pair by necessary atomhood or by a strong-world claim.
- The canonical inverse equation (2) is a genuine unconditional C identity.
  Its proof does not invoke Equivalence on a biconditional proved only from
  an optional atomhood, ND, or stability premise.

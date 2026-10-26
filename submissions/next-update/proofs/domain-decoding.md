# Decoding on definable domains is exactly Plenitude

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi.

## 1. Scope and two formulations

All operation outputs are relational. For relational types A,B, predicates
D:At, E:Bt and an operation f:AB, write

    Inj_D(f) := ∀x x' (Dx ∧ Dx' ∧ fx=fx' → x=x').

**Domain Decoding (DD)** is the type schema

    ∀D f (Inj_D(f) → ∃g^{BA} ∀x (Dx → g(fx)=x)).

**Domain Bijection Inversion (DBI)** says that whenever f maps the extension
of D bijectively onto the extension of E, there is g:BA mapping E into D
with both inverse equations on those extensions. All these assertions and
equations are current. There is no box in the inverse requirement and no
identification of whole operations from pointwise agreement.

The type variables index schemas externally. D and E are quantified
properties, and may be empty. Restricting DBI to nonempty D,E leaves the
converse theorem below unchanged.

## 2. The exact theorem

Over C,

    DD  ⇔  DBI  ⇔  Plenitude.

The source type in Plenitude may be e; the decoding principles need only
operations between relational types. The proof codes an individual input
by its singleton property and never constructs an individual-valued
operation.

### 2.1 Plenitude implies DD and DBI

Suppose f is injective on D. For b:B in the image of D there is a unique
a:A with Da and fa=b. For b outside that image, assign a fixed default
a_0:A. This defines a current total single-valued relation B→A.
Plenitude realizes it by an operation g, and g(fa)=a for every a in D.
The fixed default exists because A is inhabited (or take bottom_A).

For a bijection D→E the same construction maps every member of E into D,
so it satisfies the two inverse equations. Empty D and E cause no problem.

DD also implies DBI directly: its decoder takes each b in E to the unique
a in D with fa=b, by substituting b=fa into the decoding equation.

### 2.2 Graph projections recover full Plenitude

Fix any source type σ, any relational output τ=ρ_1…ρ_k t, and any current
total single-valued relation U:στt. The case k=0 is allowed. Put

    κ := (στt)t,
    H(a,b) := λP^{στt}. (Pa)b,
    h(a) := λx^σ. x=a.

The following coordinate operations have admitted relational output types:

    F(c) := λx^σ. c(λa^σ b^τ. x=a),
    Q(c) := λr_1…r_k. c(λa^σ b^τ. b[r_1,…,r_k]).

Thus F:κ→σt and Q:κ→τ. By the base conversion principles,

    F(H(a,b)) = h(a),       Q(H(a,b)) = b.

These are C identities, not deductions from current coextension under U.
The singleton coding a↦h(a) is injective: if h(a)=h(a'), evaluation at a
and reflexivity give a=a'. Consequently H is injective in its pair of
arguments, using F and Q.

Define the two admitted properties

    D(c) := ∃a b ((Ua)b ∧ c=H(a,b)),
    E(s) := ∃a (s=h(a)).

F maps D into E. It maps onto E because U is total. It is injective on D:
write c=H(a,b), c'=H(a',b') with U(a,b), U(a',b'). If Fc=Fc', singleton
injectivity gives a=a', and single-valuedness of U then gives b=b', hence
c=c'. Thus F:D→E is a current bijection. Both domains are nonempty.

Either DD applied to this restricted injection, or DBI applied to this
bijection, gives an admitted G:(σt)→κ satisfying

    G(Fc)=c   whenever Dc.

Define the required operation

    X(a) := Q(G(h(a))).

For arbitrary a choose the unique b with (Ua)b. Then D(H(a,b)), so
G(h(a))=H(a,b) and X(a)=b. Therefore ∀a (Ua)(Xa), the required Plenitude
instance. No choice principle, rigidity premise, BF, ND or Functionality
has been inserted into the proof.

## 3. What this says about representation independence

The established ordinary Left Inverse schema quantifies over injections
on entire ambient types. Its exact interval, from the previous inverse-map
work, is

    ND < LInv < C5,

and Actuality + LInv is equivalent to Plenitude. The strictness witnesses
are the sections-and-projection model and the full two-object retract;
the finite-support permutation model also separates LInv from Plenitude
and Actuality.

The new theorem identifies a different, natural strengthening: allow the
same decoding demand on arbitrary property-defined domains. This yields
Plenitude itself. Even only the canonical graph-projection bijections in
§2.2 suffice. An unrestricted demand that all mathematical changes of
presentation admit inverse operations therefore risks restating Plenitude.
To find a genuinely distinct intermediate principle, the allowed domains
or the allowed comparisons must be specified independently; the numerical
domains investigated in the companion notes do exactly that.

This result does not identify current subdomain bijections with categorical
isomorphisms, whose equations are identities of operations. It does not say
that DD or DBI are new principles absent from the literature. It is an
explicit classification of the formulations above over the fixed C.

## 4. Sources and checks

- Fixed framework and Plenitude: `topics/classicism/topic.yaml`,
  `background.md`, and `principles/plenitude-r.yaml`.
- Existing whole-type inverse results and model separators:
  `research/2026-10-22/notes/choice-uniformization.md`, §§7, 9, 12, 22.
- This note, §§1–3, supplies the original graph-projection argument;
  unpaginated. Any future database certificate for this proof should use
  `source_id: misc`.
- A proved-only `scripts.pmap.load_topic` / `Engine` query on 25 October
  confirmed: the sections-and-projection model has ND and necessary
  Actuality but not Plenitude; the full two-object retract has Plenitude
  but not C5; the finite-support permutation model has C5 but neither
  Actuality nor Plenitude. Optional assumptions were not placed in the
  engine background.

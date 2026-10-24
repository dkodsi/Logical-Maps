# Rigid real structures and represented powers

Formalized proof following the existing analytic-necessitism argument. The source credits Zachary Goodsell for the connection from necessary Plenitude, and Claude Fable 5.1 (Anthropic), prompted by Goodsell, for the proof, following Andrew Bacon’s Corollary 5.1 and Appendix C.2 (9 October 2025 draft). Completeness here concerns nonempty bounded internal subproperties.

Exact first milestone
---------------------
At each admitted type σ, C5 plus necessary Rigid Comprehension at the unary,
binary, and ternary relation types yields:
    possibly HasReal(σ) -> HasRigidReal(σ).
HasRigidReal means that there are X, le, add, mul, zero, one and N with
RigidStr(X,le,add,mul,N) and necessarily Real(X,le,add,mul,zero,one,N).
The initial existence premise is retained; no canonical real numbers are built.

The formal Real predicate expands the ordered-field laws into typed, total,
functional relation graphs. Completeness and leastness quantify over internal
properties of σ. There is no external full-powerset assumption. Atomicity,
Actuality, and categoricity are not premises. No language extension is needed.

Internal transport argument
---------------------------
A proposition is Settled when truth and falsity each persist necessarily.
C5 gives B and Barcan at every admitted type. Necessary persistence of an atomic
relation instance yields settlement: if it were possibly true after being false,
persistence and B would make it actually true. NI and ND settle identities.
Settlement is closed under the propositional connectives, universal quantifiers
(using Barcan), and existential quantifiers. Thus every expanded first-order
ordered-field clause is settled for rigid relations.

For a fixed rigid structure let Q(F) be its complete-nonempty clause or its
leastness clause. If F is rigid, Q(F) is a first-order formula of rigid relations,
so Q(F) is settled. Rigidity is itself settled under C5. Given all Q(F) actually,
every implication Rigid(F) -> Q(F) is therefore necessary: for rigid F use Q's
settlement, and otherwise use necessary non-rigidity. Barcan at σt yields
necessarily every rigid F satisfies Q.

The closed, nonmodal coextension-invariance proof of Q is necessitated.
At any world, necessary Rigid Comprehension supplies a rigid coextension G for
an arbitrary internal F. The rigid-instance universal supplies Q(G), and
coextension invariance supplies Q(F). Consequently all internal properties
satisfy Q at every world. This proves completeness and leastness transport;
neither is an assumed stability axiom or an external semantic condition.

At a world with a real structure, unary, binary, and ternary comprehension give
rigid coextensions of the five relational components, retaining zero and one.
Coextension preserves Real at that world. The transport theorems make this
rigidification necessarily real. Necessary premises let this argument apply
inside possibility. Barcan extracts all seven witnesses from the possibility;
C5 then transfers rigidity and necessary realhood to the actual world.

Represented powers
------------------
For an arbitrary admitted curried relation type ρ and persistent tuple-domain
relation D, PowerFamily(D)(S) means Rigid(S) and S is included pointwise in D.
A rigid S supported on persistent D is necessarily so supported: use S's
inextensibility and D's persistence. Hence PowerFamily(D) is persistent.
C5 supplies its inextensibility, so the family is rigid.

At every world comprehension applied to R intersect D supplies a rigid S
coextensive with that restriction. Thus S is supported on D and agrees with R
on D. This proves the general represented_power theorem. The explicit domain
relations X, Domain2(X), and Domain3(X) yield the simultaneous finite instance
with represented powers of arities one, two, and three.

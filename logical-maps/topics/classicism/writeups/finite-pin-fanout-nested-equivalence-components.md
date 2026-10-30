# Finite-pin fanout: nested-equivalence components

GPT-6 Astra, prompted by Daniel Kodsi, 30 October 2026.

This ZFC construction gives a model of C satisfying **No Collapse and
current Actuality**. It answers Cian Dorr's ordinary No Collapse consistency
question of 14 October 2026. Write
\[
O_0=\Box,\qquad O_{n+1}=\widehat{O_n},\qquad
\widehat X=\lambda p\,\exists q\,[q\land\Box(\neg(X(\neg q))\to p)].
\]
The target is one sentence,
\[
\exists\mathcal F^{(tt)t}\,[\mathcal F\Box\land
\forall X^{tt}((\mathcal FX\to\mathcal F\widehat X)
\land(\mathcal FX\to X\ne\widehat X))].
\]

Two ingredients are essential. Nested finite-capacity components separate
arbitrarily late finite steps. A common fanout root preserves those
separations and admits one family of whole operators. Separate finite
countermodels alone would not establish this existential family sentence.
The inequalities below are whole-operator inequalities; current coextension
of the positive iterates still holds at the fanout root.

## 1. Finite-pin semantics and the return recursion

Use the ideally full construction of Bacon–Dorr, *Classicism*, Appendix D,
Definitions D.1–D.3 and Proposition D.4, pp. 73–74. For a small category of
sets and functions, individuals at an object A are its underlying set.
At relational type tau=bar-sigma t a profile F assigns to each h:A→B a
set F_h of tuples from the full already-constructed domains at B. Admit
exactly those profiles with a finite pin S⊆A: F_h=F_h' whenever h,h'
have the same codomain and agree on S. Transport is (hF)_k=F_(kh).
Current truth is the identity row.

A shift of a profile pinned by S is pinned by h[S]. For a finite parameter
environment, arrows agreeing on the union of its pins give equal whole
transported parameters. Lambda abstraction therefore has that same finite
pin; bound variables range over the full target domains. All domains are
sets, recursively by the finite types. Literal profile identity is
represented and distinguishable: a codomain-constant predicate with
current singleton extension {u} distinguishes u from every other current
entity. These are precisely the finite-ideal hypotheses of the ideally
full C-model theorem. In particular quantifiers are not restricted to
transported root arguments.

Let U_A(S) be the proposition consisting of endomorphisms of A fixing S.
It is an admitted true proposition, and every true proposition q contains
U_A(S) for some finite pin S of q. Put R_0(A,S)=all arrows out of A and
\[
h:A\to B\in R_{n+1}(A,S)
\ \Longleftrightarrow\
\forall T\subseteq_{\rm fin}B\ \exists k:B\to A\,
[kh|_S=\operatorname{id}|_S\land k\in R_n(B,T)].
\tag{R}
\]
Then
\[
O_np\text{ holds at }A
\ \Longleftrightarrow\
\exists S\subseteq_{\rm fin}A\,[R_n(A,S)\subseteq p].
\tag{H}
\]
For n=0 this is the universal-arrow clause. Inductively let
D_n=not O_n not. Its monotonicity permits replacing any true witness q
in the hat definition by U_A(S)⊆q. At h:A→B, the condition
D_n(hU_A(S)) says that every finite T has a k∈R_n(B,T) at which hU_A(S)
is true. Exactly then k:B→A and kh fixes S. This proves (R) and (H).
Both increasing the pin and increasing n shrink R_n. The return is chosen
*after* the finite challenge T; one return need not work for all challenges.

## 2. Nested structures

Fix a positive external integer d. For n a positive integer let U_0(n) be an
n-element set, and let U_0(infinity) be countably infinite. These are the level
0 nodes; their elements are leaves. There is NO empty U_0(0).

Inductively, for j>=1 and m a nonnegative integer or infinity, a node U_j(m)
has exactly m children of type U_(j-1)(infinity), and countably infinitely many
children of every finite-parameter U_(j-1)(n). For j=1 these finite parameters
are positive integers; for j>1 they include zero. All these nodes are nonempty;
U_j(0) for j>=1 is countably infinite because of its finite-type reservoirs.
The underlying set of a node is its set of leaves. Children partition it.

A_d is a disjoint union of countably infinitely many copies of each finite-
parameter U_(d-1)(n). B_d has those copies and countably infinitely many copies
of U_(d-1)(infinity). There are d nested equivalence relations E_0,...,E_(d-1):
E_j classes are the level-j nodes. Arrows are all total leaf functions preserving
each E_j. They may collapse any level. Write lambda(v) for a node's parameter:
for j=0 its number of leaves; for j>0 its number of infinite-parameter children.

Use the full finite-pinned construction of §1 at all relational types. Set O_n=hat^n(Box). The proved
semantic recursion is

 R0(X,S)=all arrows out of X;
 h:X->Y in R_(n+1)(X,S) iff for every finite T subset Y some k:Y->X satisfies
               kh|S=id|S and k in R_n(Y,T);
 On p at X iff some finite S subset X has R_n(X,S) subset p.             (R)

For an arrow h and finite S, call a node anchored when it meets S. Its target
node hv is well-defined. Let P(h,S) say h|S is injective and reflects all d
equivalences. Preservation is already imposed on arrows. Under P, the inverse
on h[S] consistently prescribes a return on every ancestor of every point of
h[S]. Distinct anchored nodes at a given level have distinct prescribed images.

## 3. Finite allocation

All finite partial leaf maps preserving the d equivalences extend to total
arrows. Choose target nodes for the finitely many partly assigned ancestors,
respecting their existing assignments; within an assigned node send unassigned
children constantly into any child of its target. Repeat downward and fill any
remaining leaves constantly. Unassigned top nodes may be sent constantly
anywhere. This gives whole arrows, not maps defined only on the challenge.

The return construction below begins with the forced inverse h[S]->S and an
arbitrary finite T enlarged to contain h[S]. It allocates every ancestor of T
top-down, and maps T injectively with reflection of all equivalences. Therefore
distinct touched children must be assigned distinct children. Forced inverse
assignments are retained. They already form a finite subtree isomorphism on
the touched ancestors; the task is to add the new T-only nodes.

There are two allocation problems, indexed by j with 0<=j<d.

EVEN PROBLEM. Assume P(h,S), equality lambda(v)=lambda(hv) on anchored nodes
of levels <j, and lambda(v)>=lambda(hv) on anchored nodes of level j. Construct
a return k fixing S after h which reflects all equivalences on T and has
parameter equality on every T-anchored node of levels <j.

ODD PROBLEM. Assume P(h,S) and parameter equality on all anchored nodes of
levels <=j. Construct such a return with equality at levels <j and with
lambda(w)>=lambda(kw) on every T-anchored level-j node w.

Here w is a node in Y, the SOURCE of the return. Keeping this orientation is
essential. The return's inequality is not the original arrow's inequality.

Proof of the even problem:

(a) At a forced level-j node w in Y, its return target v in X is fixed. For
j>0, each infinite-parameter child of w touched by T must be assigned an
infinite-parameter child of v, because equality is required at level j-1.
Finite-parameter children must be assigned their exact finite types. There
are enough infinite children since lambda(v)>=lambda(w); the already forced
assignments occupy corresponding children, so reserving them causes no new
shortage. Every finite type has infinitely many available children. For j=0,
the same statement says simply that the finitely many challenged leaves in w
can be injected into v extending the inverse, since |v|>=|w|.

(b) At a new (unforced) level-j node w, choose its return image to be a FINITE-
parameter node with enough capacity for the finite trace. For j>0 take its
parameter at least the number of infinite-parameter children of w meeting T;
for j=0 take a positive cardinal at least |T intersect w|. Below this frontier,
match every touched finite or infinite child parameter exactly. At all lower
nodes the two types match; their infinite-child capacities match and their
finite-type reservoirs allow the remaining finite trace to be embedded.

(c) Above level j, newly allocated nodes can always have finite parameter.
If a parent is at level j+1, its new level-j children in (b) all have finite
parameter, so its infinite finite-type reservoirs supply them regardless of
its own number of infinite children. At still higher parents do the same
recursively. A new node strictly above level j can be assigned parameter zero,
since its new children can all be finite-parameter nodes. Forced children are
handled in their forced parent, where they already exist and occupy only their
own prescribed slots. No new infinite child is demanded above the frontier.

(d) At the top, there are infinitely many copies of each finite type in BOTH
objects. Thus new top nodes can be allocated distinctly, avoiding finitely
many forced top nodes. If j=d-1, use (b) directly at that top level; otherwise
use (c). All allocation involves only finitely many nodes. At the leaves make
the required injective finite assignments, and then use the total-extension
lemma. This constructs the promised return.

Proof of the odd problem:

Forced level-j nodes have equal parameter on the two sides, so case (a) works
with equality. For a new level-j node w of FINITE parameter n, choose an image
of the SAME parameter n. Its finite trace embeds because it has the same full
type. For a new level-j node of INFINITE parameter, choose a finite parameter
large enough for the finite trace as in (b). In both cases
lambda(w)>=lambda(kw), and matching parameters below level j is possible.
Every newly chosen level-j image is finite-parameter. Therefore the argument
above the frontier in (c), the top allocation in (d), and whole-arrow extension
apply unchanged. This proves the odd problem.

The allocation lemma's key feature is that an infinite-parameter node can be
replaced by a finite approximation until equality has reached its OWN level.
Once that equality is required, its parent's finite count of infinite children
becomes a real obstruction. There is no requirement for a single return to
work for every challenge T: the finite approximant may depend on T.

## 4. Uniform return-game induction

For 0<=j<d the exact clauses are:

 R1(h,S) iff P(h,S);
 R_(2j+2)(h,S) iff P(h,S), parameter equality on anchored levels <j,
                              and source>=target parameter at level j;
 R_(2j+3)(h,S) iff P(h,S) and parameter equality on anchored levels <=j. (Gd)

R1 follows from finite inverse preservation and the total-extension lemma.
The R_n relations decrease with n; this follows directly by induction from
R1 subset R0 and monotonicity of the recursion.

Assume equality through level j-1 is the clause for R_(2j+1) (for j=0 this
means R1=P). If h belongs to R_(2j+2), it already satisfies that clause. Suppose
an anchored level-j node v has lambda(v)<lambda(hv); then lambda(v) is finite.
For j=0, choose more than |v| leaves in hv, including an anchored image.
For j>0, take one leaf in each of lambda(v)+1 distinct infinite-parameter
children of hv and include h[S]. Every return sends hv into v. Its membership
in R_(2j+1) requires equality of child parameters at level j-1 and reflection
of that level's equivalence relation. Thus it needs more distinct infinite
children of v than exist. At j=0, injectivity on the challenged leaves gives
the same contradiction. This proves the even inequality's necessity.
Its sufficiency is exactly the EVEN allocation problem, which constructs an
R_(2j+1) return for every challenge.

Now suppose h belongs to R_(2j+3). It already has the even inequality. Challenge
with any finite T containing h[S]. For each anchored level-j v, the required
R_(2j+2) return k sends hv back into v. The return's inequality gives
lambda(hv)>=lambda(v), so the original inequality is an equality. Conversely
the ODD allocation problem constructs a return satisfying the even clause
for every T. This proves the odd clause and completes induction for all j.

There is no unmentioned condition on higher ancestors in this induction.
The finite-allocation lemma explicitly keeps their forced inverse assignments
and uses finite approximants for every new child above the active frontier.

## 5. Separation at every finite depth

At j=d-1, (Gd) says that R_(2d+1) reflects the whole finite nested pattern and
preserves every anchored node parameter. For every finite S subset A_d an
arrow h:A_d->B_d can do this: send each top node meeting S isomorphically into
a distinct B_d copy of the same finite-parameter top type. Extend all other
top nodes arbitrarily. Consequently

      for every finite S there is h:A_d->B_d in R_(2d+1)(A_d,S).

But R_(2d+2)(A_d,S) has no arrows to B_d, for ANY S. Challenge a proposed arrow
with one leaf b in an infinite-parameter top node of B_d. An R_(2d+1) return
on {b} would have to preserve that top parameter, whereas A_d has no such node.

Let p_d be the proposition at A_d true just on arrows with codomain A_d. It is
empty-pinned. By the semantic recursion,

             not O_(2d+1)p_d, and O_(2d+2)p_d.

Hence, for every external finite d>=1, this explicitly described full
finite-pinned model separates hats 2d+1 and 2d+2. The case d=1 is the flat finite/infinite-block construction.

## 6. Each finite component stabilizes

Let Q(h,S) be the full equality clause R_(2d+1). It is closed under the usual
finite return construction when the reverse direction has the same top types
available. Thus R_(2d+2)=Q except that A_d->B_d is empty. More explicitly:
for endomorphisms, or for h:B_d->A_d, choose a matching top type for each new
challenged top node in the reverse source; those types exist. Inside each
matched top node use the finite partial type-preserving isomorphism, which
extends because both structures have the same finite/infinite child supplies.
This provides the required Q return. Necessity follows by decreasing R_n.

R_(2d+3) is Q on endomorphisms and empty on both cross directions, and is a
raw fixed point. At B_d, adding a leaf in an infinite-parameter top node to
any pin eliminates B_d->A_d already under Q. Therefore at B_d that enlarged pin removes the only extra cross arrows, while
at A_d the two return sets already agree. Thus (H) gives
O_(2d+2)=O_(2d+3) at both objects for all admitted propositions. The operators are identical under profile semantics.
Each particular finite-d model thus STOPS at its exhibited even level.

## 7. The common fanout category

Take the disjoint union of the two-object nested-equivalence categories C_d, retaining their object labels even if their underlying sets have been represented by copies of the same set. Add a fresh object R with individuals N. Its only endomorphism is id_R. There are no old-object-to-R arrows and no arrows between distinct old components. From R to each old object V include ALL functions N->U(V).

An old arrow g:V->W postcomposes an R->V map h by ordinary function composition g h. This is an allowed R->W map because all such functions were included. Associativity follows from function composition, and identities act correctly. With typed homsets this is a faithful concrete category. The object and arrow collections are sets: it is a countable union of set-sized categories plus a set of added function spaces. Nonempty old carriers supply at least one R->A_d arrow for every d, for example a constant function.

Give R and every old object the finite-subset ideal and take the full finite-pinned hierarchy over this enlarged category. Images of finite pins under arbitrary added functions are finite. The standard ideally-full C-model theorem therefore applies.

## 8. Old domains and terms are preserved

No outgoing arrow or compositional continuation from an old object is changed. By induction on simple types its profile domain is unchanged: individuals are unchanged; at a relational type the outgoing coordinates and the lower target domains used by those coordinates are unchanged. The finite-pin admission condition is unchanged as well.

Therefore every old closed-term interpretation, including every O_n, is identical to its interpretation in the finite component. The finite-depth separation at A_d survives verbatim.

At R the full profile hierarchy is built recursively by finite types from sets, so every typed domain is a set. Logical operations and lambda abstraction use their usual coordinatewise interpretation. Finite environments have a common finite pin; agreement on it makes the whole transported parameter environment equal at the common target, while quantifiers range over the FULL target domains. The added arrows do not require restricting old quantifiers to images. Thus the standard term-transport lemma applies:

    h(O_n^R) = O_n^V                 for h:R->V.

The hats are closed terms in C, so the same operations are preserved across components.

## 9. Every root step is distinct

Fix n. Suppose O_n^R=O_(n+1)^R as whole entities. Applying the admitted hat operation to this identity repeatedly gives O_k^R=O_(k+1)^R for every k>=n. This is ordinary substitution/congruence of identity, not necessitation of an optional assumption.

Choose d with 2d+1>=n, and any added arrow h:R->A_d. Transport of equality, together with the closed-term transport lemma, gives

    O_(2d+1)^(A_d)=O_(2d+2)^(A_d),

contrary to the retained old separation. Hence O_n^R != O_(n+1)^R for every external finite n.

The inequalities need only hold at R. Neither their necessity nor their truth at all old components is asserted; individual old components may stabilize at their finite depth.

## 10. The admitted hat-closed family

Define a profile F of type (tt)t at R by, for EVERY outgoing arrow h:R->V, including id_R,

    F_h = { O_n^V : n is an external natural number }.

This is a set of whole tt-entities in the domain of V. Duplicates, which may occur after the stabilization point of an old component, are immaterial. The profile is pinned by the empty set: if two arrows have the same codomain, their rows are the same displayed set regardless of their individual action. No requirement of covariance under a separate symmetry group is present in the full finite-pinned construction.

The tt-domains and the finite terms O_n are constructed before the domain of predicates of tt-entities. The full finite-pin rule then admits F at the next type; no internal enumeration is needed.

For additional landing verification, the shift of F along h:R->V has row at any k:V->W equal to {O_n^W:n in N}, so it is itself an empty-pinned admitted V profile. All type and transport obligations are met.

At R, F contains O_0=Box. If X is a current F-member, literal equality gives X=O_n^R for some n, so hat(X)=O_(n+1)^R is also a current F-member. Section 9 gives X != hat(X). Thus F witnesses exactly No Collapse

    exists F^(tt)t [F(Box) and
       forall X ((F(X)->F(hat X)) and (F(X)->X != hat X))].

Thus the model supplies both the finite inequalities and the admitted family required by No Collapse.

## 11. Current Actuality and the extensional boundary

The root-only proposition w, true at id_R and false at every old-target arrow, is empty-pinned and is the true singleton world atom at R. It witnesses current Actuality.

Indeed the construction demonstrates why the ordinary and extensional candidate sentences must be separated. No old arrow returns to R, so Diamond(w)=w. Therefore at R, for any current proposition p,

    O_1 p iff p:

the forward implication is T for O_1, and for the reverse use the true witness w in the definition of hat(Box), since w<=p whenever p is currently true. The standard increasing tower and T then make every O_n, n>=1, currently coextensive with truth at R. Their whole profiles can nevertheless differ in old components.

The model satisfies ordinary No Collapse but fails Extensional No Collapse: positive iterates are currently coextensive. The family clause is current rather than necessary; later old-world iterates can be fixed points.

## 12. The recorded incompatibility

No Collapse implies O_n≠O_(n+1) for each external finite n: its family
contains O_0 and induction through its closure gives every O_n.
The identity O_2=Box_5 therefore contradicts No Collapse, since the S5
operator Box_5 is a hat fixed point. The fixed-point fact follows from
the S5 hat calculus in *The Bounds of Possibility*, Appendix D.
Equivalently, \(\Box_5\) is the least S5 operator above \(\Box\), and
hatting an S5 operator returns that same operator.

The native [[necessary-five-implies-two-hat-necessity]] is exactly this
O_2=Box_5 identity. Existing implications bring each of the following
premises to it: [[necessary-two-hat-implies-nd-necessity]],
[[necessary-five-implies-nd-necessity]],
[[necessary-distinctness-preserving-collapse]],
[[necessary-truth-implies-two-hat-necessity]], [[necessary-actuality]],
and [[necessary-distinctness-necessary-t]]. One incompatibility record
therefore supplies all these consequences.

The different identity Box_5=Id, expressed by
[[necessary-truth-implies-five-necessity]], does not on its own identify
a finite iterate with Box_5. No incompatibility with that principle is
claimed here. Ordinary No Collapse also does not refute current Actuality,
as the construction explicitly demonstrates.

## Sources

- Cian Dorr, *No Collapse*, 14 October 2026, Logical Maps candidate register,
  No Collapse section, unpaginated: the sentence and consistency question.
- GPT-6 Astra, prompted by Daniel Kodsi, *Hat depth: exact return recursion
  and a two-level capacity test*, 30 October 2026, §§1 and 7;
  *Arbitrary finite hat depth: uniform finite-allocation proof*,
  30 October 2026, §§1–5; and *Finite-depth models to an admitted hat
  family*, 30 October 2026, §§2–6, all unpaginated: the recursion,
  uniform allocation and fanout-family construction reproduced here.
- Andrew Bacon and Cian Dorr, *Classicism*, draft of 16 May 2023,
  Appendix D, Definitions D.1–D.3 and Proposition D.4, pp. 73–74:
  ideally full C-model semantics. The earlier paired-individuals model
  supplies the finite-return method; its bounded collapse is prior.
- Cian Dorr, John Hawthorne, and Juhani Yli-Vakkuri,
  *The Bounds of Possibility*, Appendix D, pp. 400–409:
  the hat operation and its modal calculus.

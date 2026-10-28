# Under C5, necessary propositional completeness makes Functional Choice necessary

Over C, assume C5, full current Functional Choice, and necessary BC_t. Then full necessary Functional Choice follows. No new principle or uniform-observer premise is needed.

## 1. A selector which is stable for an algebraic reason

For every relational rho=sigma_1...sigma_n t, current FC supplies an admitted S:rho rho satisfying

    R != Bottom -> exists zbar (S(R)=delta_zbar and R[zbar] != Bottom).

Indeed a nonzero relation has a nonzero instance by Functionality. Its tuple-haecceity delta_zbar is an allowed relational output even when some tuple entries are individuals. Apply FC to the total relation assigning such singleton relations, with a fixed default at Bottom. The output is a relation, never an unsupported operation ending in e.

The displayed law uses only literal equalities/disequalities and typed quantifiers. Under C5, identities and their negations are endpoints, and BF/CBF collect endpoint formulas. Therefore this law of the supplied S is necessary. In particular the closed assertion that such an S exists is necessary. This uses no boxing of current FC.

## 2. These selectors plus current BC_t imply current FC

First use the selector at rho=tt, on the property P_p(q) expressing 0<q<p. Its nonzero instances are exactly its currently true instances, because P_p is endpoint-valued. The admitted guarded existential decodes S(P_p)'s unique proposition q. Thus one admitted operation strictly splits every nonzero nonatomic proposition.

The [strict-splitter theorem](c5-functional-choice-and-necessary-propositional-completeness-imply-necessary-functional-choice.html#strict-splitter-proof), §§1–7, shows that under C5+BC_t a true atomless interval cannot admit such an operation. Apply it to the complement of the join of all atoms. That join is the material existential of the endpoint atom predicate. If the join were false, its complement would be a true atomless interval, a contradiction. Hence some atom w is true. Equivalently, Actuality holds: p is currently true exactly when w<=p.

For a currently serial relation R:sigma tau t, normalize it to the endpoint relation

    R*(x,y) := (w <= R(x,y)).

It has the same current extension. Apply the supplied singleton selector at the relational type tau t to every property R*_x. Its output defines an endpoint, total, single-valued graph G(x,y) currently contained in R. For relational tau=ubar t, the lambda term

    f(x)[ubar] := exists y (G(x,y) and y[ubar])

is literally the unique selected y: at its singleton guard the coefficient is Top, elsewhere Bottom; BF gives the guarded join and Functionality gives whole relation identity. Thus f witnesses current FC. The argument for each fixed FC instance uses only finitely many selector instances.

## 3. Apply the discharged theorem necessarily

Section 2 is a C theorem from the displayed finitely many selector laws, C5 and BC_t. Necessitate that discharged theorem. Section 1 supplies the necessary selector laws, C5 is stable, and necessary BC_t was an explicit premise. Modus ponens gives each necessary FC instance. No optional current premise has been necessitated.

The reverse implications from necessary FC to current FC, C5 and necessary BC_t are already recorded. Thus the added arrow completes the characterization without duplicate reverse arrows.

Direct sources: OpenAI Codex, prompted by Daniel Kodsi, *Uniform Boolean and logical observation: two levels of Choice*, 28 October 2026, §§1–5 (corrected endpoint-finiteness version); *Rigid algebra supplies uniform Choice among possible arguments*, same date, §§1–4,6,8; and the linked strict-splitter proof of 25 October 2026. All are unpaginated. This note extracts their direct native-principle consequence; it uses neither the greedy Boolean-ultrafilter construction nor a new principle node. Ordinary mathematical proof; no Lean certification is claimed.


<a id="strict-splitter-proof"></a>

## Appendix: strict-splitter proof

The supporting proof below retains its original internal section numbering.

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026. Direct source for the internal argument: `misc`, this note, §§1–7, unpaginated. The motivating reconstruction argument is Joel David Hamkins's [MathOverflow answer of 2 July 2018](https://mathoverflow.net/questions/303902/boolean-ultrapower-of-vg-by-g/304115), final proof paragraph. No literature-priority claim, Lean certificate, or database change is made. The construction agent independently reviewed the complete proof, proposed the two-code simplification in §§4–5, and accepted the rewritten proof after rereading it. This is independent AI review, not human review or formal verification.

## 1. Exact statement

Work in the fixed finitary relational theory C. Write 0 and 1 for Bottom and Top, and use the algebraic Boolean order. Assume C5 and **only propositional Boolean Completeness BC_t**, both at their stated scopes. Let h be a proposition and let s:tt be an admitted operation satisfying

\[
\forall p\,[0<p\le h\ \longrightarrow\ 0<s(p)<p].
\tag{1}
\]

Then h is currently false. Equivalently,

\[
\boxed{C5+BC_t\ \vdash\
\forall h\,\forall s^{tt}
\bigl[(\forall p(0<p\le h\to0<s(p)<p))\to\neg h\bigr].}
\tag{2}
\]

Thus a **true** atomless interval cannot have an admitted strict splitting operation under these premises. Atomlessness alone does not supply that operation, and Relational Choice is not being used to assert its existence. No crisp wellorder of all propositions, BC_tt, OS, or RC is a premise of (2).

A useful Actuality corollary is obtained if an admitted s splits every nonzero nonatomic proposition: under C5+BC_t this implies Actuality. The restriction to an admitted operation is essential to the proof below.

The argument has two towers. BC_t builds a possibly noncrisp, current truth-guided tower from a functional **relation**. A single Boolean element then codes its choices. C5 builds a second, crisp tower from the decoded **operation**. Comparing the towers makes a false limit into a crisp-indexed meet of truths.

## 2. Current canonical chains for a functional relation

We use the represented canonical-chain lemma proved in [Relational Choice and Boolean Completeness imply Actuality, Appendix D](boolean-completeness-and-modalized-relational-choice-imply-necessary-transversal-choice.html#canonical-chain-lemma). Its hypotheses concern a represented antisymmetric partial order with all represented chain suprema and a represented total progressive functional relation. Its conclusion includes a canonical internally wellordered chain ending at a fixed point. It uses neither Choice nor an operation representing the functional relation.

For precision, here is its order-dual form on the Boolean interval [0,h]. Suppose F is a current total functional relation there, with F(p)≤p. Function notation abbreviates its unique **current** graph value. A predicate C is an F-chain when:

1. its current members form a chain in [0,h], internally wellordered by the reverse Boolean order (every admitted nonempty subproperty has a Boolean-greatest member);
2. each member p is the actual Boolean infimum, within [0,h], of
   \[
   \{F(q):Cq\text{ and }p<q\}.
   \tag{3}
   \]

The infimum of the empty family in the interval is h. The singleton {h} is an F-chain. Any two F-chains compare by initial segment: form their common part on which strict predecessor extensions agree; if both have a first disagreement, (3) gives the same actual infimum to both first new elements. Only uniqueness of an actual infimum is used, not equality of coextensive family codes.

Their admitted union

\[
M(p):=\exists C\,[C\text{ is an F-chain}\land Cp]
\tag{4}
\]

is itself an F-chain and contains every F-chain. BC_t supplies its actual infimum m. Appending that infimum, and then F(m) if necessary, proves m∈M and F(m)=m. These are exactly the comparison, union, and endpoint arguments of the cited appendix, with order reversed.

We will also use two immediate consequences. If p∈M, its initial segment through p is an F-chain; adjoining F(p) shows F(p)∈M. If F(p)<p, this is the immediate next member. Moreover, for q<p in M, conformity at q gives q≤F(p). A fixed point in M must be terminal: otherwise the first member after it has, by (3), that same fixed point as its defining infimum.

All families here are admitted predicates of propositions. BC_t is used for their **current extensions**, not identified with a material quantifier.

## 3. A stronger crisp-chain lemma for an operation

The comparison in §6 needs a crisp chain which is fully wellordered with respect to **all admitted current subproperties**. The crisp-subproperty version in the earlier Strict local sections note, §§3–4 is not by itself sufficient. We therefore prove the needed stronger version explicitly.

**Lemma.** Under C5, let g:tt be an admitted operation such that, throughout [0,h], g(p)≤p, and let these interval and progress conditions be necessary. There is an admitted crisp g-chain D, with full current reverse wellordering and conformity (3), whose terminal member is a fixed point of g. In fact D necessarily has those chain properties. No BC premise is needed for this lemma.

Here crisp means that each membership coefficient is literally 0 or 1. C5 makes identity assertions crisp, supplies Barcan, and makes Boolean combinations and quantified formulas of crisp assertions crisp. For any crisp X:tt the term

\[
j_X:=h\land\forall p\,[Xp\to g(p)]
\tag{5}
\]

is the actual algebraic infimum, within [0,h], of the current g-values at X-members. Indeed every current member has coefficient 1, and every nonmember coefficient 0. Universal instantiation gives the lower bounds. Conversely, if z≤h bounds all current g-values from below, the endpoint coefficients and Barcan collect those bounds into z≤j_X. This argument is valid at every world under C5.

For a code C:tt define Strong(C) to assert:

* C is crisp;
* **necessarily**, its members are a chain in [0,h], fully wellordered in the reverse order against all admitted subproperties, and every p∈C is the algebraic infimum of the g-values at its strict predecessors.

This is a finite formula at existing types. Crispness is a quantified identity condition, and the necessary clause is endpoint-valued under C5. Thus Strong(C) is crisp. The singleton of h satisfies Strong: its assertions hold uniformly, with the empty predecessor infimum h.

Define

\[
D(p):=\exists C^{tt}\,[\operatorname{Strong}(C)\land Cp].
\tag{6}
\]

The coefficients in (6) are crisp, so D is crisp.

We verify its necessary chain assertions **uniformly at an arbitrary world**. Every current Strong-member there is a full g-chain there. The ordinary comparison argument of §2 therefore applies at that world, including to the possibly noncrisp differences of chain properties. It makes their union a chain. For any admitted nonempty current subproperty X of D, choose x∈X and a Strong-chain C containing x. Full wellordering of C gives the first member of X∩C. Comparing C with each Strong-chain containing another X-member shows that this member is first in all of X. Thus the union is fully wellordered, not merely wellordered for crisp X. Finally, all predecessors of a union member already occur in one Strong-chain containing it, so its infimum clause transfers by uniqueness of the actual infimum.

This argument uses only the necessary hypotheses built into Strong and the C5 crisp-family bound calculation (5). It consequently proves the union's chain assertions at every world, hence their necessity. No instance of current BC_t is used or necessitated. Therefore Strong(D).

Let u=h∧∀p(Dp→p), the actual infimum of D at every world by the same crisp-family argument. If u∉D, D has no last member. At every world, for each p∈D there is q∈D with u≤q<p; conformity at q gives q≤g(p). Together with g(p)≤p, this shows that the infima of D and g[D] coincide. Hence appending u preserves conformity. Appending a last element preserves full wellordering at every world: a nonempty subproperty either meets D, when D supplies its first member, or consists only of the appended point. The appended family is crisp. These facts give Strong(D∪{u}), contradicting the defining union (6). Thus u∈D.

If g(u)<u, appending g(u) likewise preserves the necessary full wellordering and conformity: g(u) is the least g-value of D, since conformity at u puts every earlier g-value above u. Again (6) gives a contradiction. Therefore g(u)=u.

The case distinctions used here are identity/order assertions involving admitted terms; under C5 they are stable. The append arguments are uniform proofs from necessary premises, not a boxing of optional current wellordering or completeness assumptions. This proves the lemma.

In particular, if g(0)=0 and 0<g(p)<p for every positive p≤h, the terminal member of D is 0.

## 4. The truth-guided descent and two disjoint codes

Assume h is true and s satisfies (1). Define the represented functional relation F on [0,h] as follows:

* if p is currently false, F(p)=p;
* if p is currently true and s(p) is true, F(p)=s(p);
* if p is currently true and s(p) is false, F(p)=p∧¬s(p).

An explicit graph is obtained by these three Boolean cases and identity to the displayed outputs. When p is true, exactly one of its two disjoint nonzero children is true. Thus F is total, single-valued, deflationary, and strictly deflationary at each true p. It is a relation; material case selection is not asserted to give an operation with these literal outputs.

Apply §2 using BC_t. Obtain M with terminal fixed point m. Since no true member is fixed, m is false. Since a fixed point in M is terminal, every other M-member is true. For each true p∈M put

\[
d_p:=p\land\neg F(p).
\tag{7}
\]

These are represented through the functional graph of F. Each is nonzero. They are pairwise disjoint: if p>q are in M, then q≤F(p), so d_q≤F(p) whereas d_p∧F(p)=0.

Divide these increments according to which child was discarded. Use BC_t to obtain the two actual joins

\[
b_L:=\bigvee\{s(p):Mp\land p\land F(p)=(p\land\neg s(p))\},
\qquad
b_R:=\bigvee\{p\land\neg s(p):Mp\land p\land F(p)=s(p)\}.
\tag{8}
\]

Thus b_L joins the discarded left children, and b_R joins the discarded right children. Both are suprema of represented current images, not material existential unions.

Every joinand is one of the d_p, and no increment belongs to both families. Pairwise disjointness therefore gives

\[
b_L\land b_R=0.
\tag{9}
\]

Explicitly, every right joinand is disjoint from each left joinand, so its complement bounds the entire left family. Hence it is disjoint from b_L. The complement of b_L then bounds the right family, yielding (9). It follows that at least one of b_L,b_R is currently false. No assertion that either arbitrary join preserves current falsity is used.

## 5. A crisp decoder for the chosen branch

First suppose b_L is false. For every true p∈M,

\[
F(p)=p\land\neg s(p)
\quad\Longleftrightarrow\quad s(p)\le b_L.
\tag{11}
\]

If the right child was chosen, s(p) is a joinand of b_L. Otherwise s(p)=F(p) is true, and a true proposition cannot lie below the false b_L. This proves both directions.

Define an admitted operation g:tt by g(0)=0 and, for 0<p≤h,

\[
g(p)=
\begin{cases}
p\land\neg s(p),&s(p)\le b_L,\\
s(p),&s(p)\nleq b_L.
\end{cases}
\tag{12}
\]

If instead b_L is true, (9) makes b_R false. Use the symmetric operation: for positive p≤h let g(p)=s(p) when p∧¬s(p)≤b_R, and let g(p)=p∧¬s(p) otherwise. The same reasoning shows it selects exactly the true child on M. In either case put g(0)=0 and let g(p)=0 outside [0,h].

Each case gives an actual lambda term: multiply its two displayed outputs by their identity-based case coefficients and join them. C5 makes these coefficients literally 0 or 1, so the term has exactly the stated **entity** outputs. The finite case distinction between b_L and b_R is ordinary classical proof by cases, not an assumed uniform operation choosing a false code. In either case g maps [0,h] to itself, is strictly deflationary on its positive members, and

\[
g(p)=F(p)\qquad(Mp\land p).
\tag{13}
\]

The strict splitting assertion (1), the algebraic case comparisons, and all interval/progress assertions for g are quantified identity formulas. Under C5 they are necessary when true. Thus g meets every hypothesis of §3, without boxing any truth-guided clause or BC_t.

## 6. Comparing the two towers

Apply §3 to g. Obtain a crisp, necessarily fully wellordered g-chain D, ending at 0.

Compare M and D using their common initial segment I, defined by common membership and equality of predecessor **extensions**. If m belongs to I, M is already an initial segment of D because m is M's terminal member. Otherwise every I-member is a true M-member, so (13) makes F and g agree on I.

If both M\I and D\I are nonempty, their full current wellorderings supply respective first members p,q. Both predecessor families have extension I. Their defining infima are therefore identical, since F and g agree on I. Hence p=q, which puts that point in I, a contradiction. It follows that one tower is an initial segment of the other. D cannot be a proper initial segment of M: D already contains 0, and no member of [0,h] lies below 0. Therefore M is an initial segment of D, including m.

The predicate

\[
I_m(p):=Dp\land m<p
\tag{14}
\]

is crisp. Its current members are exactly the strict predecessors of m in M, all of which are true. For each such p, (13) says g(p)=F(p), and F(p) is true. Therefore

\[
h\land\forall p\,[I_m(p)\to g(p)]
\tag{15}
\]

is currently true, by ordinary classical quantifier truth and truth of h. Since I_m is crisp, (15) is its actual algebraic infimum of g-values. Conformity of D at m identifies that infimum with m. Thus m is true, contradicting its construction as a false fixed point. This proves (2).

The final step does not assert that arbitrary current meets of truths are true. The reconstructed predecessor predicate is already crisp, which is exactly what makes its material universal quantifier the relevant actual algebraic meet.

## 7. Actuality corollaries and scope

Under C5, Atom(p) is crisp. Hence

\[
z:=\exists p\,[\operatorname{Atom}(p)\land p]
\]

is the algebraic join of the atoms. If z is true, its existential witness is a true atom and therefore an Actuality witness. If z is false, h=¬z is true and [0,h] is atomless.

Consequently, if an admitted s splits every nonzero nonatomic proposition, it satisfies (1) on this latter interval. The theorem rules that case out, so Actuality follows. More generally it suffices to have an admitted strict splitter on the atomless remainder whenever that remainder is true.

**Crisp-wellorder corollary.** Suppose W is an admitted crisp strict linear order on all proposition entities, and every nonempty admitted crisp property has a W-least member. Define

\[
L(p,q):=(0<q<p)\land
\forall r\,[0<r<p\to\neg W(r,q)],
\qquad
s_W(p):=\exists q\,[L(p,q)\land q].
\tag{16}
\]

For a nonzero nonatomic p, its proper-positive-parts property is nonempty and crisp. The assumed leastness supplies exactly one q with L(p,q). The guard L is crisp, so its coefficient at that q is literally 1 and its coefficients elsewhere are 0. The crisp-family join calculation therefore gives the **literal identity** s_W(p)=q. At an atom, or at 0, there is no such q and the same calculation gives s_W(p)=0. Thus s_W is an admitted strict splitter on every nonzero nonatomic proposition. The preceding corollary gives

\[
\boxed{C5+BC_t+\text{an admitted crisp wellorder of propositions}
\ \Longrightarrow\ \operatorname{Actuality}.}
\tag{17}
\]

Only leastness for the crisp proper-parts properties is needed in this application of W. This is an alternative proof of the earlier rigid-wellorder theorem, with the same stated crisp-subproperty scope, avoiding its regular-open product construction. An ordinary noncrisp current wellorder does not make L crisp and does not justify the literal-output calculation in (16).

If BC_t is assumed **necessary**, (2) also implies that any interval admitting a strict splitter is zero: (1) is necessary under C5, and the theorem can be applied uniformly to obtain □¬h. This boxed-completeness corollary keeps its additional premise explicit.

The motivating external proof reconstructs a generic descent from a Boolean code and a fixed splitting function. The internal proof above forms both directional codes and uses a false one, avoiding any assumption that a join of currently false differences is false. It replaces external ordinals/recursion by the two displayed represented canonical-chain constructions. The stronger necessary full-wellordering lemma in §3 is supplied here because the earlier crisp-subproperty lemma alone does not justify §6.

Nothing here derives a strict splitting operation from RC, OS, or an ordinary current wellorder. Those are separate extraction questions.

## Integration scope

This is the existing source proof, retained at referee detail with its two code construction and full-wellordering distinction. Only local links and the closing cross-reference were adapted for integration; the original research source remains unchanged. OpenAI Codex, prompted by Daniel Kodsi independently reread Sections 1–7 and the separately supplied represented canonical-chain lemma on 28 October 2026. The motivating MathOverflow comparison is not used as a proof certificate. No historical priority, human review or Lean certification is added.

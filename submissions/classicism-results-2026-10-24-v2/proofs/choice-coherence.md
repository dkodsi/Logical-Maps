# Coherent histories and finite cell ambiguity

Original mathematical argument, direct source misc; unpaginated.

## 1. Exact framework and recorded status

The target is full all-type **unboxed Relational Choice implies full all-type unboxed Transversal Choice** over the original finitary relational Classicism C. Types include e; arrows ending in e are not introduced. C's Logical Equivalence rule retains its H-theoremhood condition. Actual coextension never licenses entity identity by itself. No Actuality, BC, ND, BF, C5, infinitary language, or optional necessitation is added.

A fresh `scripts.pmap.load_topic('classicism')` / proved-only `Engine` query used RC in the premise set and only the topic's fixed background. For RC to TC, `entails` returned false, `excludes` returned none, and `separates` returned no model. These are three different absences of recorded evidence, not claims of mathematical independence or literature openness. The same query confirms the recorded RC + Actuality to TC implication. The research theorem RC_(t,t) + BC_tt to Actuality is available from the earlier work; it has not been inferred from this database query.

Completed inputs were used rather than re-proved: finite rigidification and finite-cell TC in `research/2026-10-22/notes/quotient-abstraction-lane.md`, §13; quotient-compatible Bourbaki–Witt in `notes/rc-alone-fixedpoint-obstruction.md`, §6; finite-cell selector ambiguity in `followup/choice-transversal.md`; and exact history limits plus the whole-history-code boundary in `followup/choice-compatible-history-limits.md`, §§7–8. All these abbreviated research paths are under `research/2026-10-22/`.

## 2. A sharper coherence criterion

Fix an actual equivalence R on an admitted type σ. Put ρ = σt and θ = ρσt. Write TC(R) for existence of a transversal of this particular R. The only choice instances used are RC_(ρ,σ) and RC_(θ,σ).

The new history objects P:θ have rows P[F] that are partial transversals of classes missed by F. Rows are actually identical in extension at coextensive F. Thus

    h_P(F) = F ∪ P[F]

is progressive and respects actual coextension. Its canonical trajectory Run_P has terminal partial transversal L(P), by the completed canonical-chain argument. A good history has nonempty rows exactly at the strict members of this trajectory. Order good histories by extension that **freezes every already nonempty row**. Mutual extension is actual coextension of the whole graph, not entity equality.

Represented comparable families have exact suprema: take the material union of their graphs. Row freezing makes every occupied union row equal to an old row, so all old trajectory equations transfer. The union of old trajectories, together with its possible terminal class, is the entire new trajectory. The new terminal is exactly the union of old terminals, and goodness holds in both directions. This addresses the potentially circular limit step before applying a fixed-point argument.

Call P active when it is good and L(P) is not full. RC_(θ,σ) supplies a successor chooser K(P,a) selecting one point missed by L(P) at every active P. Across codes of one whole graph, define

    A_P(a)   := ∃Q(Q is graph-coextensive with P ∧ K(Q,a)),
    A_P,x(a) := R(x,a) ∧ A_P(a).

The new condition is

    for every active P, some A_P,x is nonempty and internally Frege-finite.

For each nonempty finite A_P,x, take its unique rigid representative and apply one fixed membership selector. Include **all** the resulting points in a batch B_P. Same-cell candidates use the same rigid representative entity, so B_P is a partial transversal; coextensive histories give coextensive batches. The condition makes the batch nonempty.

The admitted successor is given everywhere by

    Ψ(P)(F,y) := P(F,y) ∨
                [active(P) ∧ F≈L(P) ∧ B_P(y)].

For an active good P it freezes old rows, defines the previously empty terminal row, and appends precisely one new trajectory class L(P) ∪ B_P. It remains good, is strictly progressive, and respects whole-graph coextension. Inactive good histories are fixed modulo coextension. Quotient-compatible Bourbaki–Witt now gives a nonactive history, whose terminal is a transversal.

Conversely, given any transversal T of R, RC_(θ,σ) can select a T-member in a missed cell at each active history. Then A_P is contained in T: each nonempty A_P,x is a singleton. Consequently the precise local result is

    C + RC_(ρ,σ) + RC_(θ,σ) proves
    TC(R) iff some successor chooser K satisfies the displayed condition.

This is a weaker requirement on an individual chooser than finiteness of its whole ambiguity range, formulated for the new batch-history domain. For identity R on ℕ, every cell ambiguity is at most singleton even when the whole ambiguity range is infinite. For universal R on ℕ, a full two-world model permits a chooser whose other-world code dependence makes the sole ambiguity cell infinite. Such examples show that arbitrary witnesses need not satisfy the condition; they are not RC/TC separators.

The exact remaining positive obligation is to derive existence of a suitable K from RC. Equivalently, under these local RC instances, a failed TC(R) would force **every K** to have an active history at which **every nonempty cell ambiguity is internally nonfinite**. The criterion transports the established finite-cell mechanism to the narrower whole-history-code boundary; it is not an independent derivation of coherence from RC.

## 3. A stronger obstruction for supported countermodels

Let G act by automorphisms of an entire interpreted C structure, preserving the designated evaluation. Suppose it preserves the actual graph of a membership selector S at (σt,σ). It is enough that the graph be invariant; S need not be fixed as an entity.

**Finite-code-orbit theorem.** If a nonempty G-invariant actual subset X of D_σ has a property code with finite G-orbit, then X contains a G-fixed member.

Indeed, take the finite Boolean union J of the orbit codes. All have extension X. G permutes the disjuncts, and unconditional H permutation identities identify the resulting lambda abstractions literally. Thus J is a fixed entity with extension X. If S selects y from J, equivariance and actual graph invariance imply that S also selects gy from J. Functionality gives gy=y.

There is also an internal version: a nonempty G-invariant represented family of codes for X cannot be internally Frege-finite when X has no fixed member. Rigidify that finite family at the property-code type. Its unique rigid representative is literally G-fixed. Taking the existential union of its members yields a fixed code J for X, and the same selector argument applies. No external standardness of finite cardinalities is used.

Thus a symmetry-based separator protecting a fixed-point-free cell must keep **every code of that cell aperiodic** under the relevant selector-preserving shift, and must avoid every nonempty invariant internally finite represented envelope of such codes. Infinite cells alone are insufficient. These restrictions sharpen the earlier finite-orbit test on individuals without assuming a second selector at the property-code output type or full higher-order domains.

## 4. Direct application to the history-code boundary

The same argument applies to the successor chooser K above, even though K is not a membership selector on arbitrary properties.

Suppose G fixes R as an entity, preserves K's actual graph, and P is an active good batch history whose actual whole graph is G-invariant. Suppose no point missed by L(P) is G-fixed. Then no code Q graph-coextensive with P can have finite G-orbit, and there can be no nonempty represented G-invariant internally finite family of such codes.

For a finite orbit, its pointwise Boolean union J:θ is a literally fixed code of the same graph. Goodness, activity, and L(J)≈L(P) are invariant under whole-graph coextension, so K selects a missed point at J. Invariance and functionality make that point G-fixed, contradiction. For the internal-family version, rigidify the family at type θ and form J(F,y) := ∃Q(B*Q ∧ Q(F,y)); this is again a literally fixed code of the same active history. This gives a direct link between the two new restrictions. It does not assert that every model has suitable automorphisms, or that any external orbit is represented.

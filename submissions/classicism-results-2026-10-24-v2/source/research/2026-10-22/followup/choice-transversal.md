# Relational Choice alone: one finite ambiguity class at each stage

22 October 2026. One bounded follow-up by OpenAI Codex. Ordinary mathematical argument; no human check, Lean verification, independence result, or literature-novelty claim. The frozen `notes/` archive is unchanged.

## Scope and result

The assignment is the **unboxed all-type** implication Relational Choice ⇒ Transversal Choice over the original fixed C. It remains unresolved here. No Boolean Completeness, Plenitude, Actuality, ND, language extension, or optional necessitation is used below.

The focused attempt weakens the saved coherence condition: at each incomplete partial transversal, require only **one** missed class with nonempty internally finite ambiguity. Other classes may have infinitely many conflicting candidates. This condition suffices, but the attempt to obtain it from an arbitrary RC selector, even by finitely repairing that selector, fails explicitly.

Fix an admitted type σ, including e, put ρ=σt, and fix an actual equivalence R on σ. Assume only the local instance RC_(ρ,σ). Write

    F≈G        := ∀z(Fz↔Gz),
    Partial(F) := ∀y z(Fy∧Fz∧Ryz → y=z),
    Full(F)    := ∀x∃y(Rxy∧Fy),
    Miss(F,y)  := ¬∃z(Ryz∧Fz).

Here Partial is wholly actual, unlike the pointwise-boxed predicate in the saved guarded-operation proof. RC supplies an actually total, entity-functional graph S contained in

    U(F,y) := (¬Full(F) → Miss(F,y)).

Define the admitted ambiguity property

    M(F,x)(y) := Rxy ∧ ∃G(G≈F ∧ S(G,y)).

Let Fin mean the existing internal Frege-finiteness predicate. The condition tested is

    Escape(S,R) := ∀F[Partial(F)∧¬Full(F) →
                      ∃x(∃y M(F,x)(y) ∧ Fin(M(F,x)))].

**Proved reduction, with exactly the displayed local RC premise:**

    TC(R) ⇔ ∃S[Functional(S) ∧ S⊆U ∧ Escape(S,R)].

TC(R) means existence of a transversal for this particular R. This is a new sufficient-condition/obstruction calculation, not a proof that RC supplies Escape.

## Proof of sufficiency

Use two previously checked bare-C lemmas from the frozen notes: internally finite properties have unique rigid coextensive representatives (`quotient-abstraction-lane.md`, §13.1); and the quotient-compatible Bourbaki–Witt theorem for represented comparable families (`rc-alone-fixedpoint-obstruction.md`, §6). The finite-representative lemma is internal Frege induction: bottom and haecceities are rigid, binary unions preserve rigidity, and coextensive rigid properties are identical. It requires neither standard finiteness nor ND.

Apply RC_(ρ,σ) once more to obtain a membership selector Q: on each nonempty property K it selects exactly one K-member. This is a second use of the same instance, not a stronger choice premise.

Define h(F) by adjoining to F the Q-choice from the unique rigid representative of **every nonempty finite** M(F,x), provided F is not full. Explicitly,

    h(F)(y) := Fy ∨ [¬Full(F) ∧ ∃x K(
                 (∃z M(F,x)(z)) ∧ Fin(M(F,x)) ∧ Rigid(K)
                 ∧ K≈M(F,x) ∧ Q(K,y))].

This is an admitted lambda operation ρ→ρ. No operation assembling the rigid representatives is asserted.

For nonfull F, every M-candidate lies in a class missed by F: its witnessing G is coextensive with F, so S's containment gives this. If x and x′ are R-equivalent, M(F,x) and M(F,x′) are coextensive. Their rigid representatives, when finite and nonempty, are therefore **identical**. Q then selects the same point. Consequently h(F) is a partial transversal whenever F is, and F is actually included in h(F). For full F, h(F)≈F by definition. Escape makes the inclusion strict at every nonfull partial F.

If F≈F′, their M-properties are coextensive class by class. Finiteness and nonemptiness are coextension-invariant; unique rigid representatives and functionality of Q give h(F)≈h(F′). This proves output congruence rather than assuming it. Crucially it does not identify h(F) and h(F′) as entities.

Ordinary partial transversals under actual inclusion form a represented preorder whose comparable families have material-union suprema, including the empty family. Their unions remain partial because each potentially conflicting pair occurs together in one of two comparable members. The saved quotient-compatible fixed-point theorem now applies to the graph of h. It supplies F≈h(F); strictness forces Full(F), proving TC(R). There is no algebraic-join claim or Boolean Completeness invocation.

## Reverse direction and sharper separator requirement

Given a transversal T, apply the same RC instance to choose a member of T in a missed class whenever F is not full, and an arbitrary point otherwise. This relation is serial because T meets every R-class. For nonfull F, each M(F,x) is a subset of T∩[x]_R and hence has at most one member. The actual output at F supplies a nonempty such M, which is internally singleton and therefore finite. Thus Escape holds.

The contrapositive of sufficiency gives a simultaneous obstruction stronger in form than requiring merely one infinite ambiguity class somewhere:

> If RC_(ρ,σ) holds but R has no transversal, then **for every** missed-point selector S there is a nonfull partial transversal F at which **every nonempty** M(F,x) is internally nonfinite.

There is at least one nonempty M at this F, witnessed by S's output at F, so this obstruction is not vacuous.

## Why arbitrary selection and finite repairs do not establish Escape

Consider the ordinary full two-world S5 model with individuals N, worlds w,v, and actual world w, in ZFC. Set R to the universal relation. This is a C model with all-type RC and TC; it is used only to test the proposed selector normalization.

An individual property F is determined by its extensions F_w,F_v. Define an admitted rigid functional graph S by choosing n when

    F_v={2n,2m+1} for some m∈N,

and choosing 0 otherwise. The pair has a unique even member, so n is unambiguous. All such graphs are admitted in the full model. For universal R the relation U above is always true: if F is nonfull it is empty, and every point is missed. Thus S is a valid RC witness for U.

Take F_w empty. For every n and every m, there is a distinct coextensive code G with G_w empty and G_v={2n,2m+1}, at which S chooses n. Therefore every M(F,x) has actual extension N, so Escape fails at F. In this full model internal Frege finiteness agrees with ordinary finite cardinality: all actual predicates on the cardinality domain are represented, so the least inductive extension consists exactly of the standard successor iterates, which count the ordinary finite sets.

Changing S's values at finitely many input entities cannot fix this failure. For each n, infinitely many of the displayed G-codes remain unchanged; thus M(F,x) still contains every n. Here “finite repairs” means finitely many input codes at the evaluation point, not an arbitrary modification defined by one formula.

This example refutes only automatic Escape for an arbitrary witness and its finite-code repair. It does **not** refute existence of a suitable S: universal R already has singleton transversals and admits constant suitable selectors.

## Stopping point

The focused attempt proves the reduction and the simultaneous all-infinite-ambiguity obstruction. It does not produce the existentially suitable selector from RC. The simplest proposed route through arbitrary RC witnesses and finite repairs fails even in a model where TC holds. Further work would require a genuinely global selection construction or a countermodel satisfying all RC instances; neither follows from the reduction. I stopped at this obstacle rather than repeat the archived support/Henkin failures or assume coherent limits.

Source boundary: definitions and statuses were checked in the topic guide, `topic.yaml`, `background.md`, and the Relational Choice/Transversal Choice records. The mathematical inputs are the frozen notes cited above and `rc-guarded-progressive-operation.md`; the current argument is not attributed to their published background sources. No database record or generated artifact was changed.

## Further proof pass: improving selectors and taking a controlled limit

22 October 2026, later pass. Original ordinary arguments by OpenAI Codex; not human checked or formalized. The earlier stopping point is historical. The target remains C plus unboxed RC alone. This section proves positive intermediate statements, rather than assuming that the existence of a suitable selector follows from failure of a particular repair.

### Scope check and a canonical partial transversal

Keep R, ρ=σt, U, M, Fin and the fixed membership selector Q from above. Write θ=ρσt for the type of missed-point graphs, and Valid(S) for actual functionality and containment S⊆U. If σ is empty the transversal question is trivial; otherwise choose a default d:σ. The local RC_(ρ,σ) instance supplies both an initial valid graph and Q.

For **every** valid S, the operation h_S displayed above is progressive on actual partial transversals, preserves that property, and respects actual coextension modulo actual coextension. Escape is needed only for strictness at every nonfull input. Thus the saved quotient-compatible Bourbaki–Witt argument applies to h_S even when Escape fails.

More precisely, let Run_S be the union of all saturated h_S-chains from `notes/rc-alone-fixedpoint-obstruction.md`, §6. A chain C is saturated under actual coextension, comparable by actual inclusion, internally well ordered modulo coextension, and each F∈C is a supremum of the h_S-images of its strict predecessors. All these are admitted formulas. Define the operation

    L(S)(y) := ∃F(Run_S(F) ∧ Fy).

The saved comparison and maximal-chain proof gives, for every valid S:

* Run_S is itself an h_S-chain and has a greatest coextension class;
* L(S) belongs to that class and is a partial transversal;
* h_S(L(S))≈L(S).

L is an admitted operation θ→ρ. It is not an entity-valued canonicalizer of actual extensions: only output **coextension** is asserted below.

If S and T have the same actual graph extension, their M-properties are coextensive, their h-values are coextensive, and exactly the same chain entities satisfy the h-chain definition. Therefore L(S)≈L(T). In particular, the necessary-totality/functionality normalization in `choice-transversal-symmetry.md`, §1, preserves every actual ambiguity range, Escape, and L. It does not improve Escape by itself. Its proof necessitates only an unconditional H theorem and uses bare-C CBF; containment remains actual.

### A strict selector-improvement operation from one higher RC instance

**Theorem.** Assume RC_(ρ,σ) and RC_(θ,σ). There are an initial valid selector and an admitted operation Φ:θ→θ such that, for every valid S with nonfull L(S),

    Valid(Φ(S)),       L(S) ⊊ L(Φ(S)).

Moreover, Run_S is an initial segment of Run_Φ(S). One may make every output Φ(S) necessarily total and functional by the safe normalization, without changing these actual conclusions.

First fix any valid S with F=L(S) nonfull, and any a with Miss(F,a). Patch its **entire actual coextension class**, not finitely many input entities:

    Patch(S,F,a)(G,y) := (G≈F ∧ y=a) ∨ (¬G≈F ∧ S(G,y)).

This is a valid graph. For inputs G not coextensive with F, the ambiguity ranges and h-values are unchanged. On the class of F, every ambiguity range is either empty or the singleton {a}; hence

    h_Patch(G) ≈ G ∪ {a}       when G≈F.

The old Run_S is still an h_Patch-chain: its defining supremum condition at each member uses only strict predecessors, none of which is coextensive with its greatest member F. The old and new h-values therefore agree in extension wherever that condition consults them.

Put V=F∪{a}. Every h_Patch-output from a strict predecessor of F lies below F, by the old chain condition at F. Every output from the terminal class is coextensive with V. Thus V is the supremum of h_Patch[Run_S]. Adjoining its whole coextension class produces another h_Patch-chain. Consequently V⊆L(Patch(S,F,a)), proving strict inclusion over F. Chain comparison also makes the old Run_S an initial segment of the new trajectory.

For uniformity, apply RC_(θ,σ) to the serial relation requiring a missed point of L(S) when Valid(S) and L(S) is nonfull, and the default d otherwise. Let K(S,a) be the resulting actual functional graph. Define Φ(S) by the same patch formula, using K(S,y) in place of y=a on the terminal class, with the patch active only in the valid, nonfull case. This is a genuine lambda operation with relational output θ, not a claimed operation selecting individual entities. Its actual values have exactly the patch behavior just proved. Optional postcomposition by the safe normalization preserves the conclusions.

This establishes an RC-derived improvement step. It neither assumes Escape nor merely reformulates TC: each incomplete canonical partial transversal can be strictly enlarged by an explicit selector construction.

### Why independently choosing locally good graphs adds no diagonal constraint

There is an exact limitation to the simpler higher-type choice proposal. Fix a baseline valid B. For each input F, consider graphs which are valid globally and constant on the entire coextension class of F. Such graphs always exist by Patch(B,F,a), with a satisfying U(F,a).

Let S₀ be **any** valid missed-point selector. The represented graph family

    H(F,T) := ∃a(S₀(F,a) ∧ T=Patch(B,F,a))

is actually total and functional as a relation from inputs to candidate graphs. Every chosen T meets the stated local coherence requirement. Yet its diagonal

    D(F,y) := ∃T(H(F,T) ∧ T(F,y))

is exactly S₀ in actual extension. Postnormalizing each Patch to necessary totality/functionality leaves this conclusion unchanged. Thus the possible diagonals of these perfectly coherent local choices include **every** ordinary RC witness. Local graph selection alone imposes no cross-input compatibility or finite-ambiguity condition. This does not rule out a deliberately constrained global selection; it identifies what the local candidate condition fails to constrain.

### A represented limit for one deterministic successor history

There is further positive progress at limits. Assume, for this paragraph and proof only, that R has **no** transversal. Every valid S then has nonfull L(S), so Φ strictly increases L at every valid input.

Fix valid S₀ and let Reach(A,B) be the ordinary impredicative reflexive-transitive closure of the operation Φ:

    Reach(A,B) := ∀P[(P A ∧ ∀T(P T→P(Φ T))) → P B].

Put D(T):=Reach(S₀,T). This is a represented successor history. It contains every ordinary finite iterate, but no external standardness, external countability, infinitary disjunction, or countable-completeness premise is assumed.

The standard ancestral induction calculations give:

1. Every D-member is valid. For D-members A,B, either Reach(A,B) or Reach(B,A).
2. If Reach(A,B) and A≠B, then L(A)⊊L(B). Thus Reach is antisymmetric on D, and distinct D-members have distinct terminal extensions.
3. The strict predecessors of Φ(T) in D are exactly the predecessors of T together with T.

For completeness, the comparability calculation uses

    Reach(A,B) → [B=A ∨ Reach(Φ(A),B)],

which follows by ancestral induction on B. Comparability with every D-member holds at S₀ and is preserved by Φ using that implication. Inclusion of L-values follows by induction from strict improvement. Antisymmetry follows immediately, and the same first-step implication then gives the predecessor calculation. These arguments are internal, not an appeal to external iteration.

Define the limit graph by retaining **all** patches along this history:

    S∞(F,y) := ∃T(D(T) ∧ F≈L(T) ∧ K(T,y))
               ∨ [¬∃T(D(T) ∧ F≈L(T)) ∧ S₀(F,y)].

At most one T∈D has F≈L(T), by items 1–2. On such an input its K-value is missed by F; otherwise S₀ supplies the value. Thus S∞ is an actually total functional subrelation of U. This is an admitted lambda graph, and its construction is uniform in S₀.

To verify that it extends the progress already obtained, ancestral induction using item 3 proves the precise history invariant: each T∈D agrees with S₀ except on the terminal classes L(A) of its strict predecessors A, where it agrees with K(A,−). It follows that S∞ and T agree on every input property F which is a **strict actual subset** of L(T). Any terminal class modified there must belong to a strict predecessor of T, so that patch is already present in T.

Hence Run_T is an h_S∞-chain: each defining predecessor image is unchanged. At its terminal class, S∞ uses K(T,−), so h_S∞(L(T)) is L(T) with the missed K-point adjoined. As in the one-step proof, adjoining that new terminal class gives an h_S∞-chain. Therefore

    L(T) ⊊ L(S∞)       for every T∈D.

This proves a represented limit extension for the entire deterministic successor history. It uses only the two displayed RC instances and ordinary C comprehension. It does not identify L(S∞) with the union of the earlier L(T)'s: additional progress is allowed. Postnormalizing S∞ preserves the result.

### Upper bounds for arbitrary compatible families of selectors

There is a more general limit construction. For valid selectors define S≼T to mean that S and T agree as actual graphs on every input F with F⊊L(S). This implies that Run_S is an h_T-chain, by the same predecessor-image argument, so Run_S is an initial segment of Run_T and L(S)⊆L(T). Consequently ≼ is a represented preorder: transitivity follows since F⊊L(S) and L(S)⊆L(T) imply F⊊L(T).

Let C be any represented family of valid selectors comparable by ≼, and fix a valid default graph B. Define

    B_C(F,y):=∃S(C(S) ∧ F⊊L(S) ∧ S(F,y))
               ∨ [¬∃S(C(S) ∧ F⊊L(S)) ∧ B(F,y)].

Any two covering selectors agree at F: use comparability and the definition of ≼ for the smaller one. Thus B_C is actually functional and valid. For every S∈C it agrees with S below L(S), hence S≼B_C. The empty family gives B. No well-ordering of C, extra RC instance, or completeness assumption is needed. The construction is an admitted operation in the family code and is invariant under coextension of that code **up to actual graph coextension**. Necessary totality/functionality may again be imposed afterwards without changing these conclusions.

If the L-values in C have no greatest member, L(B_C) strictly contains every L(S). Therefore compatible represented chains have explicit upper bounds; the obstruction is not the absence of every kind of limit. A least upper bound is not proved: the default can allow additional progress after the common history, and different defaults can produce incompatible extensions.

### Current boundary

The successor step, deterministic-history limit, and upper bounds for compatible represented chains are now supplied. What has not been supplied is a compatible choice across **different** history codes arriving at coextensive terminal states. Their next K-values can differ in one missed R-cell. Neither necessary functionality nor the independent local-candidate selection condition removes that possibility. The limit constructions do not justify an arbitrary external transfinite recursion or a union over mutually incompatible histories. The original C+RC implication remains unresolved at this point.

### Subsequent adjacent result: completeness at one fixed type suffices

The user's additional RC+BC⇒Actuality target is proved in `choice-completeness-actuality.md`. Its sharpest local form is RC_(t,t)+BC_(tt)⇒Actuality. The proof uses disjoint refinement and higher-type reflection of disjoint joins, independently of the RC+BC⇒TC argument.

Thus **all-type RC plus BC_(tt) implies all-type TC** via Actuality⇒Transversal and Transversal+RC⇒TC. A separator for RC alone must fail BC at this one fixed property type, irrespective of the type of its failed transversal. If BC_t still holds, the new proof extracts a represented false antichain of propositions with join ⊤ whose haecceities have no join at tt. This narrows the necessary missing-completeness phenomenon without resolving RC alone.

# Rigidity, actualization and evaluation: research notes

Original arguments developed by GPT-6 (OpenAI), 22 October 2026. Ordinary mathematics in the fixed framework C; no Lean work or verification. These are research proofs for independent audit, not database edits. The root agent is developing the basic Bivalent Evaluation equivalences separately. Here `C5` means **boxed ND at all types**, never merely unboxed ND.

## Scope and definitions

For a relational type tau = sigma_1 ... sigma_n t (n may be zero), write F[xbar] for its left-nested application. Write `coext(F,G)` for the **actual**, unboxed universal biconditional. The rigid and weakly rigid predicates are those in `topics/classicism/background.md`.

Bivalent Evaluation for E of type tt is

    BE(E) := forall p . (p -> E p = top) and (not p -> E p = bottom).

The basic root argument establishes:

- `exists E BE(E)` iff ND + Actuality.
- `box exists E BE(E)` iff box Plenitude.

All uses of equality below are ordinary C equality, not coextension. In particular, identities of operations require either necessary pointwise agreement or the appropriate BF/Functionality principle; actual pointwise agreement alone is never silently upgraded.

## 1. Unique Bivalent Evaluation

**Theorem.** In C, given existence of BE, uniqueness of BE is equivalent to BF at type t.

### BF_t implies uniqueness

If BE(E) and BE(D), then for each actual proposition p, E p and D p are the same one of top and bottom. Thus `forall p . E p = D p`. Necessity of identity gives `forall p . box(E p = D p)`. BF_t yields `box forall p . E p = D p`, and Intensionality gives E = D.

### Uniqueness implies BF_t

Let BE(E), and assume `forall p . box Xp`. Define

    D := lambda p . (E p iff Xp).

For each actual p, Xp is necessary. Consequently `(E p iff Xp)` and E p are necessarily equivalent, so D p = E p. Therefore BE(D). By uniqueness D = E. Intensionality, or simply necessary substitution and beta-reduction, now gives

    box forall p . ((E p iff Xp) iff E p).

The displayed matrix is propositionally equivalent to Xp, so `box forall p . Xp`, as required.

This argument does not assume that a new proposition existing only at a future world already fell under the initial BE condition. The equality D = E is what supplies the needed universal information at future worlds.

### Consequences and exact hierarchy

Using existing proved results, Unique BE is equivalent to each of:

1. BE + BF_t;
2. ND + Actuality + BF_t;
3. C5 + Actuality;
4. Plenitude + BF_t.

For (2)->(3), ND_t + BF_t yields boxed ND_t, and boxed ND_t yields C5. For (3)->(4), the recorded C5 + Actuality results give Plenitude, while C5 gives BF. For (4)->(1), Plenitude gives ND and Actuality, hence BE.

This is strictly weaker than boxed BE / boxed Plenitude. The proved model `symmetric-qualitative-contrast` has C5 and Actuality, hence Unique BE, while refuting boxed Actuality and boxed Plenitude.

Existence alone is strictly weaker than uniqueness: `finite-support-two-object-all-maps-at-singleton` has Plenitude, hence BE, and fails BF_t by the proved-only Engine closure. Hence there are at least two distinct BE operations there. The proof above explicitly constructs a second from a BF_t counterexample.

A proved-only Engine query with precisely these three models confirmed:

- `finite-support-two-object-all-maps-at-singleton`: ND, Actuality, Plenitude; fails BF_t and boxed Plenitude.
- `symmetric-qualitative-contrast`: C5, Actuality, BF_t, Plenitude; fails boxed Actuality and boxed Plenitude.
- `full-involution-group`: boxed Plenitude; fails the Fregean Axiom.

These model assertions are derived from proved records, not new model proofs or claims that the conjecture list itself is evidence.

## 2. Persistent global evaluation collapses modality

**Theorem.** The formula

    exists E^(tt) . box BE(E)

is equivalent to the Fregean Axiom, hence to Extensionality at every relational type.

If box BE(E), then at the evaluation point BE(E). For any true p, E p = top, necessarily by NI. At every accessible world BE(E) says that E p is bottom if p is false. Since E p remains top, p remains true. Thus every true p is necessary. It follows that materially equivalent propositions are necessarily equivalent and hence identical: the Fregean Axiom. Equivalently use the standard C argument from `forall p . p -> box p` to Fregean.

Conversely, the Fregean Axiom necessitates itself by the recorded result. At every world every proposition equals top or bottom according to its truth. The identity operation `lambda p . p` is therefore necessarily BE.

Thus the quantifier placements give a strict chain:

    exists E BE(E)
    Unique exists E BE(E)
    box exists E BE(E)
    exists E box BE(E)

where each displayed condition implies its predecessor. The strictness witnesses, in order, are the three models in section 1; the two-element-group model has boxed BE and fails the global condition because it has contingent propositions.

The last condition is consistent (ordinary extensional Henkin models), but it removes propositional contingency entirely. It should not be confused with boxed existence of a world-specific evaluator.

## 3. Sections of rigid relations

**Lemma.** Under C5, every section of a rigid relation is rigid. This holds for an arbitrary fixed argument, whether that argument is itself rigid at its relational type or not.

It suffices to fix the first argument x of a rigid R(a,bbar). Persistence of the section R(x,-) follows from persistence of R. For weak inextensibility, work at any accessible world v; C5 supplies ND there. Suppose Z satisfies

    forall bbar . R(x,bbar) -> box Z[bbar].

For a current R-instance (a,bbar), if a=x then box Z[bbar]. If a!=x, ND supplies box(a!=x). In either case

    box(a=x -> Z[bbar]).

Weak inextensibility of R, tested on `lambda a bbar . a=x -> Z[bbar]`, gives

    box forall a bbar . R(a,bbar) -> (a=x -> Z[bbar]).

Hence R(x,-) <= Z. Since the argument works at every accessible world using boxed ND and rigidity of R, the section is inextensible. Iteration fixes any finite argument tuple.

The C5 hypothesis matters: when distinct arguments can become identical, a section can acquire instances transported from a previously distinct argument.

## 4. One propositional evaluator actualizes every relational type

Assume Unique BE, equivalently C5 + Actuality, and let E be its unique operation. For each relational type tau = sigmabar t define

    r_tau(F) := lambda xbar . E(F[xbar]).

**Theorem.** r_tau(F) is the unique rigid relation actually coextensive with F.

The actual coextension follows directly from BE(E). For rigidity, C5 + Actuality supplies Rigid Comprehension; choose rigid G actually coextensive with F. Fix an actual tuple xbar.

- If G[xbar], persistence makes G[xbar] necessary, so it is top.
- If not G[xbar], each actual G-instance ybar is distinct from xbar. Polyadic ND makes those inequalities necessary. Weak inextensibility of G, tested on `lambda ybar . ybar != xbar`, gives `box not G[xbar]`, so G[xbar] is bottom.

Therefore E(F[xbar]) = G[xbar] for every actual tuple xbar. By NI these pointwise identities are necessary. C5 gives BF at each tuple component, so they may be collected under a box; Intensionality yields r_tau(F)=G. The empty-tuple case is immediate. Uniqueness is the standard C lemma that coextensive weakly rigid relations are identical.

Consequences:

1. r_tau(F) is rigid and actually coextensive with F.
2. r_tau(F)=F iff F is rigid.
3. r_tau(r_tau(F))=r_tau(F).
4. `r_tau(F) <= r_tau(G)` iff `forall xbar . F[xbar] -> G[xbar]` at the evaluation point.
5. r_tau respects actual coextension exactly: r_tau(F)=r_tau(G) iff coext(F,G).

For (4), the right-to-left implication uses persistence of r_tau(G) and weak inextensibility of r_tau(F); the converse follows by T. No unboxed implication between arbitrary F and G is mistaken for algebraic entailment.

### Boolean operations

For all F,G of type tau:

    r(not F) = not r(F)
    r(F and G) = r(F) and r(G)
    r(F or G) = r(F) or r(G)
    r(top_tau) = top_tau
    r(bottom_tau) = bottom_tau.

For each actual tuple, all displayed evaluations are literally top or bottom, and BE makes the corresponding scalar identities hold. NI and the tuple instances of BF collect those identities under a box, and Intensionality supplies the relational identities. The top identity uses C5's BF: the universal relation is rigid there.

These are identities of the actualization operators at the evaluation point. They do not assert F=r(F) for arbitrary F; that would collapse Extensionality.

### Quantifiers

For every type sigma (including e) and predicate X^(sigma t),

    E(forall x . Xx) = forall x . E(Xx),
    E(exists x . Xx) = exists x . E(Xx).

If all Xx are actually true, each E(Xx)=top, and BF_sigma makes the right-hand universal proposition top. If not, an actual false witness makes that universal necessarily false, hence bottom. BE evaluates the left side to the same constant. The existential identity follows dually. With parameters and additional argument tuples, the corresponding r-identities follow using BF on the remaining variables.

Moreover these algebraic and quantifier laws persist for the fixed E at future worlds: each identity is necessary by NI, and C5's BF collects the quantified identities. The evaluator ceases to represent *current* truth at other worlds; what persists is its operation as an evaluator of the original world.

## 5. Atoms and complete Boolean evaluators

The background for this section is C5 alone; Actuality and Atomicity are not assumed. Define a **complete bivalent Boolean evaluator** CE(E), E:tt, by the following finite conjunction:

1. E top = top;
2. for every p, E p = top or E p = bottom;
3. for every p, E(not p) = not E p;
4. for every p,q, E(p and q) = E p and E q;
5. for every X:tt, E(forall p . Xp) = forall p . E(Xp).

Clause 5 is an identity, not a material biconditional. Quantification there is over propositions; this one type instance suffices for the reconstruction. The canonical evaluators below in fact preserve quantification over every type.

**Theorem.** The maps

    w |-> E_w := lambda p . w <= p,
    E |-> w_E := forall p . (E p -> p)

give mutually inverse correspondences between propositional atoms w and complete bivalent Boolean evaluators E.

### From an atom to an evaluator

Under C5, every atom is necessarily nonbottom by ND. Every current proposition is decided by it. The deciding alternatives are themselves necessary, so BF_t makes the atom a strong world. Therefore E_w(p) is top or bottom, and complementation is respected at every world. Conjunction preservation and preservation of top are immediate from algebraic entailment.

For quantifiers, at every world boxed BF_sigma gives

    box(w -> forall x . Xx) iff forall x . box(w -> Xx).

The forward direction is the modal closure of universal instantiation; the reverse is BF_sigma applied to the predicate `lambda x . w -> Xx`. The equivalence holds necessarily because C5 gives boxed BF_sigma. Thus it is an identity of propositions, proving clause 5 and all other type instances.

### From an evaluator to an atom

Let CE(E), and put w=w_E. E bottom=bottom follows from clauses 1 and 3. Since E p is top or bottom, E(E p)=E p. Hence Boolean homomorphism gives

    E(E p -> p) = (E(E p) -> E p) = top

for every actual p. BF_t makes `forall p . E(E p -> p)` top. Applying clause 5 to X(p):=(E p -> p) yields E w=top. Therefore w!=bottom, since E bottom=bottom.

If E p=top, the defining universal for w entails p. If E p=bottom, complementation gives E(not p)=top, so w entails not p. Thus w is an atom. The C5 argument above makes it a strong world as well.

For each p, these cases show E p=E_w p. BF_t plus NI yields E=E_w. Conversely w_{E_w}=w: the universal defining w_{E_w} entails its p=w instance, whose antecedent E_w w is top, so w_{E_w}<=w; and w<=w_{E_w} follows from the theorem that w together with w<=p implies p, universally at every future world.

### Characterizations

Within C5:

- There is a CE evaluator iff there is a propositional atom.
- The unique BE evaluator of a world is the CE evaluator of its true atom, when that atom exists.
- Atomicity at t is equivalent to: every nonbottom proposition p is sent to top by some CE evaluator.

For the last equivalence, Atomicity chooses an atom w<=p and E_w accepts p. Conversely an accepting E gives its atom w_E<=p. Since C5 + Atomicity_t yields full Atomicity and boxed Plenitude by the existing results, this provides another finite, proposition-only characterization of the full schema over C5.

**Important caveat.** Drop clause 5 and the operators are Boolean ultrafilters. They need not correspond to atoms: infinite full S5 models in a choice metatheory admit nonprincipal ultrafilters. Do not claim every bivalent Boolean homomorphism is a world evaluation. The complete-meet condition is doing real mathematical work.

## 6. A supported hereditary rigid core

This is an interpretation theorem, not an identification of all intensional entities with their actual extensions. Assume C5 + Actuality. Recursively define predicates H_sigma of the existing types:

- H_e(x) := top;
- for tau=sigma_1...sigma_n t,

      H_tau(F) := Rigid(F) and F <= A_tau,
      A_tau := lambda xbar . and_i H_{sigma_i}(x_i).

For the empty tuple, A_t=top and H_t consists exactly of top and bottom. These type-by-type definitions are metalinguistic recursion on finite types; no object-language quantification over types is introduced.

**Lemma.** Every H_sigma is rigid. H_e is the universal property, rigid by boxed BF. Given rigidity of the earlier H_sigma_i, C5 makes their lifted finite conjunction A_tau rigid. Rigid Power then makes H_tau, its rigid power property, rigid. (C5 supplies Rigid Power as a recorded theorem.)

Every core domain is nonempty: bottom_tau belongs to H_tau, and e is nonempty by the standing logic. Its core-top A_tau belongs as well.

Application preserves the core. If H_{sigma tau}(F) and H_sigma(x), then the section lemma makes Fx rigid, and F's support condition implies Fx<=A_tau. Hence H_tau(Fx).

Extensionality holds *relative to the core*. If F,G are H_tau members and agree on all H_sigma_i arguments, then they agree on all arguments, since both vanish outside those domains. Coextensive rigid relations are identical.

Comprehension holds relative to the core. Given an ordinary C formula phi in core-bounded variables, form Q(xbar):=A_tau(xbar) and phi(xbar). Rigid Comprehension gives a rigid G actually coextensive with Q. Every current G-instance lies in A_tau, whose persistence makes that membership necessary; weak inextensibility of G gives G<=A_tau. Therefore G is a member of H_tau and represents phi on the core arguments.

Consequently these domains, with ordinary application and actual truth, form an internal extensional Henkin structure for the same relational type system. Under Functional Choice (in particular under the user's benchmark boxed Functional Choice), the structure also satisfies choice: extend a relation serial only on core inputs by a fixed default output, choose in the ambient system, restrict to the core, and rigidify; for relational outputs, ambient Plenitude plus actualization produces the corresponding core operation.

The support restriction is essential. The raw domain of all rigid relations can contain predicates distinguishing nonrigid arguments that the proposed quotient identifies. Merely saying “take the rigid relations” would not supply higher-type extensionality. H_tau removes precisely this defect by requiring predicates to vanish outside the earlier core domains.

## 7. Separate bottom-cut result

The detailed draft `/tmp/rigid-bottom-cut-proof.md` proves the proposed new theorem

    Strong Leibniz + Rigid Comprehension -> boxed BF (relational types).

Its key step is to rigidify the strong worlds **together with bottom**. For that rigid set A, every cut `R_Y(W):=A W and W<=Y` is rigid: an excluded world can enter a cut only by becoming bottom, and bottom was included from the outset. This removes the future-world RC assumption in the earlier recorded salvage proof. The root agent has independently audited the argument; no named human check or Lean verification is claimed.

A further consequence, needing no Rigid Power, is

    Strong Leibniz at sigma + RC at sigma t -> boxed Strong Leibniz at sigma.

Indeed the same A satisfies boxed A(bottom), boxed(A subset D), and J(A)=top, where D(W):=forall Y(W<=Y or W<=not Y). Work at any accessible world and let Y!=bottom. If no current nonzero A-member is below Y, D implies every current A-member lies below not Y: the below-Y alternative must be bottom. Each such entailment is necessary, and weak inextensibility of A transfers this universal condition, giving J(A)<=not Y. Since J(A)=top, this contradicts Y!=bottom. So a nonzero A-member W lies below Y. Persistence of A and boxed(A subset D) imply boxed D(W), making W a strong world. This proves Strong Leibniz at every accessible world, with all type and box scopes preserved.

## 8. Sources and status

Direct source for the original arguments here is this research note (misc). Background definitions and lemmas are from the existing database: C and Intensionality; NI; BF/CBF; the weak-rigidity uniqueness lemma; C5 implies boxed BF and Rigid Power; C5+Actuality implies RC and Plenitude; ND_t+BF_t implies boxed ND_t; boxed ND_t implies boxed ND at all types. None of those source records is edited here. No published source should be cited as the source of the new uniqueness, projection, evaluation-classification, or bottom-cut proofs.

## 9. Improved definitions and exact low-type simplifications

These are proposed explanatory equivalents. They do not replace the source's definitions or alter any source record.

### Persistence is a fixed-point condition (in C alone)

For every relational F,

    Persistent(F) iff F = lambda xbar . box F[xbar].

The definition supplies the left-to-right algebraic inequality. The reverse inequality is the pointwise modal theorem T, so equality follows by Boolean antisymmetry. This avoids describing persistence merely by an unboxed implication about current instances, which would be weaker.

### Weak rigidity is an exact universal-property condition (in C alone)

    WeaklyRigid(F)
      iff forall X . [F<=X iff forall xbar(F[xbar] -> box X[xbar])].

Given weak rigidity, the right-to-left implication is weak inextensibility. For left-to-right, an actual F-instance persists, so F<=X makes X necessary of that tuple. Conversely the equivalence's X=F instance gives weak persistence, and its right-to-left direction is weak inextensibility.

Writing H_a:=lambda xbar . xbar=a for the tuple haecceity, C proves H_a<=X iff box X[a]. Therefore the same condition says precisely:

> F is the least upper bound of the haecceities of its actual instances.

In the database's LUB notation, define U_F(K):=exists abar . F[abar] and K=H_abar. Then the equivalent formula is `LUB(F,U_F)`. Rigidity is the necessity of this universal property. This supplies a simple mathematical gloss: weakly rigid relations are exactly those generated by their current instances; rigid relations retain that generatedness at every world.

The proof uses a defining LUB condition and does not presuppose Boolean Completeness or that such a LUB exists for arbitrary F.

### Nullary cases are substantially simpler (in C alone)

For propositions p:

    WeaklyInextensible(p) iff (not p -> box not p),
    WeaklyRigid(p) iff (p=top or p=bottom) iff Rigid(p),
    Inextensible(p) iff Persistent(not p).

For the first equivalence, if p is false, weak inextensibility tested on bottom gives p<=bottom, hence box not p. If p is true, weak inextensibility is automatic: its premise says box X, which entails p<=X. Conversely if p is necessarily false, p<=X for all X. The nullary weak-persistence condition is p->box p. Combining it with the first equivalence proves the second: if p then p=top, and if not p then p=bottom. Both constants are rigid by C. Boxing the first equivalence yields the last.

Consequently the nullary instances of Tame Rigidity, Rigid Power, Weakly Rigid Power, Rigid Rigidity and Weakly Rigid Weak Rigidity are theorems of C. For the power claims, a rigid/weakly rigid proposition is top or bottom, and the corresponding power property is either the singleton of bottom or the two-element set {bottom,top}; haecceities and finite unions of them are rigid in C.

**Record-scope caution.** The note on the old TR+RP=>WRP conjecture says a countermodel must fail boxed Tame Rigidity “at type t.” If that means the nullary proposition type, it cannot be right, because that instance is already a C theorem. If it means properties *of* propositions, the type must instead be written tt and the proof checked with the necessary BF_t hypothesis for the universal relation. This ambiguity should be reviewed before any record correction; no record has been changed here.

### Under C5, persistence and inextensibility coincide

For every relational F under C5:

    Rigid(F) iff Persistent(F) iff Inextensible(F)
             iff forall xbar . (F[xbar]=top or F[xbar]=bottom).

To show Persistent=>Inextensible, work at an arbitrary accessible world. S5 plus persistence makes every current instance proposition F[a] stable in both truth directions: if it were false but could become true, at that future point persistence would make it necessary, and symmetry would contradict its current falsity. Given a weak-inextensibility test Z, each current tuple either is F and has box Z, or is not F and has box not F. Thus for every tuple, box(F->Z). BF on the tuple coordinates gives F<=Z. Since C5 supplies these laws at every world, F is inextensible.

For Inextensible=>Persistent, first note at any world that not F[a] implies box not F[a]: all current F-instances are distinct from a, ND makes those inequalities necessary, and weak inextensibility gives F<=lambda xbar(xbar!=a). If F[a] were true but possibly false, this argument at the false world would make it necessarily false there, contradicting the original truth by S5 symmetry. Thus F[a] is necessary whenever true; applying the argument at every world gives persistence.

Rigid=>pointwise top/bottom is the argument used in section 4. Conversely, pointwise top/bottom plus BF collects the stable values under a box and makes F persistent, hence rigid.

The tempting condition `forall xbar(F[xbar]->box F[xbar])` remains insufficient even under C5 and all BF: a nullary proposition false here and true at another world of the two-world S5 model satisfies it vacuously and is not rigid.

## 10. Two new simple characterizations of C5

### Persistence Suffices

The schema

    forall F . Persistent(F) -> Inextensible(F)

is equivalent over C to C5. Equivalently, every persistent relation is rigid.

C5 implies it by section 9. Conversely, box p is a persistent proposition in C. The schema makes box p rigid. By the nullary lemma, it equals top or bottom; in the case not box p, it equals bottom, yielding box not box p. Thus 5 holds, hence ND. Also every universal relation top_(sigma t) is persistent, so the schema makes it rigid. Inextensibility of that universal relation is exactly boxed BF_sigma. Therefore the schema gives boxed BF at all types. ND plus BF gives C5 by the recorded result.

This equivalence preserves the full schema. The nullary instance alone gives only 5/ND, not automatically boxed ND over future newly existing propositions.

### Unrestricted Rigid Power

The schema obtained by deleting the hypothesis of Rigid Power,

    forall F . Rigid(lambda X . Rigid(X) and X<=F),

is likewise equivalent over C to C5.

For C5=>the schema, the displayed power property is persistent in C regardless of whether F is rigid: both Rigid(X) and X<=F are necessarily stable conditions. Section 9 makes every persistent relation rigid under C5.

Conversely, F=top at each relational type makes the power property exactly the property of being rigid, so the schema gives Rigid Rigidity and therefore boxed BF. To obtain 5/ND, use just the nullary instance. Fix p with not box p and let

    P_p(q):=Rigid(q) and q<=p.

Every current P_p-instance is bottom: the only rigid propositions are top and bottom, and top<=p would say box p. Necessity of identity therefore makes the predicate q=bottom necessary of every current P_p-instance. Weak inextensibility of P_p yields

    box forall q . P_p(q) -> q=bottom.

At any future world where box p held, top would be a P_p-instance, contradicting top!=bottom. Thus box not box p. Hence 5 and ND, and with BF, C5.

In fact the unrestricted nullary power statement alone is equivalent to unboxed 5/ND. The reverse direction uses 5 to make box p either necessarily true or necessarily false, so P_p is necessarily identical to {bottom,top} or {bottom}, both rigid finite unions of haecceities. The all-type schema is what adds boxed BF and upgrades to C5.

These are ordinary mathematical equivalences, not claims that either new schema is already in the database.

## 11. The exact limitation of actualization as a map

Canonical actualization is a Boolean and quantifier projection, but generally does **not** preserve arbitrary higher-order application when it also actualizes the input. Adding

    r_tau(Fx) = (r_(sigma tau)(F))(r_sigma(x))

for all F,x collapses the Fregean Axiom already at sigma=t, tau=t.

Fix any proposition p and let F:=lambda q . q=p, its haecceity. F is rigid in C, so r_tt(F)=F. Set x=p in the proposed law. Since Fp=top, the left side is top. The right side is the proposition r_t(p)=p. Hence p equals its bivalent snapshot, so every proposition is top or bottom. Thus Extensionality holds. Conversely Extensionality makes every r the identity and the law automatic.

This is why section 6 constructs a **supported hereditary-core interpretation** rather than claiming the full intensional structure has a homomorphic extensional quotient. Those claims are mathematically different.

## 12. More explicit interpretation details for the hereditary core

For the positive benchmark C + boxed Functional Choice, section 6 applies because boxed Functional Choice gives boxed Plenitude and hence C5+Actuality. The target is extensional higher-order logic **in the same relational type system**, not an expansion to function types ending in e. No infinity assumption follows automatically.

A formal syntactic interpretation can be described by recursion on target terms, using the existing witness E and the explicitly defined r_tau and H_sigma:

- Variables of target type sigma range over H_sigma.
- Application is ambient application; it remains in the core by the section lemma.
- Equality is ambient identity on core objects. Under C5 its truth value is rigid, and core extensionality was proved in section 6.
- Target quantifiers are ambient quantifiers restricted by H_sigma, followed by E if a bivalent output is needed: for example `forall^core x phi` is represented by `E(forall x . H_sigma(x)->phi*)`.
- A relation abstraction is represented by actualizing its core-supported matrix. For a general lambda x of relational output tau, first expand the output tuple and use

      r_(sigma tau)(lambda x ybar . H_sigma(x) and term*(x)[ybar]).

  On core x this is actually coextensive with term*(x); both outputs are rigid and supported, so their identity follows. This proves beta. Core-supported extensionality supplies eta and the target extensionality schemes.

Every logical formation and proof step is thus interpreted by an actual core entity, with ordinary C comprehension and the proved canonicalization theorem doing the abstraction work. Higher-type extensionality uses support explicitly; it is not inferred merely from agreement on a smaller argument domain.

For choice, given a relation serial on core inputs with core outputs, extend it to all ambient inputs using a fixed core default. Ambient Relational Choice supplies a functional subrelation; restrict to core inputs and rigidify it, giving a supported core relation with the same actual graph. For relational outputs, ambient Plenitude represents the chosen graph by an operation, and supported actualization makes the operation a core member while retaining its core values (coextensive rigid outputs are identical). Thus both the applicable functional and relational choice principles transfer.

This is rigorous positive evidence of the benchmark's expressive strength. It is **not** a proof that the benchmark equals the logically true theory, nor that Maximalist C is inconsistent. The existing proved maximalist constructions remain evidence of consistency unless an actual mathematical defect is found in them or the framework is explicitly changed.

## 13. Strengthening the core theorem: C5 alone suffices for intrinsic comprehension

This section strengthens and clarifies sections 6 and 12. Their proofs using Actuality remain valid, but the extra assumption is unnecessary for **intrinsic target-language comprehension**. It is needed in the given transfer of arbitrary ambient choice graphs or ambient formulas with noncore parameters.

**Theorem.** C5 alone interprets extensional higher-order Henkin logic in the same relational type system, using the hereditary supported domains H_sigma above. No Actuality, Atomicity, RC or choice principle is needed for this interpretation.

Rigidity and nonemptiness of H_sigma, closure under application, and relative extensionality were already established using C5 alone. It remains to show that a target formula built from core parameters and quantifiers restricted to core domains defines a core relation without invoking ambient RC.

Proceed by induction on target syntax. At an atomic application terminating in t, closure under application puts its value in H_t={top,bottom}. An identity between core objects is likewise top or bottom, by NI and ND. Boolean connectives preserve this property. For a bounded universal

    Q := forall x . H_sigma(x) -> phi(x),

suppose first that Q is actually true. For each actual x:

- If H_sigma(x), the inductive hypothesis makes phi(x) top or bottom; since phi(x) is true, it is top, hence necessary.
- If not H_sigma(x), rigidity of H_sigma under C5 makes this nonmembership necessary.

Thus every actual x necessarily satisfies the implication. BF_sigma gives box Q, so Q=top. If Q is actually false, choose a current core x with not phi(x). Rigidity makes its core membership necessary, and the inductive hypothesis makes phi(x)=bottom. Therefore Q is necessarily false, hence bottom. Existential quantification follows by duality.

Now for a target abstraction, use the **raw core-supported matrix**, not its actualization:

    F := lambda xbar . A_tau(xbar) and phi(xbar).

At a tuple of core arguments the induction just established that phi is bivalent. At any tuple outside the core, its nonmembership in A_tau is necessary, because A_tau is rigid under C5. Thus every actual instance proposition F[xbar] is top or bottom. Section 9 shows F is rigid. The support inequality F<=A_tau is a theorem from its defining conjunction. Hence H_tau(F).

For a lambda abstraction of relational output tau, curry the same construction:

    lambda x ybar . H_sigma(x) and term*(x)[ybar].

On core x its output equals term*(x): the support conjunct is necessary, and all tuple arguments agree. The result is a core operation by the preceding argument. This yields beta directly, and supported extensionality yields eta.

Thus target quantifiers and abstractions can be translated without any witness E. C5 itself already supplies the stable extensional mathematical substructure. The additional strength of C5+Actuality is that it can import **arbitrary actual extensions** into this stable substructure via the canonical evaluator; intrinsic core formulas do not need that import.

**Choice remains a separate issue.** Ambient Relational Choice alone does not immediately produce a rigid chosen graph. The proof in section 12 uses actualization to freeze an arbitrary ambient choice graph. Consequently C + boxed Functional Choice proves an extensional core with Choice, while the C5-only theorem here claims comprehension and extensionality but not Choice or Infinity. The finite-support permutation models make this distinction natural.

## 14. Atomic-world graphs: an internal Gallin-style representation

Assume C5 + Atomicity_t. Existing proved results make this equivalent to boxed Plenitude. Write W(w) for Atom_t(w). This is a rigid predicate under C5: all the order and identity statements in the definition of atomhood are stable, and BF collects the quantifiers. Every atom is a strong world. Distinct atoms have disjoint meet; two true atoms are therefore identical. At every accessible world there is exactly one true atom, by boxed Actuality.

Here "Gallin-style" means the explicit-world extensional representation constructed below. It is not a claim that the exact theorem or its particular formulation appears in Gallin's book. The local record cites Gallin only through Classicism n. 37; the argument here is original research requiring audit.

### The basic graph correspondence

For an arbitrary original relational type tau=sigmabar t, put

    G_tau(F)(w,xbar) := W(w) and w<=F[xbar].
    J_tau(R)[xbar] := exists w . (R(w,xbar) and w).

Let K_tau be the class of rigid relations R of type t sigmabar t satisfying R<=lambda w xbar.W(w). Then G_tau and J_tau give inverse correspondences between all original F of type tau and K_tau.

First, G_tau(F) is rigid. For fixed arguments, atomhood and the algebraic order statement are bivalent under C5. Tuple BF and section 9 therefore give rigidity. The support condition follows directly from the conjunction.

To prove J_tau(G_tau(F))=F, work at any accessible world and any tuple. If the existential holds, its true atom w entails F[xbar], so F[xbar] is true. Conversely, if F[xbar] is true, choose the true atom w. Strong atomhood makes w decide F[xbar]; their joint truth rules out w<=not F[xbar], so w<=F[xbar]. Hence the existential holds. This argument is available at every world because C5+Atomicity supplies boxed Actuality and strong atomhood. Necessary universal coextension gives identity by Intensionality.

Conversely fix a current rigid supported R, atom w, and tuple a. If R(w,a), rigidity gives box R(w,a), and hence w<=J_tau(R)[a]. If not R(w,a), C5 and rigidity give box not R(w,a). Were w<=J_tau(R)[a], at a world where w is true the existential would choose a true atom v with R(v,a). True atoms are unique, so v=w, contradicting box not R(w,a). Thus

    R(w,a) iff w<=J_tau(R)[a].

Outside W both sides of the supported graph are false. G_tau(J_tau(R)) and R are rigid and actually coextensive, so they are identical. This proves both inverse equations without selecting a witness from a family and without any choice principle.

### Recursive transport of all argument types

The preceding graph leaves its arguments in the original intensional domains. A genuine explicit-world type translation transports those arguments too. Introduce target base sorts e (individuals), s (worlds), and o (Boolean truth values), interpreted internally by all original individuals, W, and {bottom,top}, respectively. Both s and o are represented using original type t, but with different domain predicates. This harmless coincidence does not identify the target sorts.

For each original type define its target translation by

    T(e)=e; T(t)=s o; T(sigma tau)=T(sigma) T(tau).

Thus a proposition becomes a Boolean-valued world predicate, and a relational intension becomes an extensional operation into a world predicate. Every translated function type still ends in o; this is the relational fragment, not an illicit addition of ee to the original framework.

The target domain at a relational type is the available supported hereditary rigid core over these three base sorts. Such a domain consists of the original rigid predicates that vanish outside the interpreted domains of their argument sorts. Section 13, with this finite list of nonempty rigid base predicates, gives the extensional Henkin interpretation and its comprehension. The proof is unchanged: supports, sections, intrinsic bounded quantification, and the induction proving bivalent matrices all work sort by sort.

Define maps j_sigma and k_sigma recursively, with j_e and k_e interpreted as the metalinguistic identity substitution (no forbidden term of type ee is introduced). For tau=sigma_1...sigma_n t, let

    j_tau(F)[a'_1,...,a'_n,w] :=
      W(w) and exists a_1...a_n .
        (and_i j_sigma_i(a_i)=a'_i) and w<=F[a_1,...,a_n];

    k_tau(R)[a_1,...,a_n] :=
      exists w . R[j_sigma_1(a_1),...,j_sigma_n(a_n),w] and w.

For n=0 these are just the preceding proposition graph and its inverse. Recursively the j_sigma_i and k_sigma_i at relational types are allowed lambda terms: their output types are relational. Formula equality in the graph is ordinary identity.

**Induction theorem.** Each j_tau(F) is in the target domain T(tau), and

    k_tau(j_tau(F))=F;
    j_tau(k_tau(R))=R for every target-domain R.

For membership, all identity and order matrices are bivalent under C5; bounded or unbounded existential quantification preserves bivalence by BF. Thus the graph is rigid. Its displayed witnesses ensure support in the lower target domains, and W supplies world support. For the first inverse, the inductive injectivity of j_sigma_i makes the existential witnesses in j_tau unique with respect to their original arguments. The calculation therefore reduces pointwise to J_tau G_tau=identity. For the second, every supported target argument tuple has original preimages by inductive surjectivity. Substitute these preimages and use G_tau J_tau=identity; outside support both relations vanish. Rigidity and actual coextension finish the identity. This also proves injectivity and surjectivity for the next induction step.

These equations preserve application:

    j_tau(Fa) = j_(sigma tau)(F)(j_sigma(a)).

The right side is a supported target section. At the remaining supported arguments and a world atom, both sides say the same atom entails the same original application; outside support both vanish. Notice the difference from section 11: j records every world rather than discarding all but the actual extension, so application preservation does not force Extensionality of the original structure.

Boolean connectives become pointwise Boolean connectives on world predicates. Original quantifiers become target quantifiers over T(sigma), at each world: the key equation is

    w<=forall x Xx iff forall x . w<=Xx,

whose reverse direction is BF_sigma and whose forward direction is modal universal instantiation. Original necessity becomes universal quantification over the world sort, since Atomicity makes p=top equivalent to every atom lying below p. Original equality becomes extensional target identity, because the j maps are injective and original equality is stable under C5.

This is an internal Henkin representation theorem with explicit inverse maps. It does not say that every external subset of the atom set, or every external function between represented domains, is an available entity. The core has all subsets/functions supplied by its interpreted comprehension; external fullness is a separate semantic condition.

## 15. Choice and Infinity in the representation

C + boxed Functional Choice supplies the assumptions of section 14 and supplies Choice to its multi-sorted core by the argument of section 12. Therefore it interprets a Gallin-style extensional Henkin structure with worlds, intensional domains, application, and choice, and every original entity is represented by a unique available world intension.

The representation preserves the translation of every original formula. Consequently adding an original Infinity axiom adds its exact explicit-world translation. In particular, ambient Axiom of Infinity at e is represented by its Gallin translation using the translated Frege-cardinality types and translated quantifiers. A boxed original Infinity axiom holds at every represented world. No claim that Infinity follows from boxed Functional Choice is made.

For the ordinary extensional mathematical core, the finite distinctness schema at e transfers immediately: the core individual domain and identity are unchanged. The quantified core Axiom of Infinity is a more delicate statement, because its impredicative FiniteCardinality predicate quantifies only over core predicates. It must not silently be identified with the original intensional FiniteCardinality predicate. One clean natural strengthening is to add the interpreted extensional-core Infinity axiom itself; section 16 supplies a standard full model satisfying that strengthening together with both original Infinity axioms. A separate proof could establish equivalence with an original axiom, but that is not assumed here.

## 16. A full Gallin-style consistency construction with Infinity

This section is a semantic construction in a choice metatheory. Choose nonempty sets I of individuals and S of worlds. Define

    D_e=I; D_t=P(S); D_(sigma tau)=all functions D_sigma -> D_tau

for exactly the admitted original relational types. Application is function application. Boolean operations on propositions are the set operations, quantification is intersection/union over the relevant fixed domain, and equality of any two entities is S if they are literally equal and the empty set otherwise. Evaluate a proposition p at w by w in p. Lambda abstractions have their ordinary function denotations.

The derived Box p is S precisely when p=S, and otherwise empty. Thus this is an S5 constant-domain intensional model. Soundness for H follows by the standard compositional induction. For C's Logical Equivalence, if two formulas are H-equivalent, their truth values agree at every world and every assignment, so their lambda abstractions are literally the same functions. This checks the theoremhood side condition directly; no equivalence merely under an optional premise is used.

At any world w, a serial U of input type sigma and relational output type tau has a selected output f(x) with w in U(x,f(x)), by metatheoretic choice. Fullness puts f in D_(sigma tau). Hence Functional Choice holds at every world, proving boxed Functional Choice. Rigid predicates are exactly those taking only empty/S values. The hereditary supported rigid core is therefore a full extensional type structure on I, and the multi-sorted version is full on I and S.

Taking I=S=N gives both original Axioms of Infinity and the ordinary core Axioms of Infinity at the individual and world sorts. In this full model the impredicative finite cardinalities are exactly the standard numerals: the set of numeral denotations is an available inductive predicate, while induction places each numeral in every inductive predicate. Each numeral counts the actual finite extension in the usual way. The domains I and P(S) are infinite, and the core individual/world domains I and S are infinite. Thus no finite numeral counts their universal properties.

This supplies relative consistency evidence, not an absolute proof of consistency stronger than the metatheory. It also shows that the intensional benchmark, a full extensional mathematical core, Choice, and both sorts of Infinity coexist naturally. With |S|>1 the model still has contingent propositions and refutes the Fregean Axiom; no modal collapse is hidden in the construction.

The parameters separate the two ordinary sources of infinity: I=N with S finite gives infinitely many individuals but finitely many propositions; I singleton with S=N gives infinitely many propositions but one individual. These are direct constructions, not asserted new database model records.

## 17. Exact transfer of the quantified Infinity axiom

This section resolves the caution in section 15 for the ordinary core over all individuals. The requisite hypothesis is only **Unique BE**, equivalently C5 + Actuality. Atomicity and boxed Actuality are unnecessary. More generally the argument works for a core whose base domain is all entities of any fixed original type sigma, interpreted as a new individual sort.

Fix sigma, and write P(X) for Rigid(X) at type sigma t. This is the power domain of the core over the complete original sigma-domain. Write

    nu := (sigma t)t;
    B(Z) := Rigid(Z) and Z<=P.

Thus B is the core cardinality domain. For a rigid property X and individual y of the new base sort, put X-y := lambda u . Xu and u!=y; under C5 this is rigid. The core zero and successor, extended by bottom outside P, are

    0c := lambda X . P(X) and forall u . not Xu;
    Sc(Z) := lambda X . P(X) and exists y . Xy and Z(X-y).

These are exactly the translations of ordinary extensional Frege zero and successor. They belong to B whenever the input belongs to B. Let N denote the original FiniteCardinality_sigma predicate, and Nc the core's translated FiniteCardinality predicate, whose second-order quantifier ranges over supported rigid predicates on B.

For the unique actual evaluator E define

    h(Z) := lambda X . P(X) and E(ZX).

For every original Z of type nu, h(Z) belongs to B: the matrix is bivalent under C5 and is explicitly supported on P. Moreover

    h(0)=0c;
    h(Suc(Z))=Sc(h(Z)).

For the first identity, evaluate at a rigid X. Its emptiness proposition forall u not Xu is bivalent by BF, so E fixes it. Outside P both sides vanish. For the second, the quantifier and Boolean laws of E give, at rigid X,

    E(exists y . Xy and Z(X-y))
      = exists y . E(Xy) and E(Z(X-y))
      = exists y . Xy and h(Z)(X-y).

Here E(Xy)=Xy because X is rigid, and X-y is in P. Outside P both sides again vanish. The pointwise equations collect to identities by BF and NI, or by coextension of the two rigid core outputs.

### First direction: h carries original finite cardinalities to core finite cardinalities

Suppose N(Z). Let V be an arbitrary core predicate on B that contains 0c and is closed under Sc. The original predicate

    U(Y):=V(h(Y))

contains 0 and is closed under original Suc by the two commuting identities. Hence N(Z) gives U(Z), namely V(h(Z)). Since V was arbitrary, Nc(h(Z)).

### Second direction: every core finite cardinality has an original finite preimage

Form the core-supported actualized image predicate

    I(Y):=B(Y) and E(exists Z . N(Z) and h(Z)=Y).

This is a core predicate on B. The original least-inductive predicate N contains 0 and is closed under Suc, directly from its impredicative definition. Consequently I contains 0c. If B(Y) and I(Y), actual BE supplies an original Z with N(Z) and h(Z)=Y. Then N(Suc(Z)), and the commuting square gives h(Suc(Z))=Sc(Y), so I(Sc(Y)). Thus I is inductive in the core. Every core finite cardinality therefore satisfies I, and BE produces its original finite preimage.

Combining the directions,

    Nc(Y) iff exists Z . N(Z) and h(Z)=Y,   for core Y.

This is a surjectivity theorem for natural cardinalities. It does not yet claim that h is injective on them under these weaker hypotheses.

Finally, top_(sigma t) is rigid under C5 and is the core's universal property. For every original Z,

    Z(top) iff h(Z)(top),

because h(Z)(top)=E(Z(top)) and E preserves actual truth. The displayed natural-cardinality surjectivity yields

    exists Z . N(Z) and Z(top)
      iff exists Y in B . Nc(Y) and Y(top).

Negating proves the exact equivalence of the original quantified Axiom of Infinity at sigma and the translated ordinary core Axiom of Infinity over the base sort of all sigma-entities. In particular, at sigma=e this is the ordinary individual core introduced in section 6. At sigma=t this is a core whose individuals are **all propositions**; it is not automatically the smaller atomic-world sort.

Thus C + boxed Functional Choice + Axiom of Infinity_e interprets extensional relational HOL with Choice and its actual quantified Axiom of Infinity. The earlier distinction between the two formulas remains necessary for their definitions, but the equivalence is now proved under the stated assumptions rather than assumed.

### General principle behind the argument

The proof is an instance of functoriality of impredicative generation. Whenever an ambient algebra and a rigid-core algebra have specified generators and operations, and an available map h preserves those generators and operations, h maps the ambient least inductively generated subdomain **onto** the core least inductively generated subdomain. Pull back core inductive predicates for one inclusion; actualize the image of the ambient generated subdomain for the other. No choice is used. The same argument works with any fixed finite family of finitary operations and constants. It is the availability of actualized image predicates, not external powerset fullness, that proves the surjectivity.

## 18. Infinity of propositions is Infinity of atomic worlds

First generalize section 17. Let D be any nonempty rigid predicate on an original type kappa. Interpret a core individual sort by D. Its power domain is

    P_D(X):=Rigid(X) and X<=D.

Define h_D as in section 17, replacing P by P_D. Core zero and successor use the quantifiers restricted to D. At an X in P_D, ambient emptiness and D-restricted emptiness agree; any witness Xy already satisfies Dy. The same zero/successor commuting identities and image-induction proof therefore give

    core-Finite(D) iff exists Z . FiniteCardinality_kappa(Z) and ZD.

Negation gives the corresponding quantified Infinity equivalence. This statement concerns the actual extension of D and requires only Unique BE.

Now assume C5 + Atomicity_t. The world predicate W=Atom_t is rigid and nonempty. The basic graph maps in section 14 give an available bijection

    all original propositions <--> the core power domain P_W,
    p |-> lambda w . W(w) and w<=p.

Its inverse takes R to exists w(Rw and w). The bijection can be expressed by a rigid relational graph, so no function type ending in an interpreted individual sort needs to be added. Work in the multi-sorted extensional core with one base sort consisting of all propositions and another consisting of W. All the required graphs and subsets belong to that core by C5 comprehension.

### The finite-powerset fact is valid for Henkin domains

In ordinary extensional relational HOL, a predicate A is Frege-finite iff it belongs to every class of predicates that contains the empty predicate and is closed under adjoining one element. For the forward direction use induction on its Frege cardinality n, with induction predicate `forall A(nA -> AdjunctivelyFinite(A))`: zero counts the empty predicate, and the successor clause removes one witness and adds it back. For the reverse direction the class `exists n(Nn and nA)` contains empty and is closed under adjunction: if the new element is already in A retain n; otherwise use Suc(n). These are internal impredicative inductions, not assertions that every internal natural is a standard metatheoretic numeral.

The adjunction characterization proves the usual finite-set facts by internal induction:

- Subsets of a finite predicate are finite. For A union {a}, remove a from the subset and use the induction hypothesis, then possibly adjoin a.
- Images under an available functional relation are finite. The image of empty is empty, and adjoining one input adds at most its one output. This uses a relational graph, not a forbidden individual-valued function type.
- Unions of two finite predicates are finite, by adjunction induction on either one.
- If A is finite, its available power domain is finite. The power domain of empty is the singleton of empty. For A union {a}, every subset either omits a and belongs to P(A), or is obtained by adjoining a to a member of P(A). Hence P(A union {a}) is the union of P(A) and an available functional image of P(A).
- Conversely, if P(A) is finite, its subset of singleton predicates is finite. The available relation taking each singleton to its unique member has image A, so A is finite.

All the images, subsets, and power predicates used here are given by ordinary comprehension. No step requires that the Henkin domain contain every external subset or that internal finite cardinalities be externally standard. Thus

    Finite(P(A)) iff Finite(A)

is available inside the represented core. Finiteness is also preserved by available bijective relational graphs, by the image argument.

Apply this to the atomic-world sort. Original propositions are bijective with P_W, whose finiteness is equivalent to that of W. Applying section 17 to the all-propositions sort, and the generalization above to W, gives the precise original-language theorem

    AxiomOfInfinity_t
      iff not exists Z . FiniteCardinality_t(Z) and Z(Atom_t).

The right side says that the actual set of atomic worlds is infinite, in exactly the map's impredicative finite-cardinality sense. The assumptions are C5 + Atomicity_t (equivalently boxed Plenitude); Choice is not used.

Consequently C + boxed Functional Choice + AxiomOfInfinity_t has a Gallin-style Henkin interpretation with an infinite world sort. Adding AxiomOfInfinity_e gives an infinite individual sort as well. The full model of section 16 realizes both together. The theorem does not identify either axiom with merely the finite distinctness schema, nor does it turn the Henkin world powerset into the full external powerset.

## 19. Natural-cardinality isomorphism under boxed Plenitude

Section 17 needed only Unique BE and proved surjectivity of h on natural cardinalities. Under the stronger assumption C5 + Atomicity_t, h is an isomorphism there. Continue with a core over all entities of the chosen original base type sigma and use the notation 0c, Sc, N, Nc, B from section 17.

For a core cardinality Z define its world lift

    L(Z)(X) := exists w . Atom(w) and w and Z(r_w(X)),
    r_w(X) := lambda u . w<=Xu.

For atomic w, r_w(X) is the rigid extension of X at w. It is in the core power domain. The graph/evaluator theorem supplies, for such w, Boolean and quantifier preservation, and r_w(X)=X whenever X is rigid.

The lift satisfies

    L(0c)=0;
    L(Sc(Z))=Suc(L(Z)) for B(Z);
    h(L(Z))=Z for B(Z).

For the zero equation, at any world choose its unique true atom w. The condition that r_w(X) is empty is exactly the condition that X is empty there. This is true at every world, giving identity by Intensionality. For successor, at the true atom w, Xy agrees with r_w(X)y and

    r_w(X-y)=r_w(X)-y.

The latter identity uses preservation of conjunction and the fact that identity/inequality propositions are bivalent under C5. Thus, at every world,

    L(Sc(Z))(X)
      iff exists y . Xy and exists w(Atom(w) and w and Z(r_w(X-y)))
      iff Suc(L(Z))(X).

The hL identity follows because, for rigid X, every r_w(X)=X and boxed Actuality makes the join over the true atom redundant. Hence L(Z)(X)=ZX on rigid inputs; E fixes the bivalent ZX, and outside the core power domain both hL(Z) and Z vanish.

Now the original predicate

    K(Y):=L(h(Y))=Y

contains 0 and is closed under Suc, by the two commuting squares. Original induction therefore gives N(Y)->K(Y). Hence Lh is the identity on original natural cardinalities. Section 17 already says every core natural has an original natural preimage under h; if h(Y)=Z and N(Y), then L(Z)=Y, so L maps core naturals to original naturals. Thus h and L restrict to mutually inverse zero/successor-preserving maps between N and Nc.

The world lift L and the core zero/successor definitions do not depend on the actual BE evaluator. Therefore the restriction of h to natural cardinalities is independent of which world's evaluator is used: it is the inverse of L there. This is stronger structural information than the finiteness equivalence, without a claim that the natural-cardinality domains are externally standard.

Necessity of pure arithmetic is already a consequence of the recorded C5+Atomicity=>No Pure Contingency theorem. It should not be advertised as a new consequence of this isomorphism.

## 20. Pure definitions cannot split a propositional Boolean cell

Assume C5 + Atomicity_t. This section extends the **recorded** atom-transposition argument for No Pure Contingency; its automorphism construction is in `writeups/c5-and-atomicity-imply-no-pure-contingency.md`. The new point is to retain propositional and hereditary-core parameters. It is a theorem schema for each pure formula/term, never a quantifier over formulas.

For propositions p_1,...,p_n and a bit vector epsilon define the Boolean cell

    c_epsilon := conjunction_i (p_i if epsilon_i=1, otherwise not p_i).

Empty cells are allowed. Let A(pbar,abar) be a pure formula whose additional free parameters abar belong to the original hereditary rigid core H of section 6 (over the original individual sort e and Boolean truth sort {bottom,top}). In particular arbitrary individual parameters and rigid relations on individuals are allowed. This is **not** the expanded core taking arbitrary propositions or worlds as a new individual sort.

**Theorem.** Every cell is decided by A:

    c_epsilon<=A or c_epsilon<=not A.

Consequently A belongs to the finite Boolean algebra generated by the p_i; explicitly,

    A = disjunction_epsilon
          (c_epsilon and (c_epsilon<=A)).

The coefficients c_epsilon<=A are bivalent. This is a Boolean-cell normal form with necessary coefficients; it does not say that one fixed truth table describes A for every parameter assignment.

### Proof by a transposition fixing the parameters

Suppose a cell c has nonbottom intersections with both A and not A. Atomicity gives atoms w<=c and w'<=c with w<=A and w'<=not A. They are distinct. The recorded transposition F exchanging w,w', extended by conjugation to all types, fixes every logical constant. Since w and w' belong to the same cell, it fixes every p_i.

It also fixes each element of the original hereditary rigid core. Prove this by induction on type. It fixes individuals because the individual component is the metalinguistic identity. It fixes top and bottom. For a supported rigid relation R in a higher core domain, all core arguments are fixed by induction and its values there are top/bottom. Arguments outside the core remain outside it: an involution that fixes every core element cannot send a noncore element to a core element. The support condition makes both original and transformed values bottom there. Hence the conjugation fixes R. The required pointwise identities lift by C5's BF and Intensionality.

The pure-term substitution lemma for the recorded automorphism now says F(A)=A. But w<=F(A) iff w'<=A, contradicting w<=A and w'<=not A. Thus no cell is split. Since the finitely many cells join to top, the displayed normal form follows.

At type e the automorphism is used as an identity substitution, not as an unavailable term of type ee. This preserves the fixed relational type system.

### Consequences

With no propositional parameters, every pure formula whose free parameters lie in H is necessarily true or necessarily false. This strengthens the recorded *closed*-sentence No Pure Contingency schema: the formula may quantify over the entire original intensional hierarchy, and its free ordinary mathematical parameters need not be closed or pure. It need not be an intrinsic core-language formula.

In particular every pure relation on individuals is rigid, even if its definition uses higher-order quantification. With one propositional parameter, A(p,abar) is one of bottom, p, not p, top. With n propositional parameters, at most 2^(2^n) different propositions are obtainable for a fixed assignment of those parameters and any choice of original-core parameters.

### A sharp obstruction to definable world choice

Call f:tt an atomic-world choice operation if

    f(bottom)=bottom;
    forall p!=bottom . Atom(f(p)) and f(p)<=p.

Boxed Functional Choice supplies such an f: use the serial relation selecting bottom from bottom, and an atom below every nonbottom p otherwise. Under C5 its selection graph consists of stable order/identity/atomhood conditions, so BF also makes the chosen condition necessary for the fixed f.

Suppose such an f is given by a pure term with finitely many propositional parameters pbar and original hereditary-core parameters abar. For any nonzero Boolean cell c of pbar, the proposition f(c) is definable from those same parameters, since c itself is a Boolean term in pbar. The theorem puts f(c) in their finite Boolean algebra. Since f(c) is nonbottom and lies below the cell c, it must equal c. Hence **every nonzero cell is an atom**.

Conversely, if every nonzero cell is an atom, an atomic-world choice operation is definable from pbar alone: fix the metalinguistic finite order of the cells and select the first nonzero cell below the input proposition. The formula is the finite disjunction of each cell conjoined with the bivalent condition that it is the first qualifying cell. Atomicity and the cell partition ensure a qualifying cell exists for every nonbottom input; bottom produces bottom.

Therefore a finite tuple of propositional parameters can define atomic-world choice (even allowing arbitrary original-core parameters) **iff its nonzero Boolean cells are all atoms**, equivalently iff it generates the entire propositional Boolean algebra. In particular, under boxed Functional Choice and AxiomOfInfinity_t, an atomic-world choice operation exists but **none is definable from finitely many propositions and original hereditary-core parameters**. The same negative statement holds with no core parameters, or only individual parameters.

This is a definability obstruction, not a failure of Functional Choice. It shows precisely why a world-choice operation in an infinite-world model must itself supply additional intensional structure beyond finitely many proposition names and ordinary core mathematics.

If the atomic-world set has an externally finite positive size m, the minimum number of propositional parameters needed is exactly ceil(log_2 m), even with arbitrary finitely many original-core parameters available for free. Necessity follows because n propositions have at most 2^n nonempty cells, each of which must be one atom. For sufficiency, enumerate the m atoms, assign distinct n-bit labels, and let p_i be the finite join of the atoms whose ith bit is 1. Their nonempty cells are exactly the atoms, and the fixed finite selector term above works. This numerical statement concerns an actual finite m; it does not assume that every internal natural cardinality is externally standard.

**Definability warning.** The assertion is about denotation by a pure lambda term with the specified parameters. It is not about unique descriptions using current truth. The actual atom is uniquely described by `Atom(w) and w` with no parameters, but in a contingent model it has no closed pure term. An atom transposition changes the designated truth point; it need not preserve current truth of a formula used as a unique description. Accordingly no model-theoretic definable-closure claim is being smuggled into the term-definability theorem.

## 21. A necessary uniform definite-description operator collapses contingency

At the propositional type, write

    Desc(delta):=forall X^(tt) . (exists unique p . Xp) -> X(delta X),

where delta has type (tt)t. Then over C,

    exists delta . box Desc(delta) iff Extensionality.

For the forward implication, fix such a delta and any p. Put

    X_p(q):=(p and q=top) or (not p and q=bottom).

At every world this predicate has a unique member. Thus if p is true, delta(X_p)=top; if p is false, delta(X_p)=bottom. The assumed necessary description condition applies at every world to the same input entity X_p and the same output entity delta(X_p). NI preserves whichever output identity holds now. Therefore p cannot change truth value. Every true p is necessary, giving the Fregean Axiom and hence Extensionality. Equivalently, E(p):=delta(X_p) is a fixed necessarily correct BE evaluator, so section 2 applies.

Conversely, under Extensionality use

    delta(X):=exists p . Xp and p.

Since propositions are top or bottom, this proposition equals the unique X-member whenever one exists. Extensionality necessitates itself, so this same lambda term satisfies Desc at every world.

Boxed Plenitude gives the weaker `box exists delta Desc(delta)`, by the canonical local descriptions below. It does not give one description operator that works necessarily. Under boxed Plenitude plus propositional contingency, there can be no **closed pure term** denoting a local description operator either: Desc of that term would be a closed pure truth, hence necessary by recorded No Pure Contingency, and the preceding theorem would collapse contingency.

This isolates a risk in expanding the language with a "logical" definite-description operator: if its unique-description axiom is required necessarily for one fixed operator, it is incompatible with propositional contingency. Merely allowing a world-specific existential witness at each world is the consistent boxed-Plenitude principle.

## 22. A single evaluator canonically computes every actual Boolean join

Assume Unique BE, with evaluator E. For every relational type tau=sigmabar t and X of type tau t, define

    Sup_E(X)[abar] := exists Y^tau . E(XY) and Y[abar].
    Inf_E(X)[abar] := forall Y^tau . E(XY) -> Y[abar].

These are respectively the algebraic least upper bound and greatest lower bound of the **actual X-family**. The family predicate need not be rigid, and its members need not be rigid. The resulting join/meet need not be rigid either.

For the join, every current X-member Y has E(XY)=top, so Y<=Sup_E(X). Conversely suppose Z is an algebraic upper bound of every current X-member. For each current Y, if XY then Y<=Z, and if not XY then E(XY)=bottom. Thus every current Y necessarily satisfies the implication from E(XY) to Y<=Z. BF_tau collects the universal quantifier. At every world, every existential witness Y in the displayed join therefore entails Z at its tuple argument. Hence Sup_E(X)<=Z. This proves the LUB property. The meet proof is dual, or use complementation of all members and the join construction.

If X has exactly one actual member Y, its actual-family LUB is Y. Therefore

    delta_tau(X):=Sup_E(X)

is a canonical local definite-description operator at every relational output type. Its behavior on nonsingleton families is specified rather than arbitrary: it returns their Boolean join. In particular it returns bottom on an empty family.

If U(x,Y) is actually functional and serial, the operation

    f(x):=delta_tau(lambda Y . U(x,Y))

represents it, because each fiber is an actual singleton. Thus the same evaluator gives explicit witnesses for every Plenitude instance, as well as every Boolean Completeness instance. No arbitrary choice is used; the hypotheses C5+Actuality supply BF and the single propositional evaluator. Selection from nonempty nonsingleton families is a different demand, as the atomic-world choice obstruction in section 20 makes concrete.

## 23. The parameter-type jump and robustness under logical extensions

The finite-propositional-parameter obstruction does not apply to arbitrary rigid higher-order parameters. Indeed every proposition p is denoted from its rigid haecceity Hp by the term `exists q(Hp(q) and q)`. Rigidity of a predicate says its extension is stable; it does not say that the entities in that extension are themselves hereditary-core entities.

A sharper positive result for world choice is available under boxed Functional Choice: **one rigid property of propositions is enough**. The interpreted extensional core over the atomic-world sort has Choice, hence a well-order of that sort. Let R be such a rigid well-order and write b<a for its strict part. For each atom a define its initial-segment proposition

    I_a := exists b . Atom(b) and b<a and b.

The graph correspondence gives, for atomic b, `b<=I_a iff b<a`. Let C be the family of these initial segments,

    C(P):=exists a . Atom(a) and P=I_a.

This C is a rigid predicate of type tt: its atomhood and identity matrix is bivalent, and BF collects the quantifier. The original strict well-order of worlds is recovered from C alone by

    a<_C b iff exists P . C(P) and a<=P and not(b<=P),

for atomic a,b. If a<b choose P=I_b. Conversely P=I_c gives a<c and not(b<c); linearity implies c<=b, hence a<b. Thus the family of initial segments contains exactly the order information needed.

Define a pure term from C by

    f_C(q):=exists a . Atom(a) and a<=q
        and [forall b . (Atom(b) and b<=q)->not(b<_C a)] and a.

For nonbottom q its atoms form a nonempty available world subset, so it has a unique least member. The displayed selection predicate is rigid and has that single atom as its member; its join is therefore that atom. For bottom the join is bottom. Hence f_C is an atomic-world choice operation. No extra proposition parameter is needed once C is given.

In an infinite-world model this C cannot lie in the original hereditary core of section 6: otherwise section 20 would prohibit the selector. Concretely C contains nontrivial initial-segment propositions, whereas original H_tt is supported on {bottom,top}. Thus the parameter result is sharp in a substantive sense: no finite stock of proposition names plus original-core mathematics suffices, but one rigid predicate describing suitable intensional structure does.

Finally the obstruction is robust under logical-language extensions that commute with atom transpositions. In particular, adding infinitary conjunctions/disjunctions does not let finitely many propositional and original-core parameters split one of their Boolean cells: order automorphisms preserve every meet/join that exists, and the same substitution induction applies. For a full Gallin model this is simply the fact that a permutation of worlds commutes with arbitrary intersections and unions of truth sets. More general new logical operations require their own equivariance check; an arbitrary added choice constant cannot be assumed invariant.

With countably many propositional parameters that separate a **countable** world set, countable infinitary conjunctions can define each world as its full truth-profile cell. Given an external enumeration of those worlds, a countable disjunction selecting the first isolated world below the input defines atomic-world choice. This last statement explicitly changes the syntax to permit the countable profile conjunctions and the countable list of parameter names; it is not a theorem about the original finitary language. It illustrates exactly which resource escapes the finite-parameter obstruction, rather than suggesting that infinitary logical connectives by themselves break symmetry.

## 24. The nullary Tame Rigidity obstruction is vacuous

In C, for a proposition p (the empty relation tuple),

    WeakRigid(p) iff Rigid(p) iff (p=bottom or p=top).

If p is weakly rigid and true, weak persistence gives box p, hence p=top. If p is false, the antecedent of weak inextensibility with test bottom is vacuous, giving p<=bottom and hence p=bottom. Bottom and top are rigid directly: persistence is immediate, and their weak-inextensibility conditions reduce respectively to a vacuous entailment and box Z implies box Z. Necessitation gives the boxed equivalence as well.

Consequently TR_t and box TR_t are theorems of C. So are RP_t and WRP_t: the power property of bottom is the haecceity of bottom, and that of top is the union of the haecceities of bottom and top. Haecceities and their finite unions are rigid in C. Here t means the empty tuple, not a predicate whose argument type is t; the latter relation type is tt and is not covered by this observation.

The record `barcan-and-weakly-rigid-power-imply-necessary-tame-rigidity` explicitly identifies its BF-free instance as the empty-tuple instance. That implication is correct but adds no obstruction. The note in `tame-rigidity-and-rigid-power-imply-weakly-rigid-power` suggesting that a countermodel must fail boxed TR at type t is therefore incorrect under that reading. What follows from `necessary-tame-rigidity-and-rigid-power-imply-weakly-rigid-power` is only that a countermodel must fail boxed TR at some nonnullary relation type. Also, the implication WRP=>box TR_t cannot be contraposed from failure of WRP to failure of its consequent. No source record has been changed here.

## 25. A fixed-point cone separating Tame Rigidity from its necessitation

This is a new proposed symmetric ideally-full construction, with a direct verification below. It uses the existing qualitative-link model only as a tail with a weakly rigid relation that is not rigid. It is not a countermodel to TR+RP=>WRP.

Start with the qualitative-link one-object base of `symmetric-qualitative-links`, using the base as individuals. Adjoin one new isolated individual d; every old arrow and every old symmetry extends by fixing d. No arrow sends an old individual to d. Call the resulting object B, its endomorphism monoid M, and its symmetry group G. The ideal is still the finite subsets. There remains a weakly rigid nonrigid unary relation U: at h its extension is the qualitative fibre R(ha,hb), for the distinguished points a,b. The added isolated point does not alter the finite-prescription extension argument; a finite pinning set containing d simply imposes one automatically satisfied prescription. Thus the B_N criterion for weak rigidity is unchanged for U. At a collapse h, its extension is the two companions of ha=hb. Their finite haecceity union is a rigid test necessarily true of both; an additional collapse merging them leaves just one image in that test, whereas U still contains both companions of the image point. Hence hU fails weak inextensibility and U is not rigid.

Now adjoin a new object A with one individual *. Its only endomorphism is its identity. There is exactly one arrow i:A->B, sending * to d, and no arrows B->A. Composition satisfies m i=i for every m in M. The symmetry group at A is trivial, and the ideal is finite subsets. This is a category of functions, closed under composition, with the indicated symmetry groups. Apply the symmetric ideally-full construction: relational intensions are exactly symmetric finitely pinned ones. Interpret all optional signature constants by top.

For every relation type tau, an A-intension is a pair (E,S), where E is an arbitrary subset of the product of A-argument domains, and S is an arbitrary G-invariant subset of the product of B-argument domains. These are its extensions at 1_A and i. There is no pinning restriction: there is only one arrow to each possible target, so the empty set pins every such pair. Symmetry imposes precisely G-invariance on S. Transport along i gives the constant B-profile S. At every type, therefore, every transported A-entity is fixed by every B-arrow; this also follows from m i=i and functoriality.

For any subset E of the A-tuples define T(E) by extensions E at 1_A and iE at i. The set iE consists entirely of B-arrow-fixed tuples, so it is G-invariant. Thus T(E) is an admitted A-intension. It is rigid. At A its future extension is exactly the image of E, and at B that extension is a constant set of arrow-fixed tuples. Persistence follows immediately. If a test is necessarily true of every current member, it is true of each transported member at every future arrow; the exact-image description gives weak inextensibility. The same argument at B proves necessary weak inextensibility.

Hence A satisfies Rigid Comprehension at every relation type: T(E) is rigid and has any prescribed actual extension E. It follows that A satisfies Tame Rigidity. But B is accessible from A and fails Tame Rigidity by U, so A fails boxed Tame Rigidity.

Atomicity also holds at A at every relation type. The Boolean algebra just described is

    P(A-tuples) x P((B-tuples)/G),

where the second factor denotes arbitrary unions of G-orbits. It is a complete atomic Boolean algebra: a nonzero pair contains either an actual tuple singleton or one future G-orbit. The corresponding pair with the other component empty is an admitted atom. This is algebraic Atomicity in the database sense, not a claim that those atoms remain atoms under transport. The recorded Atomicity+RC theorem therefore gives RP at A.

In fact WRP holds at A too, by the new Atomicity+RC=>WRP proof independently found by the principles agent (its `maximalism-modal.md`, section 16). There is also a direct proof. Let F=T(E) be rigid at A, so iF is the constant fixed-tuple relation iE. Any weakly rigid Y<=iF at B is coextensive with the admitted rigid exact-image relation T_B(D), where D=Y's current extension is a subset of iE. Coextensive weakly rigid relations are identical, so Y=T_B(D). Every such D lifts to E_D={x in E:ix in D}; iT(E_D)=Y. Thus the weakly rigid power property of F is itself the exact-image relation of its actual extension, hence rigid. The converse identification F=T(E) uses that F and T(E) are coextensive weakly rigid relations at A.

Therefore this construction gives

    C + Atomicity + RC + TR + RP + WRP + not(box TR).

It follows in particular that WRP by itself does not imply boxed TR; the BF hypothesis in the recorded WRP+BF implication has substantive content at nonnullary types. The construction must fail BF at some relation type, as the recorded implication also confirms. This conclusion does not settle the remaining TR+RP=>WRP conjecture.

Further direct verdicts for the cone sharpen the separation. Boolean Completeness holds at A at every relation type because its Boolean algebra is the complete powerset product displayed above. Relational Choice holds there: choose one witness for each actual input tuple in the metatheory, put the resulting graph in the arbitrary first component E, and take the empty second component. This is ordinary relational choice, not an operation-valued selector or a necessary graph assertion.

Let r be the root-only proposition, with profile (true,false). It is the actual atom and is a strong atom: at the root it is an atom, and at the tail it becomes bottom and therefore decides every proposition trivially. The qualitative tail's true atom is G; along symmetries it remains G and along a collapse it becomes bottom. Thus the cone in fact satisfies boxed Strong Actuality. At the root it fails ND_t, since r differs from bottom but both transport to bottom.

There is an explicit failure of BF_t. The root has exactly four propositions and all their images at B are bottom or top. Define

    Q(p) := r or p=top or p=bottom.

Every root proposition necessarily satisfies Q: at the root r is true, and at the tail its image is bottom or top. But the tail has contingent propositions, such as its actual-world proposition G, for which Q is false. Hence forall p box Qp holds at A while box forall p Qp fails. The same obstruction refutes BF at each relational argument type by the standard constant-predicate embedding of propositions and its universal-quantification retraction. BF_e fails directly: the single root individual maps to d, and the admitted predicate with actual extension {*} and tail extension {d} necessarily holds of that individual but not of every tail individual.

Strong Leibniz at t also fails at A. The future-only proposition not r is an atom there and is the only nonzero part of itself. Its image at B is top, which is not an atom because the contingent G splits it. Thus no strong world lies below not r. The contrast with boxed Strong Actuality is intentional: there is a strong true atom at every point, although an atom representing the future-only region need not remain an atom.

There is also a singleton-individual variant that removes any dependence on new individual objects. Keep the same underlying bases and arrows for pinning, but interpret e by a singleton at both A and B. At B, adding the isolated fixed pinning-base point d changes no domain whatsoever: agreement on d is automatic, so finite pinning before and after the addition is identical, and symmetry is unchanged. Thus the tail is exactly the recorded `symmetric-qualitative-links-individuals-singleton` model at every interpreted type. Its recorded weakly rigid nonrigid witness lives at type (tt)t, using the codes C_z of qualitative nonpoints; the record's proof applies verbatim. The root powerset-product, exact-image and choice arguments also apply verbatim. This yields the same separation even with one individual everywhere. Only the preceding direct failure of BF_e is omitted: BF_e holds trivially in this variant, whereas BF at every relational argument type still fails.

More generally this is an entrance-cone lemma, not a peculiarity of links. Any one-object symmetric ideally-full tail with an arrow-fixed base point admits the added singleton root. Its root satisfies Atomicity, Boolean Completeness, Rigid Comprehension, Relational Choice, Strong Actuality and Weakly Rigid Power. A closed principle that fails in the tail cannot hold necessarily at the root. Adjoining an isolated fixed pinning-base point is conservative for a tail whose interpreted individuals are a singleton. Thus the lemma systematically separates this rich local package from the necessitation of any principle refuted by an appropriate singleton-individual symmetric tail.

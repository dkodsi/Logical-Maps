# Strong Possibility: density, universal theory, and algebraic embeddings

22 October 2026. Research subagent `/root/reflection`. Original arguments, not human checked or formalized. No repository records, Lean files, or generated database files edited. Direct source of the new arguments: misc, this note. Background definitions: Bacon–Dorr, *Classicism*, draft 16 May 2023, §2.6 p. 42, as recorded in `topics/classicism/background.md` and `principles/strong-possibility-r.yaml`. The coalesced-model background is Appendix E pp. 80–83; the author-hosted 1 July 2022 draft uses different pagination, Appendix E pp. 78–81. Do not cite the new equivalences or profile-model conclusions as published results.

## 1. Fixed framework and notation

The base is C, with the topic's relational type grammar. Write `Max` for the fixed pure Maximalist Classicism theory, and `SP` for the fixed pure Strong Possibility schema

    D P, for closed pure P such that Max+P is consistent.

There is no replacement of that metalinguistic side condition by C-consistency. Let

    H p := exists q (q and box(diamond q -> p)),
    D p := not H(not p),
    box p := (p=top),   diamond p := (p!=bottom).

C validates normal S4 and the Boolean-algebra laws for propositions. Boolean order is `a<=b` iff `a and b=a`, equivalently `box(a->b)`. Necessity of identity applies at every admitted type. All displayed equivalences below are C-theorems, so their universal closures may be necessitated; ordinary necessitation is never applied to an optional premise.

## 2. Exact density forms

The raw dual is

    D p <-> forall q (q -> diamond(p and diamond q)).                 (1)

A particularly short identity-only form is

    D p <-> forall r (r!=bottom -> p and diamond r != bottom).        (2)

For (1)->(2), suppose `r!=bottom`, i.e. `diamond r` is true. Instantiate (1) at `q:=diamond r`; S4 gives `diamond diamond r=diamond r`. Conversely a true q is nonbottom, so (2), instantiated at r=q, gives (1). In particular the antecedent may be strengthened from truth to nonbottom without changing the universal statement: the possibility of any r is itself a true proposition when r is nonbottom.

An alternative form uses possibility-fixed propositions:

    H p <-> exists r (r!=bottom and r=diamond r and r<=p),            (3)
    D p <-> forall r ((r!=bottom and r=diamond r)
                       -> r and p != bottom).                      (4)

Forward in (3), if q witnesses H p, take r=diamond q. S4 gives r=diamond r; q true makes r true and nonbottom, and the witnessing box gives r<=p. Conversely r!=bottom says diamond r is true, and r=diamond r makes r true. Using q=r in H proves the reverse implication. Boolean complementation gives (4).

Thus D p says that p meets every nonzero possibility-fixed proposition. It also says that p meets the possibility of every nonzero proposition. Crucially, (2) and (4) are universal finite Boolean combinations of typed identities; no unmodalized truth predicate remains in their matrices.

For completeness H p implies p by reflexivity, so p implies D p. These are enough for the schema equivalence below.

## 3. Reflection for universal identity sentences

Let U be a closed sentence

    forall x_1 ... x_k theta(x_1,...,x_k),

where theta is a finite Boolean combination of identities between arbitrary well-typed terms. Terms may contain lambda abstraction and quantifiers. The finite Boolean matrix is the requirement; no restriction to quantifier-free term syntax is imposed. Then

    C proves D U -> U.                                             (5)

Proof by contraposition. At an actual tuple violating theta, list the finitely many identity atoms occurring in theta. Every currently true identity remains true necessarily, by NI. Let q be the conjunction of the currently false identities' disequalities, taking q=top if the list is empty. It is true. At any possibility where diamond q holds, none of those false identities can have become true: if an identity became true, NI there would exclude every further q-world. Thus the complete truth assignment of the finitely many identity atoms remains the same wherever diamond q holds, and the transported tuple still violates theta. Therefore box(diamond q -> not U). This q witnesses H(not U), proving (5).

This proof uses neither BF nor a Barcan principle for H. In particular universal atomhood of a fixed proposition is covered. The usual functionality sentence is not automatically in this fragment: prenexing its universal antecedent introduces an existential quantifier.

## 4. Exact universal-theory reformulation of SP

Let UMax be the set of all closed pure universal identity sentences U of section 3 for which Max+U is consistent. Then, over C,

    SP is equivalent to UMax.                                     (6)

SP implies each U: its side condition gives the SP instance D U, then (5) gives U. Conversely, for any SP instance D P, Max+P is consistent. Since P->D P, Max+D P is consistent. Formula (2) shows D P itself belongs to the universal identity fragment, so UMax contains this very SP instance.

Every pure Max axiom is a closed identity disequality and therefore belongs to UMax (Max is consistent by the coalesced constructions). Thus a model of UMax is already a model of Max. The equivalence does not assume SP consistent, and does not replace Max-consistency by C-consistency.

Equivalently, if N is an SP model and E is a closed existential finite-Boolean-identity sentence, then

    N satisfies E  iff  Max proves E.                              (7)

The right-to-left direction uses N satisfying Max. If Max does not prove E, Max+not E is consistent; not E is a universal identity sentence, so N satisfies not E by (6). This is the precise sense in which an SP model has the smallest possible existential algebraic theory among Max models.

## 5. A disjunction-property consistency criterion

Pure SP is consistent if and only if Max has the following restricted disjunction property:

    For closed existential finite-Boolean-identity sentences E_i,
    Max proves E_1 or ... or E_n  implies  Max proves some E_i.      (8)

If SP has a model, apply (7) to that model and the proved finite disjunction. Conversely, if SP is inconsistent, the equivalent UMax is inconsistent. Compactness/proof finiteness gives finitely many U_1,...,U_n in UMax such that Max proves not(U_1 and ... and U_n). Put E_i=not U_i. Each E_i is existential in the prescribed fragment, and Max proves their disjunction. But Max+U_i is consistent, so Max proves none of the E_i. This violates (8).

Binary disjunction suffices because this existential fragment is closed under finite disjunction (all type domains are nonempty). This criterion is exact; it does not establish that the disjunction property holds. A finite incompatible collection of individually Max-consistent universal identity sentences would settle SP negatively.

## 6. Exact common-embedding criterion, allowing elementary extensions

Use a many-sorted first-order Henkin presentation of C. For an unambiguous algebraic signature L_alg, take one sort for every admitted type and, for every pure term T(xbar), a function symbol f_T interpreted by that term. This is a conservative term-operation expansion; it avoids any delicate claim that lambda elimination needs no additional symbols. Application, Boolean operations, equality terms and quantifier terms are all included as term operations. A term-valued quantifier operation is included, whereas the external actual-truth predicate Tr on type t is omitted from L_alg. Include Tr in the full first-order presentation L_full.

The universal/existential identity fragments above are precisely the universal/existential quantifier-free L_alg formulas, after conservative translation. Identity atoms use actual equality of typed entities. L_alg embeddings preserve all pure term operations, including quantifier-valued terms, but need not preserve actual truth.

For a Max model N, the following are equivalent:

(a) N satisfies SP.
(b) For every Max model M, there is an elementary extension M' of M in L_full and an L_alg embedding of N's reduct into M'’s reduct.

Proof (a)->(b). Add names for every entity of N and take its full algebraic diagram: equations and disequations, with no Tr-literals. Any finite conjunction of this diagram, existentially closed in its finitely many names, is an existential identity sentence E true in N. By (7), Max proves E, so M realizes that finite conjunction. These realizations are consistent with any finite part of M's elementary diagram because the two groups of names impose no mixed extra constraints. Compactness with the full elementary diagram of M gives M' and a map realizing N's complete algebraic diagram. Equations ensure preservation of every operation; disequations ensure injectivity. The elementary-diagram embedding identifies M with an elementary substructure of M'.

Proof (b)->(a). Given any U in UMax, choose a Max model M satisfying U. Its elementary extension M' satisfies U, and a universal L_alg sentence passes to the embedded reduct of N. Hence N satisfies every U in UMax, and (6) gives SP.

This criterion neither asserts that a single algebra embeds directly into every Max model nor preserves Tr. It is a sharpened model-theoretic equivalence, distinct from the paper's sufficient common injective BBK-model criterion. The paper's §3.6 criterion must retain its published attribution; this elementary-extension reformulation is an original deduction here.

## 7. The common term algebra and the remaining Henkin obstruction

Every pure-Max model and actual individual a contain the same algebraic substructure generated by a under pure term operations. Indeed, if C does not prove forall x (T(x)=U(x)), the unary Possibility+ consequence of pure Max gives diamond(T(a)!=U(a)), and NI implies T(a)!=U(a). Conversely a C-theorem identity holds. Thus the equalities among pure one-individual-term denotations are exactly the C-provable identities, independently of the model and the chosen a.

This shared term algebra satisfies every U in UMax as an abstract L_alg structure: embed it in a Max model witnessing U and use universal preservation. Consequently the UMax constraints have no contradiction in the bare algebraic signature alone. A contradiction with C would have to use the full Henkin truth/quantifier requirements.

This observation is not an SP consistency proof. An arbitrary ultrafilter on the algebra of propositional term profiles need not supply witnesses for quantifiers. For example, the sole individual term is a, whereas C-consistent formulas can demand another individual. More generally restricting an existing Henkin model to term denotations can destroy the quantifier clauses. The basic one-layer profile construction avoids this by retaining arbitrary actual extensions and unchanged component domains; its true identity-coordinate atom is a strong world, so section 9 shows that this basic model fails SP. The later retract hybrids destroy that strong-world property and realize large proper SP fragments. They nevertheless fail the admitted instance D StrongActuality: the root identity-coordinate proposition witnesses this concrete failure, as proved in `.reproduction/classicism-research/reflection-retract-fragments-20261022.md`, section 12. Thus these displayed hybrids are not full SP models.

## 8. Independent audits of the profile results

I read `.reproduction/classicism-research/profile-root-construction-20261022.md` and independently checked the main construction, finite Fregean atoms, internal countability, universal reflection, and the pointed-completeness criterion.

The arbitrary actual-extension coordinate plus the one-individual pure profile is closed under all terms. Outgoing quantifiers range over the unchanged component domains; no surjectivity of root transports is needed. At F and E_n worlds, Fregean implies Extensionality (recorded Bacon–Dorr result). Finite lambda case definitions make every relational domain full. The resulting finite extensional hierarchy is unique up to permutations of its n individuals, so all pure one-individual proposition profiles are constant on these pointed worlds. Thus A_n=F and E_n is an atom at the profile root, for every n. This certifies the Max-consistency needed before applying SP to its atomhood statement.

More generally, for a C-consistent closed pure A, Max+Atom(A) is consistent exactly when C(a)+A, with one fresh individual constant a, is complete. Incompleteness gives a pure unary P for which A and P(x), and A and not P(x), are both C-consistent; unary Possibility+ then supplies two nonzero parts of A in every Max model. Conversely pointed completeness makes each root profile constant on A-components. The remaining actual coordinate vanishes because no Max model can satisfy a finitely axiomatized complete pure theory A: otherwise the consistent recursively enumerable extension C+A would contain all Max axioms.

The last impossibility follows by dovetailing a C-proof of a pure identity I with a proof of not I in the alleged r.e. extension. Max decides which search must terminate, deciding C-identity theoremhood and hence C-theoremhood. Relational first-order validity reduces to the latter by higher-type universal closure; invalid relational structures have full extensional C-countermodels. This invokes Church's standard undecidability theorem, not an undocumented theorem about SP.

The profile root's proposition domain is externally countable, while all its higher types need not be. Its internal countability witness is legitimate because an arbitrary actual graph relation is admitted and the cardinality numerals are pairwise distinct across finite extensional components. This does not prove any SP-to-countability implication.

Finally, pure SP entails Atom(F and E_1). For any added relational constant c, universal closure R(c) is independently true/false in the full singleton extensional model by taking c top/bottom. Signature Max forces both A_1 and R(c), and A_1 and not R(c), nonzero, contradicting that atom. Hence pure SP plus signature Max is inconsistent for every admitted nonempty relational signature. This preserves the different metalinguistic side conditions and is stronger than the simple named-individual monism obstruction.

## 9. Strong Possibility rules out every strong world

At any relational type tau define

    Settle_tau(w) := forall Y^tau (w<=Y or w<=not Y),
    Split_tau(w) := exists Y^tau
                     (w and Y != bottom and w and not Y != bottom),
    SWorld_tau(w) := w!=bottom and box Settle_tau(w).

These agree with the topic's strong-world definition. Boolean algebra gives not Settle_tau(w) iff Split_tau(w). Thus

    forall w not SWorld_tau(w)
       iff forall w (w!=bottom -> diamond Split_tau(w)).             (9)

This says that every actual nonzero entity can possibly acquire a proper nonzero part. It is stronger than merely denying the Strong Leibniz Biconditionals, which could fail because only some nonzero entity lacked a strong world below it.

Let Atomless_tau be the usual sentence asserting every nonzero tau-entity has a proper nonzero part. C proves

    D Atomless_tau -> forall w not SWorld_tau(w).                   (10)

Fix w!=bottom and take the true proposition q:=(w!=bottom). Necessity of identity gives box(diamond q -> q): once w=bottom becomes true, it remains true, excluding any later q. The raw dual of D, instantiated at q, gives diamond(Atomless_tau and diamond q), hence diamond(Atomless_tau and w!=bottom), and therefore diamond Split_tau(w). Apply (9).

Max+Atomless_tau is consistent, witnessed at W in the independently audited hybrid construction, in fact simultaneously at all relational types. Therefore its SP instance and (10) prove

    pure SP -> forall w^tau not SWorld_tau(w), for every relational tau.

No extra BF, rigidity, choice, or cardinality principle is used. The conclusion is itself a universal Boolean identity sentence: expand box Settle as the identity Settle=top, so its matrix is w=bottom or Settle_tau(w)!=top. It could also be obtained from the universal-core characterization once its Max-consistency is certified.

This conclusion is compatible with actual weak atoms. The hybrid root has all its canonical pure atoms and an actual true atom, while each nonzero entity injects into an atomless target and can split there. The theorem does not establish SP implies not Actuality or not Atomicity.

## 10. A necessary standard finite bound gives strong possibility of Strong Actuality

For each positive external standard integer n, let B_n say that type t has at most n entities. The following is an additional C-theorem, with D still the distinctness-preserving possibility operator:

    box B_n -> D StrongActuality.                                (11)

Here StrongActuality has exactly the topic's definition: there is a true proposition v such that box Settle_t(v). This is a finite-bound result; no quantified internal finiteness, arithmetic induction, or BF is substituted for the external standard bound.

First prove a local lemma. Suppose a world has exactly k propositions, r is true and satisfies r=diamond r, and box(r -> B_k). Enumerate its propositions as distinct p_1,...,p_k and put d=AND_(i<j)(p_i!=p_j). Its finite Boolean algebra has a true atom w. Define v=w and d and r, which is true. At any accessible world where v is nonzero, its inequality v<=d gives diamond d, and NI gives diamond d -> d. Similarly v<=r gives diamond r, hence r. Thus the transported p_i remain distinct, and B_k makes them exhaust that future proposition domain. Since w is an atom, each actual p_i is settled by w. Those algebraic order statements are identities, so NI preserves them. Therefore v settles every proposition at that future world. If v is zero, it settles them trivially. Hence box Settle_t(v), and StrongActuality holds.

Now assume box B_n and fix any true q. Among the finitely many integers k<=n for which diamond(diamond q and AtLeast_k(t)) holds, choose the largest. This set is nonempty because q is true and type t is nonempty. At a witnessing world, diamond q is true, the proposition domain has exactly k entities, and box(diamond q -> B_k) holds by maximality and transitivity. Apply the local lemma with r=diamond q, using S4's identity diamond diamond q=diamond q. The witness world satisfies StrongActuality and diamond q. Therefore

    q -> diamond(StrongActuality and diamond q).

Universally quantify q and use the exact raw dual form of D to obtain (11). The finite maximum argument can equally be expanded into a finite disjunction proof in C; no maximization over an infinite class or optional-axiom necessitation is involved.

In particular, the complete-effective-theory bound from the independently audited arithmetic report gives, for every canonical pointed-complete pure cell A,

    C+A proves D StrongActuality.

This does not force StrongActuality at the A-world itself, and does not refute SP. A canonical cell may be reached at a world different from the SP evaluation point, while the latter can have an infinite proposition domain. It also does not classify the accessible finite-domain models as rigid or as a finite category.

## 11. Finite numbers of pointed completions give exact finite atom counts

Let A be closed and pure, and let S_A be the Stone space of complete consistent extensions of C(a)+A in the language with one fresh individual constant a. Its elements are complete one-individual theories, not merely complete closed-pure theories. Suppose first that S_A has exactly n elements, with 0<n<infinity externally.

A finite Stone space has isolating formulas. Thus there are pure one-variable formulas B_1(x),...,B_n(x), each implying A, such that C proves their pairwise incompatibility and their disjunction equivalent to A, uniformly in x, and each C(a)+B_i(a) is complete and consistent. These facts also follow directly by taking finitely many separating formulas between the n complete theories and using compactness. Since the incompatibilities and covering equivalence are C-theorems, necessitation makes the B_i(a) algebraically disjoint and their Boolean join equal to A; this is stronger than a merely actual partition.

The profile-root construction has one individual a. At every old component satisfying B_i(a), every pure one-individual proposition profile has constant truth by completeness of C(a)+B_i(a). The root itself refutes B_i(a): the finite-bound theorem for complete effective theories applies to C(a)+B_i(a), while Max has arbitrarily many pairwise disjoint nonzero pure propositions (for example the finite Fregean cells). Therefore B_i(a) is an atom at the root. Consequently the single universal identity sentence

    forall x^e, Atom_t(B_i(x))

is Max-consistent, for each i (and jointly for all i). Universal reflection gives this sentence in every SP model. Unary Max makes every B_i(a) nonzero. Their disjoint join A is therefore exactly the join of n atoms, so the Boolean interval below A is a finite Boolean algebra with exactly n atoms and 2^n entities.

Conversely, if S_A is infinite, then for every positive standard n choose n distinct complete pointed theories and separate them by finitely many formulas. This gives n pairwise C-incompatible, individually C-consistent pure one-variable formulas B_i(x) implying A. Unary Max makes all B_i(a) nonzero at every Max world, and their theorem-level incompatibility makes them algebraically disjoint. Thus the interval below A has at least n disjoint nonzero elements, for every standard n, in EVERY Max model. It is externally infinite and cannot be a finite Boolean algebra.

Combining the directions: a finite interval below A is Max-consistent exactly when S_A is finite; if it has n pointed completions, the smallest possible interval has n atoms, and SP forces exactly that finite interval. The empty case means C proves not A, so A is bottom and its interval has one element and no atoms. This is conditional reasoning about SP models, not an SP consistency proof.

If C+A is itself complete, the arithmetic finite-bound theorem gives a finite domain at each type in every model of C+A. Two elementarily equivalent models with every sort finite are isomorphic in the full typed Henkin signature, including actual truth. One proof takes a finitely branching tree of finite-sort bijections compatible with successively more atomic conditions; elementary equivalence makes every finite set of conditions realizable, and the finite-branching argument gives a coherent isomorphism. The signature has countably many types and operation symbols, and no finite-category claim is involved.

It follows that C+A has one typed Henkin model up to isomorphism. Every complete one-individual type is realized in its finite individual domain: finite satisfiability plus finiteness gives one common realizing individual. Two individuals have the same complete type exactly when an automorphism carries one to the other, by the same finite-sort isomorphism argument with those individuals named. Hence the finite number n above is exactly the number of automorphism orbits on individuals. In every SP model, the Boolean interval below such a complete A has precisely that many atoms. Pointed completeness is the transitive-orbit special case n=1.

## 12. Finite base domains with BF collapse D on pure individual formulas

Use the independently audited finite-base reconstruction in `.reproduction/classicism-research/finite-base-barcan-chain-20261022.md`. For fixed external positive n,m let K_(n,m) be E_n^e and E_m^t and BF_e and BF_t. For every pure formula P(x_bar), all of whose free variables have type e, we obtain the schema

    C proves K_(n,m) -> forall x_bar (D P(x_bar) <-> P(x_bar)).     (12)

Equivalently, the distinctness-preserving necessity H also agrees with truth on those pure formulas under K_(n,m). Quantifiers inside P may have any admitted types. This does not cover arbitrary free relational parameters or added relational signature constants. Ordinary possibility need not collapse: the A_chain example has diamond A_1 and not A_1.

Here is a finite modal-algebra proof. A finite propositional Boolean algebra B has finitely many atoms and its actual truth ultrafilter is represented by one atom u. Define the usual finite S4 relation R on its atoms: a R b iff, for every p, a<=Box p implies b<=p. Then Box p consists of exactly the atoms whose R-successors all lie below p; R is reflexive and transitive. Since Box p is the identity proposition p=top, its actual truth condition says

    u<=Box p iff p=top.

Therefore u has every Boolean atom as an R-successor. Call such atoms universal-root atoms. Any two universal-root atoms u,v can be interchanged by an automorphism of the finite frame: their successor sets are both all atoms, and an atom sees either one exactly when it is itself a universal-root atom, by transitivity. The induced Boolean automorphism preserves Box.

Every proper Box-fixed element excludes every universal-root atom. Indeed, if a universal-root atom lay below r=Box r, all atoms would lie below r, making r=top. NI makes each individual-equality value delta_e(a,b) Box-fixed; for a=b it is top, while for distinct a,b it is proper. Hence the above swap fixes every entry of the individual-equality matrix. Taking the identity map on the entire finite individual set and this swap on B therefore gives an automorphism of the finite base data. The finite-base reconstruction extends it recursively to an automorphism of the entire typed algebra, preserving every pure term operation and fixing every individual. In particular, every pure proposition term P(x_bar) is fixed by it.

Now suppose D P(x_bar) at a K_(n,m) world. Let d be the finite conjunction of all disequalities among its distinct individuals and among its distinct propositions. It is true. The raw D formula gives an accessible world at which P(x_bar) and diamond d hold. NI gives diamond d -> d, so the transport is injective at both base types. BF and finite enumeration make it surjective there as well. Thus it is an isomorphism of the finite base data, and the reconstruction also gives the corresponding typed algebra isomorphism.

Pull the target's actual truth ultrafilter back to B. It is represented by another universal-root atom v: preservation of Box and the target's actual identity condition again give v<=Box p iff p=top. Swap u and v by the automorphism above. Since P(x_bar) is fixed, its truth at v equals its truth at u. The witnessing world's P is true, so P is true at the original world. This proves D P -> P; the converse is D's general reflexivity theorem.

All steps can be stated in the standard complete action semantics of C, so completeness yields the displayed C schema. The argument does not necessitate K_(n,m), assert rigidity of transports that fail the finite disequality diagram, or require a finite presentation of the world category.

Further consequence of section 11. If the nonempty S_A is finite, each complete branch C(a)+B_i(a) has a standard finite t-bound by the arithmetic theorem. Taking the maximum of finitely many bounds and eliminating the fresh marker gives a C-theorem A -> AtMost_N(t). Universal reflection then gives D A -> AtMost_N(t). Max refutes this bound, since it makes arbitrarily many distinct finite Fregean cells nonzero. Hence

    Max proves not D A,

although Max proves ordinary diamond A. This is compatible with SP: Max+A is inconsistent, so A is not admitted by the SP side condition. The same conclusion applies to each complete closed pure cell. This finite-profile-rank result was also proved independently in `.reproduction/classicism-research/sp-finite-profile-rank-20261022.md`; section 11 records an independent proof/audit, not a priority claim.

## 13. Independent audits of finite complete cells with failed Barcan

I independently read both `.reproduction/classicism-research/finite-complete-cell-failing-barcan-t-20261022.md` and `.reproduction/classicism-research/finite-coalescence-bf-e-failure-20261022.md` and found the stated proofs sound.

For A_swap, the atom-swap is an automorphism of the typed logical algebra WITHOUT the chosen actual truth ultrafilter. Rootlike propositional transports preserve the truth of every source proposition; applying that observation to the entire quantified source coextension formula transfers coextension without assuming higher-type surjectivity. At a leaf, a nonfixed transported entity F=T(u) would make the source term exists z(Atom(z) and f=T(z) and z) transport to one of the two atoms, contradicting the root proposition image {bottom,top}. Every fixed target entity has a pure name obtained by joining T(z) over the two atoms. These facts yield the exact arbitrary-actual-extension times fixed-profile reconstruction and pointed completeness. The displayed BF_t and Functionality_tt counterinstances follow directly.

For L_2 and C_n, the relational type restriction is respected: no term with output e or individual-valued choice is used. In a two-individual leaf with one marked point, the other individual is distinguished by the case x!=a; finite relational case definitions then name every target relation. In C_n, the maximal unary-predicate count supplies all singleton leaf profiles, and these finitely many relational parameters likewise name all higher relational entities. The whole quantified coextension sentence again transfers at rootlike targets without a surjectivity assumption. These are complete cells failing BF_e, while A_swap is a complete cell failing BF_t. Thus the necessary finite-domain theorem does not imply base-type BF or rigidity.

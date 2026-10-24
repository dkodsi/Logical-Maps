# Retract grafts: positive fragments of Strong Possibility

22 October 2026. Original research arguments by the reflection subagent, with independent audits by the construction lane. No human check or Lean formalization claimed. No repository edits. Direct source: misc, this note. Background action/coalesced and finite-pin methods: Bacon–Dorr, *Classicism*, 16 May 2023 draft, Appendices D–E; local Dorr 19 October finite-pinned substitution constructions. The actual grafts and deductions below are new arguments, not attributed to those sources.

## 1. Retractions give the needed distinctness-preserving possibilities

In a C action model suppose arrows a:R->W and b:W->R satisfy b a=id_R. Every entity transport along a is injective because b is its left inverse. More directly, if a proposition q is true at R, its image at W is possible: transporting again along b returns q, true at R. Thus if a closed pure P is true at W, the same arrow a witnesses

    diamond(P and diamond q)

for every true root q. By the dual definition, D P holds at R. This argument is semantic and checks the actual definition; it does not assume all injective arrows are already characterized by D.

## 2. Relative-full set-map graft

Choose any set-indexed family of nonempty sets E_i, including E_0={*}. Add one new object for each E_i, with every set map between these new objects. Take disjoint old action components complete for C. For each new E_i and every old object V, add one arrow for each function E_i->V_e. Old component arrows compose by their individual transports. No old object has an arrow to a new object.

The individual action is given by these functions. At each new relational type use all full intensions whose transports to old objects land in the original component domains; old domains are unchanged. This relative-full restriction is stable under new-arrow precomposition because any composite into an old object remains an old-target arrow. Type and term induction prove closure: root/new logical operations have their usual truth and quantifier clauses; at an old target a term evaluated on transported parameters is an original component term, hence admitted. Lambda abstraction and eta are handled by the full intensions in the usual action construction. New cycles merely impose the functor identities already built into precomposition.

Every new object is pure Max: each C-consistent pure sentence has an old witness V, and every E_i has a function into V_e since both domains are nonempty. Old component truth is unchanged.

Choose a_i:1->E_i and the unique b_i:E_i->1. Then b_i a_i=id_1. Therefore every closed pure P_i true at the new E_i world is D-possible at the singleton root.

In particular, include one E_n of each finite size n. The root simultaneously satisfies

    Max + E_1 + Actuality + {D E_n : n>=1}.

Actuality is witnessed by the proposition whose only true new/outgoing coordinate is id_1 and whose old transports are bottom. It is an admitted true Boolean atom. The cardinality formulas E_n are honest SP instances: each is Max-consistent, indeed true at the corresponding new Max object. The schema Infinity_e in the map is not a single sentence; the construction yields every D(at least n), not a silently formed infinitary conjunction.

Arbitrary actual extensions of relations on individuals can still be prescribed at each new object, with bottom old coordinates. Hence the local full second-order transfer argument applies: formulas about individuals and relations on individuals, using actual coextension rather than intensional relation identity, evaluate as in a full ordinary structure on E_i. For example one can choose E_i=N and obtain D of the finite pure assertion that a full second-order Peano structure exists on all individuals. This is a single structural sentence, unlike the Infinity_e schema. No unrestricted claim about arbitrary modal or intensional pure P_i is made.

## 3. A finitely pinned retract with possible failure of Actuality

A simpler alternative uses new sets 1 and N, all maps between them, and finitely pinned rather than full relative domains. An entity at a new E is pinned by some finite S subset E: two arrows into the same target that agree on S give it equal transported values. Require old-target landing as before. New transport by f sends a support S to f(S); term closure uses the union of the finitely many parameters' supports.

At the singleton root every generator can be put in the support, so the root-only proposition {id_1} is admitted and gives Actuality. At the N world, any true proposition p has finite support S. Choose c outside S. The proposition true precisely at new endomorphisms of N fixing S union {c}, and false at other-target arrows, is admitted, true, and finitely pinned. An endomorphism fixing S but moving c keeps p true and falsifies this smaller neighborhood. Thus no true p entails all truths; Actuality fails at N. The retraction 1->N->1 therefore gives

    Max + E_1 + Actuality + D(not Actuality).

The presence of a true atom at the root is no obstacle to its becoming false but still possible at the target. This model does not claim full SP.

## 4. Hybrid profile-pinned graft: all finite-world atoms plus possible atomlessness

This sharper construction simultaneously meets the profile atom constraints and strong possibility of atomlessness.

New objects and arrows. Let R have one individual marker and no free propositional generators. Let W have one individual marker and countably many auxiliary propositional generators d_0,d_1,... . The logical propositions bottom and top are available as substitution values and fixed by every arrow. A new arrow sends the individual marker to the individual marker and sends each free propositional generator of its source to a target generator, bottom, or top. Thus R has only the identity endomorphism, there is a unique a:R->W, and arrows b:W->R are arbitrary assignments of all generators to bottom/top. Each such b satisfies b a=id_R.

Old arrows are all interpretations of the source individual/propositional generators in each old C-component object. Their composition with new arrows is substitution, interpreting bottom/top logically; their composition with old arrows is ordinary transport. No old->new arrows exist.

At each new relational type admit those full intensions satisfying both conditions:

1. They have finite generator support (the usual finite-pinning requirement).
2. At all old-target arrows their value is the interpretation of one pure term in finitely many source generators, i.e. an old-target term profile.

Old component domains remain unchanged. A term with finitely many parameters has support the union of their finite supports, and its old profile is obtained by substituting their old profiles into that term. New transport substitutes generator images in profiles and maps finite supports to finite supports; logical bottom/top contribute no new free support. Old landing follows from original component term closure. Consequently all C terms and logical operations are admitted, with the usual Henkin quantifier clauses at each object. This is the same simultaneous type/term closure argument as for the separately audited profile and pinned constructions; it does not restrict arbitrary models to term denotations.

Every new object is Max because the old components are complete. The proposition {id_R}, with bottom old profile and false at all other outgoing coordinates, is admitted and gives Actuality at R.

Put A_n=Fregean and E_n. Every new object is Max and hence refutes Fregean, so A_n has zero new-object coordinates. At R, an old profile uses only one individual marker and no free relational generator. Pure one-individual proposition profiles are constant over all pointed finite n-individual Fregean structures. Therefore, for every root p, p and A_n is bottom or A_n. Each A_n is nonbottom by the old finite extensional component. Hence

    R satisfies Atom_t(A_n), for every n>=1.

At W, every nonzero proposition p has finite support S. Pick a fresh propositional generator d outside S. Let h_0,h_1 be endomorphisms of W fixing S and sending d to bottom/top, respectively. Finite pinning gives h_i(p)=p. Take an arrow f witnessing that p is true somewhere. Then p is true at f h_i, whereas d is false at f h_0 and true at f h_1. Both p and d, and p and not d, are therefore nonbottom. Thus every nonzero p has a proper nonzero part: W satisfies propositional Atomlessness.

The same argument works at every relational type. A nonzero relation has a witnessing arrow and tuple; varying d leaves the transported relation and that target tuple unchanged. Multiplication by the constant relation d splits it into two nonzero parts. Hence W satisfies the full Atomlessness schema.

By section 1, R satisfies D P for each closed finite conjunction P of these atomlessness instances, and in particular D(not Actuality). We have therefore constructed a model of

    C + Max + E_1 + Actuality
      + {Atom_t(Fregean and E_n) : n>=1}
      + {D P : P is a finite conjunction of Atomlessness instances}.

All these D P are actual SP instances: P is true at the Max world W. This is a positive fragment, not consistency of all SP. In particular the root has an actual atom even though an atomless Max world is distinctly possible. An old atom can acquire new subpropositions at an accessible world; reflection of universal identities is backward, not forward.

## 5. Limits

The graft does not preserve an arbitrary selected old Max model's truth when that model is promoted to a new retract target. Its domains are completed or restricted according to the explicit new construction. Thus one cannot insert every Max-consistent P as a target by assertion and infer full SP. The difficult obligation is still to realize arbitrary Max-consistent truth while retaining a common injective source algebra. The universal-theory and elementary-extension criteria are recorded separately in `reflection-universal-core-20261022.md`.

## 6. Countably many propositions in the hybrid root

The root R in section 4 has exactly two outgoing new-object arrows, id_R and a:R->W. Its proposition is determined by those two truth coordinates and its old pure one-individual-term profile. There are countably many such profiles. Hence its proposition domain is externally at most countable. It is infinite because the finite-world propositions A_n are pairwise distinct nonzero atoms. Thus it is externally countably infinite.

Every arbitrary actual root extension of every relational type is still admitted. To see this explicitly, prescribe an arbitrary extension S at id_R, the empty extension at a:R->W, and the bottom term profile at all old arrows. At R pinning by its unique individual generator suffices: new arrows to any given target are unique, while an old arrow is determined by that individual's interpretation. Thus this is an admitted intension. Its image at W is finite-pinned: every new endomorphism h of W satisfies h a=a, every return b satisfies b a=id_R, and old composite arrows have the chosen bottom profile. In particular a return recovers S automatically by composition; it imposes no requirement that S equal the empty actual extension at W. This checks the point where a retraction might otherwise seem to obstruct freely chosen root extensions.

Consequently the internal countability proof from the pure-profile root applies without change. The property whose actual extension consists exactly of the standard e-cardinality numerals is admitted and is actually inductive, so the impredicative predicate N_e has exactly that actual extension. The numerals are pairwise distinct because their old profiles differ in sufficiently large finite extensional components. Choose an external injection of the root proposition domain into these numerals and prescribe its graph as an actual root relation. That relation witnesses the exact background Ctbl_(e,t)(top_t) predicate.

Thus the positive fragment in section 4 can additionally require internal countability of all propositions. This is an existence theorem for the constructed fragment. It neither proves SP implies countability nor identifies countability with Countable Boolean Completeness.

## 7. The atomless target has uncountably many propositions

The same hybrid gives both countability and its distinct possibility of failure. Fix one auxiliary generator d of W. For every subset S of the countable set of free propositional generator symbols, define p_S by:

* at a W-endomorphism g, it is true exactly when g(d) is a free generator belonging to S;
* at every return W->R and every old-target arrow, it is false.

It has support {d} and bottom old profile, so it is admitted. Different subsets S are distinguished by a substitution taking d to a generator in their symmetric difference. Thus W has at least continuum many propositions.

Every actual extension at W is also available. Given an arbitrary relation extension H over the W argument domains, assign H at every arrow with new target W, assign an arbitrary fixed extension G at every arrow with new target R, and use the bottom old profile. This intension is empty-pinned: subsequent composition changes only the target category of the coordinate, and both the W-target and R-target choices are constant over arrows to those targets. Old landing is bottom. In particular the standard-numeral predicate used in section 6 is admitted at W too, so N_e(W) has exactly its standard countable extension.

Therefore Ctbl_(e,t)(top_t) is false at W. In the topic's exact relational definition a countability witness assigns a nonempty set of N_e-indices to each proposition, and different propositions have disjoint sets of indices. Taking the least standard numeral in each assigned set would inject the externally uncountable proposition domain into omega, impossible.

The root R is countable by section 6, W is a Max model of its negation, and R retracts into W. Consequently the combined positive fragment additionally satisfies

    Ctbl_(e,t)(top_t) and D(not Ctbl_(e,t)(top_t)).

The D-instance is legitimate because its negated countability sentence is Max-consistent, witnessed by W. Countability itself implies its own D-instance by reflexivity. Thus this one model handles both opposed countability SP instances without proving full SP or any general cardinality bound on SP models.

## 8. Unified target satisfying the full BF schema

The hybrid can be enlarged without changing its root conclusions. Give W countably many free generators of EVERY admitted type. In addition it has a distinguished individual marker z; R has only z and no free generators. New substitutions fix z. Free individual generators may be sent to any target free individual generator or z. A free relational generator of type sigma may be sent to another target generator of the same type or logical bottom_sigma/top_sigma. R->W is still the unique marker inclusion a. Every W->R substitution sends all free individuals to z and all free relational generators to logical bottom/top; all such b satisfy b a=id_R. Old arrows interpret every generator freely, with z interpreted as an arbitrary old individual.

Retain finite pinning and old-target pure term profiles in the source generators. The same support-substitution and term-profile argument verifies C. Every new object is Max. R remains monist, has Actuality, has externally and internally countably many propositions, and retains every canonical atom A for which C(a)+A is complete. In particular all Atom(A_n) survive. W now has countably infinitely many individuals, is atomless at every relational type, and has uncountably many propositions and standard N_e. Its actual relation extensions remain arbitrary as in section 7.

At W the full BF schema holds, in its equivalent converse-domain form

    diamond exists x^sigma F(x) -> exists x^sigma diamond F(x),

for every admitted type sigma. Let an arrow f out of W and a target entity y witness the premise. There are three cases.

* Old target. Choose a fresh sigma-generator c outside a finite support S_F of F. Change its interpretation to y while leaving S_F fixed. The transported F is unchanged and the transported generator c is y, giving a W witness.
* New target W. Choose a finite support S_y of y. A new substitution g can rename every free generator in S_y to a fresh generator of the same type outside S_F, with distinct images; it fixes z and the logical constants. Define f' to agree with f on S_F and send each renamed g(s), for s in S_y, back to s. These requirements are compatible by freshness. Then f'g fixes S_y, so f'(g(y))=y. Finite pinning gives f'(F)=f(F). Thus the W entity g(y) witnesses diamond F under f'. If y is the distinguished individual z, the same argument is immediate with empty free support.
* New target R. Write f=b. Take x=a(y). Since b a=id_R, b(x)=y, and the same arrow b witnesses diamond F(x).

This covers e as well as every relational type; the fresh individual generators are exactly what was missing from the e=1 target variant. It does not make BF true at the monist root.

Arbitrary actual relation extensions, together with ambient set-theoretic choice, also give Relational Choice and Transversal Choice at both new objects: choose the relevant actual selector set/graph and admit that extension. No Functional Choice conclusion is made.

Consequently one and the same root model satisfies the conjunction of

* pure Max, E_1, Actuality, internal countability of all propositions;
* every canonical finite-world atom Atom(A_n), and more generally every Max-compatible atomhood of a closed pure sentence;
* D P for every closed finite conjunction P of instances of BF, Atomlessness, Relational Choice, Transversal Choice, and the sentence not Ctbl_(e,t)(top_t), since W satisfies all of them.

Because W's individuals form a countable set and all actual relations on them are available, W also satisfies the finite pure full second-order assertion that a Peano structure exists on all individuals (in the coextensional local fragment). That sentence may be included in the finite conjunction P as well. All such D P are legitimate SP instances because W is itself Max. This is a large, explicitly modeled SP fragment. It still does not decide consistency of full SP.

## 9. Countability is not Countable Boolean Completeness in these models

Both new objects refute the Countable Boolean Completeness instance with counting type e and Boolean type t. There are only countably many old-target term profiles, even at the unified W: the generator supply is countable across the countably many types, and each term is finite. Enumerate all possible propositional profile terms as T_1,T_2,... . At the chosen full Fregean n-individual old component, fix one interpretation assigning every free relational generator its bottom value and every individual generator the same chosen individual. Define S subset of the positive integers by putting n in S exactly when T_n is false at that chosen pointed old component.

The actual property X={A_n:n in S}, where A_n=Fregean and E_n, is admitted at either new object by arbitrary actual extensions. It is internally countable: the A_n are distinct and the graph assigning A_n its standard numeral n is an admitted relation, with standard N_e.

Suppose X had a Boolean join J. For n in S, A_n<=J. For n outside S, not A_n is an upper bound of every member of X, so J<=not A_n. At the full n-individual Fregean old component, J must therefore be true exactly when n is in S. But J has some old profile T_k, which by construction has the opposite value at the k-th chosen component. Contradiction.

Thus even the root's internal countability of the entire proposition domain does not give Countable Boolean Completeness. The target W also refutes that completeness instance, so its negation can be included in the finite conjunctions P whose D-possibility the root satisfies. This argument uses an admitted internally countable family, not a merely external countable sequence substituted for an object-language property.

## 10. Finite unrestricted grafts and compactness

The unified construction admits finitely many unrestricted targets W_1,...,W_m. Each has a distinguished fixed individual marker, infinitely many free individual generators (of any chosen infinite cardinality), and countably many free generators of every relational type. Between new objects include all type-preserving substitutions of free generators into target generators or the indicated logical default values, always fixing the marker. R has no free generators, so there is exactly one a_i:R->W_i and all returns b_i satisfy b_i a_i=id_R. Profiles at every new object are pure terms in its own finitely many generators; all old component interpretations are unrestricted.

The BF proof includes arrows W_i->W_j. If f and y at W_j witness diamond exists x F(x), rename the finite support S_y into fresh generators of the corresponding types at W_i, disjoint from S_F. This gives g:W_j->W_i. Define f':W_i->W_j to agree with f on S_F and to undo g on S_y. Then f'g fixes S_y, so f'(g y)=y, while f'F=fF. This works even when the two individual generator sets have different infinite cardinalities, because only finitely many generators must be renamed injectively. Old-target and R-target cases are unchanged. Thus every target has full BF.

Atomlessness also survives every cross-arrow: precompose a witnessing arrow with source endomorphisms fixing a proposition/relation's finite support and sending a fresh propositional generator to top/bottom. The root has one truth coordinate for each new target plus its own, so its proposition domain is bounded by 2^(m+1) times the countable old profile set. It remains externally and internally countable. Canonical pure atoms remain intact because all new objects are Max and refute every finitely axiomatized pointed-complete pure sentence.

Arbitrary actual extensions at every new object are admitted by assigning a fixed chosen extension at each new target and the bottom old profile. Consequently each W_i supports every full local second-order structure on its chosen individual set. Here the local second-order fragment has individual variables and relation variables on individuals; any equality between relation variables is read as actual coextension, not typed intensional identity. It contains no modality or further quantification over entities of relational-input types. This restriction is essential: arbitrary full actual extensions do not transfer formulas that detect intensional duplicates. Each target has standard N_e, uncountably many propositions, Relational and Transversal Choice, and failure of the (e,t) Countable Boolean Completeness instance. For the last claim, even uncountably many individual generator names cause no difficulty: assign every auxiliary individual the same chosen individual and every relational generator bottom at the selected finite Fregean old components. Every old profile then normalizes to one of countably many pure one-individual terms, so the diagonal argument of section 9 still applies.

It follows that the following countable theory is consistent by ordinary many-sorted Henkin compactness:

* Max, E_1, Actuality, Ctbl_(e,t)(top_t), and every canonical pure atomhood Atom(A) whose Max-consistency was established by pointed completeness;
* D P for every pure closed local second-order individual-structure assertion P having a full model on an infinite nonempty set;
* more strongly, D(P and Q) for every such P and every finite conjunction Q of target truths from full BF, relational Atomlessness, Relational Choice, Transversal Choice, not Ctbl_(e,t)(top_t), and failure of the (e,t) Countable Boolean Completeness instance.

Each finite subtheory is witnessed by a finite graft with one target for each finitely many required full structures. The compactness model need not retain the explicit full-set target presentation or standard N_e; the conclusion is consistency of the listed object-language theory. Its Ctbl assertion is retained exactly. Finite individual-cardinality targets can be added for D E_n and local structures on finite sets, but cannot simultaneously have BF_e: a finite Max target would then make its finite individual domain necessary. Do not add BF_e to those finite-cardinality conjunctions.

This section concerns unrestricted-generator targets only. Combining these with targets whose generators are confined to selected canonical cells requires extra typed bounded-substitution closure; no such mixture is silently assumed here.

## 11. Joint compactness with necessarily separated cell patterns

The finite unrestricted grafts can be combined with canonical-cell pattern targets after the following additional closure is imposed. This paragraph records the construction lane's mixed-family repair and my independent audit.

Choose a family of canonical cells B, each closed, pure, C-consistent and complete after one individual is named, with the ADDITIONAL separation property C proves B -> box(not C) whenever B and C are distinct members of the family. The finite Fregean cells A_n satisfy this, as do the construction lane's audited rigid cells B_(n,k). Mere C-disjointness of complete cells does not suffice: a foreign cell could be false but nonbottom at a protected cell world, and a profile could distinguish its restricted generator from bottom. A pattern target has infinitely many restricted propositional generators of family B exactly for cells prescribed atomless there. At old objects a B-generator is interpreted as B or bottom. Its new substitutions may be a same-family target generator, the logical cell B, or bottom. A protected cell has no generators of its own family at that target.

Every BF target is given, in addition to its unrestricted generators of every type, infinitely many restricted generators of every cell family used by any pattern target. An unrestricted generator may map to any target generator of the same type or its logical bottom/top; for propositional generators also allow each logical cell B. This last clause is needed for closure under a composite unrestricted->restricted B-generator->B. Restricted generators always preserve their family or specialize to B/bottom. Old interpretations respect these restrictions, so composition with old arrows remains defined.

At a protected cell C in a pattern target, necessary separation makes every other family's cell proposition bottom as an entity there, so every other family's generator is bottom; all old profiles reduce there to pure one-individual terms and have constant truth. Since every new object is Max and C is false at new coordinates, C is atomic. At an unprotected cell B, every nonzero p<=B has an old B-world witness. A fresh B-generator, outside its finite support, can be interpreted as B or bottom at that same old target, preserving p and splitting it. Thus B is atomless below itself.

For BF at a BF target, an arrow into a pattern target and a witness y of finite support S_y cause no problem: rename each generator of S_y into a fresh source generator of the SAME restricted family, outside S_F, using the newly supplied reservoirs. Unrestricted target generators, if any, are renamed to fresh unrestricted source generators of their type. Define the modified forward arrow to undo these finitely many renamings and retain its original values on S_F. All substitutions respect the family restrictions, so the proof of section 10 applies. Old-target and return-to-R cases are unchanged.

The root still has no free generators and each new target receives one unique marker inclusion. Every return replaces generators by closed pure terms (and individuals by the marker), so the root's old profiles remain pure one-individual profiles. With finitely many targets its proposition domain remains countable. Its Actuality, internal countability, E_1, and all canonical atoms survive.

Therefore ordinary compactness gives one model retaining those root assertions and simultaneously satisfying:

* D of every finite consistent prescribed atom/atomless-below pattern on the necessarily separated cell family just specified, each pattern separately;
* all the D(P and Q) instances from section 10, with unrestricted full-structure/BF targets.

Each finite subset is realized by the corresponding finite mixed graft. This does NOT claim D of BF conjoined with an arbitrary protected-atom pattern: such a conjunction may be Max-inconsistent. Nor does it prove full SP. The patterns and the structural BF conjunctions remain distinct SP instances in the resulting consistent theory.

Correction to section 11, 22 October 2026: the initial wording incorrectly used mere disjointness of all canonical complete cells. The parent audit identified that false propositions need not be bottom. The pattern family is now explicitly restricted to necessarily separated cells; no arbitrary-canonical-cell pattern claim remains. Root atomicity for all canonical cells is unaffected.

Further audited families, 22 October 2026. The complete chain cells J_(n,k,H) from `finite-rigid-leaf-galois-classification-20261022.md` form another countable necessarily separated family. I independently audited the classification and the separation argument: a different chain cell stays false at every rootlike target by truth preservation, while every rigid leaf refutes all chain cells because ND_t holds there. Thus section 11 applies to finite prescribed patterns on this entire chain-cell family as well.

Targets for different necessarily separated families can coexist in one finite graft even when their UNION is not necessarily separated. Each pattern target carries restricted generators only for its own family's unprotected cells; cross-target maps send missing-family generators to the corresponding closed cell or bottom. BF targets carry the reservoirs for the union of the families, so the finite-support lifting proof still works. This gives D of each separately prescribed family pattern in one compactness model. It does not give D of a combined protected pattern mixing non-separated families at a single target. In particular the chain cells and their rigid leaf cells must not be silently treated as one necessarily separated family.

## 12. A specific admitted SP instance omitted by the present hybrids

The displayed hybrid constructions with an unrestricted atomless BF target do NOT satisfy full SP. In fact they refute D StrongActuality, although Max+StrongActuality is consistent: the ordinary one-layer full coalesced Max root has a true strong identity-coordinate atom.

At the hybrid root let q be the true identity-coordinate proposition, with zero old profile. At every old component its transport is bottom, so diamond q is false there. At every new object that can retain diamond q, StrongActuality is false. For the root and unrestricted targets this follows from their retraction into an atomless target. It also holds for the mixed pattern targets: inject their generator families into the corresponding fresh reservoirs of the unrestricted BF target and use the reverse generator assignment as a retraction. The target is globally atomless, so every nonzero entity of the source can acquire a split while remaining nonzero; no source strong world exists.

Consequently no accessible world satisfies StrongActuality and diamond q. Since q is actually true, the raw dual formula for D gives not D StrongActuality at the root. The finite grafts therefore witness the large stated SP fragment together with this particular failure. The compactness consistency result for that fragment may likewise include not D StrongActuality if desired. Nothing here proves that the abstract fragment logically implies its failure; the claim concerns these witnesses and that strengthened compactness theory.

A possible repair has NOT been completed. One could add a new StrongActuality object S with a retraction R->S->R, while forcing arrows S->W into atomless targets to factor through R, so that the true identity atom at S need not split. The BF proof at W would then require fresh-generator arrows W->S assigning arbitrary S entities, rather than the present finite-support renaming proof. Composition brings arbitrary R-entity coefficients into the substitution grammar. A valid richer coefficient construction, its C-closure, and its BF verification remain unproved. This is a research route only, not an additional consistency claim.

## 13. Joint retract graft for mixed protected chain and rigid-leaf patterns

The separately proved `mixed-chain-leaf-atom-patterns-20261022.md` extends the standalone pattern theorem to the UNION of the complete chain cells and their rigid leaf cells, despite accessibility between them. I independently audited that standalone proof. The following additional construction combines its patterns with the retract/BF targets of this report; it does not treat the union as necessarily separated.

Fix finitely many desired mixed-pattern targets. At each target, introduce infinitely many restricted propositional generators for every cell prescribed atomless. A chain-family generator for K has admissible old interpretations q satisfying q<=K. A leaf-family generator has the label F=(B,P), where P is the set of chain cells protected at that target. Its admissible interpretation q at an old object satisfies

    q<=B, and box(J -> q=bottom) for every J in P.

These are restrictions on entities and their entire forward cones. They are stable under every old transport: the first is an identity preserved by NI, and the boxed conditions persist by transitivity. Bottom is always admissible. Keep the old C-objects and all their domains unchanged. Arrows from a new source W to an old object V are labelled by admissible assignments of W's own generators in V. Composing with an old arrow transports those assignment values; precomposing with a new substitution substitutes its generator images in the labels. The stated stability makes these compositions well-defined. Bottom assignments retain C-completeness and hence pure Max at every new object.

Every BF target carries infinitely many unrestricted generators at every type AND infinitely many restricted generators of every constraint family appearing at any pattern target. New substitutions send a restricted generator only to a generator of the EXACT SAME family or to bottom. In particular a leaf generator of family (B,P) may NOT be sent to the closed cell B: that could violate a protected chain's entity-zero requirement. Unrestricted generators may be sent to any target generator of the same type or its logical defaults. Restricted generators at a return to R are all sent to bottom. These maps compose, preserve admissibility on old assignment arrows, and still satisfy b a=id_R because R has no free generators.

Use exactly the earlier domain condition: finite pinning on new substitutions, together with a finite old term profile in the source generators. Its substitution and abstraction closure is unchanged. At a protected chain world all other chain generators are zero by mutual chain exclusion, and every leaf generator is zero by its explicit protected-chain constraint. At a protected rigid leaf all chain generators are zero, as are generators of other rigid leaf families. Thus every finite profile reduces to a pure one-individual profile at a protected cell, proving that cell atomic at its pattern target.

For an unprotected chain K, a nonzero part of K has an old K-world witness, since every new object is Max and refutes K. A fresh K-generator can be given the old value bottom or K without changing that finite witness profile, so it splits the part. For an unprotected leaf B, copy the witnessed finite parameter profile into a standalone full rigid B-component, preserving its marker and actual truth atom. All protected chain cells are bottom throughout this standalone component; every foreign leaf cell is also bottom there. The copied parameter values therefore satisfy every constraint, and a fresh (B,P)-generator may be set to bottom or top there. This gives the required split. This is exactly the finite-profile replication argument in the standalone mixed-pattern proof, now applied to old targets with their assignment-labelled incoming arrows.

BF at an unrestricted BF target still has the same three cases. For an old-target witness, change a fresh UNRESTRICTED generator to the witnessed entity; no restricted-family condition is affected. For a new target witness y, rename its finite support into fresh source generators of matching type and EXACT matching family, using the reservoirs. A modified forward substitution reverses those finitely many renamings and retains its former values on the support of the predicate. Composition fixes the witness support and preserves the predicate, as before. Returns to R use the section/retraction pair. Thus every BF target retains BF at every type, alongside its atomlessness and the other previously proved target properties.

With finitely many new targets, the root still has only finitely many new truth coordinates and countably many pure one-individual old profiles. Its internal countability, E_1, Actuality and all canonical atoms therefore survive. Each target is a retract extension of R, giving D of its mixed pattern or of the relevant BF/full-local-structure conjunction. Compactness consequently combines all separately requested finite mixed chain/leaf patterns with all the structural D instances of section 10, while retaining those root assertions. No D of an arbitrary mixed pattern conjoined with BF is claimed.

The failure in section 12 remains. Every mixed-pattern target retracts into the BF target by injecting its countable generator families into the corresponding reservoirs and reversing that injection. Therefore it has no strong world; the root's identity-coordinate q still witnesses not D StrongActuality. This joint construction is a larger proper SP fragment, not a model of full SP.

Independent mathematical audit, 22 October 2026: the reflection lane checked the standalone mixed proof and this exact same-family-or-bottom extension, including old-target BF, new-target BF, root countability and the StrongActuality limitation. No human or formal verification is claimed.

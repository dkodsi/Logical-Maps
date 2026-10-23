# Independent atom patterns for complete chain cells and rigid leaf cells

22 October 2026. Original mathematical construction developed by the local-strengthening lane and independently audited in full by the construction lane. No human check, Lean verification, or repository-record change claimed. Direct source: misc, this note.

## 1. Exact claim and prerequisites

Let the countable family C consist of both:

* the rigid finite cells B_(n,k), for positive external integers n,k;
* one chain cell J_(n,k,H) for each transitive subgroup conjugacy class from `/tmp/classicism-research/finite-rigid-leaf-galois-classification-20261022.md`.

All cells are closed pure, C-consistent, and pointed-complete: every pure formula with at most one free individual variable has a uniform truth value at worlds satisfying the cell. Choose no duplicate equivalent representatives.

For a proposition X, say its Boolean interval is atomless if every nonzero q<=X has a nonzero proper subpart. This is stronger than simply saying that X is not an atom.

**Theorem.** For every externally chosen subset P of C, there is a model of C plus pure Max in which:

    Atom_t(X) holds for every X in P;
    the interval below X is atomless for every X in C\P.

Thus the atom status of a complete chain cell and that of its own accessible rigid leaf cell can be prescribed independently. In particular,

    Max + Atom_t(J_(n,k,H)) + atomlessness below B_(n,k)

is consistent. The converse pattern, with the leaf protected and the chain interval atomless, is consistent as well.

This is a Max-relative consistency construction. It is not a model of full Strong Possibility, and no combination with the separately constructed reflection retracts is asserted here.

We use three already proved facts:

1. Distinct chain cells are bottom as entities at each other's worlds.
2. Every chain cell is bottom as an entity at every rigid B_(n,k) world.
3. Distinct rigid cells B_(n,k) and B_(m,l) are bottom as entities at each other's worlds, by their incompatible boxed finite cardinality data.

There can nevertheless be accessibility from a chain cell to its own rigid leaf cell. The construction below explicitly accommodates that fact, rather than applying the old mutual-exclusion argument across the whole union.

## 2. Auxiliary generators and global component constraints

For each unprotected cell X in C\P, introduce countably many auxiliary propositional constants d_(X,j), j a positive integer. These are devices for constructing the model; the asserted theory and the cell formulas remain pure.

If X=K is a chain cell, require in every component world

    d_(K,j) <= K.                                            (1)

If X=B is a rigid leaf cell, require in every component world

    d_(B,j) <= B,                                            (2)

and, for every protected chain cell J in P, require globally

    J -> d_(B,j)=bottom.                                    (3)

The equality in (3) says that the generator is bottom **as an entity** whenever J holds. Equivalently one may write J -> Box(not d_(B,j)). Mere current falsity would not suffice.

Allowed generators in (1) and (2) are arbitrary subpropositions of the indicated cell. They are not restricted to the two choices bottom and the whole cell; those special choices will only be used for fresh generators in the splitting argument.

Fix a set of underlying action models complete for C, and add a full rigid S5 model for every B_(n,k). For each underlying model include every interpretation of the countable auxiliary language satisfying all the constraints at all its worlds. This is a set of components, and it is closed under the fresh-generator changes used below. Every underlying C-model has an allowed expansion with every generator bottom, so the bottom expansions alone retain the original completeness coverage. Global constraints ensure that every accessible object of an included expanded component satisfies them as well. No countability assumption on the underlying model domains or categories is needed.

## 3. The profile root

Use the audited one-individual profile-root construction, now allowing these auxiliary constants in the profiles. Add a singleton root o. For every component object V and every a in D_e(V), add an arrow (V,a), carrying the root individual to a. Composition uses transport of a, as in the original profile-root construction.

A profile is an auxiliary-language term T(z), with no free variable other than one individual variable z, identified by its entity values at every component object and marker. Each term contains only finitely many auxiliary constants. At relational tau=sigma_1...sigma_m t set

    D_tau(o) = P(product_i D_sigma_i(o)) × Profile_tau.

The first coordinate is any actual extension; transport uses the second coordinate. Interpret every auxiliary constant with actual truth false and its own constant-term profile. Application, abstraction, equality and quantification are the usual profile-root operations. Closure follows from finite substitution of parameter profiles; target quantification uses the unchanged full target domains, not the root profile images. Therefore the model validates C.

The bottom expansions of a C-complete family ensure pure Max at o: every C-consistent closed pure sentence is true at an accessible component object, independently of the auxiliary constraints.

Every cell in C is currently false at o. Indeed the root has infinitely many propositions: distinct finite rigid/Fregean pure cells already supply infinitely many different profiles across the bottom-expanded components. Each chain cell requires exactly four current propositions, and each rigid leaf cell requires a specified finite number. Thus their actual root truth coordinate is zero.

## 4. Every protected cell remains an atom

Fix a protected cell X. Every auxiliary generator is bottom as an entity at every component world satisfying X.

If X is a protected chain cell, an unprotected chain generator lies below another chain cell and is zero there by mutual chain exclusion. Every leaf-family generator is zero by (3).

If X is a protected rigid leaf cell, all chain generators are zero there because every chain cell is bottom at rigid leaf worlds. A generator belonging to another rigid leaf cell is zero by the mutual exclusion of distinct rigid cells. There is no generator family belonging to X itself, because X is protected.

Consequently, if q is any root proposition with finite profile T(z,d_1,...,d_m), its value at an X-world equals the pure one-individual term T(z,bottom,...,bottom). Pointed completeness of X makes its truth uniform across all such component worlds and markers. Hence q and X is either bottom or X as a profile, and its actual root coordinate is zero in both cases. Thus q and X is either bottom or X as an entity.

The cell X is nonbottom at o because an X-model with the bottom expansion is included. Therefore X is an atom at the root.

The inference from uniform component truth to profile identity is justified because every component object and its accessible objects occur in the profile family. Uniform truth agreement at all of them gives equality of the corresponding proposition intensions.

## 5. Every unprotected chain interval is atomless

Let K be an unprotected chain cell and let 0<q<=K at the root. Write q's profile using a term T(z) involving finitely many auxiliary generators. Since q's actual root coordinate is false, nonzeroness supplies an expanded component object and marker where K and T(z) are both true.

Choose a fresh d=d_(K,j) absent from T. Keep the underlying component and all its other auxiliary interpretations fixed. There are two allowed new expansions, interpreting this fresh generator globally as bottom or as the closed pure proposition K. Both satisfy (1); no extra constraint involving protected chains applies to a chain-family generator. All other constraints are unchanged.

At the chosen K-world, T remains true in both expansions, while d is false in one and true in the other. Both expanded components are included in the profile family. Thus `q∧d` and `q∧¬d` are both nonbottom root propositions. They are disjoint parts of q, so `q∧d` is a nonzero proper subpart. Every nonzero q<=K therefore splits.

## 6. Every unprotected rigid leaf interval is atomless

Let B=B_(n,k) be an unprotected rigid leaf cell, and let 0<q<=B at the root. Again a component B-world with some individual marker makes the finite term profile T(z,d_1,...,d_m) true.

Its local typed logical algebra is the full finite rigid B_(n,k) algebra. Copy this algebra, its chosen marker, its actual truth atom, and the finitely many values of the generators occurring in T into a standalone full rigid k-world S5 component. The copied T has the same truth value because all term operations and the actual truth ultrafilter are preserved.

The copied generator values satisfy all the global constraints on this standalone component:

* every chain cell is bottom at every world of the rigid component, so every copied chain-family generator is bottom and all conditions (3) are vacuous;
* every other rigid leaf cell is bottom there, so its generator values are bottom;
* the generators belonging to B may be arbitrary propositions in the rigid Boolean algebra, because B is top throughout this component.

These are exactly the restrictions already satisfied by the original finite parameter values at the witnessed B-world. Assign all unused generators bottom except for a fresh d=d_(B,j) absent from T. There are two allowed standalone expansions with this fresh generator bottom or top. Since B is top throughout the component, (2) holds in both; since protected chain cells are nowhere true there, (3) holds in both. All remaining constraints concern their individual generators and are unaffected.

At the copied marked world, T stays true and the fresh d takes the two opposite truth values. Thus `q∧d` and `q∧¬d` are both nonbottom at the profile root, splitting q. This proves atomlessness below B.

This replication step is the reason accessibility from a protected chain cell to B is not an obstruction. Generators are forced to be zero in those protected chain cones, while separate standalone B components can reproduce every finite B-profile and provide fresh splits. No backwards modal condition or predecessor is part of the copied local algebra.

## 7. Consequences and limitations

Sections 4–6 establish the theorem for an arbitrary chosen subset of the whole countable chain-and-leaf family. In particular Atom_t(J) together with pure Max does not entail Atom_t(B) for the rigid leaf cell made possible by J; the model can make the entire interval below B atomless. Atomicity of B likewise does not force atomicity of J.

As in the original profile-root construction, the root proposition domain is externally countable and the arbitrary actual coordinate supplies an actual atom. The construction can retain the earlier internal countability witness for propositions. These are compatibility observations, not an SP consistency argument. The isolated root atom is strong, so this basic construction does not satisfy full Strong Possibility; adding the separate reflection-retract features would require another proof.

Agent audit, 22 October 2026: the root research agent independently read sections 1–7 and checked the finite-profile replication, including higher typed terms, and the entity-zero protection of chain cones; no gap was identified. This is an agent mathematical audit, not a human check or formal verification. The standalone proof is frozen after this note. All consistency conclusions are relative to pure Max and the specified finite-cell atom patterns; consistency of full pure Strong Possibility remains unresolved.

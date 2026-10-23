# Relational universality and infinitary structure — research scratch

22 October 2026. Original arguments developed by OpenAI Codex in the relational research lane. No human check or Lean verification is claimed. No database records have been edited. The background is exactly C from `topics/classicism/topic.yaml`; T below is C + □Functional Choice. Results explicitly marked as semantic concern the displayed full models, not all models by stipulation.

## 1. Recorded inputs and scope

The proved-only engine confirms □Plenitude ⇒ □ND, Atomicity, □Atomicity, □Actuality, □BF, □Functionality, and □Boolean Completeness. C5+Atomicity ⇒ □Plenitude is recorded. C5+Atomicity ⇒ □Rigid Comprehension is recorded. Functional Choice entails Plenitude and Relational Choice, and their boxed conjunction gives □Functional Choice. Thus all these inputs are available in T. The prototype argument below in fact needs only □Plenitude until the explicitly choice-dependent strengthening.

Relevant local sources: `results/c5-and-atomicity-imply-necessary-plenitude.yaml`, `results/c5-and-atomicity-imply-necessary-rigid-comprehension.yaml`, `results/necessary-plenitude-r-implies-necessary-distinctness-necessary-r.yaml`, and the Plenitude/rigidity definitions in Background. Their published source is Bacon–Dorr, Classicism, draft of 16 May 2023, §§2.1–2.3, pp.21–34. None is cited as the source of the new arguments here.

The positive benchmark was changed by the user from C+□Plenitude to T during research. The user permits natural language extensions, including infinitary conjunction, and small files to track results. We preserve the distinction between a consequence, a genuinely stronger consistent axiom, and a new logical resource.

## 2. A simple strict enrichment: universal qualitative variability

For an argument type σ, define

    UQV_σ : ∃R^{σt} ∀X^{σt} (Rigid(X) → ◇∀x^σ (Rx ↔ Xx)).

Read this as: there is one property whose possible extensions include every rigid profile. `Rigid` has exactly the source definition, not merely persistence. The principal candidate is UQV_e. The restriction to the individual type is essential: the corresponding axiom at EVERY relational argument type is inconsistent with □Plenitude (Theorem 2 below).

A more transparent, equivalent definition over □Plenitude is: the atoms of the propositional Boolean algebra can be mapped onto the rigid properties of σ. This is an exact internal statement, not informal cardinal arithmetic:

    ∃F^{t(σt)} [∀a (Atom_t(a) → Rigid(Fa))
                 ∧ ∀X (Rigid(X) → ∃a (Atom_t(a) ∧ Fa=X))].       (WP_σ)

All quantification here is actual. The proposition a is used as a world only because it is an atom; no primitive world sort is added.

### Preparatory lemmas under □Plenitude

1. Identity propositions at every type are settled: NI gives x=y→□(x=y), and ND gives x≠y→□(x≠y). BF therefore makes equality-built formulas with object quantification settled too. In particular Atom_t(a) is settled.

2. A rigid property X has settled instances. Persistence gives Xx→□Xx. If ¬Xx, put Z=λy.y≠x. Whenever Xy actually, y≠x, so ND gives □Zy. Weak inextensibility of X gives X≤Z, hence □¬Xx. Conversely, a property all of whose instances are settled is rigid given □BF. First settledness at each x is itself necessary: in the true case □Xx and S4 give □□Xx, and in the false case □¬Xx and S4 give □□¬Xx. BF then gives □∀x settled(Xx), rather than illicitly boxing an unboxed premise. At every accessible point, if all instances of X necessarily satisfy Y, settledness and BF give X≤Y. Necessitating this discharged implication and using □BF gives full inextensibility; persistence follows from the same necessary settledness. This converse is used only for equality-built properties below.

3. Coextensive rigid properties are identical. If X,Y are rigid and coextensive, every actual X-instance necessarily satisfies Y by persistence; weak inextensibility gives X≤Y. Symmetrically Y≤X, hence X=Y.

4. For an atom a and any p, exactly one of a≤p and a≤¬p holds. If p is settled, a≤p iff p. Distinct atoms are disjoint. Atomicity gives an atom below every nonzero proposition.

### Theorem 1 — world-profile representation

Over □Plenitude, UQV_σ ↔ WP_σ, for every admitted argument type σ.

Forward. Given R, put

    (F_R a)x := □(a → Rx),

so F_R=λa x.□(a→Rx). Each displayed instance is an equality proposition, so it is settled; by Lemma 2 each F_R a is rigid. For rigid X, UQV supplies ◇Q where Q:=∀x(Rx↔Xx). Atomicity gives an atom a≤Q. For every actual x, a≤(Rx↔Xx). As Xx is settled, Lemma 4 yields Xx iff a≤Rx. Thus F_R a and X are coextensive rigid properties, hence identical.

Reverse. Given F witnessing WP, put

    Rx := ∃a (Atom_t(a) ∧ a ∧ (Fa)x).

Fix any atom b. Necessarily, whenever b is true, it is the unique true atom: distinct atoms cannot both be true. Since Atom(b) is necessary, at any such point the displayed existential reduces to (Fb)x. Hence b≤∀x(Rx↔(Fb)x). This does not require choosing a world externally. If X is rigid, choose b with Fb=X. NI preserves that equality, and b is possible, so ◇∀x(Rx↔Xx). This proves UQV.

Box audit: no optional assumption was necessitated illicitly. The atom-disjointness argument is a C theorem; the only hypotheses carried to other points are settled Atom(b), boxed background consequences, and the identity Fb=X via NI. The final equivalence may be boxed by first discharging the finitely many needed instances of □Plenitude.

### Theorem 2 — the higher-order barrier

Over □Plenitude, UQV_σ is impossible for every relational argument type σ≠e.

More generally UQV_σ is incompatible with an injection from the propositional atoms into σ. Here an injection may be encoded relationally, so the statement also applies to σ=e despite the absence of function types ending in e.

Proof with an operation j:t→σ injective on atoms (σ relational). Suppose F witnesses WP_σ. By Rigid Comprehension choose rigid X coextensive with

    D(y) := ∃a (Atom_t(a) ∧ y=j(a) ∧ ¬(Fa)y).

Choose atom b with Fb=X. At y=j(b), injectivity of j on atoms makes D(j(b)) equivalent to ¬(Fb)(j(b)). Thus X(j(b))↔¬X(j(b)), contradiction. For a relational injection graph the same proof uses its unique image of b.

For every relational σ=ρ1…ρn t, the map j(p):=λz1…zn.p is injective (apply an alleged equality to any tuple; each type is inhabited). Thus the required injection always exists. In particular UQV_t is contradictory. The same argument rules out polyadic profiles when at least one argument coordinate is relational, by fixing the remaining coordinates. It does not rule out purely individual n-ary profiles.

This is a precise limit on higher-order recombination within the strong positive theory. It should not be mistaken for a failure of Functional Choice.

### Choice strengthening of the representation

Under T, WP_σ is also equivalent to an injection of the rigid properties of σ into the propositional atoms. From F, Functional Choice selects an atom s(X) with F(s(X))=X for each rigid X, using an arbitrary actual atom as a default outside the rigid properties. If s(X)=s(Y), applying F gives X=Y. Conversely an injection of rigid profiles into atoms, together with a default rigid profile, gives a functional relation mapping each tagged atom back to its unique profile; Plenitude represents it and gives WP. This is an internal Cantor comparison, requiring no unsupported identification of Henkin domains with full external power sets.

### Explicit full-model consistency and separation

Take the standard full constant-domain S5 model with nonempty world set W, nonempty individual set D, proposition domain P(W), all admitted relational function spaces full, crisp identity, and a designated w0∈W. In ZFC it satisfies T. Rigid individual properties correspond exactly to subsets of D.

In this construction, UQV_e holds iff there is a surjection W→P(D): the function sends w to the extension of R at w. Conversely any such surjection defines R. Consequently:

* D=N, W=P(N), and R(w,n) iff n∈w give T+UQV_e with infinitely many individuals and worlds.
* D=N, W=N give T+¬UQV_e by Cantor, despite infinitely many individuals and worlds.
* If |D|=n and |W|=m are finite, UQV_e holds exactly when m≥2^n.

These are explicit models and countermodels, not merely lack of recorded arrows. UQV_e is therefore a genuine, simple strict enrichment of T. Since UQV_e is a closed pure sentence and T implies No Pure Contingency, adding UQV_e to T also yields its necessity. No change of the reference theory C in Maximalism is involved.

### Finite patterns versus full profiles

With D=N and W the finite subsets of N, let R(w,n) iff n∈w. Every finite assignment of positive and negative values to distinct individuals is realized: choose the world consisting of the finitely many positive individuals. No R in this model can realize all rigid profiles, because W is countable and P(N) is not. Thus even one relation exhibiting unrestricted finite independent variation, plus T and both infinities, does not entail UQV_e.

A formal single-sentence finite-pattern principle can quantify disjoint finite rigid properties X,Y and ask ◇∀x[(Xx→Rx)∧(Yx→¬Rx)], using the existing Frege-finiteness apparatus. The full-profile principle avoids that apparatus and is simpler to state.

### Recombination reading

For a fixed R, identify its profile at an atom a with F_R a. UQV is equivalent to: (i) R has an everywhere-true possible profile and an everywhere-false possible profile, and (ii) its possible profiles are closed under patching any two profiles along an arbitrary rigid region X. The nontrivial direction patches the true profile on X with the false profile outside X. Conversely full profile realization immediately gives every patch. This gives a direct qualitative reading: two extremes plus unrestricted recombination.

## 3. Further branches (separate agent reports)

`quotient-abstraction-lane.md`: Actuality/quotient equivalence, typed quotient obstruction, recursively normalized extensional Henkin hierarchy, and the proposed infinitary full-model representation theorem.

`retraction-extension-lane.md`: Sikorski extension from T; exact retraction/completeness criterion; modal extension obstruction and finite amalgamation.

`homogeneity-amalgamation-lane.md`: Boolean automorphism extension, finite-parameter locality, and definability obstruction for UQV.

Reports may still be under development. Their filenames identify scratch documents, not database entries or completed formal verifications.

# Independent audit: finite-signature SP forces explicit Barcan and Functionality failures

22 October 2026. Gallin-audit agent. Independently checked `signature-sp-barcan-20261022.md`, `audit-signature-to-pure-sp-20261022.md` §10, and their finite-cell/profile interfaces against the original Barcan, Functionality, signature Max and signature Strong Possibility records. Ordinary mathematics; no main database changes, Lean verification, human checking, or SP consistency claim.

## Verdict

**PASS.** For every fixed finite signature Sigma, the proposed construction gives a Barcan counterpredicate at every original input type and explicit distinct functions with equal actual values at every allowed output type. For a signature with infinitely many relational constants but finitely many individual names, the individual-input part remains valid. The stable-cell step, closed retract and handling of names all preserve the required reference language.

## 1. The stable cell and its atomhood

Let Delta be B_(1,2) together with c=top_tau for every relational constant c:tau in the finite signature. The cell has one individual and four propositions and includes the type-t C5 sentence. The local finite-cell result gives the full finite hierarchy. All individual names must denote its sole individual. All relational names are fixed by every Boolean-atom permutation because they denote the appropriate constant-top relations.

Consequently Delta describes one pointed truth-isomorphism class: Boolean-atom permutations act transitively on the possible actual atoms and preserve every named value. With no individual names, the anonymous individual marker adds no distinction because there is one individual. With names, the closed-profile construction applies. Thus the previously established complete-cell atom argument does give

    Con(Max(C(Sigma))+Atom_t(Delta)).

The profile root has infinitely many propositions, so Delta is actually false there, ensuring that the profile equality of its cuts also agrees in the actual truth coordinate. The nonzero finite component witnesses Delta's nonbottomness. These are the required interfaces to the earlier profile theorem; arbitrary current coextension is not being mistaken for identity.

Atom_t(Delta), after expanding Boolean order, is a universal Boolean combination of identities whose terms may contain Delta's internal quantifiers. That is within the identity-reflection lemma: internal term complexity is not an extra outer quantifier alternation. Its correctly referenced SP_Sigma instance therefore yields actual atomhood. The separate full finite interpretation with all relational constants top proves C(Sigma)-consistency of Delta, so signature Max yields Diamond Delta.

Stability is justified term by term. C proves B_(1,2)→Box B_(1,2). Each additional conjunct c=top_tau implies its own box by NI. Finite conjunction and the modal laws give the C(Sigma)-theorem

    Delta→Box Delta.

Since Box Delta is defined as Delta=top, a future point where Delta is true identifies Delta with the **top entity**, not merely an actually true proposition. This is the essential strengthening used next.

## 2. The explicit proposition counterpredicate

Set Phi(p)=Delta→(p=top or p=bottom). From Atom(Delta), for each actual p the Boolean atom law gives

    Delta≤p or Delta≤not-p.

Each inequality is a term identity, so NI preserves the selected inequality at every future point. At a future Delta-point, stability turns Delta into top. In the first case top≤p gives p=top; in the second top≤not-p gives p=bottom. At a future point where Delta is false the material conditional Phi(p) is true. Thus every actual p satisfies Box Phi(p).

No optional atomhood assumption was itself necessitated. Only the particular actual cut identity was preserved by NI, and the stability implication was already a C(Sigma)-theorem.

For the other half, C(Sigma) proves that Delta implies failure of forall p Phi(p), since its four local proposition entities cannot all be the distinct top and bottom. Necessitating this discharged theorem and combining it with Diamond Delta gives

    not Box forall p Phi(p).

Equivalently, at the accessible Delta-point a local nonbivalent proposition witnesses the failure. Such a local proposition need not be the image of any source proposition. The proof therefore gives the required strict counterinstance rather than accidentally assuming Barcan surjectivity.

## 3. Every relational input: the closed retract is valid

For alpha=rho_1...rho_h t, both

    c_alpha(p)=lambda xbar.p,
    r_alpha(X)=forall xbar X[xbar]

are admitted closed pure operations. The empty argument list is the identity case. Beta and H's vacuous quantifier laws, using standing nonemptiness, make r_alpha(c_alpha(p)) logically equivalent to p. The theorem-level Logical Equivalence rule yields the entity identity r_alpha(c_alpha(p))=p.

Hence Phi_alpha(X)=Phi(r_alpha(X)) is a closed Sigma-predicate. The source side follows by instantiating the already proved forall p Box Phi(p). At a Delta-point choose a nonbivalent local p and the admitted local X=c_alpha(p); the retract identity makes Phi_alpha(X) false. This proves failure of BF_alpha without selecting an evaluation tuple, introducing individual names, or relying on Functionality.

## 4. The actual individual-domain theorem and BF_e

Let u be the finite number of individual constant symbols, with an arbitrary relational-constant part. For u≥1 the named closed-profile root has exactly those u symbols as actual individuals. Its Max(C(Sigma))-consistency of

    U_Sigma=forall x (x=a_1 or ... or x=a_u)

is therefore legitimate. This universal identity formula reflects from its SP instance. Distinct name symbols have unprovable C(Sigma) equality, as witnessed by a two-individual interpretation separating the selected pair; signature Max therefore makes them actually pairwise distinct. Thus SP_Sigma forces exactly u actual individuals. For u=0 the singleton-marker root and the universal identity form of E_1 give the one-individual result.

This is unboxed actual cardinality. It does not make the individual transports injective, and it does not contradict future points where names coalesce.

For u≥1 use Psi(x)=OR_i(x=a_i). Actual enumeration and NI give forall x Box Psi(x). Signature Max supplies Diamond E_(u+1), using a full finite consistency witness with arbitrary name interpretations. At that future point the u transported names occupy at most u values, so some local individual fails Psi. Therefore not Box forall x Psi(x).

For u=0 choose an arbitrary actual a using standing nonemptiness and use Psi_a(x)=(x=a). Actual E_1 gives the source side; Diamond E_2 gives the target failure. The parameter a is a bound object variable in the eventual closed counterexample, not a newly adjoined signature constant. Thus no change to the SP side condition occurs. These arguments use no finite diagram of the relational names, so they retain validity when there are infinitely many such names.

## 5. Explicit Functionality failure without circular extensionality

Suppose P:alpha t satisfies forall x Box Px and not Box forall x Px. For relational beta define the closed constant-value constructor c_beta:t→beta, and set

    f=lambda x.c_beta(top),
    g=lambda x.c_beta(Px).

At each actual x, Box Px is the identity Px=top. Congruence for the admitted operation c_beta gives fx=gx. This step uses ordinary identity congruence and beta; it does not assume the Functionality instance being refuted or infer abstraction identity from mere actual coextension.

If f=g, NI gives Box(f=g). The H/C theorem that equality of these displayed operations implies forall x Px follows by application, beta, and nonemptiness of the finitely many output argument sorts. Necessitating that theorem and using the boxed equality yields Box forall x Px, a contradiction. Thus f and g are distinct while agreeing at every actual input.

The output beta=t is the zero-output-argument case; the same proof works. Every admitted original function output is relational, so the construction covers all Functionality type instances. In the zero-name individual case, quantify the same parameter a used in P=Psi_a; no forbidden operation into e appears.

## 6. Scope retained

The relational-input argument needs a finite full signature diagram. It is not extended to infinitely many unspecified relational constants. The individual-input argument needs only finitely many individual names. All conclusions are formal consequences conditional on SP_Sigma; none supplies an SP model or settles its consistency. Failure at every type means a counterpredicate or counterfunction pair at each type, not that all predicates or all pairs fail.

No mathematical repair was required. The audit also implemented the requested clarity refinements in the separate world-geometry note: W is explicitly nonempty, and the regular-limit reservoir cardinal mu bounds |S| as well as the chosen witness supports.

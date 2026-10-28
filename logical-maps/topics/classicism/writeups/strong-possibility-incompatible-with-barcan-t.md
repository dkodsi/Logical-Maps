# Strong Possibility: explicit Barcan failures and the signature boundary

Original proof: OpenAI Codex, prompted by Daniel Kodsi research, 22 October 2026, signature-sp-barcan-20261022.md and finite-c5-profile-cells-20261022.md. Independently reviewed and streamlined for integration 28 October 2026. Ordinary mathematics only; no assertion that either Strong Possibility theory is consistent.

## 1. The native arrow and the stronger scoped theorem

Pure Strong Possibility is incompatible with BF_t. By existing schema implications this also excludes full BF and full Functionality. The proof actually supplies a counterpredicate at every relational input type, and the individual-input argument below supplies the remaining type e.

For each fixed FINITE signature Sigma, the same all-input theorem holds for SP_Sigma. It also holds at input e if Sigma has only finitely many individual constant symbols, even with infinitely many relational constants. The relational-input construction uses a finite complete signature diagram. There is no unguarded claim about arbitrary infinite Sigma.

The map's native Strong Possibility (signature Sigma) node allows arbitrary fixed signatures and does not impose a finite-name restriction. Consequently the finite-signature result must not become an unqualified native incompatibility attached to that node. It is supplied here as a conditional proof for a future signature-aware presentation. The pure instance, whose reference theory is Max(C), is a valid native arrow now.

## 2. The one stable finite cell needed for the pure proof

Let K be boxed ND at t, the single closed sentence equivalent over C to C5 by the recorded type-transfer theorem. Let E_m^sigma mean exactly m entities at the fixed type. Put

    B = K and E_1^e and E_4^t.

B is consistent: use one individual, the four-element proposition Boolean algebra, and full finite function domains with crisp equality and quantifiers given by Boolean meets. It is stable, B→Box B. C5 supplies BF; the finite enumerations remain exhaustive by BF and retain distinctness by ND.

Every B-point has the same full typed logical structure. Functionality bounds each function carrier by the finite function set. Conversely equality masks, which are Top/Bottom under C5, realize every finite function. BF makes local finite enumerations exhaustive at every accessible point, so the quantifier value is the corresponding finite meet. The Boolean algebra, crisp equality, application and abstractions are therefore uniquely determined up to isomorphism. Permuting its two Boolean atoms moves the designated truth atom, so all pointed B-structures have the same pure theory, also with their unique individual marked.

In the singleton definable-profile root, every proposition is an arbitrary actual bit plus the denotation profile of a pure term with one individual variable. On B-components each such term has one fixed truth value. This is also true at every transported target. Thus for every root proposition p, B∧p is either B or Bottom as a whole entity. The actual B bit is false because the root has infinitely many propositions. A finite B-component proves nonzeroness. Hence this root satisfies pure Max and Atom(B).

All-type admission is the usual profile construction: substitute the finitely many parameter profiles capture-avoidingly in the term; the actual extension is unrestricted. At a component, bound variables range over its entire domain, not the image of root transport. This verifies abstraction and C's theoremhood-restricted Equivalence rule. The underlying profile construction is recorded in [the definable-root proof](coalesced-definable-root.html). The finite-cell argument below is supplied separately; it does not rely on that older writeup’s atomlessness assertion.

## 3. Reflection and the counterpredicate

For a closed universal Boolean combination U of identities, C proves Diamond_ne U→U. If U fails, choose an actual countertuple and a true DNF clause for its negation. Let q be the conjunction of its disequalities, or Top if none. Its equality literals persist by NI. Also NI gives Box(Diamond(a≠b)→a≠b); since Diamond q implies the possibility of each conjunct, Box(Diamond q→not U). The true q therefore witnesses Box_ne not U. No BF is used. Identities may have quantified terms as their operands.

Atom(B) is in this fragment and is consistent with Max(C) by the profile root. Pure SP therefore entails Atom(B). It entails pure Max as well, hence Diamond B by B's C-consistency.

Define the closed pure predicate

    Phi(p) = B -> (p=Top or p=Bottom).

For every current p, atomhood gives B≤p or B≤not p. Each alternative is a literal identity and persists. At any possible point where B is true, stability makes B=Top; the transported p must then be Top or Bottom. At points where B is false the implication is true. Thus every current p necessarily satisfies Phi.

But Diamond B gives a possible point with four propositions. Two of them are neither Top nor Bottom, and Phi fails there. Therefore

    forall p Box Phi(p), and not Box forall p Phi(p).

This is exactly a BF_t counterinstance. All necessitations were of unconditional C laws or were applications of NI to literal identities; no optional premise was necessitated.

## 4. Other input/output types and finite signatures

For any relational alpha=alpha_1...alpha_h t, let c(p)=lambda xbar.p and r(X)=forall xbar X[xbar]. Vacuous-quantifier laws and standing nonemptiness give the C identity r(c(p))=p. The predicate Phi_alpha(X)=Phi(r(X)) has all current instances necessary; at a B-point a nonbivalent p and X=c(p) refute its necessary universal closure. This covers all relational input types without choosing an evaluation tuple.

For input e, pure SP entails the actual singleton-domain sentence E_1: that universal identity sentence holds in a pure-Max singleton root, so the same reflection applies. Fix any actual a. Every current x is a, hence necessarily x=a. Pure Max gives a possible two-individual point, where some local x differs from transported a. The predicate x=a refutes BF_e.

Every displayed BF counterpredicate P:alpha t gives Functionality counterfunctions at any admitted relational output beta: f(x)=Top_beta and g(x)=lambda ybar.Px. Each current equality f(x)=g(x) follows from Box Px. Whole equality f=g would, by NI and necessary coextension of identical relations, imply Box forall x Px, contradiction. No individual-output operation is used.

For finite Sigma replace B by Delta=B conjoined with c=Top_type(c) for each relational constant c. Individual names collapse at its one-individual points. The finite conjunction is stable and specifies one complete pointed signature structure. The corresponding Sigma-profile root makes Atom(Delta) consistent with Max(C(Sigma)), and the same reflection/counterpredicate argument works, always with that reference theory.

If there are u>0 individual names, the closed-profile root with those u names as actual individuals makes forall x(x=c_1 or ... or x=c_u) Max-consistent. SP forces it; signature Max makes distinct symbols currently distinct. The names therefore enumerate the actual e-domain. Their necessary equality cover fails at a possible u+1-individual point. For u=0 use the singleton-marker root. This individual argument tolerates infinitely many relational names, but neither it nor the finite diagram licenses relational-input conclusions for an arbitrary infinite signature.

## 5. Source and review obligations

Sources: the two research notes named above, §§1–6 and §§1–6,9 respectively; audit-profile-20261022.md §6.1; audit-signature-to-pure-sp-20261022.md §§9–10 for the exact signature-profile/domain theorem; the original definable-profile construction. All are ordinary source arguments checked in the integration review. The native pure arrow needs no signature conservativity, and no conjectured signature-SP-to-pure-SP implication is used. The finite-signature theorem remains conditional in the accompanying scope receipt.

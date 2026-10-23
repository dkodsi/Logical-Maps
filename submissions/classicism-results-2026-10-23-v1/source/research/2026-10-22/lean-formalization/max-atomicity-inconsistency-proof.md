# Pure Maximalism excludes unboxed Atomicity

22 October 2026. Mathematical argument by OpenAI Codex, developed from the earlier rigid-selector notes. Direct source of this argument: misc, this note, §§1–7. This is an ordinary proof in ZFC metatheory, not a completed Lean formalization.

The claim is about the original finitary pure relational language of C. All object-language types used below are built from t. The reference theory in Maximalism remains C.

**Theorem.** C together with pure Max(C) and unboxed Atomicity at type t is inconsistent. Consequently pure Max(C), over C, implies the negation of Atomicity at type t and excludes all-type Atomicity.

The proof constructs a single closed pure sentence S such that

$$
C\nvdash S=0,\qquad C+\mathrm{Atomicity}_t\vdash S=0.
$$

The first assertion is established by a Boolean-valued soundness argument. The second is a derivation in C using unboxed Atomicity. Max(C) supplies the single contradictory instance S≠0.

## 1 Atomicity annihilates the splitting sentence

For any term F of type t→t, write

$$
S_F:=\forall p^t\bigl(p\ne0\to
 ((p\wedge Fp)\ne0\wedge(p\wedge\neg Fp)\ne0)\bigr).
$$

Here 0 and 1 are logical bottom and top; p≤q is Boolean-algebra order, equivalently □(p→q). C proves the Boolean laws, necessity of identity (NI), the normal modal laws, and □p↔p=1.

**Lemma.** C proves

$$
\mathrm{Atomicity}_t\to S_F=0.
\tag{1}
$$

**Proof.** First reason in C alone. Suppose p≠0 and p≤S_F. Universal instantiation and p→p≠0 are C-theorems, so their necessitations, together with □(p→S_F), give

$$
\Box\bigl(p\to
 ((p\wedge Fp)\ne0\wedge(p\wedge\neg Fp)\ne0)\bigr).
\tag{2}
$$

If p∧Fp=0 currently, NI gives □(p∧Fp=0). Combining this with (2) gives □¬p, hence p=0, a contradiction. The same argument applies if p∧¬Fp=0. Thus C proves that F splits every nonzero part of S_F into two nonzero parts.

Now assume unboxed Atomicity_t and S_F≠0. There is an atom a≤S_F. The preceding conclusion gives both a∧Fa≠0 and a∧¬Fa≠0. Both are parts of a, and they are disjoint. Atomhood makes each nonzero part equal to a, which would make a=0. Contradiction. Hence S_F=0. ∎

Only C-theorems were necessitated. The necessary equality used in the proof comes from NI applied to a current equality; Atomicity was never necessitated. This is the b=1 specialization of the bounded-splitter argument.

It remains to construct a closed pure F for which C does not prove S_F=0. Naming an external selector would not meet that requirement. Sections 3–6 give its finite definition.

## 2 A sound Boolean-valued interpretation

For now work inside the constructible universe L. The Jech–Shelah theorem supplies a nontrivial rigid complete atomless Boolean algebra A. All cardinalities, function spaces and set constructions until §7 are computed in L.

The external input is the existence of such an algebra, not any assertion that its elements are first-order definable. See Jech and Shelah, *A Complete Boolean Algebra That Has No Proper Atomless Complete Subalgebra*, Journal of Algebra 182 (1996), pp. 748–755, theorem and corollary on p. 749, [primary source](https://shelah.logic.at/files/95558/566.pdf). A Boolean-algebra automorphism of a complete algebra preserves all existing joins because it preserves the order and least-upper-bound property, so the usual formulations of rigidity agree here.

Interpret the fixed type system by

$$
D_e=\{*\},\qquad D_t=A,\qquad
D_{\sigma\to\tau}={}^{D_\sigma}D_\tau\quad(\tau\ne e).
$$

Application and abstraction are ordinary function application and abstraction. Connectives are Boolean operations. Equality at every type has value 1 for literal equality of domain elements and 0 otherwise. Quantifiers are

$$
\llbracket\forall x^\sigma P(x)\rrbracket
 =\bigwedge_{d\in D_\sigma}\llbracket P(d)\rrbracket,\qquad
\llbracket\exists x^\sigma P(x)\rrbracket
 =\bigvee_{d\in D_\sigma}\llbracket P(d)\rrbracket.
$$

All these operations and all term denotations exist by completeness and fullness inside L.

**Soundness lemma.** Every C-theorem has value 1 under every assignment.

**Proof.** The propositional axioms are valid in a Boolean algebra. UI and EG follow from the defining bounds for meets and joins. Reflexivity and Leibniz's law hold because equality is literal. Capture-avoiding substitution has the ordinary substitution lemma, proved by induction on terms; beta and eta conversion consequently preserve denotations, including inside larger contexts.

MP preserves value 1. For Gen, if P→Q(x) has value 1 under every assignment and x is not free in P, the fixed value p of P is below every value q_d of Q(d); hence p≤∧_d q_d. For the existential rule, if x is not free in Q, every value p_d is below the fixed q, hence ∨_d p_d≤q. This verifies H's quantified rules.

If H proves P↔Q, the values of P and Q are equal under every assignment. Their lambda abstractions therefore denote literally equal functions, validating Logical Equivalence. More generally, substitution of these equal denotations into any term context, including under binders, preserves denotation. Thus both the Logical Equivalence and Logical Substitution presentations are sound.

The set of formulas valid under all assignments is consequently an H-theory containing Logical Equivalence, and it contains C by C's defining minimality. ∎

The rule list and the H-plus-Logical-Equivalence definition appear in Bacon and Dorr, *Classicism*, §§1.1 and 1.3; see Figure 2 and §1.3 of the [author-hosted draft](https://andrew-bacon.github.io/papers/Classicism.pdf). The bundle's fixed relational type system and reference theory are unchanged.

No homomorphism A→2 is used. In particular, this interpretation is being used as a soundness certificate for theoremhood, not as an ordinary pointed model obtained from an arbitrary ultrafilter.

## 3 A finite code for the required set universe

Set κ=|A|, which is infinite, and set U:=t→t. Then

$$
|D_U|=\kappa^\kappa=2^\kappa=|H_{\kappa^+}|.
\tag{3}
$$

The last equality follows because every subset of κ belongs to H_{κ+}, while every hereditarily size-at-most-κ set can be coded by a pointed well-founded relation on a subset of κ. There are at most 2^κ such codes.

For X of type U→t and E of type U→U→t, use the following finite formulas. E[u,v] means explicitly left-nested application (Eu)v.

$$
\begin{aligned}
\mathrm{Crisp}(X)&:=\forall u^U(Xu=0\lor Xu=1),\\
\mathrm{Small}(X)&:=\exists f^{U\to t}\ \forall u^U v^U
 ((Xu\wedge Xv\wedge fu=fv)\to u=v),\\
\mathrm{Crisp}_2(E)&:=\forall u^U v^U(E[u,v]=0\lor E[u,v]=1),\\
\mathrm{Ext}(E)&:=\forall u^U v^U
 ((\forall z^U(E[z,u]\leftrightarrow E[z,v]))\to u=v),\\
\mathrm{WF}(E)&:=\forall X^{U\to t}
 ((\mathrm{Crisp}(X)\wedge\exists u^U Xu)\to\\
 &\hspace{42mm}\exists u^U(Xu\wedge
       \forall v^U(E[v,u]\to\neg Xv))),\\
\mathrm{Rows}(E)&:=\forall u^U\,
       \mathrm{Small}(\lambda v^U.E[v,u]),\\
\mathrm{Fill}(E)&:=\forall X^{U\to t}
 ((\mathrm{Crisp}(X)\wedge\mathrm{Small}(X))\to
   \exists u^U\forall v^U(E[v,u]=Xv)).
\end{aligned}
$$

Let HCode(E) be the conjunction of Crisp₂, Ext, WF, Rows and Fill.

For crisp X, Small(X) has value 1 precisely when the extension of X injects into A, hence has size at most κ. The witness f is an arbitrary A-valued function, not a crisp characteristic function. All tests in this assertion are crisp, and fullness supplies every required injection.

**Coding lemma.** HCode is crisp, and HCode(E) has value 1 exactly when E presents the membership structure (H_{κ+},∈) on D_U. Such an E exists.

**Proof.** When E is crisp, it defines an ordinary relation on D_U. Every subset of D_U has a crisp characteristic function in D_{U→t}, so WF expresses actual well-foundedness inside L. Ext and WF yield a Mostowski collapse π:D_U→M onto a transitive set.

Rows implies that each element of M has at most κ members. For x∈M, each finite membership level below x has size at most κ; the union of these countably many levels has size at most κ. Therefore M⊆H_{κ+}.

Fill says that every subset of M of size at most κ belongs to M: pull that subset back along π, apply Fill, and collapse the resulting predecessor row. Membership induction now gives H_{κ+}⊆M. Indeed, if x∈H_{κ+} and every member of x lies in M, then x⊆M and |x|≤κ, so Fill gives x∈M.

Conversely, H_{κ+} is transitive; each of its elements has at most κ members; and a subset of H_{κ+} of size at most κ is itself hereditarily of size at most κ. Equation (3) therefore lets us pull its membership relation back along a bijection D_U→H_{κ+} to obtain E.

Finally, if E is noncrisp, Crisp₂(E) has value 0, annihilating the conjunction. For crisp E, Ext and Rows are crisp. In WF and Fill, noncrisp X makes its guarded antecedent false; for crisp X the remaining tests are crisp. Meets and joins of values from {0,1} remain in {0,1}. Hence HCode is crisp. ∎

Everything in HCode is a fixed finite formula. κ and H_{κ+} occur in its semantic analysis, not as parameters or new symbols in that formula.

## 4 A fixed finite formula for a well-order of the coded universe

Inside L,

$$
H_{\kappa^+}=L_{\kappa^+}.
\tag{4}
$$

For one inclusion, |L_α|≤κ for α<κ+, and L_α is transitive, so L_{κ+}⊆H_{κ+}. Conversely, given x∈H_{κ+}, choose a sufficiently large limit level L_θ containing x. Take an elementary hull of size at most κ containing every member of the transitive closure of {x}. Condensation identifies its transitive collapse with some L_α. The collapse fixes x, and |α|≤κ gives α<κ+, proving the reverse inclusion.

Fix a single parameter-free first-order set formula χ(x,y) defining Gödel's canonical well-order in L_{κ+}. The required formula is uniform; κ is not a parameter. The definability statement is recorded in Khomskii, *Regularity Properties and Definability in the Real Number Continuum*, Fact 1.2.10(2), pp. 14–15, [primary source](https://www.math.uni-hamburg.de/en/personen/khomskii/papers/Yurii_Khomskii_PhD_Dissertation.pdf).

Here is why the relevant interpretation of that formula fits our code. For α<κ+, the sequence of constructible levels through α, the finite-formula satisfaction relations for those levels, and the corresponding canonical-order recursion all have hereditary size at most κ. They therefore belong to H_{κ+}. First-order satisfaction for a set structure is definable by a finite formula, using a set-coded satisfaction relation and its recursive clauses. Its correctness in a transitive universe containing those objects follows by induction on finite formulas. The constructible hierarchy and order recursion are consequently computed correctly there.

Thus χ may be chosen by existentially coding those constructions through a level containing x and y and reading the resulting order. Every needed witness exists in H_{κ+}; every purported witness there has the correct interpretation. This proves the particular definability claim needed in (4). No claim about arbitrary, possibly ill-founded set models is used.

For a good E, let χ_E be the fixed translation replacing membership by E and making every set variable a variable of type U. It is crisp and defines a well-order of D_U. Under the unique collapse π_E it is the same order on H_{κ+}, independently of the presentation E.

## 5 Rigidity makes the transported order independent of the code

Use ordinary finite set codes c=(D,z,o,m,n) for an algebra carrier, zero, top, meet graph and complement graph. Kuratowski ordered pairs and a fixed nested five-tuple suffice. All of their definitions are first-order formulas in membership and equality.

For precision, write Tup_E(c,D,z,o,m,n) for that translated tuple relation, App_E(n,x,y) for coded graph application, and App₂_E(m,x,y,z) for application to the coded ordered pair (x,y). Require m and n to be graphs of total functions D×D→D and D→D, respectively. This is one finite first-order condition, denoted Graphs_E(D,m,n).

Define Iso_E(c,h), with h of type t→U, by existentially binding D,z,o,m,n and asserting

$$
\begin{gathered}
\mathrm{Tup}_E(c,D,z,o,m,n)\wedge
\mathrm{Graphs}_E(D,m,n),\\
E[z,D]\wedge E[o,D],\\
\forall p^t E[h(p),D],\\
\forall u^U(E[u,D]\to\exists p^t\,h(p)=u),\\
\forall p^t q^t(h(p)=h(q)\to p=q),\\
h(0)=z\wedge h(1)=o,\\
\forall p^t q^t\,
 \mathrm{App}_{2,E}(m,h(p),h(q),h(p\wedge q)),\\
\forall p^t\,\mathrm{App}_E(n,h(p),h(\neg p)).
\end{gathered}
$$

Under a good E, this says exactly that π_E∘h is a Boolean-algebra isomorphism from A onto the decoded algebra. It is crisp. The isomorphism conditions imply the Boolean laws on the decoded structure; no completeness predicate needs to be added to the formula.

Now put

$$
\begin{aligned}
\mathrm{Candidate}_E(c)&:=\exists h^{t\to U}\,\mathrm{Iso}_E(c,h),\\
\mathrm{Least}_E(c)&:=\mathrm{Candidate}_E(c)\wedge
 \forall d^U(\mathrm{Candidate}_E(d)\to\neg\chi_E(d,c)).
\end{aligned}
$$

Candidates exist. Copy A onto the ordinal κ. Its two operation graphs and five-tuple code have hereditary size at most κ, so this code belongs to H_{κ+}. Fullness supplies the map h to its representatives under E.

After collapse, the candidates are exactly the codes in H_{κ+} for algebras isomorphic to A by isomorphisms in L. This collection is independent of E. It has a unique least member c₀ in the fixed well-order. There is exactly one isomorphism

$$
i:A\longrightarrow\operatorname{carrier}(c_0).
$$

Indeed, if i and j were two, j⁻¹∘i would be an automorphism of A in L, and rigidity gives i=j.

Define the pure binary formula

$$
W(p,q):=\exists E^{U\to U\to t}c^Uh^{t\to U}\,
 \bigl(\mathrm{HCode}(E)\wedge\mathrm{Least}_E(c)
 \wedge\mathrm{Iso}_E(c,h)\wedge\chi_E(h(p),h(q))\bigr).
\tag{5}
$$

All quantifiers displayed together abbreviate successive individual quantifiers.

**Order lemma.** In the interpretation, W is crisp and is a well-order of A.

**Proof.** Every successful witness to (5) collapses c to c₀ and h to the same i. Hence W(p,q) has value 1 exactly when i(p) precedes i(q) in the fixed well-order of H_{κ+}. Conversely a good E exists, and its representatives of c₀ and i witness (5) whenever that order comparison holds. Bad E contribute 0 because of HCode. Thus the existential does not combine incompatible orders. ∎

This is the essential use of rigidity. It turns quantification over all presentations and isomorphisms into a single well-defined order.

## 6 The closed pure selector and its value

Write 0<q<p for q≠0∧q≤p∧q≠p. Define

$$
\begin{aligned}
\mathrm{Part}(p,q)&:=(0<q<p)\wedge
 \forall r^t(0<r<p\to\neg W(r,q)),\\
F&:=\lambda p^t.\exists q^t(\mathrm{Part}(p,q)\wedge q),\\
S&:=S_F.
\end{aligned}
\tag{6}
$$

These are finite pure definitions. Expand tuple and graph notation into their finite membership formulas, translate the fixed finite χ, expand HCode and W, and finally (6). Every definition depends only on earlier definitions. Every auxiliary object variable is bound. The only types required are t, U=t→t, U→t, U→U→t, and t→U, all admitted by the fixed relational type system.

In particular no A, κ, L, chosen code, order constant or selector constant appears as a free parameter of F or S. This construction asserts no general well-ordering or choice principle within C.

For any nonzero p∈A, atomlessness gives a nonzero proper part of p. The order lemma gives a unique W-least such part q_p. Part(p,q) is crisp, and its value is 1 exactly at q=q_p. Consequently

$$
\llbracket F\rrbracket(p)
 =\bigvee_{q\in A}
    \bigl(\llbracket\mathrm{Part}(p,q)\rrbracket\wedge q\bigr)
 =q_p.
\tag{7}
$$

Thus p∧F(p)=q_p≠0. Also p∧¬F(p)≠0: if it were zero, p≤q_p, contrary to q_p<p. Every nonzero p is therefore split, and the p=0 implication in S is vacuous. Hence

$$
\llbracket S\rrbracket=1_A,\qquad
\llbracket S=0\rrbracket=0_A\ne1_A.
\tag{8}
$$

Soundness gives C⊬S=0.

## 7 The contradiction and the role of the metatheory

The preceding construction was performed inside L. This does not assume V=L in the ambient metatheory or add it to C.

The finite syntax of F and S is fixed by §§3–6. If a C-proof of S=0 existed in the ambient universe, its finite proof code, including the finite H-proof certificates required for Logical Equivalence instances, would belong to L. Correctness of that finite syntactic proof is absolute. L would then contain a C-proof of S=0, contradicting the soundness calculation (8) carried out there. Thus the non-theorem conclusion holds in the ambient ZFC metatheory as well.

Because S=0 is a closed pure identity not provable in C, pure Max(C) contains the instance

$$
S\ne0.
\tag{9}
$$

Lemma (1), instantiated with the same closed pure F, gives

$$
C+\mathrm{Atomicity}_t\vdash S=0.
\tag{10}
$$

Equations (9) and (10) contradict one another. Therefore

$$
\boxed{C+\mathrm{Max}(C)+\mathrm{Atomicity}_t\vdash\bot.}
$$

The optional hypothesis is unboxed Atomicity_t. There is one Max instance, with reference theory C unchanged. The proof uses neither an infinitary extension of the object language nor object-language set-theoretic axioms. ∎

## Verification boundary

The elementary bounded-splitter module and the earlier conditional reduction have successful Lean module checks. The complete coding and model argument in this note is an ordinary mathematical proof; it has not been checked end to end by Lean. No database record, generated Lean statement, or original research note is changed by this file.

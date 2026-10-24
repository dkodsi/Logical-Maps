# Independent audit: standard Frege arithmetic and effective Gallin presentations

22 October 2026. Gallin-audit agent's independent mathematical audit of §§18–19 of `positive-effective.md`, with the exact H_0/H_ch coding from §§3–7 and the arithmetic/atomic-presentation interfaces in §§13,17. Source status of the new verification and §8 strengthening: original argument (`misc` if recorded). No main database edit, Lean claim, named human check, or literature-novelty claim.

## Verdicts

- **PASS:** I_sigma plus externally standard Frege numbers at the evaluation point interprets an omega-model of full second-order comprehension.
- **PASS:** the displayed pure fixed-point term gives a genuine external fixed point of Gregoriades' positive arithmetic operator; no unproved external completeness of the interpreted set family is used.
- **PASS:** every complete actual pure theory and every adequate truth-evaluable presentation under those hypotheses is nonhyperarithmetical and computes each hyperarithmetical real individually.
- **PASS:** the atomic-diagram result is valid for the specified auxiliary application structures. It uses finitely many hardcoded element indices, not a claimed uniform algorithm extracting arbitrary lambda values from an unnamed atomic diagram.
- **PASS:** the externally standard complete Henkin codes form a nonempty lightface Pi^0_2 class. The standardness test quantifies over all closed terms and, when requested, all closed world terms.
- **PASS:** the cited basis theorems supply standard positive solutions strictly below Kleene's O, the exact common-information HYP result, and no least Turing degree/hyperdegree among solutions or least oracle degree solving the problem.
- **DETAIL SUPPLIED:** the no-least-oracle conclusion, the elementarity argument for countable standard models, and the exact finite-parameter uniformity restrictions are expanded below.
- **STRENGTHENING:** every real represented in the interpreted omega-model has strictly smaller hyperdegree than any adequate presentation or specified auxiliary atomic diagram. In particular a standard model cannot represent a real hyperarithmetically equivalent to its own such presentation.

No substantive defect was found in the audited §§18–19. The qualifications in §§6–7 below are necessary restrictions already substantially present in the note, not claims of a new gap.

## 1. Exact standardness and the interpretation

The model is evaluated at a fixed point w. The arithmetic premise is actual I_sigma, not a claim that an externally infinite domain automatically satisfies a quantified Frege Infinity axiom. Let nu=(sigma t)t. The external standardness requirement says the actual N_sigma extension consists exactly of the pairwise distinct denotations z_0,z_1,... of the standard numeral terms. It is not a finitary original axiom schema.

The recorded arithmetic interpretation under I_sigma supplies the PA axioms for the relational Sum and Prod definitions. On the displayed standard number domain, the recursion equations determine their values uniquely by external finite induction: Sum(z_m,z_n,z_k) holds exactly when k=m+n, and similarly for Prod. This is the point where standardness eliminates nonstandard arithmetic. No inference from an arithmetic interpretation alone to standard arithmetic is made.

For each admitted X:nu t define

    A_X={n∈N : X(z_n) is true at w},
    S={A_X : X∈D_(nu t)}.

Interpret second-order set variables by S, with set equality as equality of actual extensions. Several intensions can represent the same set without affecting this interpretation. For every second-order formula phi(n,Xbar), replace number quantifiers by quantifiers restricted to N_sigma, membership by application, and set equality by coextension on N_sigma. The original lambda

    lambda n . N_sigma(n) and phi#(n,Xbar)

then has the desired actual extension. This proves all second-order comprehension instances, including those with set quantifiers. Arithmetic truth with parameters from S is absolute because the first-order domain and arithmetic operations are the standard ones. Induction is true externally on N for every interpreted formula.

Two separations must be retained: full second-order **comprehension** is not external powerset fullness, and the collection S consists of extensions at the specified point, not the original property intensions themselves.

## 2. The fixed-point proof has the required closure

Take the parameter-free positive arithmetic formula psi from Gregoriades' Theorem 1. Put Phi(X)={n:psi(n,X)}. For every X∈S, arithmetic comprehension puts Phi(X) in S. Positivity implies monotonicity on actual subsets of N, externally as well as internally.

Full comprehension supplies

    L={n : for every X∈S, Phi(X)⊆X implies n∈X}.

For every available prefixed X, L⊆X; hence Phi(L)⊆Phi(X)⊆X. Therefore Phi(L)⊆L. Monotonicity gives Phi(Phi(L))⊆Phi(L), so the already available set Phi(L) is itself prefixed. The defining universal condition for L then gives L⊆Phi(L). Thus L=Phi(L) externally.

This is a valid restricted-family fixed-point argument because the two required constructions, the comprehension defining L and the image Phi(L), both belong to S. It does not identify L with the least fixed point in the full external powerset, which need not be correct. The external source obstruction applies to **every** fixed point, so that identification is unnecessary.

The original term for L is pure and fixed once sigma and psi are fixed. All arithmetic notation can be recursively expanded into the pure N_sigma, zero, successor, Sum and Prod definitions. The translation of psi remains positive in the set argument: arithmetic coding relations add no negative occurrences of that argument.

Primary source checked directly: [Gregoriades, *On a Question of Jaegers*, v2](https://arxiv.org/abs/1905.09609v2), Theorem 1, printed pp.2–3, and Lemmas 13–14, pp.7–8, in the [PDF](https://arxiv.org/pdf/1905.09609). Theorem 1 provides a positive arithmetic operator without hyperarithmetical fixed points. Lemmas 13–14 identify columns of every fixed point representing each hyperarithmetical set. The arXiv revision date is 1 March 2022; the PDF's internal date is 3 March 2022. The note accurately uses the revision date.

## 3. What each presentation computes

For a complete actual pure theory Gamma, the map

    n -> the code of the closed sentence L(z_n)

is recursive. Testing membership in Gamma computes L. Hence Gamma is nonhyperarithmetical. Each hyperarithmetical A has one fixed source column index a with `n∈A iff pair(a,n)∈L`. Hardcoding that natural number computes A from L and thus from Gamma.

This is separate reducibility for each A; it does not give a recursive list of valid hyperarithmetical indices or a uniformly effective listing of HYP. In particular the conclusion does not imply that Gamma computes Kleene's O.

Any presentation which computes actual truth of all closed original formulas computes Gamma and inherits that lower bound. Stronger adequate codes, including parameterized lambda denotations, certainly qualify. Nothing here shows that an arbitrary abstract category, action, or bare operation graph computes the complete original pure theory.

For the explicit auxiliary H_0/H_ch first-order application language, a much smaller interface suffices. Given an atomic diagram D, hardcode the indices of the denotations of zero, successor, L and the chosen world w. Application is total and its graph is D-decidable, so a D-search finds each output value. Starting from zero, repeatedly apply successor, then apply L and finally w, and compare with the distinguished truth value 1. This computes L. Only finitely many indices are hardcoded, independent of n.

The reduction is nonuniform across unnamed presentations, exactly as a Turing-degree lower bound permits. Adding names for this finite tuple does not alter the degree of an individual presentation. It would be an error to claim that the raw atomic diagram uniformly locates these pure denotations, but the note makes no such claim. No complete elementary diagram or uniform quantifier-elimination procedure is used in this atomic lower bound.

This also explains the different world scopes: an auxiliary atomic diagram can evaluate the chosen L at **any** world whose index is hardcoded. A complete actual pure theory only directly evaluates its own distinguished point; the unrestricted-C assertion should retain that point qualification.

## 4. Exact Pi^0_2 code class

Fix the recursive many-sorted auxiliary signature, c.e. theory U, and recursive Henkin expansion used in the note. Add the finitely many definitional names for zero, successor and N_sigma required for the selected counting types. Their formulas define unique objects by comprehension plus extensionality. This is a conservative c.e. extension.

Use a real D coding truth decisions for all closed sentences in that fixed expanded language. The conditions that D is complete, consistent and contains U^H are effectively closed: every failure has a finite syntactic/proof witness. Choosing a bit for each sentence automatically gives a decision, while consistency forces the Boolean and equality coherence. The fixed Henkin axioms supply witnesses in the term model.

For each well-typed closed number term u and selected closed world term w require

    not D[N_sigma(u)(w)=1] or exists n D[u=z_n].

The sentence codes in both oracle queries are recursive in u,w,n; hence this is one forall-u,w exists-n condition with D-recursive matrix, i.e. Pi^0_2. If only the actual point is wanted, hold w=w0 fixed. Adding both e and t instances, or all recursively enumerated selected types, does not increase the arithmetical level.

The statement is exact for the term model because every element is represented by a closed term. The number direction follows from the test; the converse follows from the pure theorem that each standard numeral is an N-number. Pairwise distinctness follows from the selected strong Infinity hypotheses. Syntactically distinct terms denoting the same object do not create a problem: D decides their equality and one can select least representatives computably in D.

Nonemptiness is properly shown by starting with the full auxiliary hierarchy over E=N and W={0,1} or W=N, satisfying the desired H_ch and boxed Infinity axioms. Interpret each fresh Henkin witness constant in turn by an actual witness. The full model has standard Frege arithmetic, so its complete theory in the countable expanded language satisfies all the displayed standardness tests. This provides an element of K, without asserting that its truth set is effective.

There is no contradiction between nonempty Pi^0_2 and no hyperarithmetical member. Pi^0_2 subsets of Cantor space need not be closed; the compact effectively closed Low Basis argument no longer applies. One should not import Low Basis into this strengthened class merely because the unstrengthened completion class was Pi^0_1.

## 5. Basis outputs, exact common information, and no least oracle

The directly checked source is [Harrington–Shore–Slaman, author-hosted draft of 11 July 2016](https://math.berkeley.edu/~slaman/papers/Sigma1116.pdf). Theorem 2.9, printed p.7, gives a member D of any nonempty lightface analytic class recursive in O and of smaller hyperdegree, with omega_1^D=omega_1^CK. Theorem 2.6, p.6, gives simultaneous hyperarithmetical avoidance of a countable list of nonhyperarithmetical reals. The Kreisel consequence for one real is stated on p.2.

The class K just constructed is arithmetical, hence lightface analytic. Choose D∈K as in Theorem 2.9. The fixed term-model construction computes from D the auxiliary elementary diagram, therefore the atomic diagram, the adequate Gallin code, and the complete actual pure theory. For each output Q,

    Q≤_T D≤_T O,
    O not≤_h D,
    Q not hyperarithmetical.

Thus Q<_T O; otherwise O≤_TQ≤_TD, contradicting the middle fact. Also O not≤_hQ and omega_1^Q=omega_1^CK by monotonicity of relative recursive ordinals. Each implication is valid for the atomic-diagram output because §3 provides its own lower bound.

For the common-information claim, fix a solution family Sol with the exact standardness and arithmetic assumptions of the note. If X is hyperarithmetical, §3 gives X≤_TQ for every Q∈Sol. If X is not hyperarithmetical, the basis theorem gives D∈K with X not≤_hD. Any corresponding output Q belongs to Sol and satisfies Q≤_TD, so X not≤_hQ. This establishes both versions of the common-information equivalence. The same reasoning with the countable-avoidance theorem handles any externally specified countable list; no uniform procedure choosing its avoiding model is claimed.

The no-least-degree proof is correct. If a solution Q0 had degree below every solution, its real would be common information and hence hyperarithmetical, contrary to §3. For a putative least **oracle** degree d capable of computing some solution, choose such a solution Q≤_Td. Since degree(Q) is itself capable, leastness gives d≤_TQ; thus d=degree(Q). It would be a least solution degree, already ruled out. The analogous reasoning applies to hyperdegrees where that solution ordering is used. These statements concern the whole class of solutions, not one fixed isomorphism type's spectrum.

## 6. Elementarity and standardness

The downward-elementarity existence check in §18.4 is sound but merits its precise mechanism. Begin with the full auxiliary model, and retain the finitely or countably many required pure numeral/number-operation denotations as parameters, or name them by definitional constants. Take a countable elementary substructure in the countable expanded language. If an element x in its number sort satisfies N(x) there, elementarity says it satisfies N(x) in the full model; full standardness makes x a standard numeral. Conversely all standard numerals are retained and remain numbers. The same argument works at every retained world when the full model was standard everywhere.

External standardness is not being preserved by an infinitary first-order sentence. It is preserved here by elementarity plus the external description of the original model's definable extension and retention of all its standard numeral elements. No general preservation claim for arbitrary elementary extensions is intended.

## 7. Restrictions that must remain explicit

1. I_sigma (or the stated sufficient Infinity hypotheses) is needed to identify the intended standard arithmetic operations. A standard-looking list of numeral denotations alone should not replace it without proof.
2. Number standardness is an external condition, tested arithmetically on complete **Henkin theory codes**, not claimed to be a first-order axiom or a Pi^0_2 condition on arbitrary raw atomic diagrams.
3. Ordinary finite-type fullness is not required by §§18–19. Requiring a full hierarchy over an infinite base would preclude countable presentations.
4. The auxiliary atomic lower bound relies on the represented pure L, successor and world sorts. Arbitrary reducts omitting those objects or application access are outside its scope.
5. The whole-solution basis argument supplies no standard Strong Possibility model and no complete classification of the exact oracle degrees capable of solving the standard problem.

## 8. Additional verified strengthening: each represented real lies strictly below the presentation in hyperdegree

The same fixed-point method relativizes to any represented set A∈S. The uniform positive formula psi_A supplied in the source's relativization discussion, printed p.4, has no fixed point hyperarithmetical in A. Repeat §2 with A as a parameter; full comprehension supplies an external fixed point L_A∈S.

Let D be an adequate original presentation with parameterized evaluation, or an atomic diagram of the specified auxiliary H_0 structure. Since A and L_A are represented objects, their extensions at w are individually Turing reducible to D by finitely many hardcoded object indices. If D≤_hA, then L_A≤_TD≤_hA, contradicting the relativized source obstruction. Therefore

    for every represented A∈S: A≤_TD and D not≤_hA,
    hence A<_hD.

For the auxiliary presentation one may simply hardcode L_A itself; uniform discovery of the fixed-point object is unnecessary. The conclusion is invariant under the choice of any representative intension for A.

In particular the real coding D cannot itself be represented in S, nor can any real of its hyperdegree. This is compatible with D having omega_1^D=omega_1^CK: sharing a relative recursive ordinal does not imply having the same hyperdegree. The statement is an additional semantic obstruction, not an exact characterization of which reals can occur internally.

## 9. Sharper original-code lower bounds, without a general term interpreter

The source lower bound extends beyond adequate codes in one specific direction. Suppose a numbered original C-model supplies sorted domain enumerations, the graphs of application, and actual truth of proposition objects. No general lambda/term-evaluation algorithm is assumed. Under I_sigma plus Std_sigma, hardcode the three denotation indices of zero, successor and the pure L from §2. Iterating application computes z_n; one more application computes L(z_n), and the actual-truth interface decides its truth. Thus this weaker application-and-truth code still computes L and is nonhyperarithmetical, with every hyperarithmetical real reducible to it individually. This is a nonuniform reduction for each presentation.

For a B-model, even the proposition-truth interface can be replaced by application and equality, provided these mean the specified original model's application graphs and decidable semantic equality. B supplies an actual true propositional atom a. Hardcode a and the binary join operation along with the preceding finite tuple. Then for every p,

    p is actually true iff a≤p iff a join p=p.

To verify the first equivalence, if p and a are true then a meet p is true and therefore nonbottom; atomicity of a makes a meet p=a. Conversely a≤p and truth of a imply truth of p by Boolean validity. The second equivalence is the Boolean algebra order law. Thus two applications of the named join and one equality test compute actual truth, and the previous reduction applies.

The existence of a true atom is essential here and comes from the positive B assumptions (Actuality/strong Actuality as verified in the companion representation proofs); Atomicity of an arbitrary external Boolean algebra alone does not force every ultrafilter to contain an atom. In the present B package the necessary structural consequence is available.

Again there is no uniform method asserted for finding the hardcoded atom, join or pure term denotations in an unnamed raw code. These lower bounds therefore do not supply a uniform general term interpreter and do not transfer to an arbitrary category/action presentation lacking the stated application and equality interfaces.

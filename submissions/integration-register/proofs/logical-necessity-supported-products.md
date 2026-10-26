# Logical Necessity without Actuality

OpenAI Codex, 22 October 2026. Direct source: misc; ordinary ZFC metatheory.

## 1. The supported product model

Choose an infinite cardinal κ ≥ |Σ|. Let I have cardinality κ⁺ and let L be the free monoid of finite words on an alphabet of cardinality κ, with empty word ε. Set

    M = L^I,       (kh)_i = k_i h_i.

Regard M as the arrows of a one-object category. Its identity 1 has every coordinate ε and is the evaluation point. The individual domain is a singleton, on which all arrows act trivially. Recursively, for every relational type τ = σ₁…σₙt, including n=0, take D_τ to contain exactly the profiles

    F : M → P(D_σ₁ × … × D_σₙ)

for which some S ⊆ I, |S| ≤ κ, satisfies

    m|S = m'|S  ⇒  F_m = F_m'.                         (support)

For n=0 identify a profile with a subset of M. Thus propositions are precisely the subsets depending on at most κ coordinates. All these domains are sets, defined recursively on type complexity. Define transport by

    (h·F)_k = F_kh.

It preserves S-support: agreement of k,k' on S implies agreement of kh,k'h on S. Also h·F as an entire profile depends on h only through h|S. Transport is functorial, since `(g·(h·F))_k = F_kgh`.

The support condition concerns the arrow variable. It does not impose an equivariance condition on the members of F_m. In particular, for any set E of tuples, the constant profile F_m=E is admitted with empty support. This is the same distinction used by the extensionally full, pinned action constructions in the local records.

**Closure and C.** Use ordinary action-model interpretation: a formula at h is evaluated at the sole object with its parameters transported by h; quantifiers range over the displayed domains. If F has support S and a has support T, application has profile

    (Fa)_h(b̄)  ⇔  F_h(h·a,b̄),

so it has support S∪T. For λ-abstraction with parameters ā, its profile at h consists of the tuples b̄ satisfying its body with parameters h·ā and bound variables b̄. This depends on h only through the union of the parameters' supports. Boolean operations, equality, and quantification preserve that dependence: after the transported parameters agree, they are evaluated in the same object with exactly the same quantified domains. Finite unions of supports still have size ≤κ.

Induction on terms therefore gives λ-closure, closure under all logical operations, and commutation of interpretation with transport. The usual action-model verification gives H and Logical Equivalence: an H-valid equivalence holds at every arrow with every assignment, so the corresponding abstraction profiles are equal. Thus this is a model of the fixed C, without upgrading an equivalence under optional hypotheses to Logical Equivalence. Curried relational types are handled by the application rule above; no type with output e is added.

Every pure closed sentence has the same truth value at every arrow, because there is one object and it has no parameters to transport. In particular, No Pure Contingency holds.

**Adversarial audit of currying and quantification.** Write τ=ρ₁…ρ_nt for the output of a permitted abstraction, and let A denote λx.T(x;ā). Its flattened profile is

    A_m(b,c̄) ⇔ c̄ belongs to ⟦T(x;m·ā)⟧ at the identity with x=b.

The external parameters ā here include the denotations of all constants occurring in T. Substituting b=m·a shows, by induction on the body, that `(Aa)_m=⟦T(a;ā)⟧_m`: β is profile equality. For η, `(λx.Fx)_m(b,c̄)=((m·F)b)_1(c̄)=F_m(b,c̄)`. Thus currying does not discard off-identity information. Applying h to the abstraction replaces m·ā by (mh)·ā=m·(h·ā), which also verifies transport through λ.

For a quantified body, e.g. λx̄.∀y φ(x̄,y;ā), the values compared at m and m' use the same fresh argument tuple b̄ and the same full domain D_y. Agreement of m,m' on the external parameters' supports makes those parameters identical as whole transported entities, and hence gives the same truth value for every y. No union of the supports of all quantified entities is taken. This is why arbitrary higher quantification preserves support despite the very large domains. Identity is literal profile equality; if presented through Leibniz tests, the empty-supported constant profiles with singleton extensions separate unequal entities. Such constant profiles are not being confused with the moving logical haecceities `m↦{m·a}`.

## 2. A gluing lemma that preserves the support bound

Suppose at most κ entities F_α of one relational type have been specified, and choose j outside the union of their supports. Let h_α be the arrow with the one-letter word α at coordinate j and ε elsewhere. Define a profile G by

    G_m = (F_α)_m   if m_j ends in the letter α,
          ∅         if m_j is empty or its last letter is not a used index.

This is unambiguous. It has support `{j} ∪ ⋃_α S_α`, of size ≤κ, so G is admitted. For every k,

    (h_α·G)_k = G_kh_α = (F_α)_kh_α = (F_α)_k.       (gluing)

The last equality uses j∉S_α; right multiplication by h_α changes no other coordinate. Hence h_α·G=F_α as entities, not merely in their current extensions. The same sites work simultaneously for at most κ such families: choose j outside the union of all their supports, still a set of size ≤κ. The singleton individual type needs no gluing.

This is the point at which finite support would be inadequate. Supports of size ≤κ accommodate all κ many witness assignments, and I has a coordinate left over. No infinitary conjunction is introduced into the object language.

## 3. Interpret the fixed signature to obtain Logical Necessity

Keep the pure model just constructed fixed. There are at most κ finitary Σ-sentences. Enumerate the sentences φ_α that are true at the object under some interpretation J_α of Σ, choosing one such interpretation for each. Each J_α(c) has a support of size ≤κ. There are at most κ² pairs (α,c), so a coordinate j exists outside the union of all their supports.

For each relational constant c, glue the family J_α(c) using §2, and interpret c by the resulting G_c. Interpret individual constants by the unique individual. Then, simultaneously for every c,

    h_α·G_c = J_α(c).

Consequently φ_α is true at h_α. Conversely, any Σ-sentence true at some arrow h is true in an expansion of the same pure object, with constants interpreted as h·G_c. We have proved

    ◇φ holds in the glued expansion
       iff φ is satisfiable by an interpretation over this pure model.  (★)

Now let P be pure, with free variables among x̄, and let c̄ be distinct matching constants of the fixed Σ. The sentence P[c̄/x̄] is satisfiable over the pure model iff ∃x̄ P holds there: assign the constants a witness tuple in one direction, and read their interpretations as witnesses in the other. Distinct symbols need not denote distinct entities. Combining this fact with (★) yields

    ◇P[c̄/x̄] ↔ ∃x̄ P.

Apply it to ¬P and take duals to get the required schema

    □P[c̄/x̄] ↔ ∀x̄ P.

The empty tuple is covered as well. The construction handles the prescribed Σ itself, including all its constants and all admitted instances; it is not a counterexample obtained only by replacing a richer signature with a singleton signature. Logical Necessity is asserted at the identity. It is a signature schema, so the one-object argument for pure sentences does not automatically box it; no boxed Logical Necessity claim is made.

The second audit checked the simultaneous cardinal bound, not just gluing one tuple: κ assignments × κ constants × at most κ coordinates per support still use at most κ coordinates, in ZFC. The pure domains are fixed before any assignments are selected, and gluing changes only the constant interpretations. Thus neither a circular enlargement of the domains nor an unproved expansion to the prescribed signature is used.

## 4. Atomlessness, failure of Actuality, and failure of Vicinity

For i∈I put

    q_i = {m : m_i=ε}.

This is an admitted, true proposition supported by {i}. Its transports satisfy

    h·q_i = q_i  if h_i=ε,
            ⊥    otherwise.                          (kill)

Let p≠⊥ have support S and choose j∉S. Changing just coordinate j of a member of p to ε or to a nonempty word produces members of p on both sides of q_j. Thus p∧q_j is nonzero and strictly below p. This proves Atomlessness.

More directly, if p is true, take j∉S and h with a nonempty word at j and ε elsewhere. Then p holds at h, whereas q_j does not, although q_j is true at the identity. Hence p does not entail every truth, proving failure of Actuality.

Furthermore ◇q_j=q_j. Indeed, k_j h_j can be empty for some k iff h_j is empty. The same h therefore satisfies p but not ◇q_j. No truth entails the possibility of every truth, proving failure of Vicinity. These pure failures hold at every arrow of this one-object model.

## 5. Failure of Weakly Inextensible Comprehension

Let E={q_i:i∈I}, and let X∈D_tt have the constant profile X_m=E. It is admitted with empty support. Suppose Y∈D_tt is actually coextensive with X, so Y_1=E, and let S support Y. Choose j∉S and let h have one letter at j and ε elsewhere. Then Y_h=Y_1=E.

Define an admitted test relation Z∈D_tt by

    Z_m = D_t              if m_j=ε,
          D_t \ {q_j}     otherwise.

Its support is {j}. For every actual member q_i of Y and every arrow m, (kill) says that m·q_i is q_i or ⊥. If i=j and m_j is nonempty, it is ⊥; if i≠j, neither possible value is q_j. Thus Z necessarily holds of every actual Y-member:

    ∀p (Yp → □Zp).

But q_j∈Y_h and q_j∉Z_h. Consequently Y≰Z. This contradicts WeaklyInextensible(Y). Since every actual coextension Y is defeated this way, Weakly Inextensible Comprehension fails at the relation type tt. Its boxed version fails as well.

The untransported q_j in the definition of Z_m is legitimate: Z is an externally specified domain element whose profile depends on one coordinate. It is not being claimed to be the denotation of an expression that silently treats q_j as a rigid parameter.

The second audit checked this against the exact definition: the cover hypothesis quantifies over actual Y-instances and asks for □Z of each transported instance, whereas Y≤Z tests every fresh target instance at every arrow. The former uses m·q_i; the latter can test q_j itself at h. Their difference is the exhibited failure, not an interchange of the two quantifier scopes. The choice of j and Z may depend on Y, as the negation of the comprehension instance allows.

## 6. All-type □BF nevertheless holds

Every arrow h acts surjectively at every type. This is immediate at e. For a relational F with support S, define G_m as follows. If, for every i∈S, m_i has h_i as a suffix, remove those suffixes and let r(m) be the resulting prefixes on S and ε elsewhere; set G_m=F_r(m). In the other case set G_m=∅. This profile is S-supported, hence admitted. For every k, the suffix test passes at kh and r(kh)|S=k|S, so

    (h·G)_k = G_kh = F_k.

Thus h·G=F. To verify BF directly, suppose ∀a □Ra. At any h and for any target entity b, choose a with h·a=b. Then □Ra gives b∈R_h. Therefore □∀b Rb. The argument applies at every type; each BF instance is a pure closed sentence, so it holds at every arrow, giving □BF.

## 7. Optional countable conjunctions

The original-language result above needs no extension. It also survives adding pointwise countable conjunctions and disjunctions with the corresponding λ-terms. Fix that set-sized syntax first and choose κ large enough to bound its set of sentences and the sizes of its parse trees. Induction on those trees preserves the support bound, since a countable union of sets of size ≤κ still has size ≤κ. Sections 2–3 then glue witnesses for all sentences of this larger language, giving its Logical Necessity schema for the same finite matching tuples. Sections 4–6 are unchanged. This is a separately identified extension of the result, not an assumption in its original-language proof. Unrestricted conjunctions of all actual propositions are not licensed: their parameter family can exceed the support bound.

## 8. One further verdict: all-type □Tame Rigidity

Here is a new structural lemma for this same model, in the original language. For a set E of argument tuples write

    H_E(m) = m·E.

This is initially an external profile; it is not assumed to belong to a domain. **Exact-image lemma:** an admitted relation Y with actual extension E is weakly rigid iff Y=H_E. In that case Y is rigid at every arrow.

For the nontrivial direction, suppose Y is weakly rigid and supported by S. Weak persistence gives m·E⊆Y_m. For any T⊆I of size ≤κ define the admitted, T-supported approximation

    B_T(E)_k = ⋃{n·E : n|T=k|T}.

Every actual ā∈E necessarily falls under B_T(E), taking n=k at each arrow. Weak inextensibility therefore gives Y≤B_T(E). This approximation is the analogue of the finite-pinning test in the recorded `arguments/tame-rigidity-factorizable.yaml`; the following coordinate factorization is specific to the present construction.

Fix b̄∈Y_m. Enlarge S to T by adding supports of the finitely many entries of b̄; |T|≤κ. From Y≤B_T(E), choose n and ā∈E with n|T=m|T and n·ā=b̄. Define arrows r,u coordinatewise by

    r_i=u_i=ε       for i∈T,
    r_i=n_i, u_i=m_i for i∉T.

These are arrows of the full product M, even if they have more than κ nonempty coordinates. We have mr=un: on T this is m_i=n_i, and outside T both sides are m_i n_i. Since r fixes S, Y_r=Y_1=E; weak persistence therefore gives r·ā∈E. Since u fixes the supports of b̄, u·b̄=b̄. Consequently

    m·(r·ā) = (mr)·ā = (un)·ā = u·b̄ = b̄.

Thus Y_m⊆m·E, proving equality at every m. No cancellation or inverses, and no support bound on the arrows themselves, were assumed.

Conversely, if the admitted Y equals H_E, it is weakly persistent. Any admitted Z necessarily holding of every ā∈E contains m·E at every m, so Y≤Z, proving weak inextensibility. For any arrow h,

    (h·Y)_k = (kh)·E = k·(h·E),       (h·Y)_1=h·E.

Hence every transported Y also has the exact-image property and is weakly rigid. This proves Rigid(Y). The empty tuple and individual arguments are covered: the empty tuple and the singleton individual have empty support. Thus Tame Rigidity holds at all relational types. Its instances are pure closed sentences of the one-object model, so □Tame Rigidity holds as well.

The lemma does **not** make every H_E admissible. For example, E={q_i:i∈I} yields H_E(m)={q_i:m_i=ε} together with ⊥ when some coordinate is nonempty; its dependence on all I coordinates prevents a support of size ≤κ. The full-model proof of Rigid Power cannot therefore be imported. Section 9 now turns this lifting issue into a counterexample in this same model. The original pinned models have not been altered or assigned new verdicts.

## 9. Rigid Power fails: a family of shifted relations

Fix o∈I and put J=I\{o}. Retain the distinct propositions q_j of §4. Let y_j∈D_tt be the constant profile with extension {q_j}. Each y_j is fixed **as an entity** by every arrow; it need not be rigid as a relation. The y_j are pairwise distinct.

Let χ(n) be 1 when the integer n is a nonnegative square, and 0 otherwise. Its right tails χ(n+z), n≥0, are different for different integers z: sufficiently large consecutive squares have gaps exceeding any prescribed nonzero shift. Every tail also contains a 1. For z∈Z and j∈J define e_(z,j)∈D_tt by the following extensions, where r=|m_o| and n=|m_j|:

    r=0:  {q_j} ∪ ({⊥} if χ(n+z)=1, otherwise ∅);
    r=1:  {q_j} if n+z≥0, otherwise ∅;
    r≥2:  {q_j}.

These profiles have support {o,j}. The square markers distinguish all z in a fixed j-family, and the q_j markers distinguish the families. Let a have one letter at o and ε elsewhere; let b_j have one letter at j and ε elsewhere. Direct right translation gives

    b_j·e_(z,j)=e_(z+1,j),       a²·e_(z,j)=y_j,
    a·e_(z,j)=y_j  iff z≥0.

For z<0 the last image has empty extension at the identity, so it is not any y_k. Also b_j fixes every e_(z,k) for k≠j. All of these are equalities of complete profiles. The q_j appearing inside their extensions are fixed set members in these definitions, not silently rigidified propositional parameters.

Put E=⋃_(j∈J){e_(z,j):z∈Z} and B={y_j:j∈J}. The exact-image profile F=H_E is admitted at type `(tt)t` with support {o}. Indeed, an arbitrary arrow m shifts the integer z in each j-family by |m_j|, which permutes Z. Thus m·E depends only on |m_o|: it is E if that length is 0, a·E if it is 1, and B if it is at least 2. The profile X=H_B is the constant profile B, hence admitted with empty support. Both F and X are rigid by §8, and X≤a·F.

There is no rigid Y≤F with a·Y=X. Otherwise §8 writes Y=H_A for A⊆E, and a·A=B. Let S support Y and choose j∈J\S. Since b_j fixes S, b_j·Y=Y, whence b_j·A=A. The nonempty set

    A_j={z∈Z:e_(z,j)∈A}

is invariant under the bijective shift z↦z+1: no other family maps into this one. It is nonempty because a·A contains y_j, whose only preimages in E have the form e_(z,j) with z≥0. Shift invariance forces A_j=Z. It then contains e_(-1,j), whose a-image is not in B, a contradiction.

Let P_F=λY(Rigid(Y)∧Y≤F). At a its extension contains X, whereas the a-image of its actual extension does not. The exact-image lemma therefore says P_F is not weakly rigid, and in particular not rigid. This refutes Rigid Power at the bound type `(tt)t`. Its boxed version fails; Weakly Rigid Power fails as well, since that principle implies Rigid Power. These are pure failures, unaffected by the glued interpretation of Σ.

**Why small tests miss this obstruction.** If a future rigid subrelation H_D≤h·H_E has |D|≤κ, choose one preimage in E for each member of D. Their set A has size ≤κ, and the union of their supports has size ≤κ. Therefore H_A is admitted and rigid, and h·H_A=H_D. Every such small target lifts. In the counterexample |B|=κ⁺, and every ≤κ-sized subfamily lifts even though B itself does not. This is an external cardinal statement in the fixed model, not a new object-language cardinality axiom.

## 10. Countable Boolean Completeness holds at every counting type

At every relational type, the pointwise union or intersection of at most κ admitted profiles is admitted: take the union of their supports. This external closure alone should not be confused with the map's internal countability predicate; the following verifies the connection.

For any counting type σ, the actual extension of FiniteCardinality_σ is exactly the external orbit {Suc_σⁿ(0_σ):n∈N}. Every actual inductive property contains this orbit by external finite induction. Conversely, the constant profile whose extension is exactly this orbit is admitted and is an inductive property, so the impredicative definition includes no other entities. This proves external countability of the number domain without assuming that all numerals are distinct, or assuming I_σ.

If Ctbl_(σ,τ)(A) holds, its witnessing relation assigns a nonempty set of these labels to each actual A-instance, with disjoint label sets for distinct instances. Assign each instance the least external iteration index of one of its labels. This is an external injection into N, so the actual extension E=A_1 is countable. The pointwise union ⋃_(x∈E)x is admitted by the support bound and is its least upper bound under profile inclusion. This is exactly the map's LUB definition with A's **actual** instances. Thus the whole Countable Boolean Completeness schema holds for every σ and relational τ; its boxed instances hold by the one-object pure-sentence argument. The proof does not use a small individual domain to trivialize the schema.

## 11. A variant with infinitely many moving individuals

The Choice + Countable BC counterexample can also have infinitely many individuals, while retaining Logical Necessity for signatures containing individual constants. Let U have cardinality κ⁺ and S be the monoid of surjections U→U. Replace M by L^I×S, take D_e=U with action (m,s)·a=s(a), and allow every relational profile that depends on at most κ coordinates of its L^I argument and arbitrarily on its whole S argument. Impose no symmetry condition. This is a separate model. All constant extension profiles remain admitted, so the Relational Choice proof remains valid.

Closure under application, abstraction and quantification is unchanged: parameters have bounded dependence on the L^I coordinates, while unrestricted dependence on the S-coordinate is permitted. Individual parameters have empty L^I-support. For BF, retain the coordinatewise suffix lifts of §6. Right multiplication by s∈S is injective, since rs=ts and surjectivity of s imply r=t. Therefore a profile F has a preimage under s by assigning F_(m,r) at coordinates (m,rs), and empty extension outside this image. This preserves its L^I-support. The action at e is onto by definition, so all-type □BF holds.

The exact-image lemma also survives. In B_T(E), require not only agreement on T but also equality of the whole S-coordinate. For b∈Y_(m,s), this produces (n,s)·a=b with n|T=m|T. Use the same coordinatewise r,u as §8, giving both of them S-coordinate id. The factorization (m,s)(r,id)=(u,id)(n,s) still holds. Both the fixed-support arguments are unchanged, so □Tame Rigidity follows. The Rigid Power obstruction in §9 ignores the S-coordinate, and its fresh-coordinate shifts have S-coordinate id; it therefore refutes Rigid Power here as well.

For gluing, choose distinct a_c∈U for all individual constants. For each full witness interpretation J_α, extend the prescriptions a_c↦J_α(c) to a surjection s_α; there are at most κ prescriptions and κ⁺ remaining arguments. For each relational constant c choose B_(α,c) with s_α·B_(α,c)=J_α(c), using the preceding profile lift. This lift does not enlarge L^I-supports. Choose a coordinate j outside the union of all these supports and glue B_(α,c) by the last letter at j, as in §2. At the arrow with that letter only at j and with S-coordinate s_α, all constants simultaneously become their J_α-values, including the individual constants. This proves the same full fixed-signature Logical Necessity schema.

The proofs of Atomlessness, failure of Vicinity and failure of Weakly Inextensible Comprehension keep the S-coordinate equal to id, and hence remain valid. The Countable Boolean Completeness argument in §10 uses admitted constant profiles and bounded unions of supports, both still available. It therefore remains valid too. Finally the impredicative finite-cardinality domain is still exactly the external successor orbit, by the constant-orbit-property argument in §10. Its nth member holds precisely of n-element actual extensions, by finite induction. Since D_e=U is infinite, this proves the quantified Axiom of Infinity at e; Atomlessness gives an infinite D_t and the same proof gives its Axiom of Infinity. These pure truths are necessary.

Thus the weaker Choice + Countable BC question has a negative answer even with quantified infinity at e and t and the other positive properties stated above. This extra construction is a direct mathematical self-audit, not an independently checked model record; full BC still fails by the verified weak-inextensibility obstruction.

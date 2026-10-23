# Finite selector audit for Maximalism and Atomicity

22 October 2026. New arguments and definitional expansion by OpenAI Codex; direct source: misc, this note. **Status: proposed, self-audited, not independently checked.** This supplements [the proposed inconsistency proof](max-atomicity-rigid-selector.md), especially its direct ZFC route in §7. It does not change the records, their verification status, or the frozen research archive.

The target remains fixed C plus **pure Max(C) and unboxed Atomicity_t**. No optional preset is added. The construction below specifies one finite pure term; it does not introduce a selector constant, a type quantifier, an infinitary formula, or a set-theoretic assumption into C. ZFC is the metatheory in which the witnessing C model is constructed.

**Shortest route through this audit.** Sections 2–7 make a closed pure operator F_A available by finite coding. Section 9 gives a sound interpretation in which its global splitting assertion S_A has value 1, so `C ⊬ S_A=0`. The general C argument in §8 gives `C+Atomicity_t ⊢ S_A=0`. Pure Max(C) supplies S_A≠0. Section 10 additionally extracts an ordinary countable Henkin model with S_A true. The conclusion remains proposed, rather than independently verified.

## 1. What the further audit establishes

The original HCode construction can be weakened for the direct route. It is enough to code a well-founded extensional universe closed under small subsets; its collapse need only CONTAIN the required hereditary-size segment. A bound on every membership row is unnecessary. Section 2 proves this separate coding lemma.

Sections 3–6 give an acyclic finite library of set-theoretic formulas for the direct selector. Definitions by comprehensions and finite recursions are expanded as formulas about set-coded graphs, so the construction has no implicit additional symbols. Section 7 checks the size and absoluteness conditions that make those formulas characterize the same objects in every permitted code. Section 8 gives the typed selector and the unboxed contradiction argument. Section 9 gives an additional simplification: an algebraic soundness certificate can use the atomless algebra directly, eliminating the added atom and the interval term b. Section 10 supplies an ordinary countable Henkin witness by choosing its domains together with a filter that supplies witnesses for existential claims.

Two presentational corrections to the earlier note are recorded here. The entire HCode predicate is crisp; its individual unguarded clauses need only be crisp WHEN E is crisp. Also W(p,q) is a pure predicate with p,q free; its lambda closure, rather than that open formula itself, is closed. Neither correction changes a denotation or the proposed conclusion.

The external mathematical input remains the rigidity theorem for the particular Jech–Shelah forcing completion. The coding, the splitting-family argument, and the bounded-splitter obstruction are the present deductions. No independent checking is claimed.

## 2. A weaker universe code

Fix the full Boolean-valued source model with proposition algebra B, where κ=|B| is infinite. Put U:=tt. Its domain has size κ^κ=2^κ. Use square brackets for explicitly left-nested curried application.

Define the following finite typed formulas:

    Crisp(X^{Ut}) := ∀u^U (X(u)=0 ∨ X(u)=1).

    Small(X^{Ut}) := ∃f^{Ut} ∀u^U v^U
                       ((X(u) ∧ X(v) ∧ f(u)=f(v)) → u=v).

    Crisp2(E^{UUt}) := ∀u^U v^U (E[u,v]=0 ∨ E[u,v]=1).

    Ext(E) := ∀u^U v^U
                ((∀z^U (E[z,u] ↔ E[z,v])) → u=v).

    WF(E) := ∀X^{Ut}
               ((Crisp(X) ∧ ∃u^U X(u)) →
                ∃u^U (X(u) ∧ ∀v^U (E[v,u] → ¬X(v)))).

    Fill(E) := ∀X^{Ut}
                 ((Crisp(X) ∧ Small(X)) →
                  ∃u^U ∀v^U (E[v,u]=X(v))).

    Cover(E) := Crisp2(E) ∧ Ext(E) ∧ WF(E) ∧ Fill(E).

For crisp X, Small(X) holds exactly when its extension has size at most κ. A witnessing function is an injection of that extension into B, extended arbitrarily outside it. Conversely the displayed clause makes its restriction injective. Full domains supply all the characteristic functions and injections used here.

**Cover lemma.** Cover(E) has Boolean value 1 exactly when E presents a transitive set M, of cardinality |D_U|, which is closed under taking subsets of size at most κ. In particular every such M contains H_(κ+). At least one such E exists.

**Proof.** Crisp2 identifies an ordinary relation on D_U. Since every ordinary subset of D_U has a crisp characteristic function, WF is actual well-foundedness, not a restricted definability version of it. Extensionality and the Mostowski collapse theorem therefore give a bijection π:D_U→M onto a transitive set, with

    E[u,v]=1  iff  π(u)∈π(v).

If x⊆M and |x|≤κ, its inverse image under π is a crisp Small subset. Fill supplies a u whose predecessors are exactly that inverse image, so π(u)=x. Thus x∈M. The converse follows by pulling small subsets back under the same bijection.

For any x∈H_(κ+), every member of x is again in H_(κ+). Membership induction gives that all those members belong to M. Since |x|≤κ, closure under small subsets then gives x∈M. Hence H_(κ+)⊆M.

Finally |H_(κ+)|=2^κ: subsets of κ give the lower bound, and pointed well-founded relation codes on a set of size κ give the upper bound. A subset of H_(κ+) of size at most κ is itself in H_(κ+), since the union of at most κ hereditary sets of size at most κ has size at most κ. Pull membership back along a bijection D_U→H_(κ+) to obtain the required E. ∎

Cover is crisp as a whole. If E is noncrisp, Crisp2 has value 0 and annihilates the conjunction. For crisp E, Ext is crisp. In WF and Fill, a noncrisp X makes the antecedent false; a crisp X makes every remaining test crisp. Meets and joins of values in {0,1} are again in {0,1}.

The original HCode is Cover together with `∀u Small(λv.E[v,u])`. That extra clause bounds the immediate members of every collapse element. The union of its finite membership levels then has size at most κ, giving M⊆H_(κ+) and hence equality. Thus the original coding lemma survives the audit, but its row bound is not used below. This weakening is specific to the direct selector: it does not by itself justify interpreting the canonical L-order in arbitrary larger collapse universes. Substituting Cover changes the syntactic term; its agreement with the old selector is established in the source interpretation, not asserted as an identity provable in C.

## 3. Finite set-formula conventions

All formulas in §§3–6 are ordinary first-order formulas in = and ∈. Every quantifier is over the interpreted set universe. On translation through E, each variable has the single type U and `x∈y` becomes E[x,y]. The typography below uses bounded quantifiers, unique existence, named outputs, and finite tuples as abbreviations, not as added language primitives. Expansion always renames bound variables to avoid capture; numerical variables in a macro are distinct from names for sequence graphs in an enclosing formula.

The elementary macros are:

    Empty(x)      := ∀z ¬(z∈x).
    Sub(x,y)      := ∀z (z∈x → z∈y).
    Sing(s,x)     := ∀z (z∈s ↔ z=x).
    Pair(d,x,y)   := ∀z (z∈d ↔ (z=x ∨ z=y)).
    OP(p,x,y)     := ∃s d (Sing(s,x) ∧ Pair(d,x,y) ∧ Pair(p,s,d)).
    App(f,x,y)    := ∃p (p∈f ∧ OP(p,x,y)).
    App2(f,x,y,z) := ∃p (OP(p,x,y) ∧ App(f,p,z)).
    Succ(y,x)     := ∀z (z∈y ↔ (z∈x ∨ z=x)).

`Func(f,D,C)` says that every member of f is an ordered pair of an element of D and an element of C, and that for every x∈D there exists exactly one y∈C with App(f,x,y). `Inj(f,D)` is

    ∀x∈D ∀x'∈D ∀y ((App(f,x,y) ∧ App(f,x',y)) → x=x').

A bijection additionally has every element of its target in its range. Unique existence abbreviates existence conjoined with a universally quantified uniqueness clause. For example `∀x (x∈D ↔ Φ(x))` is a formula characterizing the set D; no comprehension operator is added to the language. A right-nested five-tuple is encoded by four occurrences of OP.

Let `Ind(v)` assert that v contains an empty set and contains the successor of each of its members. Then

    Omega(w) := Ind(w) ∧ ∀v (Ind(v) → Sub(w,v)).

In every transitive M containing H_(κ+), Omega picks the actual ω. The real ω is present and is inductive; every internally inductive set is externally inductive, since Empty and Succ have their literal meanings in a transitive set. Consequently it contains every actual natural number. The least-inductive-set clause therefore singles out ω. No nonstandard natural-number interpretation remains.

In the remaining set formulas, 0 denotes the unique empty set, 1 its successor, and 2 the successor of 1. In a literal expansion use fresh U-variables z_0,z_1,z_2 for them, bound existentially with their displayed defining clauses. They are distinct from the logical proposition terms 0 and 1 of type t used in §8. All arithmetic arguments are required to belong to w satisfying Omega(w). When a displayed arithmetic or tree macro omits w and these numeral variables from its argument list, they are explicit additional macro parameters, supplied by the surrounding JSCode binder; none remains free in JSCode(c,G).

Arithmetic has finite graph definitions. For Add(a,b,c), quantify a function f:b+1→w with f(0)=a and f(b)=c, and require f(i+1) to be the successor of f(i) for every i∈b. For Mul(a,b,c), use f(0)=0 and Add(f(i),a,f(i+1)). For Pow(a,b,c), use f(0)=1 and Mul(f(i),a,f(i+1)). Here b+1 and i+1 mean variables satisfying Succ; f(i)=j means App(f,i,j). Each is one finite formula, and the dependency order is Succ, Add, Mul, Pow. There is no recursion in the syntax and no infinite list of numeral cases.

`Seq(s,n,w)` abbreviates `n∈w ∧ Func(s,n,w)`. Prefix(s,t) says that s and t are such sequences and that s is a subgraph of t. ProperPrefix also requires s≠t. Concatenation `Cat(s,i,u)` says that for some length n and its successor n', u is a sequence of length n', agrees with s on n, and has value i at n. For equal-length sequences, Lex(s,t) says that their values agree below some j in the common domain and the value of s at j is a member of the value of t at j. These are finite formulas using only the preceding macros and quantification over w and finite domains.

## 4. The exact source construction as a finite definition

Use Jech–Shelah, *A Complete Boolean Algebra That Has No Proper Atomless Complete Subalgebra*, Journal of Algebra 182 (1996), pp. 748–755: the rigidity theorem on p. 749, sequences and master tree (2)–(3), pp. 749–750, forcing (4), p. 750, and restriction property after (8), p. 750. [Primary source](https://shelah.logic.at/files/95558/566.pdf). The theorem is in ZFC; no V=L or CH hypothesis is used. Minimality of the generic extension is not an input to our argument.

To avoid conflating the numerical sequence with the forcing, call the two sequences d,n and the forcing set P. They are functions ω→ω characterized by

    d(0)=n(0)=1;
    d(k+1)=d(k)·n(k),       n(k+1)=2^(d(k+1)).

The master tree T_* consists of finite natural sequences. Its indexing map I:T_*→ω is a bijection, sends the empty sequence to 0, increases with length and then lexicographically, and gives a node of index k exactly the children s⌢i with i<n(k). It is nonempty and downward closed. These clauses uniquely specify T_* and I, by breadth-first construction with finite levels.

P consists exactly of the nonempty downward subtrees T⊆T_* such that

    ∀s∈T ∀m∈ω ∃t∈T
       (ProperPrefix(s,t) ∧ t has at least d(I(t))^m children in T).

The relation “has at least r children” quantifies an injective function from r into ω whose range consists of i with s⌢i∈T. Thus this is a finite formula using Pow, Func, Inj and Cat. The set P is specified by a single membership biconditional. The nonempty convention is explicit, so the vacuous empty tree is not admitted as a condition.

All functional notation in this paragraph is eliminated using App and auxiliary variables. The two sequences are described by one universally quantified recursion equation, not one clause per k. There are only finitely many symbols to expand. The forcing order S≤T is Sub(S,T), with S,T∈P.

The source gives rigidity of B(P). We take its canonical realization A=RO(P) with the downward-open order topology. If passage to the separative quotient is needed, it gives the same regular-open completion. Rigidity transfers across that Boolean-algebra isomorphism. A Boolean-algebra isomorphism between complete algebras preserves arbitrary joins automatically, since it preserves their least-upper-bound characterization; no separate completeness condition on the isomorphism is needed later.

## 5. Completion, product algebra, and the coordinate sequence

Define

    Open(X,P) := Sub(X,P) ∧
                   ∀T∈X ∀S∈P (Sub(S,T) → S∈X).

    Dense(X,T,P) := ∀S∈P (Sub(S,T) →
                            ∃R∈P (Sub(R,S) ∧ R∈X)).

    Reg(X,P) := Open(X,P) ∧
                  ∀T∈P (T∈X ↔ Dense(X,T,P)).

    RegOf(Y,X,P) := Open(X,P) ∧ Sub(Y,P) ∧
                      ∀T∈P (T∈Y ↔ Dense(X,T,P)).

Thus RegOf(Y,X,P) says Y=ro(X). Define A by `∀X (X∈A ↔ Reg(X,P))`. For regular opens the meet is intersection, and their complement is specified by

    Comp(Y,X,P) := Sub(Y,P) ∧
                     ∀T∈P (T∈Y ↔ ∀S∈P (Sub(S,T) → S∉X)).

Intersection is the elementary formula `∀T(T∈Z ↔ (T∈X ∧ T∈Y))`. These formulas specify all of the Boolean operations used below, with zero ∅ and top P.

Let D be the product carrier, specified by

    ∀u (u∈D ↔ ∃i∈2 ∃X∈A OP(u,i,X)).

Its zero z is OP(0,∅), and its top o is OP(1,P). Meet acts by the two-element meet on the first coordinates and intersection on the second. Complement exchanges 0 and 1 in the first coordinate and uses Comp in the second. The first-coordinate operations are finite case distinctions.

Let M_B and N_B be the exact graphs of meet and complement. For precision, a binary-operation graph associated with a formula Φ(x,y,z) is characterized by

    ∀r (r∈M_B ↔ ∃x∈D ∃y∈D ∃z∈D ∃u
                      (OP(u,x,y) ∧ OP(r,u,z) ∧ Φ(x,y,z))).

The unary graph uses OP(r,x,z) and the corresponding product-complement formula. These biconditionals prohibit extraneous graph entries. Set c to the right-nested tuple `(D,(z,(o,(M_B,N_B))))` using OP.

For natural numbers n,m, define the open set V_(n,m) by the following exact membership clause:

    T∈V_(n,m) iff T∈P and every s∈T of length greater than n
                  has value m at n.

Lengths and values use Seq and App. Let g_(n,m)=ro(V_(n,m)), using RegOf. Enumerate pairs by Cantor's pairing k=⟨n,m⟩, expressed arithmetically as

    2k=(n+m)(n+m+1)+2m.

This is an equation among natural numbers, expanded using Add, Mul and Succ. Define G as a function from ω to D whose k-th value is the ordered pair `(0,g_(n,m))` for that unique pair n,m.

**JSCode(c,G)** is now the following single finite first-order formula: existentially bind w,0,1,2,d,n,T_*,I,P,A,D,z,o,M_B,N_B and the finitely many auxiliary variables, and conjoin the defining clauses in §§3–5, including the tuple definition of c and graph definition of G. The universally quantified event and regularization clauses introduce their auxiliary sets under those quantifiers. Every abbreviation in this specification expands through an earlier definition; there is no circular use of JSCode, satisfaction predicate, unnamed parameter, or variable-length conjunction.

## 6. Why the coordinate family actually splits

The master tree itself is a condition: sufficiently far along any branch, 2^d(k) exceeds d(k)^m for any fixed m, as observed after source formula (4). Every condition has a splitting node above each of its nodes. Indeed it has arbitrarily long extensions, their indices are unbounded, and the growth condition with m=1 eventually requires at least two children. Restrictions to two different such children are incompatible conditions. This also verifies directly that the completion is nontrivial and atomless. The imported theorem is needed for rigidity.

For each fixed n, the regular opens g_(n,m), m∈ω, are pairwise disjoint and have join 1. Given a condition T, take a node s∈T of length greater than n and restrict to nodes comparable with s. The source restriction property gives another condition, now in V_(n,s(n)). Thus the union of these open sets is dense. Different coordinate values cannot hold in a common condition. Regularization preserves their disjointness: if a condition lay in two regularizations, refine first into one open set and then into the other, obtaining the impossible intersection.

For each actual sequence z∈ω^ω,

    ∧_n g_(n,z(n))=0.

A condition has splitting extensions above every node, by its growth condition, and therefore has a node that is not an initial segment of z. Restriction to that node yields a condition in V_(n,m) for some m≠z(n). If a nonempty regular open x lay below every g_(n,z(n)), start with a condition in x and make this restriction. Downward openness keeps it in x, while the other coordinate event makes it disjoint from one of the purported upper bounds. This contradiction proves the displayed meet equation. No generic filter is assumed to exist in the construction universe.

Now let x>0 be any element of A. If no g_(n,m) splits x, every x∧g_(n,m) is either 0 or x. For each n, the partition and

    x∧(∨_m g_(n,m)) = ∨_m (x∧g_(n,m))

give exactly one m with x≤g_(n,m). Those unique values form an actual sequence z. The meet equation would give x=0. Consequently some coordinate splits x, and there is a least such coordinate in the fixed pairing order. The only infinite distributive law used here is distribution of one finite meet over an arbitrary join, valid in every complete Boolean algebra.

This proves that the fixed sequence G, restricted to the atomless component of 2×A, canonically determines a nonzero proper part of each nonzero element there. Countable generation of the completion is not needed as a separate premise.

## 7. Size, existence, and absoluteness

Take B=2×A and κ=|B|. A complete atomless Boolean algebra has at least continuum many elements: recursively find a countably infinite disjoint family of nonzero elements, and send each subset of ω to the join of its corresponding subfamily. Distinct subfamilies have distinct joins. Hence 2^aleph_0≤κ.

The master tree is countable. Every condition is a subset of it, so |P|≤2^aleph_0≤κ. The hereditary size of P is at most κ. EVERY subset of P likewise has hereditary size at most κ, whether or not it is regular open. The family A itself has cardinality κ and hereditary size at most κ. Its finite operation graphs, D, M_B, N_B, c, and G have hereditary size at most κ as well. The numerical sequences, finite sequences, tree indexing map and auxiliary finite-function graphs are countable or hereditarily countable.

Thus every object needed to satisfy the defining formulas belongs to H_(κ+), including every individually quantified subset of P. No step requires the whole powerset of P to be an ELEMENT of H_(κ+).

Consider any Cover code and its transitive collapse M⊇H_(κ+). The formulas in §§3–5 have the intended meanings in M:

1. Empty sets, finite pairs, ordered pairs, graph membership and subset tests are absolute by transitivity. All finite pair constructions needed as witnesses are present.
2. Omega gives actual ω. All finite-function witnesses for arithmetic are present, so the arithmetic and finite-sequence formulas are absolute. The countable d,n,T_*,I are present and the defining recursions uniquely determine them.
3. Every subset of T_* is present. The condition test involves only its nodes, natural numbers and finite graphs. The membership biconditional for P therefore ranges over all actual candidate trees and specifies the actual P.
4. Every subset of P is present. Open, Dense and Reg quantify only over P once their subset clauses are imposed. The formula defining A therefore tests all actual candidates and gives actual RO(P).
5. Product operations, their graphs and the coordinate events use those already identified objects. All their required graphs and regularizations are present. Consequently c and G are the same actual sets in every M.

Larger collapse universes cannot contribute spurious candidates. For example, if X∈M satisfies Sub(X,P), transitivity ensures that this is actual inclusion, so X is already one of the subsets of P in H_(κ+). The same argument applies to candidate trees and operation-graph entries. Thus the extra elements allowed by Cover do not change JSCode.

This proves both existence and uniqueness of the decoded c,G, and is the exact absoluteness statement required. It does not assert that M satisfies ZFC, or that arbitrary formulas are absolute between M and the universe.

## 8. The typed term and the contradiction

Decode the tuple c into D,z,o,M_B,N_B. For h^{tU}, define Iso_E(c,h) by the finite conjunction

    ∀p^t E[h(p),D];
    ∀u^U (E[u,D] → ∃p^t h(p)=u);
    ∀p^t q^t (h(p)=h(q) → p=q);
    h(0)=z and h(1)=o;
    ∀p^t q^t App2_E(M_B,h(p),h(q),h(p∧q));
    ∀p^t App_E(N_B,h(p),h(¬p)).

Tuple decoding is existentially quantified as part of this formula. This requires an isomorphism onto the coded carrier, preserving its displayed operations. Full domains provide such maps in the source model. The product B is rigid because its unique atom and its complement are fixed, and the latter interval is the rigid A. Therefore the map from B to the canonical decoded product is unique. After Mostowski collapse, every admissible E yields that same map.

For coded x,k,r, define J_E(c,G,x,k,r) by: existentially decode c into D,z,o,M_B,N_B as in Iso; require that k belongs to the unique coded ω; for some g require App_E(G,k,g) and App2_E(M_B,x,g,r); and require that r differs from both z and x. All decoded fields and the coded ω are bound inside J, so its only free variables are E,c,G,x,k,r. Let

    First_E(c,G,x,k,r) := J_E(c,G,x,k,r) ∧
                           ∀j^U (E[j,k] → ¬∃s^U J_E(c,G,x,j,s)).

The membership test E[j,k] is the natural strict order because k is a coded von Neumann natural. This is a finite least-index formula, with no minimum operator in the language.

Use the original pure terms and predicate

    b := ¬∃p^t (Atom_t(p) ∧ p),

    Sel(p,q) := p≠0 ∧ p≤b ∧
                  ∃E^{UUt} c^U G^U h^{tU} k^U
                    (Cover(E) ∧ JSCode_E(c,G) ∧ Iso_E(c,h) ∧
                     First_E(c,G,h(p),k,h(q))),

    F := λp^t. ∃q^t (Sel(p,q) ∧ q),

    Split_b(F) := ∀p^t ((p≠0 ∧ p≤b) →
                         (p∧F(p)≠0 ∧ p∧¬F(p)≠0)),

    Q := b ∧ Split_b(F).

All auxiliary types are t, U=tt, Ut, UUt and tU; every one is admitted. Set-formula variables are all at U. After expanding the finite acyclic definitions, F and Q are closed pure terms in the original language. κ, A, M, the collapse map and the source construction universe are not free object-language parameters.

**Source-model calculation.** Interpret all admitted function types by full set-function domains, equality by literal equality with values 0_B or 1_B, connectives by Boolean operations, and quantifiers by arbitrary meets and joins. Designated truth is the first-coordinate projection B→2. This complete homomorphism preserves ordinary quantified truth, including existence of an actual witness whenever an existential is designated true. The verification of H and Logical Equivalence is in [the existing construction write-up, §§1–2](../../../topics/classicism/writeups/full-boolean-valued-atom-and-atomless.md); no optional premise is involved.

The only Boolean atom is a=(1,0), so b denotes b_0=(0,1). Every good E makes all translated tests crisp; a bad E makes Cover false. Therefore Sel is crisp. By §§6–7 and rigidity, each nonzero p≤b_0 has exactly one q with Sel(p,q), and that q is a nonzero proper part of p. The existential defining F has Boolean value precisely that q. This remains true when q is false at the designated evaluation: the calculation concerns its Boolean value, not a claim that the selected q is actually true.

It follows that Split_b(F) has value 1_B and Q has value b_0≠0_B. The identity Q=0 has crisp value 0_B and is false at the designated evaluation. Thus it is not a C-theorem.

**The C derivation, without semantic shortcuts.** Put S=Split_b(F). Suppose p≠0 and p≤b∧S. Boolean identities give p≤b and p≤S. The former identity is necessary by NI; the latter is □(p→S). Necessitate the C-theorem given by universal instantiation of S, and the theorem p→p≠0. These yield

    □(p → (p∧F(p)≠0 ∧ p∧¬F(p)≠0)).

If either displayed part were zero currently, NI would make that equality necessary. The last display would then imply □¬p, equivalently p=0, a contradiction. Hence both parts are currently nonzero. Generalizing proves the C-theorem `Split_(b∧Split_b(F))(F)`. No open hypothesis was necessitated: the only necessary facts obtained from premises are identities handled by NI.

If Atomicity_t holds and Q≠0, take an atom w≤Q. The theorem just established splits w into two nonzero parts, contradicting atomhood. Therefore `C+Atomicity_t ⊢ Q=0`.

Pure Max(C), with its reference theory still C, includes Q≠0 because the source model falsifies Q=0. The proposed conclusion is consequently

    C + pure Max(C) + unboxed Atomicity_t is inconsistent.

The argument uses one Max instance. All-type unboxed Atomicity implies its type-t instance, so would be excluded as well. No conclusion about the accuracy of this new argument is certified by bundle validation: that checks the records and their structure, not this proof. Independent mathematical scrutiny remains outstanding.

## 9. A shorter non-theorem certificate, without the added atom

This additional variant is also proposed and self-audited. It uses the atomless rigid A itself as the proposition algebra. It gives a direct algebraic proof that a particular identity is not a C-theorem, rather than presenting another ordinary pointed Henkin model. The ordinary pointed model of §8 remains available and is unchanged.

**Soundness lemma.** For any nontrivial complete Boolean algebra A, use D_t=A, D_e={*}, full function domains, crisp equality, Boolean connectives, and meet/join quantifiers. Let T_A consist of the formulas whose value is 1_A under EVERY assignment. Then T_A is an H-theory containing Logical Equivalence, and hence contains C.

**Proof.** PC, UI and EG have value 1 by the Boolean laws and the definitions of meet and join. Ref and LL hold because equality is literal and crisp. Beta and eta conversion preserve actual set-function denotations, including when the replacement occurs inside a larger term or under binders. MP preserves value 1.

For Gen, if P→Q has value 1 under every assignment and v is not free in P, fix the other variables. Its fixed value p is below every value Q(d), so p≤∧_d Q(d), giving value 1 to P→∀vQ. For Inst, if v is not free in Q, every P(d) lies below the fixed q, so ∨_d P(d)≤q. This gives value 1 to (∃vP)→Q. These are exactly the H closure conditions; no preservation-of-witnesses claim is used.

If H proves P↔Q, its Boolean value is 1 under every assignment, hence the two values are equal under every assignment. Their permitted lambda abstractions are therefore literally equal functions. Thus every Logical Equivalence instance has value 1. By the definition of C as the smallest H-theory containing those instances, C⊆T_A. ∎

This is the same algebraic soundness argument as §2 of the existing Boolean-valued write-up, before that construction adds its designated projection. The three H rules can also be checked directly in Bacon–Dorr's [author-hosted draft of 1 July 2022](https://andrew-bacon.github.io/papers/Classicism.pdf), §1.1, Figure 2, p. 8. That older copy is cited only for the displayed rule list; the bundle's fixed C definition remains controlling.

Now use the canonical atomless A=RO(P) from §§4–6. Set κ=|A| and retain Cover. Define JSCode_A by taking c to code A itself, with zero ∅, top P, intersection and regular-open complement graphs, and G(k)=g_k. This deletes the two-element product clauses of §5. Every size and absoluteness proof in §7 still applies. Rigidity makes the isomorphism from the actual A to this canonical code unique.

Define Sel_A by the formula in §8 with JSCode_A in place of JSCode and with the conjunct p≤b deleted. Let

    F_A := λp^t. ∃q^t (Sel_A(p,q) ∧ q),
    S_A := ∀p^t (p≠0 →
                   (p∧F_A(p)≠0 ∧ p∧¬F_A(p)≠0)).

These are finite pure terms, and S_A is closed. In the A-valued interpretation every nonzero p has a uniquely selected proper part, so S_A has value 1_A. Consequently S_A=0 has value 0_A and is not in T_A. The soundness lemma gives `C ⊬ S_A=0`. In fact C+S_A is H-consistent, since T_A contains it and does not contain falsity.

The bounded-splitter lemma, with b=1 and F=F_A, gives `C+Atomicity_t ⊢ S_A=0`. Pure Max(C) includes S_A≠0, establishing the same proposed inconsistency conclusion. This version needs neither the pure term b nor a first-coordinate projection. It does NOT claim that an arbitrary ultrafilter on atomless A supplies ordinary quantified truth: that would generally be false. What licenses the non-theorem inference is the displayed H-theory argument for T_A, not such an ultrafilter.

## 10. Extracting an ordinary countable Henkin witness

The algebraic certificate in §9 also admits an ordinary model construction. This is an additional argument of this note, not an attribution to the forcing paper. It is unnecessary for the non-theorem inference but checks that the lack of a designated atom in A is no obstacle once full domains are replaced by a suitable Henkin substructure.

Start with the full A-valued interpretation of §9. There are countably many types and pure terms. Choose countable nonempty sets of entities in every type, containing the logical constants, and close them under the source denotations of terms with finite tuples of parameters from the chosen sets. Iterate closure as needed. All these sets remain countable. In particular application and parameterized lambda abstraction are included. Quantifiers retain the source meet/join operations on the admitted predicates.

Concurrently construct a descending sequence a_0≥a_1≥… of nonzero elements of A, starting with a_0=1. Fairly schedule a requirement for every predicate f:D_σ→A that enters the selected domain of type σt. Let e_f=∨_{d∈D_σ}f(d), the ORIGINAL full-domain existential value, which is also selected by term closure. At the stage serving f, do the following:

* If a_n∧e_f=0, retain a_(n+1)=a_n. This already forces ¬e_f into any ultrafilter extending the descending filter.
* If a_n∧e_f≠0, distribution of a finite meet over a join gives some source d with a_n∧f(d)≠0. Add d to the selected σ-domain, set a_(n+1)=a_n∧f(d), and repeat term closure.

A countable dovetailing of the successive countable lists serves each selected predicate. Complements `λx.¬f(x)` enter the lists by term closure, so universal failures are covered as well. ZFC supplies the successive witnesses and an ultrafilter V on A extending the proper filter generated by the a_n. This filter is proper because every finite intersection of its generators is one of the nonzero a_n.

Use membership in V as truth on the final selected propositional domain. Entities retain literal identity: V selects truths and does not quotient the proposition algebra. Each scheduled e_f is decided by its stage. If e_f∈V, its positive stage supplied a SELECTED d with f(d)∈V. Conversely f(d)∈V for any selected d implies e_f∈V, since f(d)≤e_f. Thus existential quantification has the ordinary truth clause over the selected domain. Applying this to the selected complement predicate gives the ordinary universal clause. Boolean truth and literal identity have their usual clauses; all term denotations are inherited from the source interpretation.

The H axioms and rules consequently hold in the resulting Henkin structure. Logical Equivalence also holds: its identities were already literal identities of source denotations, and term closure retains them. The domain restrictions introduce no new free constants or Max schema instances. If a presentation by actual functions on the selected domains is desired, restriction is injective: two distinct selected source functions differ at some source input, and the requirement for the selected predicate `λx.F(x)≠G(x)` adds such an input. Hence no accidental identification of function entities is necessary.

S_A has source value 1, so it is true in this ordinary model. The selected propositional domain is a countable Boolean subalgebra closed under F_A. Every nonzero p has the selected nonzero proper part F_A(p), so that Boolean algebra is atomless. It need not be rigid: rigidity was used in the full source interpretation to define the pure operator, and is not asserted of this countable subalgebra. Higher-type Henkin domains retain the structure needed for the operator's pure definition.

Even its Boolean algebra of CLOSED PURE propositional denotations is atomless. It contains 0 and 1, is closed under the Boolean operations, and is closed under applying the closed pure F_A. Thus each of its nonzero members has another member as a nonzero proper part. The same argument applies to the one-individual term-profile algebra for any individual marker. This supplies an ordinary-model counterexample to the universal atomic-profile condition discussed in [the earlier follow-up, §9](max-atomicity.md). More directly, S_A is C-consistent while `C+Atomicity_t+◇S_A` is inconsistent, so it defeats the atomic-predecessor criterion in that note's §6.

Thus the shorter route yields both its algebraic non-theorem certificate and an ordinary countable C model where the specified pure global splitter works. This extraction and the original proposed inconsistency proof still await independent checking.


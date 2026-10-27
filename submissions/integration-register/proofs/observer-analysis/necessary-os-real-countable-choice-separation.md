# Finite-cylinder observers: necessary CH without real countable choice

Ordinary mathematical argument by OpenAI Codex, 26 October 2026 (`misc`); numbered sections, unpaginated.

**Result.** From a model of ZF + PSP + ¬CC(R), construct an atomless relational Henkin model satisfying C5 + □Rev at every finite qualification list, hence C5 + □OS. One persistent real-field tuple satisfies Real necessarily. Native CH and failure of real countable choice both hold necessarily for that tuple. Consequently even current CH, added to atomless C5 + □OS and persistent necessary real existence, does not imply real countable choice.

This is an obstruction to a proposed intrinsic consistency-strength argument, not a countermodel to CH propagation: CH is necessary in this construction. The genuinely contingent-CH target remains separate.

## 1. Ground premise and the exact choice sentence

Work internally in a model W of ZF. The construction through §5 requires no Choice. For the final separation assume

```math
W\models\mathrm{PSP}+\neg\mathrm{CC}(\mathbb R),
\tag{1}
```

where PSP says every uncountable real subset has a perfect subset. The cited Truss construction supplies this ground at the relative-consistency strength of ZFC. The primary source actually read for these properties is Keremedis and Tachtsis, [*On Sequentially Compact Subspaces of R without the Axiom of Choice*](https://www.researchgate.net/publication/242933912_On_Sequentially_Compact_Subspaces_of_without_the_Axiom_of_Choice), Theorem 5.4, proof of (2), printed p. 182, DOI [10.1305/ndjfl/1091030855](https://doi.org/10.1305/ndjfl/1091030855). It describes Truss's singular-cardinal model, states its perfect-set property and singular ω₁, and derives failure of CC(R). The original Truss article is cited there; it was not independently read here. Relative consistency is meant in the usual formal forcing sense, not as a claim that Con(ZFC) produces a countable transitive model.

Here is a fixed native real-choice sentence, so the conclusion is not merely a failure of some unspecified higher-type choice scheme. For predicates N,X of type et and binary relations H,F of type e(et), write

```math
\begin{aligned}
\mathrm{Serial}_{N,X}(H)
&:=\forall n\,[Nn\to\exists x\,(Xx\land(Hn)x)],\\
\mathrm{Select}_{N,X}(F,H)
&:=\bigl[\forall n\,(Nn\to\exists!x\,[Xx\land(Fn)x])\bigr]\\
&\quad\land\forall n\,x\,[(Fn)x\to Nn\land Xx\land(Hn)x],\\
\mathrm{CC}_{N,X}
&:=\forall H\,[\mathrm{Serial}_{N,X}(H)
             \to\exists F\,\mathrm{Select}_{N,X}(F,H)].
\end{aligned}
\tag{2}
```

In the construction N is the standard ground natural-number predicate within the ground real field and X is its whole real carrier. This quantifies over admitted real relations. It asserts exactly that every admitted sequence of nonempty real sets has an admitted selecting graph. Application is parenthesized according to the project's right-associating convention.

## 2. The finite-cylinder algebra and the supported hierarchy

Put K=2^ω as computed in W. Let C be the Boolean algebra of its finite-cylinder sets: a member's membership depends on a finite set S⊂ω of coordinates. For such S let C_S be the finite Boolean subalgebra of sets determined by S. Explicitly,

```math
C=\bigcup_{S\in[\omega]^{<\omega}}C_S.
\tag{3}
```

Let Γ be the group of finite subsets of ω, with symmetric difference as product, acting on K by flipping the listed bits. It acts on C by direct image. Set

```math
H_S=\{g\in\Gamma:g\cap S=\varnothing\}.
\tag{4}
```

A Γ-object is supported by S if H_S fixes it. The H_S form a normal filter base; Γ is abelian and H_S∩H_T=H_{S∪T}.

Define the typed domains inductively, using only the fixed relational grammar:

```math
D_e=\mathbb R^W\quad\text{with trivial }\Gamma\text{-action},\qquad D_t=C,
\tag{5}
```

and, whenever τ≠e,

```math
D_{\sigma\tau}
=\{f\in(D_\tau^{D_\sigma})^W:
                 f\text{ has a finite support}\}.
\tag{6}
```

The action on functions is conjugation:

```math
(g\cdot f)(x)=g\cdot f(g^{-1}\cdot x).
\tag{7}
```

All these collections are sets in W. The action preserves each domain, application is equivariant, and a finite tuple of parameters has the union of its finite supports as a support. No sequence of independently chosen supports is required by this construction.

An ambient regular-open completion is optional. Its finitely supported elements are precisely C: an H_S-invariant regular open is a union of S-cylinders by the argument below. The proposition domain in (5) is C itself, not the full completion.

## 3. Quantifier closure and ordinary truth without genericity

The essential lemma concerns literal unions, not just completed Boolean joins.

**Finite-cylinder lemma.** An H_S-invariant open subset O⊆K is a union of S-cylinders, hence belongs to C_S.

To prove it, take x∈O and y agreeing with x on S. Some basic finite cylinder [x↾T] lies in O. Flip exactly those coordinates of T\S where y and x differ. This gives g∈H_S with g·y∈[x↾T]⊆O. Invariance gives y∈O. Thus O contains the whole S-cylinder of each of its points. There are only finitely many such cylinders. Complements show that an H_S-invariant closed subset also belongs to C_S.

For F∈D_{σt}, choose a finite support S. Equivariance and the Γ-invariance of D_σ imply that both

```math
\bigcup_{x\in D_\sigma}F(x),
\qquad
\bigcap_{x\in D_\sigma}F(x)
\tag{8}
```

are H_S-invariant. The first is open and the second closed, since each F(x) is clopen. The lemma puts both in C_S. Interpret ∃ and ∀ by the respective **literal** union and intersection in (8).

These operations are equivariant as functions of F; therefore the quantifier objects themselves have empty support and belong to the required higher function domains. Boolean connectives are also equivariant. A lambda term with finitely supported parameters defines a function supported by their finite union. This proves closure under the complete finite typed syntax, including quantified lambda terms.

Choose the old point z∈K with every coordinate zero, and call b∈C true iff z∈b. Because (8) consists of actual unions and intersections,

```math
z\in\bigcup_xF(x)\iff\exists x\ z\in F(x),\qquad
z\in\bigcap_xF(x)\iff\forall x\ z\in F(x).
\tag{9}
```

Thus evaluation obeys the ordinary Henkin quantifier clauses. It needs no generic ultrafilter, no antichain selection, and no no-new-reals forcing theorem. The same holds at every old point of K. Pointwise interpretation of H and extensional equality of the interpreted functions validate Logical Equivalence, giving the fixed background C.

For a nonstandard W the construction, supports, cylinders, and statements (3)–(9) are interpreted internally. Their ZF proofs externalize to the standard finite object-language formulas. No external well-foundedness or transitivity assumption is needed. In particular “finite” need not mean externally finite when describing an element of W.

## 4. C5, atomlessness, and necessary reversible observers

For every a∈D_σ, its endpoint-valued singleton property is supported by any support of a and belongs to D_{σt}. It distinguishes a from every different domain object. Hence defined Leibniz equality at every type has value K or ∅ according as its arguments are equal or different. Defined necessity is the global top test:

```math
\|\Box\varphi\|=
\begin{cases}
K,&\|\varphi\|=K,\\
\varnothing,&\|\varphi\|\ne K.
\end{cases}
\tag{10}
```

In particular all instances of boxed distinctness hold, so the model satisfies C5.

The proposition algebra is atomless. A nonempty b∈C_S splits into two nonempty proper parts by intersecting it with the two values of any coordinate outside S. These parts belong to C. Thus atomlessness is also native atomlessness, with admitted splitting witnesses.

For each g∈Γ let E_g:C→C be its Boolean action. The group is abelian, so E_g has empty support under conjugation and is admitted at type tt. Its inverse E_{g^{-1}} is admitted too. These are inverse operations as actual functions. They preserve all Boolean operations and the literal unions and intersections (8). Therefore they satisfy every finite list of the whole-operation observer qualification identities, at arbitrary admitted types.

For every nonempty b∈C_S,

```math
\bigcup_{g\subseteq S} E_g(b)=K.
\tag{11}
```

Indeed the finite flips of S move a point of any nonempty S-cylinder to every other S-cylinder. For distinct proposition objects apply (11) to their nonempty symmetric difference. For different relational functions choose one argument tuple where their proposition values differ, and use the same argument. At each point there is an admitted reversible qualified observer witnessing the required difference. The ordinary quantifier semantics (9) turns this cover into value K for every observer-separation instance. Consequently

```math
\Box\mathrm{Rev}_{\rm all},
\qquad\text{and hence}\qquad
\Box\mathrm{OS}_{\rm all}.
\tag{12}
```

The all-types notation in (12) denotes an external schema, not an object-language quantification over types. This uses only the explicit admitted finite-flip observers, not an assumed enumeration of all observers.

## 5. Exact real-relation interpretation and necessary Real

Let F have finitely many individual arguments and proposition output, with support S. The Γ-action fixes every individual argument. Thus each output F(\bar r) is H_S-invariant and lies in C_S. Consequently F evaluated at any point is one of finitely many W-relations on the ground real line. Conversely every W-relation on finitely many reals is represented by its endpoint-valued characteristic function, which has empty support and is admitted.

Therefore, at each point, the admitted real subsets and finite-arity real relations have **exactly** the ground W extensions. This statement includes potential injection, bijection, and selecting graphs. It is stronger than merely saying that the individual labels stay fixed.

Take the whole real carrier, ground 0 and 1, field operations as endpoint-valued relational graphs, ground order, and the ground natural-number predicate. The same tuple is persistent and satisfies Real at every point. In particular any admitted nonempty bounded real subproperty evaluates to a W-subset of W's reals and has its W-supremum. The usual ground induction clause also applies to exactly the admitted evaluated subsets. Thus

```math
\Box\mathrm{Real}_e(\top_e,0,1,+,\times,\le,N).
\tag{13}
```

Completeness here uses the authorized nonempty bounded convention. No externally full real line is claimed for a nonstandard ground.

## 6. Necessary CH and necessary failure of real countable choice

PSP in W implies its subset-cardinality form of CH without Choice. For A⊆R, either A injects into ω, or A has a perfect subset. A nonempty perfect subset of R admits an injection of R, while A itself injects into R. Cantor–Bernstein then gives A≈R. These witnesses are W-relations, so §5 shows that at every point native CH holds for the real tuple (13).

To verify the universal real-field form as well, an admitted tuple satisfying Real at a point has W real-relation extensions. All W real subsets are admitted, so it is a complete Archimedean ordered field in W. The usual ZF categoricity proof supplies its W-isomorphism with the standard W real field; that graph is admitted. Transferring W's CH witnesses proves

```math
\Box U_{e,\mathrm{CH}}.
\tag{14}
```

Now choose in W a sequence (A_n) of nonempty real sets with no choice function, supplied by (1). Its incidence relation H(n,x) is an endpoint-valued admitted relation. It satisfies Serial_{N,top_e}(H) at every point. If an admitted F selected from H at any point, its evaluated relation would be a W graph selecting one element from each A_n, contrary to the choice of the family. Consequently the existential selector assertion has value ∅, while its seriality premise has value K. Hence

```math
\Box\neg\mathrm{CC}_{N,\top_e}.
\tag{15}
```

The same persistent H witnesses (15) everywhere. This is failure of the explicit real-choice fragment (2), even though CH is necessary and one complete real field is necessarily present. In particular adding current CH cannot rescue the proposed derivation of real countable choice from C5 + □OS.

## 7. Scope of the intrinsic lower-bound obstruction

The construction establishes the relative consistency, at the ground strength stated in §1, of

```math
\mathrm{C5}+\Box\mathrm{Rev}_{\rm all}
+\mathrm{Atomless}_t
+\Box\mathrm{Real}(\text{one persistent tuple})
+\Box U_{e,\mathrm{CH}}
+\Box\neg\mathrm{CC}_{N,\top_e}.
\tag{16}
```

Thus the architecture-specific step deriving CC(R) from simultaneous repairs with no new reals cannot be replaced by a theorem deriving (2) from native necessary observers, even with the CH-true side and persistent real existence added. A native inaccessible lower-bound proof must use some further consequence of **genuine CH contingency**, or a different interpretation that does not depend on this false choice implication.

There is a precise reason this example itself cannot yield the desired contingent CH. A pure closed formula has empty support, and the only Γ-invariant elements of C are ∅ and K. Thus every pure closed proposition is noncontingent here. This remains true for formulas with the displayed empty-supported ground field data. The model changes the truth values of individual contingent propositions while its homogeneous observer action fixes the truth value of closed mathematics.

No consistency-strength lower bound for the bare atomless C5 + □OS + nonvacuous contingent-CH theory is proved here. Nor is (16) a model of that contingent-CH theory. It isolates a definite failed intermediate implication, while leaving the intrinsic use of contingency and a Con(ZFC)-only contingent-CH construction unresolved.

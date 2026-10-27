# Generic Boolean choice with reversible observer separation

25 October 2026. Ordinary mathematical argument by OpenAI Codex. Direct source: `misc`, this note, unpaginated.


## 1. Result and construction

There is a model satisfying

```math
\boxed{C5+\Box\mathrm{Rev}+\Box\mathrm{TC}_{r}
 +\Box\mathrm{RC}_{r}+\Box\mathrm{Zorn}_{r}
 +\Box\neg BC_t+\Box\neg\mathrm{Actuality}}
```

Rev denotes full typed separation by reversible logical observers, qualified by identities of whole Boolean and quantifier operations at each finite external type list. Boxed schema assertions mean their separately boxed instances. In particular this model has necessary ordinary observer separation. It is a countermodel after dropping BC_t from the proposed Actuality implication, not a countermodel with BC_t included.

Use the existing generic Boolean Henkin construction of [the choice model note](generic-boolean-choice-model.md), §§1–4. Its full source construction is [Structural mixing models, §31](../../source/research/2026-10-22/notes/structural-mixing-models.md). Specialize its Boolean algebra to B=RO(2^ω), the regular open algebra of Cantor space. The ambient domains are A_e=ω, A_t=B, and the full function sets A_(στ)=A_τ^{A_σ} for the permitted arrows. Take a sufficiently large regular H_θ and a countable M≺H_θ containing these domains, the Boolean structure, and the concrete sequences used in §4. The actual domains are D_σ=M∩A_σ, with ordinary restricted application. Worlds are all M-generic ultrafilters on B∩M; accessibility is universal.

The cited construction verifies all typed lambda closure, classical quantifier truth at every generic world, crisp identity, and C5. An admitted predicate's quantifier is computed from its full ambient Boolean range; genericity, rather than completeness of an arbitrary ultrafilter, supplies the classical truth clause on D. Distinct ambient M-functions remain distinct after restriction, by elementarity. The choice note verifies admitted rigid wellorders of every D_σ and consequently all boxed TC and RC instances, including individual outputs represented by graphs. The recorded TC-to-Zorn theorem then gives boxed Zorn. These existing construction facts are not new claims here.

## 2. Admitted involutions of the Cohen algebra

Every nonzero principal interval of B is isomorphic to B as a complete Boolean algebra. Indeed, a nonempty open subset of Cantor space is a disjoint union of finitely or countably many basic clopen cylinders. Its regular open algebra is the corresponding product of copies of B. Finite clopen partitions identify each nonzero finite product with B; the dense open union of the cylinders 0^n1 identifies the countably infinite product with B. Passing to a dense open subspace leaves the regular open algebra unchanged. This also gives the principal-interval assertion for nonzero regular open elements.

Fix b∈B∩M with 0<b<1. In H_θ choose a complete Boolean isomorphism

```math
h:B\mathbin{\upharpoonright}b\longrightarrow
 B\mathbin{\upharpoonright}\neg b
```

The relevant maps, subsets and completeness tests lie in H_θ by its size choice. Elementarity supplies such an h in M. Define

```math
g(x)=h(x\land b)\lor h^{-1}(x\land\neg b)
```

Then g∈M is an involutive complete Boolean automorphism, with g(b)=¬b. In particular g is an admitted operation of type tt and is its own admitted inverse.

For every permitted input type σ and every ambient F:A_σ→B, completeness gives

```math
g\left(\bigvee_{x\in A_\sigma}F(x)\right)
 =\bigvee_{x\in A_\sigma}g(F(x)),
\qquad
g\left(\bigwedge_{x\in A_\sigma}F(x)\right)
 =\bigwedge_{x\in A_\sigma}g(F(x))
```

Together with the Boolean identities, these are identities of the full ambient operations. Restriction therefore gives the required identities of the admitted whole operations, not merely their current truth equivalence. Crisp equality supplies the equality clauses of observer qualification. Thus the same g is Good at every requested finite type list, and g∘g=I as a whole-operation identity.

## 3. Necessary reversible separation and failure of Actuality

At any generic world G, take distinct p,q∈D_t and put d=p△q≠0. If d∈G, identity separates p and q. Otherwise 0<d<1, and the involution from §2 sends d to ¬d∈G. Since g preserves symmetric difference, gp and gq then have different current truth values. This proves propositional reversible separation, with arbitrary finite qualification.

For unequal higher relational objects, elementarity supplies an admitted tuple where their B-valued applications differ. Apply the preceding propositional separator at that tuple. This proves full typed Rev. The argument works at every generic world, establishing every separately boxed instance. The underlying individual domain and all parameter domains are the same at these worlds; no transport surjectivity assumption is being added.

Actuality fails at every such world. If a∈G, then a≠0. Atomlessness and elementarity give 0<c<a with c∈M. If c∈G, the truth c is not above a. If c∉G, the truth ¬c is not above a, since a∧c=c≠0. Thus no true a entails every truth. This establishes □¬Actuality.

## 4. One admitted predicate refutes BC_t at every world

Let a_n be the clopen cylinder [0^n1], for n∈ω. These are pairwise disjoint nonzero Boolean elements. Let q_n be the clopen set of binary sequences whose n-th bit is 1. Include these two definable sequences in M. Every natural number is in M, so all their entries are admitted.

The ambient function Y:B→B defined by

```math
Y(p)=
\begin{cases}
q_n,&p=a_n,\\
0,&p\ne a_n\text{ for every }n
\end{cases}
```

belongs to M by definability and therefore is an admitted predicate of type tt. At a generic world G put, externally,

```math
r_G=\{n\in\omega:q_n\in G\}
```

Y's actual extension is exactly {a_n:n∈r_G}. Suppose it has an actual least upper bound b∈B∩M. Then

```math
n\in r_G\quad\Longleftrightarrow\quad a_n\le b \tag{1}
```

The forward direction is upper-boundedness. If n∉r_G, pairwise disjointness makes ¬a_n an upper bound of every actual Y-member. This upper bound is admitted. Leastness therefore gives b≤¬a_n, and a_n≰b because a_n≠0. This proves the reverse direction without using any external completeness of B∩M.

The right side of (1) defines a real z_b in M, from b and the sequence (a_n). But r_G is not any real in M. For each z∈2^ω∩M, the set

```math
D_z=\{c\in B\setminus\{0\}:\exists n\,
 c\le(q_n\text{ if }z(n)=0,\ \neg q_n\text{ if }z(n)=1)\}
```

is dense and belongs to M. To see density, refine a nonempty regular open condition to a basic cylinder and choose a fresh coordinate with the bit opposite to z. Genericity gives c∈G∩D_z∩M, and a witnessing natural number gives a coordinate at which r_G differs from z. Hence r_G≠z_b, contradicting (1).

Thus Y has no current Boolean supremum at any generic world. By the equivalence of the LUB and GLB formulations, □¬BC_t holds. This is an admitted-family failure. The complete ambient algebra B does not imply internal BC_t for the actual extensions in the restricted generic model.

## 5. Independence boundary

The existing [two-colour model](finite-colour-propositional-completeness.md), §§1–6, satisfies C5+□Rev+□BC_t+¬Actuality and fails Zorn_t. By the established C5+RC⇒TC⇒Zorn implications, its all-type RC schema fails too.

Together the two models show that **propositional Boolean Completeness and all-type Relational Choice are independent even over C5 with necessary reversible logical separation**. The same two examples separate BC_t and Zorn_t in both directions. These claims concern the displayed current principles; the witnesses in fact carry the stronger boxed positive assumptions just stated.

Both models fail Actuality. They establish that neither additional premise alone suffices at this observer base. They do not establish either answer when BC_t and choice are present together.

The new automorphism, separation and missing-supremum arguments in §§2–4 were independently reviewed by the observer subagent and the coordinating agent on 25 October 2026. No native model record, human-authored proof, or formal-verification status is changed.

# A true image gap without a true split kernel

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new observer and verdicts: `misc`, this note, §§1–5, unpaginated. The unchanged full-function model is linked below.

The one-observer condition J does not imply the qualified inverse-pair condition K, even over C5. This is already witnessed by the full-function regular-open model used for the individual Boolean-transversal obstruction. A different observer in that same model has a currently true proposition containing no nonzero image value. Every logical observer nevertheless preserves current truth, so no qualified observer can kill a true proposition.

The new J witness even has a qualified left inverse. Its inverse's kernel is false. Thus the issue is the truth of the kernel, not merely the availability of an inverse. Ordinary logical separation fails in the model, so this does not settle whether OS together with J entails Rev or K.

## 1. Exact conditions and the unchanged model

Work with the qualifications in [Injective separation decomposition](injective-separation-decomposition.md), §1. Fix a finite external list Δ containing t. $`\mathrm{Good}_\Delta`$ uses whole Boolean and listed quantifier identities. Write 0,1 for Bottom, Top, and use the Boolean order. The relevant conditions are

```math
\begin{aligned}
J_\Delta:={}&\exists E^{tt}c^t\,[\mathrm{Good}_\Delta(E)
 \land\mathrm{Inj}(E)\land c
 \land\forall p\,(Ep\le c\to p=0)],\\
K_\Delta:={}&\exists E^{tt}F^{tt}c^t\,[\mathrm{Good}_\Delta(E)
 \land\mathrm{Good}_\Delta(F)
 \land F\circ E=I\land c\land Fc=0]
\end{aligned}
\tag{1}
```

For an injective logical E over C5, the last clause of J is equivalently R_Ec=0, where R_E is its admitted right order adjoint. The condition c is current truth, not the identity c=1.

Use exactly the model in [Injective observers and Boolean transversals](injective-observers-and-boolean-transversals.md), §§4–6. Let

```math
X=(2^{\mathbb N})^2,\qquad C=\mathrm{RO}(X),
\qquad A=\mathbf 2\times C
\tag{2}
```

Propositions are elements (ε,U) of A; current truth is ε=1. Individuals form a singleton. At every relational function type use the full actual function set on the preceding domains. Primitive Boolean operations are the operations of A, quantifiers are its actual meets and joins over the relevant domains, and equality returns the actual endpoints 1_A or 0_A according to equality of its arguments.

The linked construction proves C5, including full operation identities and all the required typing. In particular the first projection A→2 preserves arbitrary meets and joins, so these quantifiers have the required current truth conditions. All Boolean-valued H theorems have value 1_A, giving C's Logical Equivalence; crisp equality gives necessary distinctness. This note changes none of those domains or logical operations.

The algebra C is atomless. Hence A has exactly one atom,

```math
c=(1,0_C),
\tag{3}
```

and that atom is currently true. Every nonzero proposition of the form (0,U) is false.

## 2. An explicit complete embedding supplies J

Partition X into the two nonempty clopen sets P and Q according to the first bit of its first Cantor coordinate. The map which prepends the bit 1 to that coordinate and leaves the second coordinate unchanged is a homeomorphism X→Q. It induces a complete Boolean isomorphism

```math
h:C\longrightarrow C\mathbin{\upharpoonright}Q
\tag{4}
```

The codomain is the principal Boolean algebra below Q, with relative unit Q. Define

```math
i(\varepsilon,U):=(\varepsilon\cdot P)\lor h(U),
\qquad
E(\varepsilon,U):=(\varepsilon,i(\varepsilon,U)),
\tag{5}
```

where 0·P=0_C and 1·P=P. Since P,Q are complementary, masking i(ε,U) by P recovers ε·P, and masking by Q recovers h(U). Thus i:A→C is injective. It is a unital complete Boolean homomorphism: on the P-component it is the complete map ε↦ε·P, and on the Q-component it is h. The same is therefore true of E:A→A.

E is an admitted tt object because the function domains are full. A complete Boolean homomorphism commutes with every interpreted quantifier: for any admitted type σ and any F:D_σ→A, it preserves the actual meet or join of the family {F(x):x∈D_σ}. These equations hold for every argument, and equality of actual functions gives the whole composite identities. Thus E is $`\mathrm{Good}_\Delta`$ for every requested finite Δ, with the same E. The translated equality clauses follow from C and Boolean qualification. This reasoning does not identify arbitrary complete homomorphisms with observers in other models.

For the true proposition c from (3),

```math
E(\varepsilon,U)\le c
\quad\Longrightarrow\quad i(\varepsilon,U)=0_C
\quad\Longrightarrow\quad(\varepsilon,U)=0_A
\tag{6}
```

The second implication is injectivity of i and i(0_A)=0_C. Hence E,c witness J_Δ. Equivalently R_Ec=0_A, so the image floor E R_E sends this true c to Bottom.

## 3. Every logical observer preserves current truth

The following argument, already used for OS failure in the linked model, controls all possible K witnesses rather than just the displayed E.

Let T be any admitted $`\mathrm{Good}_{\{t\}}`$ observer. Its Boolean laws and Q_t imply that T preserves arbitrary meets in A. Indeed every nonempty external subset S⊆A is the range of an actual function A→A: fix s₀∈S and send a to a if a∈S, and to s₀ otherwise. That function is admitted by fullness. Applying Q_t gives preservation of the meet of S; the empty meet is covered by endpoint fixing. Boolean duality gives all joins as well. This argument takes place in the specified full-function metamodel; it imports no object-language Choice axiom into a general theorem.

Consequently

```math
\chi:=\mathrm{pr}_1\circ T:A\longrightarrow\mathbf 2
\tag{7}
```

is a complete Boolean character. Its accepted elements have a meet w with χ(w)=1. If 0<v≤w, either χ(v)=1, in which case the definition of w forces w≤v, or χ(v)=0, in which case χ(¬v)=1 and w≤¬v, contradicting v>0. Therefore w is an atom. The unique atom of A is c, so w=c. It follows that

```math
\chi(p)=1\quad\Longleftrightarrow\quad c\le p
\quad\Longleftrightarrow\quad\mathrm{pr}_1(p)=1
\tag{8}
```

Every $`\mathrm{Good}_{\{t\}}`$ observer thus has exactly the original current truth profile. In particular, for every currently true d and every such T, Td is true and cannot be 0_A. This proves

```math
\neg K_\Delta\qquad(t\in\Delta)
\tag{9}
```

There is also no ordinary propositional logical separation at Δ={t}: 0_A and (0,Q) are distinct, but every qualifying observer rejects both. Reversible and injective separation fail there as well, since their qualified classes are subclasses of $`\mathrm{Good}_{\{t\}}`$.

## 4. The J witness already has a qualified inverse on one side

For clarity, the witness E in (5) is not another example of an individually unsplittable injection. Define

```math
F(\varepsilon,V):=
 \bigl(\varepsilon,h^{-1}(V\land Q)\bigr)
\tag{10}
```

This is a unital complete Boolean homomorphism A→A, so it is admitted and Good at every finite list by the same full-function argument. Direct calculation gives

```math
F(E(\varepsilon,U))=(\varepsilon,U),
\qquad F\circ E=I
\tag{11}
```

Its greatest kernel element is k_F=(0,P), which is currently false. In contrast F(c)=c. Equation (8) shows that no other $`\mathrm{Good}_{\{t\}}`$ observer can kill c or any true proposition either. Therefore even J witnessed by an E having a qualified left inverse does not give K.

The finite relative-generation theorem supplies a further exact limitation. For every fixed external finite n, this E fails $`\mathrm{FG}_n(E)`$: if it were generated over its image by n Boolean generators, the controlled-selector theorem would produce a qualified left inverse killing c, contradicting (8). This is a failure for each fixed finite generating bound, not a claim about internal Frege finiteness. See [Finite generation over an observer's image](finite-relative-image-generation.md), §§1–3.

## 5. Scope and sources

The unchanged model therefore verifies

```math
\boxed{\mathrm{C5}+J_{\{t\}}+\neg K_{\{t\}}
 +\neg S_{t,\{t\}}[\mathrm{Good}]}
\tag{12}
```

In particular $`J_t`$⇒$`K_t`$ is refuted. The additional premise OS in the remaining comparison is essential to its formulation: the stronger failure of C5+OS+$`J_t`$ implying Rev or $`K_t`$ is proved by the separate [rigid Souslin model](rigid-souslin-injective-separation.md). Nor does the existence of this individual injective E establish injective separation.

The new embedding, inverse and J/¬K verdict are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–5, unpaginated. The full-function construction, its C5 verification and the complete-character argument retain their proof and attribution in [Injective observers and Boolean transversals](injective-observers-and-boolean-transversals.md), §§4–6. The meanings and whole-operation scope of J and K are in [Injective separation decomposition](injective-separation-decomposition.md), §§1 and 6; the finite-generation consequence uses the linked theorem. No claim is attributed to a published source for the new argument.

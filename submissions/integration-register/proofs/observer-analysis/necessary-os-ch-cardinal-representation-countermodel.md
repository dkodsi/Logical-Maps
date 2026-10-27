# Finite-bit forcing: necessary reversible observers without cardinal representatives

Ordinary mathematical research by OpenAI Codex, 25 October 2026. The forcing input is Asaf Karagila and Philipp Schlicht, *How to have more things by forgetting how to count them*, arXiv:1910.14480v2, Theorem 6.1 and Corollary 6.2, printed p. 8. The finite-flip cardinal argument and its typed interpretation below are new arguments in this research; their direct source is `misc`, this note, §§2–8, unpaginated. No native records, Lean files or compilation targets are changed.

**Result.** Given a countable model M of ZF containing an infinite Dedekind-finite set of reals, there is an atomless, internally full Boolean-valued relational Henkin model satisfying C5 + □Rev, with one persistent real-field tuple satisfying Real necessarily, in which an admitted real subproperty has no persistent cardinal representative at any finite type. In particular, CR_{e,T} fails for every fixed finite list T of representative types, even necessarily.

CH is necessarily false in this example. Thus this refutes the unconditional cardinal-representation route from C5 + □OS, even after adding necessary real existence. It does **not** refute CH propagation, or the narrower conjecture that current CH supplies a persistent representative for the continuum. Here Rev denotes reversible qualified-observer separation, so □Rev implies □OS.

## 1. Ground model and the precise forcing input

Fix a countable M satisfying ZF and containing an infinite Dedekind-finite set A of real numbers. Dedekind-finite means that no injection from ω into A exists; equivalently, A is not equinumerous with any proper subset. All constructions in the next sections, before external generic truth is selected, are performed internally in M.

Let

```math
\mathbb P=\mathrm{Fn}(A,2,{<}\omega),
\qquad B=\mathrm{RO}(\mathbb P)
\tag{1}
```

Conditions are finite partial functions, ordered by extension. This is Add(A,1) in the cited paper. Since A is linearly orderable, [Theorem 6.1 and Corollary 6.2, p. 8](https://arxiv.org/pdf/1910.14480) imply both that this forcing preserves A's Dedekind finiteness and that it adds no real numbers. These are the only preservation conclusions needed here. The paper's §3, especially Proposition 3.2 on p. 4, supplies Cohen's first model as a source of such ground models.

No transitivity of the chosen countable M is assumed. In the nonstandard case, “finite” in (1), the Boolean algebra, the typed domains and the forcing assertions are interpreted in M. The external argument uses the truth lemma for standard finite formulas, as explained in §4. The stated exact metatheoretic premise avoids treating the existence of a countable transitive model as a consequence of consistency.

Write $`\dot S`$ for the canonical name for the set of coordinates receiving bit one. Both $`\dot S`$ and its complement in A are forced infinite: any condition can be extended to assign either prescribed bit at any specified finite number of unused coordinates. Both are forced Dedekind-finite, since A remains so.

## 2. The generic subset has no old cardinal representative

For every ground set T, no condition forces

```math
\dot S\approx\check T
\tag{2}
```

Suppose otherwise that p forces (2), where the statement asserts existence of a bijection. Choose $`a\in A\setminus\mathrm{dom}(p)`$. Let $`\pi_a`$ be the forcing automorphism which flips the bit at coordinate a. It fixes p and every canonical check-name, and it sends the generic subset name to a name forced equal to its symmetric difference with $`\{a\}`$. The symmetry lemma therefore gives

```math
p\Vdash \dot S\mathbin{\triangle}\{\check a\}
                      \approx\check T
\tag{3}
```

Extend p to q by assigning bit one at a. Together, (2) and (3) give

```math
q\Vdash \dot S\approx\dot S\setminus\{\check a\}
\tag{4}
```

This contradicts preservation of Dedekind finiteness. The composition of the two bijections in this argument is a ZF operation; neither their existence nor their composition requires Choice. In particular, the proof applies directly to the existential statement (2) and does not select one name for a bijection uniformly below p.

Equivalently, the Boolean truth value of (2) is zero for each old T. If it were nonzero, a forcing condition below that value would give the prohibited p. This is stronger than merely saying that the canonical generic subset is new: its cardinality has no representative among **any** of the old sets.

## 3. Full finite types over the ground reals

Use the ground real numbers as the individual domain and B as the proposition domain:

```math
D_e=\mathbb R^M,\qquad D_t=B
\tag{5}
```

For each admitted relational type, take the full function set computed in M. In curried notation,

```math
D_{\sigma\tau}=(D_\tau^{D_\sigma})^M
\tag{6}
```

whenever that arrow is an admitted relational type. Thus every domain at a standard finite type is an old M-set. Boolean operations interpret propositional connectives, and internally indexed Boolean meets and joins interpret quantifiers. Every lambda-definable relation is an internal function and belongs to its specified domain.

Regular-open completeness and these function-set constructions are available in ZF. Internal Choice is not being inserted into the model. This matters: the argument establishes no Relational Choice or Functional Choice claim.

Leibniz equality is crisp at every type. If x and y are different domain objects, the internal endpoint-valued characteristic function of $`\{x\}`$ distinguishes them; it is an admitted property. Thus the defined equality has value zero. If they are the same object, its value is one. Consequently native necessity is the global top test on proposition values, and necessity and distinctness of identities hold at every type. Together with the full typed interpretation of the background logical theory, this gives C5. In particular,

```math
\|\Box\varphi\|=
\begin{cases}
1,&\|\varphi\|=1,\\
0,&\|\varphi\|\ne1
\end{cases}
\tag{7}
```

Here and below Boolean-valued formulas have only standard finite syntax, although their parameters and internal domains need not be externally well-founded.

## 4. Actual truth and quantifiers without Choice

Choose an external M-generic ultrafilter U on the internally computed B. Such a U can be built by meeting the countably many internally dense subsets, using external countability of M. Declare a proposition actually true just when its Boolean value belongs to U.

For completeness, the generic quantifier argument does not need an internal maximal antichain. Given any internal family $`f:I\to B`$, put $`b=\bigvee_{i\in I}f(i)`$. The internal set

```math
D_f=\{c>0:c\le\neg b\ \text{or}
                 \exists i\in I\ c\le f(i)\}
\tag{8}
```

is dense in $`B\setminus\{0\}`$. Indeed, if a nonzero d has nonzero intersection with $`\neg b`$, refine to that intersection. Otherwise $`d\le b`$; some $`d\wedge f(i)`$ is nonzero, since b is the least upper bound. Refining to that intersection suffices. This selects a single witness for a single d, not a choice function over all d.

Since U meets (8),

```math
\bigvee_i f(i)\in U
\quad\Longleftrightarrow\quad
\exists i\in I\ f(i)\in U
\tag{9}
```

Complements give the dual statement for universal quantifiers. Induction on formulas therefore makes the external generic interpretation an ordinary Henkin interpretation of the fixed language. All standard finite formulas used below transfer through this induction even when M is nonstandard. Forcing-extension terminology in that case abbreviates the corresponding generic quotient and its truth lemma, rather than a claim of external well-foundedness.

## 5. Necessary reversible observer separation and atomlessness

Every finite bit flip extends to an internal complete Boolean automorphism of B, with its inverse another finite bit flip. It is an admitted function of type tt. It preserves all the internal meets and joins used by the typed quantifiers, all Boolean operations, and the crisp identity predicates. Hence it satisfies every finite qualification list of whole-operation observer identities. Its inverse does too, and their two composites are the identity operation as objects, not just currently coextensive graphs.

The finite-flip group is weakly homogeneous. Given p and q, flip precisely those coordinates in their common domain on which their bits disagree. The resulting image of p is compatible with q. Consequently, for every nonzero $`b\in B`$,

```math
\bigvee_{\pi\text{ a finite bit flip}}\pi(b)=1
\tag{10}
```

To verify the join directly, take any nonzero c and conditions p below b and q below c. The preceding flip supplies a nonzero common refinement of c and $`\pi(b)`$. Thus the complement of the join in (10) cannot be nonzero. This uses only finite changes, not an enumeration of A.

For distinct propositions u and v apply (10) to their nonzero symmetric difference. The join of the truth values saying that an admitted reversible qualified observer distinguishes u and v is one. For different predicates at a higher relational type, choose an argument tuple where their values differ and apply the same reasoning there. The identity direction is automatic. Therefore every required reversible-observer separation instance has value one:

```math
\Box\mathrm{Rev}_{\rm all},
\qquad\text{hence}\qquad\Box\mathrm{OS}_{\rm all}
\tag{11}
```

Finally B is atomless. Below any nonzero element take a condition p, choose an unused coordinate, and extend with its two opposite bits. Their regular-open values are disjoint nonzero refinements. The same argument works internally in M and supplies actual witnesses in the externalized Boolean algebra.

## 6. One persistent real field is necessarily complete

Use the whole carrier $`\top_e`$, the ground field's 0 and 1, and its ground addition, multiplication, order and natural-number predicates, represented by endpoint-valued relation graphs. Each of these properties or relations is persistent. We claim that this **same tuple** satisfies Real with Boolean value one.

The algebraic and order axioms hold directly. For completeness, an admitted property $`X:D_e\to B`$ is the Boolean name of a subset of $`\check{\mathbb R^M}`$. The no-new-reals forcing theorem says that the ground reals are still all the reals in the extension. Hence any nonempty bounded interpreted X has a least upper bound among the ground real labels. Concretely, its lower rational cut is a real code, that code is old, and its ground real supremum satisfies the required inequalities.

This is exactly completeness for **nonempty bounded** subproperties, the convention authorized for this project. It includes all the new subsets named by admitted B-valued functions. One must not reduce it to completeness for old subsets.

The native existential quantifier over potential suprema is the join over the ground real labels. The forcing assertion that some old real is the supremum makes that join one; it does not require a choice of a globally named supremum for every X. The ground natural-number predicate is likewise the least inductive subset of the field in the extension, and the internal forcing proof gives the native induction clause. Therefore

```math
\Box\mathrm{Real}_e
 (\top_e,0,1,+,\times,\le,N)
\tag{12}
```

holds for the displayed persistent tuple. This resolves the possible representability gap that arises when one merely mentions a symmetric extension's reals without giving them admitted, uniquely labelled native field data.

## 7. No persistent cardinal representative at any finite type

The generic subset is an admitted real subproperty: define $`S:D_e\to B`$ by assigning, at $`a\in A`$, the Boolean value of the coordinate statement “a receives bit one,” and assigning zero outside A. This function belongs to M and to $`D_{et}`$.

For any admitted property $`Z:D_\rho\to B`$, native persistence is

```math
P(Z):=\Box\forall x\,(Zx\to\Box Zx)
\tag{13}
```

By (7), this holds exactly when every Z(x) is an endpoint. Indeed, for a nonendpoint value b the inner implication has value $`\neg b\ne1`$; endpoints give one. Thus a persistent Z has the current extension

```math
T_Z=\{x\in D_\rho: Z(x)=1\},
\tag{14}
```

and (14) is an old M-set by Separation. This conclusion applies to every finite type ρ, however high. It does not require its domain to be externally countable in a way available internally to M, or to be well-orderable in M.

Every admitted candidate graph $`F:D_e\times D_\rho\to B`$ is an M-coded Boolean name for a relation on the corresponding ground domains. If it were currently a bijection between S and persistent Z, its interpretation in the generic extension would be a bijection

```math
S_U\approx\check T_Z
\tag{15}
```

Section 2 prohibits (15). More precisely, for each endpoint-valued Z the Boolean value of existence of such a bijection is zero: a nonzero value would have a forcing condition below it, contradicting the finite-flip lemma. Nonpersistent Z contribute zero to the existential assertion requiring P(Z), since P(Z) itself is crisp. Taking the internal join over all Z and candidate graphs therefore still gives zero.

For every standard finite type ρ we obtain

```math
\left\|\exists Z^{\rho t}
          [P(Z)\land S\approx Z]\right\|=0
\tag{16}
```

The same S witnesses every one of these separate instances. Given any fixed finite list T, the finite disjunction of (16) is zero. Applying it to the necessarily real tuple (12) shows

```math
\Box\neg\mathrm{CR}_{e,T}
\tag{17}
```

Here CR is the exact finite-type-list assertion defined in [the cardinal-profile note](necessary-os-ch-cardinal-profiles.md), §3. There is no illicit object-language quantification over all types in (16)–(17); the all-types conclusion is an external schema. Intensional identity, passage to higher cut-code types, or a Scott-cardinal construction cannot supply an admitted persistent representative for this S, because any such representative would still have an old extension (14).

## 8. Exact CH scope

The old set A itself is an endpoint-valued real subproperty. It remains infinite Dedekind-finite. It is not countable: an injection into N would identify it with an infinite subset of N, whose increasing enumeration gives a countably infinite subset of A. It is not equinumerous with the whole real carrier either, since that carrier has an admitted countably infinite subset. These ZF arguments apply to the interpreted admitted graphs and have Boolean value one.

Thus A necessarily witnesses failure of the project's subset-cardinality formulation of CH in the persistent real field (12). Native real-field categoricity and transport of the relevant relations give

```math
\Box U_{e,\neg\mathrm{CH}}
\tag{18}
```

In particular, the model does not switch CH's truth value. It establishes that necessary observers and a persistent complete real carrier do not force **every subset** to have a persistent cardinal representative. Its continuum already has one, namely $`\top_e`$; the obstruction concerns the intermediate Dedekind-finite cardinal of S. Under CH the intermediate case is excluded, so the narrower route through a persistent representative of the whole continuum remains unrefuted by this model.

The positive implications proved in the cardinal-profile note retain their stated extra hypotheses. What is now ruled out is deriving necessary CR unconditionally from C5 + □OS, or repairing that derivation merely by assuming necessary real existence or even a single persistent necessary real-field tuple.

## 9. Independent research audit

# Internally finite affine separation over H

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: misc, this note, §§1–6, unpaginated. The base is H. No C, NI, BF, Choice or Functionality is assumed.

The material theorem below is strengthened by [Finite affine normalization](finite-affine-normalization.md): internal finiteness supplies two-output pointwise homomorphisms, and even finite images of material separators suffice for profile-preserving normalization. The proof below remains the character-extension argument; its final limitation about pointwise preservation is superseded under those stated hypotheses.

## 1. Internal finiteness and the exact statements

Use the material observer qualifications from [Truth profiles and connective reducts](truth-profiles-and-connective-reducts.md), §6. Let X_m(E) mean material preservation of a fixed XOR operation, and D_m(E) material preservation of a fixed biconditional operation. Their truth tables are the H XOR and biconditional tables. As in [Term closure and affine branches](term-closure-and-affine-branches.md), particular abbreviation expansions must be specified if syntactic consequences for other operations are intended.

Let Fin_t(U) abbreviate

$$
\exists Z^{(tt)t}
  (\mathrm{FiniteCardinality}_t(Z)\land ZU).
$$
The definition is the existing Frege induction definition in [Background, Notation](../../source/topics/classicism/background.md):

$$
\mathbf0:=\lambda U.\forall x\neg Ux,
\qquad
\mathrm{Suc}(Z):=\lambda U.\exists y(Uy\land Z(\lambda x.Ux\land x\ne y)),
$$
$$
\mathrm{FiniteCardinality}_t(Z):=
\forall W\,[(W\mathbf0\land\forall Y(WY\to W(\mathrm{Suc}(Y))))\to WZ].
$$
All types here are admitted relational types. Put All:=λx.Top, and assume Fin_t(All). This is internal Frege finiteness of the proposition domain. It does not assert that the finite cardinality is a standard numeral or supply an external enumeration.

**Theorem 1.** Over H+Fin_t(All), material XOR separation is equivalent to the Boolean-group equations for XOR. Explicitly, for z:=a⊕a at any fixed proposition a, these equations say ⊕ is associative and commutative and

$$
p\oplus z=p,\qquad p\oplus p=z.
$$
**Theorem 2.** Over the same base, material biconditional separation is equivalent to the analogous Boolean-group equations for ↔, with identity u:=a↔a.

Here z is false and u is true by the H truth conditions. Necessity follows from the truth-profile argument: symmetric difference, or complemented symmetric difference, gives the corresponding group equations. Sufficiency is proved by the internal finite induction below.

## 2. Admitted subgroups and truth characters

For the proof, write the group operation as + and its identity as 0, regardless of which of the two applications is intended. Assume the commutative group equations and x+x=0. A subgroup is an admitted predicate L:tt containing 0 and closed under +. Every element is its own inverse, so no additional inverse-closure clause is needed.

An admitted truth character e:tt on L satisfies

$$
\neg e0,
\qquad
\forall x,y\,[Lx\land Ly\to
(e(x+y)\leftrightarrow((ex\land\neg ey)\lor(\neg ex\land ey)))].
\tag{1}
$$
The right side is a truth-level XOR expression. There is no assertion that e takes only two proposition objects, nor that it preserves + as an output identity. Its outputs are used through their truth values.

Fix an admitted subgroup L₀ and a character e₀ on it. An extension (L,e) means L contains L₀, e is a character on L, and ∀x(L₀x→(ex↔e₀x)). All of these conditions are formulas of H and therefore can occur in the comprehension terms and induction property below.

## 3. The one-element extension

Suppose (L,e) extends (L₀,e₀), and let y be any proposition object. If Ly holds, no extension is needed. Otherwise define the admitted predicates

$$
L'(x):=Lx\lor L(x+y),
$$
$$
e'(x):=(Lx\land ex)\lor(L(x+y)\land e(x+y)).
\tag{2}
$$
The two cosets in L' are disjoint: if both Lx and L(x+y) held, closure and x+x=0 would give Ly. The predicate L' contains L and y, contains 0, and is closed under +. Its two membership cases are exactly L and y+L.

On L, e' agrees with e. On y+L, it agrees with the character at the translated element x+y. The four coset combinations verify (1) for e'. For example, if x and v both belong to y+L, then x+y and v+y lie in L and

$$
x+v=(x+y)+(v+y).
$$
Thus e'(x+v) has the XOR truth value of e(x+y) and e(v+y), which are e'(x) and e'(v). In the mixed case, x+(v+y) lies in L and the same character law applies. The case where both inputs lie in L uses the old law directly. Also e'(0) is false, and e'(y) is false because y+y=0. Hence (L',e') is an extension assigning y character value zero.

Every new predicate in (2) is a displayed lambda term using the existing parameters. This step chooses neither an external coset representative family nor a basis.

## 4. Frege induction extends a character to the entire domain

With L₀,e₀ fixed, define the admitted property W of cardinality objects by

$$
W(Z):=\forall U\,[ZU\to
\exists L,e\,(\mathrm{Extension}(L,e;L_0,e_0)
 \land\forall x(Ux\to Lx))].
\tag{3}
$$
**Zero.** If the cardinality-zero predicate $\mathbf0(U)$ holds, then U is empty in truth. The original pair L₀,e₀ witnesses (3).

**Successor.** Assume W(Z), and suppose Suc(Z)U. By its defining formula, choose y with Uy and

$$
Z(\lambda x.Ux\land x\ne y).
$$
Apply W(Z) to that deletion predicate, obtaining an extension containing every U-member other than y. Use §3 to adjoin y if necessary. The resulting extension contains every U-member and proves W(Suc(Z)). This uses only a witness in this single existential-elimination step; it does not select witnesses uniformly over a family of steps.

The definition of FiniteCardinality now gives W(Z) for every internally finite cardinality Z. Choose the witness Z for Fin_t(All) and apply W(Z) to All. The resulting subgroup contains every proposition object, so its character is defined on the whole group and extends e₀ there.

This is a direct use of the impredicative induction formula. It neither identifies its finite cardinalities with externally standard integers nor presumes that every external subgroup or character is admitted. Only the explicitly comprehended subgroups, character terms and induction property are used. No equality-necessity principle or extensionality of cardinality objects is required: W quantifies over the actual predicates U to which Z applies, and the successor case uses the exact deletion term appearing in the definition of Suc.

## 5. Separating a pair and proving the two theorems

Given d≠0, take

$$
L_0(x):=(x=0)\lor(x=d),
\qquad e_0(x):=(x=d).
$$
The group equations make L₀ a subgroup, and e₀ is a character on it with e₀d true. Section 4 yields an admitted character e on the entire group with ed true.

For distinct p,q, put d:=p+q. Then d≠0, since p+q=0 would imply p=q. The character law makes ep and eq have different truth values.

For **XOR**, use +=⊕ and E:=e. The H XOR truth table and (1) give the material X law directly; E distinguishes p,q. Thus the group equations and internal finiteness imply S[X_m].

For **biconditional**, use +=↔ and E:=λx.¬ex. Its unit is the true proposition u, but the auxiliary character e still sends that group unit to false. The character law gives

$$
E(p\leftrightarrow q)
\leftrightarrow\neg(ep\mathbin{\mathrm{XOR}}eq)
\leftrightarrow(Ep\leftrightarrow Eq).
$$
So E is materially biconditional-preserving and distinguishes p,q. This proves S[D_m]. The equality-to-agreement directions of both separation biconditionals are ordinary H substitution.

### Endpoint orientations

The same proof can orient the character at a specified nonidentity element c while still distinguishing any given pair. Put d:=p+q≠0 and demand e(c) and e(d) both true. If c=d, use the two-element subgroup above. Otherwise 0,c,d,c+d are pairwise distinct and form a subgroup; the admitted initial character is true exactly at c and d and false at 0,c+d. Its truth table verifies the character law. Apply §4 to extend it.

For XOR, Top≠z by their H truth values. Taking c=Top proves that adding acceptance A does not change Theorem 1. Adding rejection Z instead has the exact extra condition Bottom=z: forward, all qualified observers reject both propositions and separation identifies them; reverse, every material XOR observer rejects z. Thus, under internal finiteness, the four endpoint variants are:

| Material XOR qualification | Exact additional condition beyond the group equations |
|---|---|
| X_m | None |
| A∧X_m | None |
| Z∧X_m | Bottom=z |
| A∧Z∧X_m | Bottom=z |

For biconditional, Bottom≠u. Taking c=Bottom makes E=¬e reject Bottom while retaining separation. Acceptance has the exact extra condition Top=u, since every material biconditional observer accepts its derived unit. Therefore:

| Material biconditional qualification | Exact additional condition beyond the group equations |
|---|---|
| D_m | None |
| Z∧D_m | None |
| A∧D_m | Top=u |
| A∧Z∧D_m | Top=u |

These are character constructions, not an assertion that post-negation preserves XOR or biconditional qualification.

## 6. Scope and comparison with bounded finite versions

For any fixed external n, an exhaustive n-element list of the proposition domain also implies the result: it supplies an internally finite All predicate, or the one-element extension proof can be repeated finitely along that list. But the theorem proved here has the single internal Frege-finiteness premise and uses its actual induction definition. It is not the schema asserting separation separately for each n, and it does not fix a uniform standard bound on the proposition domain.

The conclusion is material separation. A character here is an admitted proposition-valued truth test; the proof does not make its output objects a two-element subalgebra, prove output-preservation identities, or infer identities between complete composite operations. The strong affine branch is not identified by this argument. No dimension, standard finite-rank classification, general character extension over an infinite group, or Choice principle is claimed.

Definition source: the Frege cardinality formulas in [Background](../../source/topics/classicism/background.md), Notation. Proof source: misc, OpenAI Codex, 24 October 2026, this note, §§2–5, unpaginated.

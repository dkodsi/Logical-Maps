# Negation and affine operations: compatible reversible separation

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–7, unpaginated.  Plenitude and the earlier affine construction are attributed in §8.

Negation together with either affine operation has a positive reversible classification under Plenitude. The exact compatibility requirement is an output identity: negation is translation by the negation of the group unit. For XOR together with biconditional, the corresponding requirement says that the two operations differ by one fixed translation. Material separation already characterizes these compatibilities over bare H. Plenitude then supplies admitted involutions preserving the entire linked signature.

## 1. Fixed operations, tiers and notation

Use H and the fixed proposition abbreviations Top and Bottom. Write N for the original negation operation. A(E) means E(Top) is true, and Z(E) means E(Bottom) is false. Mat_f(E) means material preservation of the specified operation f; Pt_f(E) means preservation as a proposition-output identity at every input. Whole preservation is identity of the complete displayed composite operations. These tiers retain the distinctions in [Truth profiles](truth-profiles-and-connective-reducts.md), §§1 and 6.

The operations called XOR and biconditional below are fixed admitted operations with those H truth tables. No primitive or independently expanded operation is replaced merely because its truth table matches. One explicit choice of abbreviations is

```math
D(x,y):=(\neg x\lor y)\land(\neg y\lor x),
\qquad X(x,y):=\neg D(x,y)
\tag{1}
```

The main theorems apply to arbitrary fixed operations with the indicated truth tables. Section 6 alone adds the actual expansion X=ND from (1). This is a specified convention, not an assertion about an unverified alternative abbreviation.

For one affine operation write +, and let 0 be its derived unit a+a at a fixed proposition a. Material + separation supplies the Boolean-group equations BG(+): associativity, commutativity, x+0=x and x+x=0. It also makes the unit independent of the chosen a. The unit is false for XOR and true for biconditional. These are output identities, not assumed identities of entire operation objects.

Set

```math
c:=\neg0,
\qquad
\tau(x):=x\quad\text{for XOR},
\qquad
\tau(x):=\neg x\quad\text{for biconditional}
\tag{2}
```

The last two clauses specify an admitted formula in each of the two separate cases. Its truth values satisfy an XOR character law for +, with τ(0) false and τ(c) true. No new two-element object domain is postulated.

S[K] is propositional separation by the admitted K-observers. Invol_pt(E) means ∀x(E(Ex)=x). Fix(O) requires fixing the endpoint objects mentioned by O, where O is no condition, A, Z, or A∧Z.

## 2. Bare-H compatibility of negation with one affine operation

**Theorem 1.** Over H,

```math
\boxed{S[\mathrm{Mat}_N\land\mathrm{Mat}_{+}]
\ \longleftrightarrow\
S[\mathrm{Mat}_{+}]\ \land\
\forall x\,(\neg x=x+c)}
\tag{3}
```

The right side includes BG(+) through S[Mat₊]. The translation identity is additional information about the original negation operation.

**Forward.** Forgetting N yields material + separation and BG(+). Every eligible observer E sends 0 to the unit's truth value: evaluate its material law at x+x=0. It sends c=¬0 to the opposite truth value, by Mat_N. Consequently E(x+c) and E(¬x) have the same truth value for every x. For XOR this adds a true value; for biconditional it takes biconditional with a false value. In both cases the result is the negation of Ex. Separation gives ¬x=x+c.

**Reverse.** Suppose the right side of (3), and take p≠q. Put d=p+q; BG(+) gives d≠0. If τ(d) is true, p and q differ in truth, and identity separates them while preserving both operations.

Otherwise τ(d) is false. Material + separation of d from 0 gives an admitted E such that χ(x):=τ(Ex) is a truth character with χ(d) true and χ(0) false. Arrange χ(c) true as follows. If it is true already, keep χ. If false, replace χ by the admitted truth-XOR formula

```math
\chi'(x):=(\chi x\land\neg\tau x)
\lor(\neg\chi x\land\tau x)
\tag{4}
```

Both χ and τ are material XOR characters for +, so (4) is one too. Since τ(c) is true and τ(d) false, the replacement makes χ(c) true and keeps χ(d) true. Write χ for the resulting character.

For XOR use E′:=χ; for biconditional use E′:=λx.¬χx. Its character law makes E′ materially + preserving. The translation identity and χ(c) true give

```math
\chi(\neg x)\leftrightarrow\chi(x+c)
\leftrightarrow\neg\chi x,
```

so E′ also preserves original negation materially. The character value at d shows E′p and E′q have different truth values. Every operation constructed here is an admitted lambda term. No Plenitude, Choice, Functionality or object-valued conditional was needed for (3).

## 3. Exact endpoint alignments

Every materially N,+ preserving observer gives 0 and c their respective, opposite truth values. Therefore the optional endpoint conditions have the following exact effect over H:

| Signature and orientation | Exact condition beyond S[Mat₊] and ∀x(¬x=x+c) |
| --- | --- |
| XOR, no orientation | None |
| XOR, A | Top=c |
| XOR, Z | Bottom=0 |
| XOR, A∧Z | Top=c and Bottom=0 |
| Biconditional, no orientation | None |
| Biconditional, A | Top=0 |
| Biconditional, Z | Bottom=c |
| Biconditional, A∧Z | Top=0 and Bottom=c |

For example, in the XOR A case every eligible observer accepts both Top and c; separation identifies them. In the Z case it rejects both Bottom and 0. The biconditional cases exchange the truth roles of 0 and c. Conversely each listed alignment makes the corresponding endpoint truth condition automatic for every material N,+ observer, so Theorem 1 supplies the required separation.

Thus the endpoint of truth opposite to the group unit is no longer free once original negation is preserved. In the single-affine theorem A added no condition for XOR and Z added none for biconditional. Here these conditions align an original endpoint with c. No identity between Top and c, or between Bottom and c, is silently assumed.

## 4. Plenitude supplies joint involutive separators

Assume the single Plenitude instance Plen_{t,t}: every admitted current total single-valued relation from propositions to propositions is represented by an admitted operation. Its exact formula is [Plenitude normalization](plenitude-material-normalization.md), §1.

**Theorem 2.** Over H+Plen_{t,t}, for every orientation O,

```math
\boxed{S[O\land\mathrm{Mat}_N\land\mathrm{Mat}_{+}]
\ \longleftrightarrow\
S[\mathrm{Fix}(O)\land\mathrm{Pt}_N\land\mathrm{Pt}_{+}
       \land\mathrm{Invol}_{\mathrm{pt}}]}
\tag{5}
```

For the forward direction, Theorem 1 supplies material + separation and the translation identity. Apply the affine involution construction of [Partial reversible normalization](partial-reversible-normalization.md), §3, with its distinguished opposite-unit element a set equal to c. It gives, for each unequal p,q, a separating admitted pointwise group involution J with Jc=c. A pointwise group homomorphism also fixes 0. Consequently

```math
J(\neg x)=J(x+c)=Jx+Jc=Jx+c=\neg Jx
\tag{6}
```

This proves preservation of the original negation operation as an output identity. The endpoint alignments in §3 make J fix every endpoint required by O. The reverse implication in (5) forgets the extra qualifications.

For clarity, the cited construction uses a separating auxiliary character with value one at d=p+q and adjusts it to value zero at c. Plenitude represents Lx=c when that character is true and Lx=0 otherwise. Then L is a pointwise group homomorphism, Lc=0 and L²=0. The admitted Jx=x+Lx has J²x=x, fixes c, and separates the pair. When τ(d) is true, identity suffices. The construction needs only material + separation, not an admitted basis or uniform choice of characters.

Equation (6) is not a full-operation bridge inferred from the truth table of N. It uses the specific translation output identity proved by separation. Whole-operation conclusions are addressed in §7.

## 5. A compatible XOR/biconditional pair

Now keep two fixed operations X,D with their respective XOR and biconditional truth tables. Write x⊕y for X(x,y), let z:=X(a,a), and let u:=D(a,a), for a fixed a. The truth of u is already supplied by H. Joint separation additionally gives both group laws and makes the two units independent of a.

**Theorem 3.** Over H,

```math
\boxed{S[\mathrm{Mat}_X\land\mathrm{Mat}_D]
\ \longleftrightarrow\
S[\mathrm{Mat}_X]\ \land\
\forall x,y\,[D(x,y)=(x\oplus y)\oplus u]}
\tag{7}
```

**Forward.** Joint profiles give BG(X) and BG(D). Every eligible E accepts u. Material X preservation makes its value on (x⊕y)⊕u have the biconditional truth value of Ex and Ey, which is its value on D(x,y). Separation gives the displayed compatibility identity.

**Reverse.** Start with material X separation and that identity. For d=p⊕q≠z, identity separates if d is true. Otherwise choose an admitted XOR character χ true at d and orient it to be true at u using (4), now with τ(x)=x. The resulting χ preserves X materially. Since it accepts u, the compatibility identity makes it preserve D materially as well. It separates p and q. This is again a bare-H argument.

Adding A in (7) has the exact additional condition Top=u; adding Z has the exact additional condition Bottom=z; adding both requires both identities. Forward the qualified profiles identify the endpoints with these units. Conversely those alignments make A/Z automatic.

Under Plen_{t,t}, the involution construction with distinguished element a=u gives a separating pointwise X-homomorphism J fixing u, and hence

```math
J(D(x,y))=J((x\oplus y)\oplus u)
=(Jx\oplus Jy)\oplus u=D(Jx,Jy)
\tag{8}
```

Thus (5) holds with the joint signature X,D in place of N,+, for every orientation. It fixes the corresponding endpoints by the preceding alignments. For independently specified X,D, no preservation of the original N is asserted by this theorem unless an additional bridge to N is proved.

## 6. When the actual expansion links all three operations

Add the explicit syntactic assumption X(x,y):=¬D(x,y), as in (1). Under this assumption, for each orientation O, the three material separation packages

```math
S[O\land\mathrm{Mat}_N\land\mathrm{Mat}_X],\quad
S[O\land\mathrm{Mat}_N\land\mathrm{Mat}_D],\quad
S[O\land\mathrm{Mat}_X\land\mathrm{Mat}_D]
\tag{9}
```

are equivalent. Each is also equivalent to material separation by observers preserving all three operations.

- N,D preservation gives X preservation directly from its actual displayed expansion.
- N,X separation supplies the double-negation output identity, either by the negation profile law or by its translation form. Therefore D(x,y)=¬X(x,y). Every material N,X observer consequently preserves D as well.
- X,D separation supplies BG(X) and the compatibility in (7). Setting y=z gives D(x,z)=x⊕u and X(x,z)=x. The actual expansion therefore yields ¬(x⊕u)=x. Substituting x⊕u for x and using BG(X) gives

```math
\neg x=x\oplus u
\tag{10}
```

  Every material X,D observer accepts u, so (10) makes it preserve N materially too.

These arguments remain valid with O present: forgetting O gives the needed structural identities, while each original observer retains its endpoint truth restrictions. This proves the equivalences rather than merely showing that the operations have related truth tables.

Under Plenitude, the common theory supplies pointwise involutive separators preserving all three operations, with required endpoint fixing. Use the X,D involution fixing z and u, then (10) supplies pointwise N preservation. Its exact endpoint alignment is Top=u for A, Bottom=z for Z, and both for A∧Z. The pointwise identities in this paragraph do not by themselves identify the original complete operation objects.

## 7. Whole-operation scope and existence hypotheses

At propositional scope, Fun_{t,t} upgrades pointwise negation preservation and J²x=x to whole-operation identities. For each binary operation, Fun_{t,t} and Fun_{t,tt} collect the two input variables. Under these explicit local premises, each pointwise involutive separation theorem above is therefore equivalent to the corresponding whole-operation involutive separation theorem. Allowing any admitted qualified two-sided inverse gives the same separation strength: involutions are such witnesses, and reversible qualified observers are material observers.

At full relational scope, [typed factorization](typed-separation-and-classicism.md), §2, gives FullSep[K] exactly as propositional S[K] together with Functionality. Hence, under Plen_{t,t}, the full typed material, pointwise involutive, whole-operation involutive and reversible versions coincide for each linked signature established here. The structural side of (3) becomes full typed material + separation together with its translation identity; the side of (7) becomes full typed material X separation together with its compatibility identity. Alternatively one can display propositional separation and all Functionality separately. No extra type quantifier is inserted into H.

These are normalization theorems given material character separation. For an independent existence premise, [Zorn affine character extension](zorn-affine-character-extension.md), §§2–6, proves over H+Zorn at tt that BG(+) supplies material + separation. Combining it with (3), or with (7), gives exact algebraic characterizations from the corresponding group and compatibility identities. Plenitude then supplies involutive witnesses; the local or full Functionality premises remain as just stated. Neither Zorn nor Plenitude is silently inferred from compatibility.

With internal Frege finiteness of the entire proposition domain, the earlier [finite affine theorem](finite-affine-separation.md) likewise supplies the material character premise from BG(+). Plenitude is still the explicit admission premise used here for the pairwise involution construction. This note does not claim that its witnesses arise from finiteness alone.

No lattice-operation, quantifier or arbitrary-parameter preservation is added. The compatibility identities concern the named operations only. In particular these linked affine collapses do not supply an unrestricted reversible/ordinary collapse for the complete logical signature.

## 8. Sources

Plenitude is Bacon and Dorr, *Classicism*, draft of 16 May 2023, §2.3, pp. 31–33, as recorded in [the principle](../../source/topics/classicism/principles/plenitude-r.yaml) and [Plenitude normalization](plenitude-material-normalization.md), §1. The earlier truth-profile algebra is [Term closure and affine branches](term-closure-and-affine-branches.md), §§2 and 4. The admitted affine involution is [Partial reversible normalization](partial-reversible-normalization.md), §§3–5. These local proof sources have direct attribution `misc`, unpaginated.

The bare-H compatibility equivalences, endpoint tables, paired-operation and actual-expansion corollaries, and the linked reversible consequences in §§2–7 are new arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, unpaginated.

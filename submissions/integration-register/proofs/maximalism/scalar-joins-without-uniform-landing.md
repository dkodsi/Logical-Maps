# Scalar joins that cannot form an admitted predicate

OpenAI Codex, 26 October 2026. Direct source: `misc`, numbered proof sections below, unpaginated.

**There is a C model with full current logical observer separation, necessary ordinary Barcan and necessary propositional Boolean Completeness in which every scalar join of the current-number equality propositions exists, but their assignment to the argument is not an admitted predicate.** The assignment respects native identity. Its failure of admission has a concrete explanation: in a preserved Henkin target it would become the standard-number cut, contradicting induction there.

This realizes the nonuniformity isolated in [the numerical-join theorem](numeric-singleton-join-boundary.md), §5. Adding finite targets also supplies every persistently finite numerical possibility, as shown in §6. Neither construction establishes consistency of Max(C) plus BC_t or the Pi-guarded gap from the numerical-join note's §6.

## 1 A target with nonstandard numbers

Write

```math
\nu=(et)t,\qquad N=\mathrm{FiniteCardinality}_e,
\qquad \bar n=\mathrm{Suc}_e^n\mathbf 0_e
\quad(n\in\mathbb N)
```

Here the displayed index set is the external standard natural numbers. An admitted entity satisfying N need not be one of these numeral values.

Put E=C+Extensionality_all and T=E+I_e, with I_e as in the database. Expand temporarily by an auxiliary constant c of type nu and impose Nc and c≠bar n for every external standard n. Every finite subset has a full standard extensional model over an infinite individual domain: assign c a sufficiently large standard numeral. Henkin compactness therefore supplies a one-world extensional Henkin model of the whole theory. Forget c and call the pure reduct M.

The proposition domain of M is the two-element Boolean algebra. Its numberhood extension contains a member not equal to any standard numeral value, and I_e ensures that different standard numerals remain distinct. This is the usual compactness construction of a nonstandard Henkin model; no novelty is claimed for it. Alternatively the arithmetical Henkin targets in [the completeness triangulation](completeness-triangulation.md), §3, can supply such a model when their chosen arithmetic sentence is false in the standard interpretation. No arithmetical independence argument is needed for the present construction.

Apply [the complete-Henkin interpretation-cover theorem](../complete-henkin-interpretation-cover.md), §§1–7, to this single target. Call the new source o. It satisfies

```math
C+OS+\Box BF_{\rm all}+\Box BC_t+\neg\mathrm{Actuality}
\tag{1}
```

All qualifications of OS are the whole-operation qualifications of that theorem. The old target M is unchanged. Selected interpretation arrows I:o→M are onto at every type. Source loops are typed permutations, so their transports are bijective; they fix pure closed term values, including every standard numeral.

## 2 The current numbers at the source are exactly the standard numerals

In the source-domain construction, define a predicate W of type nu t as follows:

- at every source-loop row, its extension is exactly the set of source values of the standard numeral terms;
- at every old-target row, its extension is universal.

This is an admitted source entity. Its rows are empty-pinned: the self row does not depend on the loop, and the old row does not depend on the interpretation. The self row satisfies the required symmetry because every source permutation fixes the numeral values and, being bijective, preserves their complement. Its full old section lands as the universal predicate in the one-world target. These are precisely the pinning, symmetry and landing requirements of the cover construction.

Currently W contains zero and is closed under successor. The unconditional induction property of N therefore gives N⊆W at o. Conversely each standard numeral satisfies N by C. Hence

```math
\{m\in D_\nu(o):N(m)\text{ currently holds}\}
=\{\bar n_o:n\in\mathbb N\}
\tag{2}
```

There are no identifications between different standard numeral values at o: any such identity would transport to the false identity between their values in M. Equation (2) is a statement about the source's current numberhood, not about every future numerical domain.

## 3 The scalar joins and every row of their profiles

Fix any source entity m of type nu. For each external standard n, let

```math
e_{n,m}:=(\bar n=m)
```

All these propositions share a finite pin for m, since the numeral is pure. Define u_m by taking their rowwise union.

At a source loop h, the native identity e_(n,m) is true exactly when the transported objects are equal. Since transport along h is bijective and fixes the numerals, this says exactly m=bar n at the source. Thus the entire self-loop part of u_m is constant, with value

```math
u_m(h)=1\quad\Longleftrightarrow\quad
m=\bar n_o\text{ for some external standard }n
\tag{3}
```

At an old interpretation I:o→M, transport of the native identity is the native identity in the extensional target. Consequently

```math
u_m(I)=1\quad\Longleftrightarrow\quad
\rho_I(m)=\bar n_M\text{ for some external standard }n
\tag{4}
```

This profile is admitted. Its old rows depend only on the finite pin of m; its self rows are constant and symmetric. At each old interpretation its full old section is just one of the two propositions of the one-world target, so it lands. Equivalently, it is the fixed-pin join provided by §4 of the cover theorem, whose old Boolean joins here are unions of bits.

The native Boolean order at source proposition type is pointwise inclusion of the whole profiles. The rowwise union therefore is the actual least upper bound of the e_(n,m), among all admitted source propositions. By (2), these are precisely the members of the admitted scalar family

```math
S_m(p):=\exists n^\nu\,[Nn\land p=(n=m)]
```

Thus every current m has its scalar join u_m, with both its self rows and all old rows given by (3)–(4). No operation m↦u_m has been inserted into a higher domain.

## 4 Why no admitted predicate can assemble them

Suppose an admitted B of type nu t satisfies Bm=u_m for every current m, where these are native proposition identities. Fix a selected interpretation I:o→M and let B_I be the admitted target predicate obtained by transporting B.

For any a∈D_nu(M), onto transport supplies a current m with rho_I(m)=a. The current identity Bm=u_m is identity of whole source proposition profiles, so evaluation at I and (4) give

```math
B_I(a)\quad\Longleftrightarrow\quad
a=\bar n_M\text{ for some external standard }n
\tag{5}
```

Thus B_I would be an admitted target predicate whose extension is exactly the standard numeral cut. That cut contains zero and is closed under successor. Induction in M would therefore place every member of its N-extension in the cut. Section 1 supplied a nonstandard member of that extension, giving a contradiction.

Hence

```math
\neg\exists B^{\nu t}\,\forall m^\nu\,
\mathrm{LUB}_t(Bm,S_m)
\tag{6}
```

holds at o. Together with ordinary BF_nu in (1), [the numerical-join equivalence](numeric-singleton-join-boundary.md), §5, also gives failure of J_N and BF_N there. The direct argument above identifies the omitted object; it does not infer nonrepresentation only from an arithmetic contradiction.

## 5 Compatibility with native identity and scope

The external scalar assignment respects current native identity. To see the algebraic point, fix m,k and put e=(m=k). Equality substitution gives

```math
e\land(n=m)=e\land(n=k)
```

for each current number n. Finite meet distributes over each existing scalar join, so

```math
e\land u_m=e\land u_k
\tag{7}
```

Since an identity proposition is open, (7) yields e≤Box(u_m↔u_k), the native identity proposition u_m=u_k. Thus a restriction requiring only nonexpansiveness for native equality would not exclude this assignment. The full landing condition does exclude it, by §4.

The example therefore realizes scalar completeness without uniform higher-type assembly, including in the presence of full current OS and boxed ordinary BF. So far it uses one permitted target, rather than a C-complete family. It neither proves Max(C) nor settles the consistency of adding BC_t to Max(C).

## 6 Adding every positive finite individual size

Retain M and also include, for each external positive integer k, a full one-world extensional target M_k with exactly k individuals. Every target still has the complete two-element proposition algebra and only the identity arrow. The same cover therefore retains all the assertions in (1).

The predicate W from §2 still lands: give it the universal row at each of the additional targets. Its source-loop argument is unchanged, so the current source numbers remain exactly the standard numeral values. The proof of §3 also remains valid. At an interpretation into any target V, the scalar join has value 1 exactly when the image of m is a standard numeral value in V. Each such value is a legitimate target bit. Any purported uniform predicate still transports to the forbidden standard cut in the original nonstandard M, so (6) continues to hold.

Put

```math
a_n:=(\mathrm{Suc}_e n)(\lambda x^e.\top),
\qquad
\Psi:=\forall n^\nu\,[Nn\to\Diamond\Box a_n]
\tag{8}
```

For a current number bar n, the target M_(n+1) makes a_(bar n) true. Its one-world extensional interpretation also makes Box a_(bar n) true. A source arrow to that target therefore witnesses Diamond Box a_(bar n). Since these are all the current numbers, Psi holds at the source. Consequently the enlarged model satisfies

```math
C+OS+\Box BF_{\rm all}+\Box BC_t
+\Psi+\neg\mathrm{Actuality}+\neg J_N
\tag{9}
```

In particular it satisfies Pi and the precise premise Psi+BC_t of [the persistent number-set representation](persistent-number-set-codes.md), §§2–4. It therefore contains the stated Boolean representation of its admitted current number sets by Box-fixed propositions, including Box-fixed complements relative to the representation's unit, while the scalar numerical joins still have no admitted uniform assignment.

In this model the admitted current number sets are exactly the full external power set of the standard numerals. For any external X⊆N, use the self-row {bar n:n∈X} and universal old rows. The same pinning, symmetry and landing checks as for W admit this predicate. Consequently the persistent representation is a Boolean copy of external P(N), with relative unit d, whose arbitrary joins are also joins in the whole source proposition algebra. Explicitly, its value at X is the actual join of the blocks d_n=Box a_(bar n) for n∈X. For any external family X_i, an ambient upper bound of all their codes bounds every block selected by their union, and hence bounds the union's code. This proves ambient join preservation, not merely completeness inside the abstract copy. Complements give preservation of arbitrary meets in the interval below d; its empty meet is d.

This is a stronger lower model for the scalar-completeness question. It does not assert Max(C), and it supplies no claim of a possible Pi-guarded nonstandard-number gap.

Sources: the model is the linked complete-Henkin cover, §§1–7; the scalar-join/nonrepresentation equivalence is the linked numerical-join note, §5. Nonstandard-target existence uses ordinary Henkin compactness as set out in §1. The explicit source-numberhood predicate, join profiles and landing contradiction are verified in §§2–4 above. The persistent-code consequence in §6 uses the linked persistent-number-set note, §§2–4.

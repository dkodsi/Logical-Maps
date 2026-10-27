# Number sets encoded by propositions under Maximalism and completeness

26 October 2026. Ordinary mathematical research by OpenAI Codex. Direct source: `misc`, §§1–7 below, unpaginated. The coding argument and its persistence and uncountability corollaries received independent AI mathematical review; no human review or formal certification is claimed.

**Over C, pure Maximalism together with propositional Boolean Completeness supplies an atomic Boolean representation of every admitted current set of natural numbers inside the proposition algebra.** The representation preserves every existing union of such sets. Its nonzero elements remain possible, and its distinct elements remain distinct, wherever the sentence “there could be any positive finite number of individuals” holds.

Neither observer separation nor Choice is required. The atoms are atoms of this relative algebra of codes; they need not be atoms of the whole proposition algebra.

The representation also gives a Cantor diagonal argument: the proposition domain is not countable in the database's internal relational sense. This does not assert external uncountability of a Henkin model.

## 1 The number propositions

Work in the fixed relational language of C. Put

```math
\nu=(et)t,\qquad N=\mathrm{FiniteCardinality}_e,
\qquad a_n=(\mathrm{Suc}_e n)(\lambda x^e.\top),
```

and let

```math
\Pi=\forall n^\nu\,(Nn\to\Diamond a_n)
\tag{1}
```

Thus a_n says that there are exactly one more individuals than n counts. Numbers throughout are the current members of N, including any nonstandard members admitted by the model.

The established [Maximalism-to-Infinity proof](../../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/pure-possibility-implies-axiom-of-infinity-t.md), §§1–4, supplies the following facts in C:

- Nn implies Box Nn.
- Under Pi, every a_n indexed by a current number is nonzero.
- Distinct current numbers index algebraically disjoint a_n, using the boxed exclusivity lemma and successor injectivity under Pi.
- Diamond Pi implies Pi, and pure Max(C) implies Pi.

No forward persistence of Pi is assumed. The new theorem therefore has the slightly weaker premises C + Pi + BC_t; Max(C) supplies Pi.

Let B be the current Boolean algebra of propositions. All joins below mean least upper bounds in its algebraic order, not material disjunctions evaluated only at the current truth point.

## 2 Coding the admitted number sets

For an admitted X of type nu t, form the admitted property of propositions

```math
S_X(p):=\exists n^\nu\,(Nn\land Xn\land p=a_n)
\tag{2}
```

BC_t gives a unique proposition b_X that is the current least upper bound of S_X. Put b=b_Top, where Top here denotes the constantly true numeric predicate. Equivalently,

```math
b_X=\bigvee\{a_n:Nn\text{ and }Xn\text{ currently hold}\},
\qquad b=\bigvee_{n\in N}a_n
\tag{3}
```

These values are specified by the admitted functional relation LUB_t(c,S_X). The notation X↦b_X does not assert that this relation is represented by an admitted operation.

For every current number n,

```math
Xn\quad\Longleftrightarrow\quad a_n\le b_X
\tag{4}
```

If Xn holds, this is the upper-bound property. If Xn fails, every selected a_m is disjoint from a_n: any selected m is a current number different from n. Consequently not a_n is an upper bound of S_X, so b_X≤not a_n. Since a_n is nonzero, a_n≤b_X is then impossible.

Let A be the Boolean algebra of current subsets of N that are extensions of admitted numeric predicates, identifying predicates currently coextensive on N. Equation (4) makes the code assignment well-defined and injective on A. It also shows that an unselected block a_n is disjoint from the code.

## 3 The exact algebra of codes

The image is the following definable subset of B:

```math
D=\{c\le b:\forall n\in N\,
       (a_n\le c\ \lor\ a_n\land c=\bot)\}
\tag{5}
```

Every code satisfies (5), by §2. Conversely take c satisfying (5), and use the admitted predicate

```math
X_c(n):=(a_n\le c)
\tag{6}
```

Finite meet distributes over every existing join in a Boolean algebra. For clarity, if s=join S and v bounds all c∧x with x∈S, then not c∨v bounds S, whence c∧s≤v. Apply this to (3):

```math
c=c\land b=\bigvee_{n\in N}(c\land a_n)
```

The condition defining D makes each summand either a_n or Bottom. Thus c=b_(X_c). This proves the image characterization and gives its inverse.

The code assignment is a Boolean isomorphism A→D, with relative unit b:

```math
b_{X\land Y}=b_X\land b_Y,\qquad
b_{\neg X}=b\land\neg b_X,\qquad
b_{\bot}=\bot,\qquad b_{\top}=b
\tag{7}
```

For example, intersecting either side of the complement equation with a_n gives a_n exactly when Xn fails, and zero otherwise. Both sides lie below b, which is the join of the a_n; distribution therefore gives equality. The meet equation follows in the same way.

D is atomic, with atoms exactly the a_n. Each singleton predicate n'=n is admitted, so a_n lies in D. A member of D below a_n is either zero or a_n, by (5). Conversely, a nonzero c∈D contains some a_n: otherwise c∧a_n=0 for every n, and distribution over b would give c=0.

## 4 Preservation of all existing unions

The isomorphism A→D preserves every join that exists in A, even for an externally specified family of admitted extensions.

First, such a join must be the actual set union. Suppose Y is a least upper bound in A of a family of extensions, and n lies in Y but in none of them. The extension Y minus the singleton n is admitted, remains an upper bound, and is strictly smaller. This contradicts leastness. Hence Y is exactly the union.

Each selected code b_X lies below b_Y. If u∈B is any upper bound of all those codes, every n∈Y belongs to one selected X, so a_n≤b_X≤u. Definition (3) then gives b_Y≤u. Thus b_Y is their least upper bound in the whole B, not merely in D. Complements give preservation of all existing meets, with meets read in the interval B restricted to b.

In particular every admitted family of codes has its B-join in D. One direct proof avoids any choice of predicate representatives. Apply BC_t to the given family, obtaining c≤b. Fix a current number n. If some selected code contains a_n, then a_n≤c. Otherwise every selected code is disjoint from a_n, so not a_n is an upper bound and c≤not a_n. Thus c satisfies (5).

## 5 Conditional persistence of the codes

For every current c∈D,

```math
c\ne\bot\quad\Longrightarrow\quad
\Box(\Pi\to\Diamond c)
\tag{8}
```

Choose a current number n with 0<a_n≤c, as §3 permits. Numberhood persists. The inequality a_n≤c is an identity, namely a_n∧c=a_n, so it persists by Necessity of Identity. At any evaluation where Pi holds, the transported n is a number and a_n is nonzero. The persistent inequality then makes c nonzero there as well. This proves (8), equivalently by necessitating the unconditional C implication from Nn, a_n≤c and Pi to Diamond c and applying K to the two persistent premises.

Apply (8) to the Boolean symmetric difference of two codes. It belongs to D and is nonzero exactly when they are distinct. Consequently,

```math
c,d\in D,\ c\ne d\quad\Longrightarrow\quad
\Box(\Pi\to c\ne d)
\tag{9}
```

These statements concern the current codes transported to other evaluations. They neither assert that Pi persists nor identify every future code with a transported current code.

Each code also supplies a persistent representative of the set it encodes. For a current numeric predicate X, let c=b_X and put

```math
Y_c(n):=(a_n\le c)
\tag{10}
```

Then Y_c agrees with X on current N. The predicate Y_c is an identity predicate, so C proves its positive persistence, including the universally boxed form

```math
\Box\forall n\,(Y_c(n)\to\Box Y_c(n))
\tag{11}
```

If a current number n fails X, then a_n is disjoint from c. That identity persists. Wherever Pi holds, a_n remains nonzero, so it cannot then lie below c. Thus negative membership is conditionally persistent:

```math
Nn\land\neg Xn\quad\Longrightarrow\quad
\Box(\Pi\to\neg Y_c(n))
\tag{12}
```

The decoder c↦Y_c is an admitted operation, given by lambda abstraction. Choosing b_X uniformly as an admitted operation is still not asserted.

There is also a canonical admitted term that fixes every code:

```math
c=\exists n^\nu\,[Nn\land(a_n\le c)\land a_n]
\qquad(c\in D)
\tag{13}
```

The displayed existential is algebraically below c because its matrix implies c by a theorem of C. Conversely, for each current n with a_n≤c, both Nn and this inequality are necessary. Existential introduction therefore puts a_n below the displayed existential. The characterization c=b_(Y_c) and leastness of that join give the opposite inequality. No BF is used. Equation (13) says that this term fixes D; it does not say that its value at every proposition belongs to D.

## 6 Internal uncountability

The algebra of codes is not countable in the database's native sense:

```math
\neg\mathrm{Ctbl}_{e,t}(D),
\qquad
\neg\mathrm{Ctbl}_{e,t}(\lambda p^t.\top)
\tag{14}
```

Here numberhood is N=FiniteCardinality_e. The native definition permits an admitted relation R(c,n) with nonempty number fibres for every selected c and disjoint fibres for distinct selected c. It does not require choosing a single number in each fibre.

Suppose such a relation counts D. Form the admitted numeric predicate

```math
X(n):=\forall c^t\,[Dc\land R(c,n)\to\neg(a_n\le c)]
\tag{15}
```

and let d=b_X. Since d lies in D, choose one current n∈N with R(d,n). Every c∈D related to this n is identical to d, by disjointness of the number fibres. Consequently

```math
Xn\ \longleftrightarrow\ \neg(a_n\le d)
```

But code recovery (4) gives Xn if and only if a_n≤d, a contradiction. This proves the first assertion of (14). A relation counting all propositions would restrict to one counting D, giving the second.

In particular no admitted operation from N onto all propositions exists: its inverse graph would be a relation of the forbidden kind. The same holds for an enumeration of D. The result is internal; it is consistent with the external domain of a Henkin model being countable. No Choice or observer principle enters the diagonal argument.

## 7 Consequence for the consistency question

Any model of C + Max(C) + OS + BC_t, including the proposed strengthening by all-type Zorn, must contain this atomic algebra of number-set codes. It must preserve all existing numeric unions through that representation, satisfy (8)–(13), and have an internally uncountable proposition domain as in (14). These are positive structural restrictions on a prospective model, already forced before adding OS or Zorn.

The representation is an admitted functional relation and a current Boolean-algebra isomorphism on extensions. It is not yet an admitted operation or a full typed interpretation. In particular it does not supply Goodsell's higher-type least upper bound of the numeric singleton predicates. The unrestricted Maximalist consistency question remains open.

Sources: the finite-cardinality, exclusivity and Pi lemmas are the linked Maximalism-to-Infinity proof, §§1–4, attributed there to Cian Dorr's argument of 20 September 2026 with the displayed lemmas and verification. BC_t is the database principle `boolean-completeness-t`, Bacon and Dorr, *Classicism*, draft of 16 May 2023, §2.2, pp. 23–26. The native countability definition is in [background.md](../../../classicism-results-2026-10-24-v2/source/topics/classicism/background.md), the Countable Boolean Completeness discussion, following Goodsell, *Arithmetic is Necessary*, §3.1, eq. (10), p. 8. The coding, exact image, existing-join preservation, persistence and diagonal deductions are the new argument above (`misc`). Independent AI review checked the admitted family (2), both directions of (4)–(5), singleton deletion, the existing-join argument and the modal scope of (8)–(9).

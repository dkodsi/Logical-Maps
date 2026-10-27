# Logical observers and numberhood

OpenAI Codex, 26 October 2026. Direct source: `misc`, numbered proof sections below, unpaginated.

**Maximalism and the Barcan formula at the numerical type imply that something which is not currently a number could be a number while every positive finite individual size remains possible.** Full logical observer separation then supplies, for this same object and every finite qualification list, an observer accepting both claims together. Adding propositional Boolean Completeness gives a complementary description: every observer accepting the unit of the number-set code algebra reads all its codes through one observed number. Every current number supplies a principal reader; these results do not establish the existence of a nonprincipal reader of the code algebra.

Work throughout over C in its fixed relational language. Max means pure Max(C), with C unchanged as its reference theory. Put

```math
\nu=(et)t,\qquad N=\mathrm{FiniteCardinality}_e,
\qquad a_n=(\mathrm{Suc}_e n)(\lambda x^e.\top).
```

Use the whole-operation qualification $`\mathrm{Good}_\Delta(E)`$ and full typed OS from [the observer definitions](../../../classicism-results-2026-10-24-v2/proofs/logical-observer-hierarchy.md), §1. Each qualification list $`\Delta`$ is finite. Over C a qualified observer is a unital Boolean endomorphism of the current proposition algebra. It need not fix identity propositions, numberhood, or other pure propositions. Full OS supplies current BF at every relational type; no boxed OS or boxed BF is assumed here.

## 1 Maximalism forces a change in observed numberhood

Put

```math
\Pi:=\forall n^\nu\,(Nn\to\Diamond a_n),
```

the sentence that every positive finite individual size is possible. Max(C) implies Pi. Pi is backward persistent, but no forward persistence is assumed. Write pointwise preservation of nonnumberhood conditional on Pi as

```math
\mathrm{NN}_\Pi:=\forall n^\nu\,(\neg Nn\to\Box(\Pi\to\neg Nn)).
\tag{1}
```

**Internal bridge in C.** The conjunction of $`\mathrm{NN}_\Pi`$ and current $`\mathrm{BF}_\nu`$ implies the Pi-relative numerical Barcan principle

```math
\forall X^{\nu t}\,
 [\forall n(Nn\to\Box(\Pi\to Xn))
   \to\Box(\Pi\to\forall n(Nn\to Xn))].
\tag{2}
```

Let X satisfy the antecedent of (2). For each n, if Nn is true, $`\Box(\Pi\to Xn)`$ gives $`\Box(\Pi\to(Nn\to Xn))`$. If Nn is false, $`\mathrm{NN}_\Pi`$ gives $`\Box(\Pi\to\neg Nn)`$, with the same consequence. Hence

```math
\forall n\,\Box(\Pi\to(Nn\to Xn)).
```

BF and moving the n-independent Pi through the universal quantifier give (2). This is an implication of C with the two displayed premises; no metatheoretic Maximalism argument is needed for the bridge.

**Relative arithmetic determinacy.** The [recorded Maximalism-to-Infinity proof](../../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/pure-possibility-implies-axiom-of-infinity-t.md), §4, Lemma 6, proves that Pi implies successor injectivity on current numbers. Zero is never a successor, since they differ at the empty property. Thus C proves $`\Pi\to I_e^*`$, and hence $`\Pi\to I_e`$, with the arithmetic conditions as defined in the [background](../../../classicism-results-2026-10-24-v2/source/topics/classicism/background.md).

Use the [proof of Goodsell's Necessity of Arithmetic theorem](../../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/countable-boolean-completeness-implies-necessity-of-arithmetic.md), Lemmas 3–7 and Theorem 9. Those lemmas hold in C. For current numeric parameters, they give atomic determinacy conditional on I; the necessitated C theorem $`\Pi\to I_e`$ weakens each conditional box to Pi. This covers equality, Sum and Prod. Numberhood itself is necessarily true for a current number. Boolean steps use K.

For the inductive step with $`\forall m\in N\,A(\vec n,m)`$, the induction hypothesis gives, for each current m, either $`\Box(\Pi\to A)`$ or $`\Box(\Pi\to\neg A)`$. If every m takes the first disjunct, apply (2) to $`\lambda m.A(\vec n,m)`$, obtaining the positive quantified box. Otherwise choose a current m taking the second disjunct. Numberhood persistence gives $`\Box Nm`$, and K yields the negative quantified box. Thus (2) handles the entire numerical domain at the possible evaluation; it is not assumed to consist only of current numbers. This proves, for every closed arithmetical sentence A,

```math
\Box(\Pi\to A)\ \lor\ \Box(\Pi\to\neg A).
```

This contradicts Max(C), by the following Pi-relative version of the recorded [arithmetic incompatibility argument](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/possibility-and-necessity-of-arithmetic-incompatible.yaml). C + Pi is consistent: the [coalesced sum over all finite individual domains](../../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/coalesced-all-finite-individual-domains.md) satisfies Pi at its root. C + Pi is recursively enumerable, and $`\Pi\to I_e`$ together with Goodsell's Lemma 1 gives the interpreted Peano axioms. Its arithmetical consequences therefore form a consistent recursively enumerable extension of PA. Gödel–Rosser supplies an arithmetical A for which both $`\Pi\land A`$ and $`\Pi\land\neg A`$ are C-consistent pure sentences. Max(C) makes both possible, contrary to the displayed disjunction. The reference theory in both consistency conditions remains C.

Consequently Max(C) together with BF refutes $`\mathrm{NN}_\Pi`$, proving the observer-independent theorem

```math
\mathrm C+\mathrm{Max}(\mathrm C)+\mathrm{BF}_\nu
\quad\Longrightarrow\quad
\exists n\,(\neg Nn\land\Diamond(\Pi\land Nn)).
\tag{3}
```

In particular, a current nonnumber could be a number. The stronger claim says that this can happen while every positive finite individual size remains possible. It cannot be explained solely by collapse at evaluations where Pi fails.

Full OS supplies $`\mathrm{BF}_\nu`$. Fix an n given by (3). Since $`\Pi\land Nn\ne\bot`$, for each fixed finite $`\Delta`$, propositional separation supplies a qualified E accepting that conjunction. Its Boolean laws give both $`E\Pi`$ and $`E(Nn)`$. Thus

```math
\exists E^{tt}\exists n^\nu\,
 [\mathrm{Good}_\Delta(E)\land E\Pi\land E(Nn)\land\neg Nn].
\tag{4}
```

One fixed n can serve for all finite external lists; E can vary with the list. Neither BC_t nor Choice enters this conclusion.

The same current nonnumber can also possibly be instantiated as a finite cardinality of a co-singleton individual domain:

```math
\Diamond(Nn\land a_n).
\tag{4a}
```

Indeed C proves $`\Pi\land Nn\to\Diamond(Nn\land a_n)`$: Pi gives $`\Diamond a_n`$, and numberhood persistence gives $`\Box Nn`$. Apply possibility to (3) and then use $`\Diamond\Diamond P\to\Diamond P`$, the dual of 4. Consequently, for every finite qualification list, OS supplies a qualified observer F accepting both $`F(Nn)`$ and $`F(a_n)`$. The observer in (4) accepts Pi and Nn; this possibly different observer accepts Nn and a_n. The proof does not combine all three observations in one observer.

In particular, Max(C) plus full OS refutes numberhood reflection at every such list:

```math
\forall E^{tt}\forall n^\nu\,
 [\mathrm{Good}_\Delta(E)\land E(Nn)\to Nn].
\tag{5}
```

The intermediate structure is exact. Under (5), if a current n is not a number, all qualified E reject Nn and Bottom, so the propositional OS instance for this same list gives $`Nn=\bot`$. If n is a number, the C persistence theorem gives $`Nn=\top`$. Therefore

```math
\forall n\,(Nn=\top\ \lor\ Nn=\bot).
\tag{6}
```

Conversely, (6) implies (5) because observers fix Bottom. Thus, with this propositional separation instance, reflection is exactly endpoint-valued numberhood. That condition implies $`\mathrm{NN}_\Pi`$, which with BF yields (2) and the arithmetic contradiction above.

## 2 A common-instance lemma in C

The profile theorem below uses the following unconditional C theorem:

```math
Nn\land Nm\land a_n\land a_m\quad\longrightarrow\quad n=m.
\tag{7}
```

Here no possibility premise is needed. By the exclusivity lemma for finite cardinalities, either $`n=m`$, or
$`\Box\forall X\,\neg(nX\land mX)`$.
Assume the latter. Unfolding $`a_n`$ gives an individual y with
$`n(\top_e-y)`$; unfolding $`a_m`$ gives z with
$`m(\top_e-z)`$. If y=z, the displayed property is a common instance of n and m. If y differs from z, the finite-cardinality swap lemma, applied to m, changes the latter instance into $`m(\top_e-y)`$, again giving a common instance. Either case contradicts exclusivity and T.

The swap and boxed exclusivity lemmas are Lemmas 3–4 of [the Maximalism-to-Infinity proof](../../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/pure-possibility-implies-axiom-of-infinity-t.md), §1; the same common-instance step appears explicitly in its §4. That source also proves numberhood persistence and the modal bookkeeping used above.

Define the admitted operation

```math
T(p):=\exists m^\nu\,[Nm\land(a_m\le p)\land a_m],
\qquad a_m\le p\;:\!\iff\;a_m\land p=a_m.
\tag{8}
```

From (7), ordinary existential reasoning proves in C

```math
Nn\land a_n\quad\longrightarrow\quad
 [T(p)\leftrightarrow(a_n\le p)].
\tag{9}
```

For the forward direction a witness m in (8) equals n by (7). For the reverse direction n itself is a witness. Since (9) is a C theorem with free n,p, it has proposition value Top at every substitution. Applying a Boolean observer therefore preserves its truth; this uses endpoint fixing, not identity fixing.

## 3 One observed number reads an observer's whole code profile

Assume C + Max(C) + BC_t. The [number-set coding theorem](../dependencies/number-set-codes-in-complete-maximalism.md), §§1–5, supplies the following current objects and identities. Let

```math
b=\bigvee_{n\in N}a_n,
\qquad
D=\{c\le b:\forall n\in N\,
       (a_n\le c\ \lor\ a_n\land c=\bot)\}.
\tag{10}
```

The join is in the current algebraic order. Every a_n indexed by a current number is nonzero. D is the atomic Boolean algebra of number-set codes, with relative unit b and atoms precisely these a_n. Crucially, its members obey

```math
T(c)=c\quad(c\in D),
\qquad T(b)=b.
\tag{11}
```

These facts need only C + Pi + BC_t, where Pi is the sentence that every positive finite individual cardinality is possible. Max(C) supplies Pi. We use them only at the current evaluation.

Under the full target C + Max(C) + full OS + BC_t, b is currently false and nonzero. This uses existing map implications: [Max gives Possible Infinity at e](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/possibility-schema-r-implies-possible-infinity-e.yaml), and [Possible Infinity at e together with BF gives the Axiom of Infinity at e](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/possible-infinity-e-and-bf-imply-axiom-of-infinity-e.yaml). Full OS supplies BF. A true conjunct $`Nn\land a_n`$ would make the finite cardinality $`\mathrm{Suc}_e n`$ apply to all individuals, contrary to actual Infinity at e. Hence T(b), and therefore b, is false. Pi makes $`a_{\mathbf 0}`$ nonzero, and $`a_{\mathbf 0}\le b`$, so b is nonzero. Every current code c is consequently false because $`c\le b`$, although every nonzero code is possible. The conclusion that b is false uses OS through BF; it is not asserted from Max(C) + BC_t alone.

**Profile theorem.** Let $`\nu\in\Delta`$, let $`\mathrm{Good}_\Delta(E)`$, and suppose Eb is true. There is one object n such that

```math
E(Nn)\land E(a_n)
\tag{12}
```

is true and, simultaneously for every current $`c\in D`$,

```math
Ec\quad\longleftrightarrow\quad E(a_n\le c).
\tag{13}
```

Indeed, apply E to $`b=T(b)`$. Its whole existential law at $`\nu`$ and its Boolean laws give

```math
Eb\leftrightarrow
\exists n\,[E(Nn)\land E(a_n\le b)\land E(a_n)].
\tag{14}
```

Choose one witness n. For an arbitrary current code c, apply E to the C theorem (9) with p=c. By (12), Boolean preservation gives
$`E(T(c))\leftrightarrow E(a_n\le c)`$.
The actual identity $`T(c)=c`$ permits substitution of c for T(c) inside E, proving (13). The same n works for every c; the existential witness in (14) was chosen only once.

The expression $`E(a_n\le c)`$ means E applied to the proposition $`a_n\land c=a_n`$. It has not been replaced by a statement of native identity between the outputs of E. No commutation with identity, no fixation of N or Pi, and no persistence of Pi is used.

## 4 Principal readers and the remaining distinction

If the witness n in the profile theorem is already a current number, E's truth profile on D is the principal reader at that number:

```math
Ec\quad\longleftrightarrow\quad a_n\le c
\qquad(c\in D).
\tag{15}
```

If $`a_n\le c`$, Boolean preservation carries this algebraic inequality to $`E(a_n)\le E(c)`$; (12) then makes Ec true. Otherwise the defining condition on D gives $`a_n\land c=\bot`$, so $`E(a_n)\land E(c)=\bot`$; (12) makes Ec false. These are consequences of E preserving Boolean operations on proposition values, not of E fixing the propositions expressing inequalities.

Conversely, full OS supplies every such principal reader. Fix a current number n and any finite qualification list $`\Delta`$. Since $`a_n\ne\bot`$, propositional separation supplies a qualified E for which $`E(a_n)`$ is true. The inequality $`a_n\le b`$ gives Eb, and the preceding argument proves (15). This existence assertion holds separately for each n and $`\Delta`$; no admitted uniform selection operation is claimed. Qualification at $`\nu`$ is required for the representation theorem in §3, but not for this direct principal-reader argument.

Thus a nonprincipal profile on D, if one exists and accepts b, must have a witness in §3 that is not a current number. The converse is not proved: a witness that is not currently a number can still induce a principal profile. Nor does §1 force a nonprincipal profile. It supplies both an observer accepting Pi and Nn and a possibly different observer accepting Nn and a_n, but neither is shown to accept b. These theorems therefore impose structural requirements on C + Max(C) + full OS + BC_t without deciding its consistency.

Sources: observer qualification and OS-to-BF are the linked observer hierarchy, §§1 and 3, and its linked endpoint-reduction proof. Numberhood persistence, swap, and exclusivity are the linked Maximalism-to-Infinity proof, §§1 and 4, based on Cian Dorr's argument of 20 September 2026 with the displayed lemmas. The arithmetic bridge is Goodsell, *Arithmetic is Necessary*, draft of 5 June 2024, Lemma 8 and Theorem 9 as transcribed in the linked write-up; the Max incompatibility is §6, Theorem 11 and n. 14, pp. 24–26, with its application to C recorded in the linked result. The code identities are the linked current research note, §§1–5. The deductions in §§1–4 here are `misc`, unpaginated, ordinary mathematical proofs.

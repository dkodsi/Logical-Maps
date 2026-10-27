# Triangulating Maximalism and propositional completeness

OpenAI Codex, 26 October 2026. Direct source: `misc`, numbered proof sections below, unpaginated.

**Neither C + Max(C) + BC_t nor C + Max(C) + BF_all + BC_t has an established consistency or inconsistency verdict in the checked work.** The full-OS strengthening also remains unresolved. The useful bounds now isolate both a forbidden higher-type join and substantial consistent fragments of Max(C) compatible with scalar completeness.

## 1 The upper boundary is one countable higher-type join

Let nu=(et)t, N=FiniteCardinality_e and h_n=lambda m.(n=m). Let J_N assert that the admitted family of h_n for current Nn has a least upper bound at type nu t.

The [single-join theorem](numeric-singleton-join-boundary.md), §§1–4, proves over C:

```math
J_N\ \longleftrightarrow\ \mathrm{LUB}_{\nu t}(N,\{h_n:Nn\})
\ \longleftrightarrow\ \mathrm{BF}_N.
```

Here BF_N is Barcan restricted to numberhood, not the ordinary BF instance at nu. Goodsell's arithmetic argument needs precisely this restricted principle. Consequently Max(C) rules out J_N. In particular:

```math
C+\mathrm{Max}(C)+BC_{((et)t)t}\quad\text{is inconsistent}.
```

This is a genuine strengthening of the scalar target: BC at nu t implies BC_t by taking joins of constant predicates and evaluating at 0. The stronger conclusion is that Max forbids one fixed countable join, without needing all of BC at that type. The join-to-arithmetic argument is Goodsell's Lemma 8 and Theorem 9; the exact join characterization is the refinement proved in the linked note.

Other checked upper bounds are Max(C) plus [boxed BC_t](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/maximalist-distinctness-incompatible-with-necessary-boolean-completeness-t.yaml), Max(C) plus [boxed BF_all](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/maximalist-distinctness-incompatible-with-necessary-barcan-r.yaml), and Max(C) + BF_all + Atomicity_t. For the last, [Atomicity_t plus BF](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/atomicity-t-and-bf-imply-necessary-actuality.yaml) yields necessary Actuality, which [conflicts with Max](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/maximalist-distinctness-incompatible-with-necessary-actuality.yaml). None supplies a verdict for current BC_t alone.

## 2 Consistency from both sides

Keeping full Max(C) and dropping BC_t, the [unrestricted interpretation roots](../unrestricted-roots-fail-propositional-completeness.md), §1, give ZFC models of

```math
C+\mathrm{Max}(C)+OS+BF_{\rm all}+RC_{\rm all}+Zorn_{\rm all}+\neg BC_t,
```

with either Actuality or its negation. This is an established lower bound, not a new construction here.

Keeping BC_t and restricting the possibilities required by Max(C), the [mixed cover](../mixed-finite-pin-henkin-completeness-cover.md), §6, gives a single ZFC model of

```math
C+OS+BF_{\rm all}+BC_t+\neg\mathrm{Actuality}
```

in which every pure sentence consistent with C + Extensionality_all is possible. The same source can additionally satisfy

```math
\Diamond(\Box ND_t\land\neg BC_t),\qquad\Diamond\neg BF_e,
\qquad\Diamond\neg BF_t.
```

For the first extra possibility use the finite-support permutation component already specified in the mixed-cover proof. For the other two use the singleton object of the [two-object all-maps component](../../../classicism-results-2026-10-24-v2/source/topics/classicism/models/finite-support-two-object-all-maps.yaml), whose recorded arguments verify both BF failures there. The cover preserves and reaches those objects. Thus current completeness and Barcan need not persist in this lower model.

Every displayed possibility is an instance demanded by Max(C). Extensionality is a restriction on the selected witness sentences, not an assumption at the new source. The reference theory of the unresolved Max(C) target remains C. The claim is a consistent restricted collection of its demands, not full Max(C).

## 3 A finite arithmetic fragment distinguishes scalar and higher completeness

There is an arithmetical sentence A for which both

```math
\Diamond(I_e\land A),\qquad\Diamond(I_e\land\neg A)
\tag{1}
```

are compatible with BC_t, BF_all and full OS, but jointly incompatible with J_N.

To see this, put E=C+Extensionality_all. E+I_e is recursively enumerable, interprets PA and is consistent, as witnessed by the full extensional hierarchy over an infinite individual domain. Gödel–Rosser applied to its arithmetical consequences gives A with both E+I_e+A and E+I_e+not A consistent. Extensional Henkin completeness supplies one-world witnesses. These are two of the permitted targets in the [complete-Henkin cover](../complete-henkin-interpretation-cover.md), §§1 and 7.

With just these two targets, that cover gives even

```math
C+OS+\Box BF_{\rm all}+\Box BC_t+\neg\mathrm{Actuality}
+\Diamond(I_e\land A)+\Diamond(I_e\land\neg A).
\tag{2}
```

By contrast J_N gives Box(I_e implies A) or Box(I_e implies not A), contradicting (1). Thus the model in (2) has neither J_N nor BF_N. This is an application of the existing cover theorem and the new single-join characterization, not a new cover construction. The mixed model in §2 can retain the same arithmetic witnesses; its future failures of BC and BF are not combined with the boxed positive assertions in (2).

This gives an actual nonimplication: even necessary scalar completeness, necessary ordinary Barcan and current full OS do not supply the forbidden numerical join. Ordinary BF cannot silently be replaced by BF_N, because numberhood is a contingent restriction on its domain.

## 4 The exact assembly requirement

The [single-join note](numeric-singleton-join-boundary.md), §5, further isolates the relevant higher-type requirement. For each current m, BC_t supplies the unique scalar join of the propositions n=m indexed by current numbers n. Over BF_nu, these scalar joins can be represented by one admitted predicate B(m) if and only if J_N holds.

Therefore any model of Max(C)+BC_t+BF_nu must supply each scalar join separately while omitting an operation representing this particular total functional assignment. This is a necessary structural condition on a prospective model, not a contradiction in the target. It identifies a precise distinction between the availability of scalar suprema and their assembly into an admitted higher-type object.

The [explicit scalar-join model](scalar-joins-without-uniform-landing.md), §§1–6, now realizes this nonuniformity directly. It satisfies C + OS + boxed BF_all + boxed BC_t + not Actuality, with every current positive finite size possibly necessary. Its current numbers are exactly the standard numerals. Each scalar join exists, but a uniform predicate would land as the standard-number cut in a preserved nonstandard Henkin target, contradicting induction there. The assignment respects native identity. The model also has a persistent Boolean copy of external P(N) preserving arbitrary ambient joins. This demonstrates that the required failure of uniform assembly is compatible with these strong lower premises; it does not assert full Max(C).

There is also a stronger positive consequence of BC_t here. The [new numerical-gap theorem](numeric-singleton-join-boundary.md), §6, shows that Max(C)+BC_t+BF_nu forces a current nonnumber m and one nonzero condition r such that r entails Pi and Nm, while r entails m differs from n for every current number n. Pi says every positive finite individual size is possible. Thus at that possible evaluation, m is a number distinct from every transported current number. With OS, a single qualified observer accepts Pi and Nm and rejects each current-number identity m=n. The precise formula keeps all current-number guards outside the boxes. This sharpens the earlier Max+BF result, which did not exclude coalescence with current numbers.

## 5 Current verdicts

| Package over C | Checked verdict |
| --- | --- |
| Max(C) + BC_t | Unresolved |
| Max(C) + BF_all + BC_t | Unresolved |
| Max(C) + full OS + BC_t | Unresolved |
| Max(C) + the single numerical join J_N | Inconsistent |
| Max(C) + BC at ((et)t)t | Inconsistent |
| Full Max(C) + OS + BF_all + RC_all + Zorn_all, without BC_t | Consistent; the supplied models fail BC_t |
| BC_t + OS + BF_all + the mixed collection of Max(C) instances in §2 | Consistent |
| Two opposed arithmetic possibilities + OS + boxed BF_all + boxed BC_t | Consistent; J_N and BF_N fail |
| Every current positive finite size possibly necessary + OS + boxed BF_all + boxed BC_t | Consistent with scalar joins but no uniform assembly, failure of J_N, and a persistent external P(N) copy |

The scalar target is still open. The checked bounds show that its resolution cannot come merely from replacing scalar completeness with numerical higher-type completeness or from treating restricted numerical Barcan as ordinary Barcan.

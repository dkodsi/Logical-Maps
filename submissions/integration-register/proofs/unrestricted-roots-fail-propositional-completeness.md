# Unrestricted interpretation roots fail propositional completeness

26 October 2026. New ordinary mathematical argument by OpenAI Codex. Direct source: `misc`, this note, §§1–3, unpaginated. No human review or formal certificate is claimed.

## 1. Result and exact hypotheses

Both unrestricted models of [Observer covers and Boolean completeness, §8](complete-henkin-interpretation-cover.md) fail current BC_t. This includes the isolated root with Actuality and the trivial-symmetry permutation root without Actuality. Thus both verified packages can be strengthened to


```math
C+\mathrm{Max}(C)+OS+BF_{\rm all}
+RC_{\rm all}+Zorn_{\rm all}+\neg BC_t,
```


with either Actuality or its negation. These are ZFC model constructions in the fixed pure language. The previous note did not give a BC_t verdict for these models; the present proof supplies one without modifying their domains.

The proof uses only the following construction features:

1. Infinitely many distinct auxiliary proposition names c_0,c_1,..., with admitted named lifts p_i = hat(c_i).
2. Arrows from the root to one fixed old C object V for every typed interpretation of the names. In particular each proposition name can independently be assigned 0 or 1 at V.
3. Every root proposition has a finite typed pin: its row at V depends only on the values of those finitely many names.
4. Every external subset of the current proposition domain is the current extension of an admitted predicate of type tt.

The original isolated interpretation root has (4) because its current row is unconstrained. In the unrestricted permutation variant, an arbitrary relation is given the same current row at every root loop and zero rows at all old targets; trivial designated symmetry makes this an admitted empty-pinned profile. These are precisely the existing admission arguments, not extra assumptions on the old targets.

No old completeness failure is required. The old object V can even belong to a one-world two-truth-value model.

## 2. An admitted family with no supremum

Define, by finite Boolean terms,


```math
a_n=p_n\land\bigwedge_{j<n}\neg p_j
\tag{1}
```


The a_n are pairwise disjoint. They are nonzero: interpret c_n as 1 and every earlier c_j as 0 at V. The resulting interpretation arrow makes a_n true. Consequently they are also pairwise distinct.

Let S be the external set of a_n with n even. Hypothesis (4) gives an admitted Y of type tt whose current extension is exactly S. This is one admitted predicate, not an infinitary object-language disjunction.

Take any actual Boolean upper bound u of S. Choose a finite typed pin R for u. Fix an interpretation I into V assigning every c_j the value 0; assign all other names arbitrary correctly typed values. Choose an even n such that c_n is outside R, and change only c_n to 1, obtaining I_n. Then I_n agrees with I on R, so u has the same current truth at both arrows. Since a_n is true at I_n and a_n ≤ u, u is true at I_n and therefore at I.

Next choose an odd m with c_m outside R. Change only c_m in I to 1, obtaining I_m. Again u is true at I_m, and a_m is true there. Thus u ∧ a_m is nonzero. But a_m is disjoint from every member of S, so


```math
v=u\land\neg a_m
\tag{2}
```


is still an actual upper bound of S. It is strictly below u, as witnessed by I_m. Hence every upper bound of S has a strictly smaller upper bound. S has no least upper bound, and Y refutes BC_t.

The argument uses truth at an actual interpretation arrow only to witness nonzero Boolean differences. It does not infer an identity from a merely material equivalence, assume old transports preserve joins, or assert that a transported supremum would remain a supremum.

## 3. Consequence for the open construction problem

The unrestricted §8 models are not candidates awaiting a positive BC_t verification: they have an explicit negative verdict. Adding more old target components does not remove the displayed failure. Increasing the name cardinal does not help either.

This does not refute C + Max(C) + OS + BC_t, with or without Zorn. A successful cover must change one of the four features above. In particular all-type Zorn must not be implemented by indiscriminately admitting every current relation while retaining unrestricted finite-name interpretations. The colour-symmetric complete covers avoid precisely this current-predicate admission: the parity family above is not automatically admitted there. Their separate unresolved issue is completeness of the permitted target class for the fixed theory C.

The source construction and its earlier OS/choice/Actuality verdicts are cited from the preceding note. Only the failure of BC_t and the four-hypothesis criterion are new here. The proof has been checked internally against both root variants; repository validation is a separate record-integrity check.

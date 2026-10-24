# Atomicity supplies logical observers

Original mathematical argument, direct source misc; unpaginated.

1. PATCHED PRINCIPAL OBSERVERS

Work over C. For any a:t put c:=DIAMOND a, P_a(p):=BOX(a->p), and define

  O_a(p):=(c AND P_a(p)) OR (NOT c AND p).

All these are admitted terms. If a is a current propositional atom, O_a
preserves both Boolean constants, negation, meet and join.
No necessary atomhood or necessary nonbottomness of a is assumed.

Proof. P_a preserves meet and top by the unconditional C modal
and Boolean identities. Since O_a combines P_a and the identity along the
complementary Boolean parts c,NOT c, distribution gives

  O_a(p AND q)=O_a(p) AND O_a(q),
  O_a(top)=top.

Moreover P_a(bottom)=BOX(NOT a)=NOT c, so O_a(bottom)=bottom.
For negation, a current atom lies below p or below NOT p, for each current p.
In the first case, Boolean algebra gives a->p=top and a->NOT p=NOT a.
Consequently P_a(p)=top and P_a(NOT p)=NOT c. Thus

  O_a(p)=c OR p,
  O_a(NOT p)=NOT c AND NOT p=NOT O_a(p).

In the second case interchange p and NOT p, obtaining the same result.
This is an equality calculation from the assumed order equations;
no conditional conditional equivalence is lifted to an identity. De Morgan
and meet preservation then give join preservation.

At the current point c is true, since an atom is nonbottom. Thus O_a(p)
is true exactly when P_a(p) is true, equivalently when a<=p. The second
summand is necessary for Boolean preservation when a can become
bottom at a future point; it then lets the operator use p itself. That
is why no ND or stable-atom premise is needed.

Theorem. C + Atomicity_t entails Boolean-observer separation S_B.
Given p!=q, choose an atom a below their nonzero symmetric difference.
Exactly one of a<=p and a<=q holds, so the qualifying O_a observes different
truth values. Equivalently, for a nonbottom p choose an atom a<=p to prove
the Breach formulation in operator-separation-new-results.txt section 3.
The converse fails: the finite-support permutation example has S_B and is
atomless. This is a strict sufficient condition, not an equivalence.

2. COMPOSITE QUANTIFIER IDENTITIES

Under Atomicity at t, BF at t and necessary BF at every tested type,
these observers satisfy the composite operation identities and separate
propositions. The proof is in [Logical Observers, section 5](logical-observers.md#5-atomicity-supplies-observers-under-bf).

3. FULL ACTION MODELS ALSO HAVE BOOLEAN SEPARATION

Every full action model has Atomicity_t at its base point: propositions
are the entire powerset of the arrows out of that point, so singleton
arrows are atoms. Section 1 therefore supplies S_B. Here is also a direct
admissibility construction, which requires no choice principle.

Let the base be W and fix an arrow h out of W. Give an observer its
relational truth profile R on (g:W->V,a in D_t(V)) by

  R(id_W,a) holds iff h belongs to a,
  R(g,a) holds iff id_V belongs to a, when g!=id_W.

As usual this profile represents the exponential
  alpha(g,a)={l: R(lg,l_t(a))}.
Coherence follows directly by composition, and fullness admits alpha.
Its current application is the Boolean map

  O_h(p)(id_W)=p(h),
  O_h(p)(g)=p(g) for g!=id_W.

It is a coordinate-selection map and hence preserves all Boolean operations
literally. If p!=q, take h in their symmetric difference; O_h observes the
difference at id_W. This establishes separation at W. The construction
can be repeated at any object, but does not assert that each transported
O_h satisfies all Boolean laws on every new future input.

This direct proof and the Atomicity proof agree on the S_B verdict. They
do not establish C->S_B in arbitrary restricted-domain models, because
neither full powersets nor the needed arbitrary profile is available there.

SOURCE LOCATORS

Atomicity_t: topics/classicism/principles/atomicity-t.yaml, quoting
Bacon-Dorr Classicism, 16 May 2023 draft, section 2.2 p.24.
The reused full action construction: groups/full-action-models.yaml,
section 3.5 pp.58-61 and Appendix D pp.73-74 in that draft.
Directly checked action semantics: author-hosted 1 July 2022 draft,
Definitions 3.18-3.20 pp.55-56, https://andrew-bacon.github.io/papers/Classicism.pdf.
The observer constructions and deductions here are new arguments (misc),
not attributed to the source. The two draft page schemes are kept separate.

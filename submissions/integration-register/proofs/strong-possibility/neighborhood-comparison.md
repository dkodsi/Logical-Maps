# Constructor tests and one further hat

26 October 2026. Ordinary mathematical deductions by OpenAI Codex.
Direct source: misc, this note, §§1–4. These are applications of the earlier
profile and inductive-domain results, not a resolution of either full SP
target. No human check, independent audit, or Lean verification is claimed.

Fix either language separately: the pure language, with M=Max(C), or exactly
Σ={c:e→t}, with M=Max(C(Σ)). No individual name belongs to the original
signature. Put H=hat(Box), D=dual(H), H₂=hat(H), and D₂=dual(H₂), where

    hat(X) P := exists q (q and Box(dual(X) q -> P)).

The fixed reference M is used in every consistency side condition below.

## 1. A simultaneous consistent lower bound with unrestricted sentences

Let I(r;a) be a proposition-sort component of any finite mutual constructor
system from [inductive-witnesses.md](inductive-witnesses.md), §§2–4. Its
constructors are fixed terms in the original language with one auxiliary
individual parameter a; applicability guards satisfy that note's
C-provable persistence condition. Let

    W_I(P) := forall a:e, r:t,
      ((I(r;a) and r != bottom) -> (P and diamond r) != bottom).

Every W_I(P) is an ordinary finitary sentence of the original language:
the auxiliary a is universally bound, not added to the reference signature.
Define W to be M plus all W_I(P), for all such I and every closed original-
language P consistent with M. There is no restriction on the quantifiers,
types or term operations occurring in P.

**Theorem.** The same singleton profile model R satisfies all of W.
Moreover full SP entails W, but W does not entail full SP.

**Proof.** First fix an original-language term Q(x):t with just one free
individual variable. For every M-consistent P,

    M proves forall x,
      (Q(x) != bottom -> (P and diamond Q(x)) != bottom).       (1)

If C(a) proves Q(a)=bottom, the antecedent is uniformly false. Otherwise
Q(x) is C-consistent: a C-proof of its negation would, by necessitation,
prove Q(a)=bottom. Unary Possibility+ therefore gives
M proves forall x diamond Q(x). In a model of M+P, the formula
P and diamond Q(x) holds of an individual. It is consequently C-consistent.
A second application of unary Possibility+ gives
M proves forall x diamond(P and diamond Q(x)), establishing (1).
Here and throughout, C means the base for the chosen original language.
No optional premise was necessitated.

At R every actual I-member is the value Q(a) of a finite valid constructor
tree, by inductive-witnesses.md, §4. Apply (1) to that term. This proves
W_I(P) at R, simultaneously for every I and P.

The C-theorem

    D P iff forall r (r != bottom -> (P and diamond r) != bottom)

shows that SP entails every W_I(P), and SP also entails M. Conversely,
R has one individual and satisfies H E₁, where E₁ says that there is exactly
one individual: its admitted root indicator witnesses this H-instance.
The sentence not E₁ is M-consistent, but R refutes D(not E₁). Thus R
refutes the full SP schema while satisfying W. QED.

The two required M-consistency facts hold in each language. The singleton
profile root supplies M+E₁. For M+not E₁, take a model of signature
Maximalism after adjoining two fresh individual names, then forget those
names. Maximalism makes the two names distinct, and the reduct retains M.
This is a model construction certifying the original side condition, not
a change to that side condition.

## 2. One further hat gives an inconsistent upper bound

Define S₂ to be C plus D₂P for every closed original-language P consistent
with the same M. The C-theorem H <= H₂ gives D₂P -> DP, so S₂ entails SP.
In fact only two licensed instances make S₂ inconsistent:

    D₂ E₁,    D₂(not E₁).                                    (2)

**Proof.** C proves D E₁ -> E₁ by universal identity reflection. Hence
D₂E₁ -> DE₁ -> E₁. Unfolding the other instance gives

    D₂(not E₁) iff forall q (q -> diamond(Dq and not E₁)).

Instantiate q with E₁. Given E₁, it follows that
diamond(DE₁ and not E₁). But the necessitation of the C-theorem
DE₁ -> E₁ makes that proposition impossible. This contradicts (2).
Both instances are licensed by the models in §1. QED.

This is a direct variant of the earlier two-hat incompatibility argument;
it is not offered as a new inconsistency result for SP.

## 3. Why a further hat changes the quantifier behavior

There is a useful general calculation. Fix a definable operator X for
which C proves X <= hat(X) and reflexivity of hat(X). Suppose C also proves
A -> XA, with any displayed parameters universally closed before
necessitation. Contraposition gives dual(X)(not A) -> not A. Necessitate
this C-theorem and use q=not A in the definition of hat(X). Thus

    not A -> hat(X)(not A),
    A -> XA -> hat(X) A.

A is therefore fixed by both hat(X) and its dual.
In particular, every existential finite-Boolean-identity sentence E is
H-persistent, and so both E and its negation are H₂-persistent. This
explains the upper-bound contradiction: the next hat fixes both sides
of identity assertions which H itself only preserves in one direction.

## 4. What the comparison leaves to prove

For both exact reference theories the established comparison is

    W is consistent;     SP is unresolved;     S₂ is inconsistent.

The lower bound already allows every eligible sentence P. Its restriction
is on the propositions r used to test DP: in the verified model they have
finite constructor descriptions. Removing that restriction is precisely
the unproved extension. The upper-bound contradiction uses D₂, and gives
no inference from DP to D₂P. Neither bound settles the middle theory.

Inputs: [universal-core analysis](../../../classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/reflection-universal-core-20261022.md),
§§2–3 (density and reflection); [profile construction](../../../classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/profile-root-construction-20261022.md),
§§1–3, 6 (the model and unary Possibility+);
[signature audit](../../../classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/audit-signature-to-pure-sp-20261022.md),
§§9–10 (the separate signature case); and
[the existing two-hat argument](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/strong-possibility-and-two-hat-implies-nd-incompatible.yaml).
The necessary operator ordering H <= H₂ is stated in
[Background](../../../classicism-results-2026-10-24-v2/source/topics/classicism/background.md), “Hats, two-hat
necessity and 5-necessity,” with its source in *The Bounds of Possibility*,
Appendix D. The calculations above use only C-theorems, not necessitation
under an optional assumption.

# Old/new model: Boolean Completeness fails at O, although it holds at E

22 October 2026. New ordinary argument, direct source `misc`. This accompanies the independently audited all-type BC proof at E in `old-new-boolean-completeness-source-caveat.md`. It does not edit the source model or change its evaluation point. The construction is the existing symmetric ideally-full old/new model in `topics/classicism/writeups/symmetric-old-new-individuals.md`.

## An admitted family at O

Let D be the individual predicate at O whose extension at every arrow into E is all E-individuals, and whose extension at every arrow into O is exactly the old individuals. This is symmetric under the target symmetry groups and pinned by the empty set: its extension depends only on the target. At 1_O its extension is the old individuals.

Let η_x=λy(y=x), the available haecceity operation, and define

    X(F) := exists x (D(x) and F=η_x).

This is an admitted property by C comprehension. Its actual extension at 1_O is exactly {η_n:n old}. There is no external-family gap: alternatively, its arrow extension consists of the haecceities of all individuals at target E, and of the old individuals at target O, which directly verifies symmetry and empty pinning. Equality of individual haecceities is exactly equality of their individual parameters.

## No least upper bound

Suppose L were a least upper bound of that current family, and let finite S⊆O^e pin L. Choose an old n outside S and a new m outside S. Fix any injection h:O→E.

There is an injection h':O→E agreeing with h on S and satisfying h'(n)=h(m). Indeed h(m) is outside h(S), since m∉S and h is injective; this is a consistent finite partial injection, extendible to an injection from the countable source into E.

Since η_n≤L, the instance L(h'(n),h') holds. Thus L(h(m),h') holds. Pinning by S and h'|S=h|S then give L(h(m),h).

But the admitted predicate

    Q_m(y,k) iff y≠k(m)

is an upper bound of every old haecceity η_a: a≠m, and every arrow is injective. It is symmetric and pinned by {m}, or simply the C term λy(y≠m). It fails at (h(m),h). Therefore L is not below this upper bound, contradicting leastness.

So the et instance of BC fails at 1_O. Since O is reachable from E, □BC_et fails at the original evaluation point 1_E.

## Exact conclusion

Combining the separately audited root proof with this one, the original pointed model satisfies BC at every relational type at E but fails necessary BC already at et. In particular BC at E does not become necessary merely from the model's additional verified ND, boxed Atomicity, and boxed Strong Actuality. Its boxed Countable Boolean Completeness claim has a separate recorded proof and is not used here.

The former even-haecceity argument at E cannot establish its recorded verdict because that family is absent. The old-haecceity family at O is admitted because the source symmetry group preserves the old/new partition, while arrows O→E can mix both source sorts into the single E-sort. That precise asymmetry makes the repaired failure argument work at O.

## Independent audit

Parent/root and the principles lane independently checked this proof on 22 October 2026, including the admission of D and X, the finite partial-injection extension, pinning, and Q_m as an upper bound. This is mathematical AI-agent review, not human review or formal verification.

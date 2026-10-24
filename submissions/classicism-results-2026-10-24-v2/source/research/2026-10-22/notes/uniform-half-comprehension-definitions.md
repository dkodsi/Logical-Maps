# Uniform half-comprehension: two exact definitions of Actuality

Research derivations, 22 October 2026 (`misc`); fixed C, ordinary proofs, no record edits or novelty claim. Here “uniform” explicitly means one admitted operation, not merely pointwise existence or unique existence. Fix any one permitted relational type τ=σ_1...σ_n t, including τ=t.

## Uniform persistent comprehension

At this one type, each of the following is equivalent to Actuality:

    ∃R^(ττ) ∀X (Persistent(RX) ∧ Coext(RX,X)),
    ∃R^(ττ) ∀X (WeakPersistent(RX) ∧ Coext(RX,X)).

Given an actual atom w, the explicit operation

    R(X)(a)=□(w→X(a))

has persistent outputs by axiom 4. If X(a) is currently true, Actuality gives w≤X(a), making R(X)(a) true; conversely w is true, so R(X)(a) entails current X(a). This proves uniform full persistence, and hence its weak variant.

Conversely, choose any current tuple a of the argument types (none when τ=t), and define T(p)=R(λa.p)(a). Uniform coextension gives T(p)↔p currently. If p is currently true, weak persistence makes □T(p), hence T(p)=top. The proposition

    w:=∀p(T(p)→p)

is currently true. For each currently true q, T(q)=top remains an identity necessarily. At every future point satisfying w, its universal instance at the transported q therefore gives q. Thus w≤q for every current truth q, so w witnesses Actuality. This does not move a universal quantifier through a box.

## Uniform weakly inextensible comprehension

At the same arbitrary fixed type, Actuality is also equivalent to

    ∃R^(ττ) ∀X (WeakInextensible(RX) ∧ Coext(RX,X)).

Given Actuality with w, take R(X)(a)=w∧X(a). It is currently coextensive with X. Suppose Z is necessary on every current instance of R(X). The universal proposition B=∀a(X(a)→□Z(a)) is currently true, because w is true. Actuality gives w≤B. Hence any future instance of R(X) satisfies w, X(a), B and therefore Z(a). Thus R(X)≤Z, proving weak inextensibility.

Conversely, let R be the uniform witness and put T(p)=¬R(λa.¬p)(a), for a fixed current tuple a. Coextension gives T(p)↔p. If p is true, R(λa.¬p) is currently empty. Weak inextensibility tested against bottom makes that entire output relation equal to bottom. Therefore T(p)=top. The same proposition w=∀p(T(p)→p) and the preceding argument witness Actuality.

Uniform full Inextensible Comprehension consequently implies Actuality, but no converse for the full inextensibility condition is claimed. The distinction matters: a cut by the actual atom is weakly inextensible now and may fail inextensibility after transport.

These are definition improvements, not a count of four separate discoveries. They identify precisely what the single-operation uniformity adds to the corresponding comprehension formulations.

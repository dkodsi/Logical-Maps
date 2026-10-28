# Strong worlds necessarily cover the present

Over C, current propositional Strong Atomicity implies necessary Strong
Actuality. No Barcan, ND, comprehension, or Choice premise is needed.

## 1. A strong world entails the strong-world cover

Put
\[
D(w):=\forall q^t(w\le q\lor w\le\neg q),\qquad
c:=\exists w^t(w\land\Box D(w)).
\]
Thus \(c\) is exactly the Strong Actuality proposition. If \(w\) is a
current strong world, then \(\Box D(w)\). By 4 this remains necessary
at every accessible evaluation. Wherever \(w\) is true, the same
available \(w\) witnesses \(c\). Consequently \(w\le c\).
Formally, necessitate the unconditional implication
\(w\land\Box D(w)\to c\), and use 4 and C's persistence of the
parameter under existential introduction. No instance of Strong Atomicity
is necessitated.

If \(c\ne\top\), Strong Atomicity supplies a nonzero strong world
\(w\le\neg c\). But the preceding argument gives \(w\le c\), a
contradiction. Hence \(c=\top\), which is \(\Box c\), the desired
necessary Strong Actuality.

## 2. The same argument at relational types

At \(\tau=\bar\sigma t\), put
\[
C_\tau[\bar x]:=\exists W^\tau
  (\operatorname{SWorld}_\tau(W)\land W[\bar x]).
\]
Every current strong \(W\) lies below \(C_\tau\): its boxed decision
law persists, and wherever it has an instance it is nonzero and witnesses
the cover there. Thus Strong Atomicity at \(\tau\) gives
\(C_\tau=\top_\tau\). In particular, necessarily every currently
instantiated relation has a strong world below it. A strong world covering
an instance decides the relation and cannot entail its complement.

This last conclusion concerns instantiated relations, not every nonzero
relation at the later evaluation. It does not establish necessary Strong
Atomicity or any Barcan instance.

## Sources and review

Direct source: OpenAI Codex, prompted by Daniel Kodsi, *Strong worlds do not control modal domains*,
26 October 2026, §6, unpaginated; simplified 28 October 2026. The existing
current Strong Actuality theorem and its separately boxed-premise version,
attributed to Cian Dorr's 6 October formulation, remain unchanged. This
proof strengthens the conclusion from the current Strong Atomicity premise.
Ordinary independent AI proof review; no human or Lean certification.

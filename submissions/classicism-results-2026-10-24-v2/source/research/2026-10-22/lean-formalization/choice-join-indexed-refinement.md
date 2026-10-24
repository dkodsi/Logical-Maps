# Selecting by the unique propositional join

22 October 2026. Original ordinary mathematical refinement by OpenAI Codex,
direct source `misc`, this unpaginated note and `ChoiceActuality.lean`.
Prepared during translation; no independent check or completed Lean certification
is claimed. It preserves the proposed theorem's original finitary C language.

The sharp `RC_(t,t) + BC_tt -> Actuality` theorem can use the guarded fixed-point
proof directly. The separate disjoint-refinement construction is unnecessary for
this route. The previously saved arguments are preserved.

Assume not Actuality. `BC_tt` gives `BC_t`. For each proposition `j`, use RC at
`(t,t)` on the serial relation

```
U(j,a) := not j -> [not a and a != bottom and a <= not j].
```

If `j` is false, its negation is nonzero. Failure of Actuality supplies a nonzero
false part of that negation. If `j` is true, every output meets the implication.
Let `T` be an actual total functional subrelation of `U`.

Define a represented graph, with no operation selecting suprema,

```
S(F,a) := exists j [LUB(j,F) and T(j,a)].
```

Completeness at `t` makes this graph total. Algebraic antisymmetry makes the
supremum entity unique, so functionality of `T` makes `S` functional. This
argument does not identify coextensive property codes or assert future
functionality. In fact, coextensive properties have the same actual supremum
entity, so the graph also respects current coextension, though the guarded
operation proof does not need that extra fact.

For a guarded false antichain `F`, the higher-type disjoint-join lemma says its
join `j` is false. Therefore any selected `a` is nonzero, false, and below `not j`.
Every current `F`-member is below `j`, so `a` is disjoint from every such member
and cannot itself be a member. Thus `S` has exactly the safe-extension property
needed by the guarded operation proof. Embedding the actual selector's
functionality, falsity, nonzeroness, and both compatibility orientations inside
the new-member clause gives a progressive operation preserving the guarded
domain and strictly enlarging every current member.

The represented guarded domain is chain complete by `BC_tt`. The fixed-point
lemma consequently contradicts strictness. This proves Actuality using only
`RC_(t,t)` and `BC_tt`. The same consequence for Transversal Choice follows using
the recorded Actuality-to-Transversal theorem and the additional RC instance
`RC_(sigma t,sigma)`. All-type RC with BC only at `tt` therefore suffices for
all-type TC, subject to the correctness/certification checks still pending.

## Translation audit

`ChoiceFixedPoint.lean` implements the fixed-point argument through the existing
Lewin core. The core requires a coextension-invariant selector on chain codes.
That selector is supplied by the unique supremum entity followed by the given
functional progressive graph. The proof explicitly establishes its invariance;
it assumes neither TC nor a transversal of property codes.

`ChoiceCompleteness.lean` obtains disjoint-join reflection by joining haecceities.
Evaluation preserves algebraic joins through its right adjoint. Compatibility
is a disjunction of positive identities and is necessary when true by NI.
The proof uses CBF only through established evaluation/order lemmas, not BF.

`ChoiceActuality.lean` contains both guarded and sharp routes. All optional
hypotheses are actual. Only closed logical implications are necessitated;
the boxed corollary boxes both RC and BC. No unboxed-to-boxed strengthening is
asserted. No infinity axiom, infinitary connective, quotient type, external
ordinal, Mathlib theorem, `sorry`, or new axiom is used by these source proofs.

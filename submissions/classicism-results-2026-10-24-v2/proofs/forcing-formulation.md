# The forcing/CH conjecture: strict-smallness formulation audit

Original source comparison and connecting argument by OpenAI Codex, prompted
by Daniel Kodsi, 23 October 2026. The model constructions and their shared
arguments retain their existing attributions. This note has no Lean certificate.

## 1. Exact verdict and scope

The recorded conjecture asks whether the following four premises are
incompatible over the map's fixed Classicism:

```math
\Box\mathrm{RigidComprehension},\quad
\mathrm{IntensionalChoice},\quad
\mathrm{ForcingPossibilism}_{<},\quad
\mathrm{NonContingencyOfCH}
```

Here the subscript emphasizes the **existing** definition: Forcing Possibilism
requires representations only of complete Boolean algebras which are finite
or have strictly smaller cardinality than the proposition domain. It does
not change the principle's ID or introduce a new principle.

Under metatheoretic Choice, the existing full action model
`full-free-monoid-glued-constants-singleton` satisfies all four premises.
Thus it refutes the incompatibility as currently formulated in the database.
The same conclusion is supplied by three other recorded constructions:
`full-free-monoid-glued-constants`, `full-free-product-glued-constants`, and
`full-double-retraction-glued-constants`.

This is a connecting argument from existing model evidence, not a new model
construction or a proof that the premises are themselves inconsistent.
It does not by itself refute Bacon's theorem under every possible reading of
his intended definitions and background language.

## 2. Why strict smallness is decisive

Let M be the free monoid on countably infinitely many generators. Its finite
words form a countably infinite set. In its full action model the propositions
are all subsets of M, so their cardinality is the continuum.

In ZFC every infinite complete Boolean algebra has at least continuum many
elements. To see this, first choose countably infinitely many pairwise disjoint
nonzero elements. If there are infinitely many atoms, choose countably many
of them. If there are finitely many atoms, their join has a nonzero atomless
complement unless the algebra is finite; successive splitting in that
complement gives the required sequence. Completeness sends each subset of
the sequence to its join. Distinct subsets have distinct joins: an element
present in one subset and absent from the other is disjoint from every
member of the latter, whose join therefore lies below its complement.
This is an injection from the power set of the natural numbers.

Consequently a complete Boolean algebra with fewer elements than the
proposition domain in this model must be finite. A finite Boolean algebra
with n atoms is isomorphic to the powerset algebra of any n distinct arrows
of M. For their finite set p, the interval of propositions below p is exactly
that powerset algebra, and p is not top because M is infinite. The degenerate
one-element algebra is represented by p = bottom.

These are the internal conditions required by the principle, not merely
external cardinality observations. At every object full domains contain a
relation with any prescribed extension. Thus every external subfamily of an
internal Boolean carrier is represented by a property; every external map or
isomorphism is represented by a binary relation; internal Boolean completeness
is external completeness; and the internal injection comparisons and Dedekind
finiteness agree with their ordinary set-theoretic readings. This is exactly
the scope of `forcing-possibilism-countably-many-arrows`.

In particular the strict principle does not demand any infinite atomless
forcing algebra in this model. The expected route from that principle to
CH contingency lacks the required algebra-existence/size step.

## 3. The other three premises

**Necessary Rigid Comprehension.** The full-action construction contains the
intension whose extension at each arrow is the image of a given root
extension along that arrow. This supplies a rigid coextension. The same
construction works at every reachable object, giving the boxed schema.
See `arguments/full-rigid-comprehension.yaml` for the full general argument.

**Intensional Choice.** With metatheoretic Choice, well-order each relevant
domain and use the intension selecting the least witness at the target of
each arrow. Full domains contain this intension. The shared argument
`intensional-choice-well-ordering` proves necessary Intensional Choice,
which implies the required unboxed instance by T. The construction condition
`codomain-intensions` is semantic evidence, not an extra object-language axiom.

**Non-contingency of CH.** At every reachable object every relation on the
extension of an admitted carrier is represented. A real number structure is
therefore a complete ordered field in the metatheory, and its second-order
relations range over every external relation on that field. Each such field
is isomorphic to the metatheoretic reals; each second-order analytical sentence
therefore has the same truth value in every admitted real structure at every
object. This proves Necessity of Second-Order Analysis and hence its CH
instance. See `second-order-analysis-extensionally-full` and the recorded
implication from that schema to `non-contingency-of-ch`.

Completeness here has its standard **nonempty bounded-subset** meaning.
Including the empty subset would prevent any ordered field from satisfying
the definition and would make the analytical principles vacuous. The
background's explanatory clause has been clarified accordingly. The present
model argument is not dependent on that accidental vacuity: its type-t
domain has continuum cardinality, so, in the full domains, an external
bijection transports the ordinary real-field structure to that carrier and
all its relations are available internally. This gives actual real structures
at type t with the corrected definition.

## 4. Correspondence with the cited theorem

Andrew Bacon's *Could the truths of mathematics have been different?*, draft
of 9 October 2025, main p. 27, defines smallness as finite or strictly fewer
elements than there are propositions and states Theorem 6.1 immediately
afterwards, with the proof deferred. Appendix A.3, appendix pp. 3–4
(PDF pp. 37–38), instead describes SmallCBA using a non-strict cardinal bound
and displays the additional requirement that the representing proposition
is not top. Appendix A.1 permits the full simple-type hierarchy; the map
works in the relational-output hierarchy.

The current principle record intentionally adopts the strict convention,
following the separate large-model handout. The discrepancy therefore needs
to be reconciled with the source, rather than repaired by silently changing
the database's established definition. Nor does the fact that the non-strict
principle is stronger prove that it yields the intended CH theorem.

The remaining source-level audit must fix one precise formulation and its
background language, then either transfer the countermodel to that exact
setting or establish the additional forcing-algebra availability needed by
the intended proof. Until then, preserve the attributed theorem statement
and distinguish its intended reading from the encoded incompatibility.

Source: [Bacon's draft](https://andrew-bacon.github.io/papers/Could%20mathematics%20have%20been%20different.pdf),
main §6, p. 27; Appendix A.1 and A.3. No source PDF is redistributed.

## 5. Database integration and separate forcing results

The original conjecture record keeps its ID, premises, conclusion, source
attribution and conjectured status. Its computed resolution can report the
existing countermodels. No redundant model verdict or new incompatibility
theorem is needed for this consequence of their recorded properties.

The explicit modalized-lottery-cloud transfer results address a different
claim: a specified construction realizes both sides of CH. They remain
useful even though the three abstract modal principles, with the strict
size convention used here, do not entail CH contingency. Which lottery
presentations have been proved equivalent is a separate construction audit.

This note records the current ordinary mathematical argument. It does not
upgrade any model or generated statement to Lean verified, and the existing
certificates retain their precise scopes.

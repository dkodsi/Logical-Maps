# The exact finite bound on necessary distinctions under Max

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi.

## 1. One finite model supplies the bound

For each fixed admitted type define an external finite integer c_tau by

    c_e = 1,       c_t = 2,       c_(alpha beta) = c_beta ^ c_alpha.

Equivalently, if tau=sigma_1 ... sigma_k t, then
c_tau=2^(product_j c_sigma_j). These are the carrier sizes in the full
one-world extensional C model with one individual. They are integers in
the metatheory, not newly quantified object-language type sizes.

Let AtMost_m(tau) be the ordinary finite pure sentence saying that every
m+1 objects of type tau include an equal pair. The finite model witnesses
C-consistency of AtMost_c_tau(tau). Pure Max therefore gives

    diamond AtMost_c_tau(tau).                              (1)

Only this one Max instance at the fixed type is needed below.

## 2. Necessary distinctions cannot exceed that bound

**Theorem.** Under pure Max, there are no c_tau+1 current objects of
type tau that are pairwise necessarily distinct.

Suppose a_0,...,a_m, m=c_tau, were such objects. Their finitely many
necessary inequalities imply box AtLeast_(m+1)(tau), by existential
introduction inside the box with those same witnesses. Equivalently,
necessitate the pure logical finite-pigeonhole implication, instantiate
it at the current witnesses and use K. This contradicts (1). No universal
law about all future members of a current property has been inferred.

Consequently every current property X whose distinct instances are
necessarily distinct has at most c_tau instances. X need not be rigid,
persistent, inextensible, definable without parameters, or necessarily a
domain of the same structure. Pairwise protection of its current
distinctions already suffices.

Examples: at e the bound is 1; at t and et it is 2; at tt and (et)t
it is 4. The bound increases with type, but remains externally finite
at every fixed type.

This should not be read as finiteness of the whole actual type. Pure Max
allows and requires many actual distinctions that could disappear.

## 3. The bound is sharp already in C

**Lemma.** C proves the existence of c_tau pairwise necessarily distinct
objects at each fixed type tau.

Proof by external induction on the finite type expression. At e choose
one individual, using inhabitedness; there is no pair to distinguish.
At t use bottom and top, which are necessarily distinct in C.

Suppose at each argument type sigma_j we have a finite list
a_(j,1),...,a_(j,c_sigma_j) with necessarily distinct members. For every
subset S of the finite Cartesian product of the index sets, form the
relation

    R_S(x_1,...,x_k) =
      OR_{(i_1,...,i_k) in S} AND_j (x_j=a_(j,i_j)).

The empty disjunction is false. Evaluating at a listed argument tuple
gives necessarily true when its index tuple lies in S and necessarily
false otherwise. Self-identities are necessary; other entries are
excluded by the chosen necessary distinctions. If S differs from T,
one listed tuple therefore necessarily distinguishes R_S from R_T.
There are exactly 2^(product_j c_sigma_j)=c_tau such relations.

All constructions and conjunctions are externally fixed and finite.
The lemma does not invoke extensional fullness or unrestricted Choice,
and no optional hypothesis is admitted into Logical Equivalence. This
proves the induction. QED.

Combining the lemma with section 2 makes c_tau the exact largest size
of a necessarily distinct current family under Max. The lower-bound
construction does not assert that its family exhausts the type.

## 4. Use in simplifying the analysis comparison

To rule out a proposed stable mathematical domain under Max, it is enough
to show that its current instances include c_tau+1 necessarily distinct
objects. One need not prove that its whole domain is rigid or that its
entire theory is necessary.

For an operation-represented field, preservation of its fixed current
algebraic identities makes any merger of distinct elements force the
merger of zero and one. Thus protecting just zero from one protects all
current field distinctions; section 2 then rules out every current
ordered field with that protection. The stronger divisible-group
argument in [field operations](field-operations-under-max.md) needs only an
addition representative for a real field.

The conceptual source of these obstructions is that actual operation
identities survive possible identifications of their arguments. The
finite-model Max instance and elementary algebra supply the rest.

## Sources and relationship to earlier work

- Bacon and Dorr, Classicism, 16 May 2023 draft, section 2.4, pp. 35–36,
  for pure Maximalism. The singleton one-world full interpretation is
  the standard extensional model of C.
- [Earlier certified predecessor argument](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/predecessor.md)
  uses that same finite interpretation to obtain a particular collision.
- [Earlier finite-core proof](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/relational-coding-recursion-20261022.md#30-the-e-free-primitive-core-is-already-canonically-finite-and-stable-in-c)
  uses the same finite truth-table induction. The present upper bound
  applies to every current necessarily distinct family, without a
  hereditary-core or monism premise.

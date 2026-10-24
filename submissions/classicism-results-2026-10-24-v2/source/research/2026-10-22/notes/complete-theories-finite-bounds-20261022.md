# Complete effective Classicist theories have standard finite bounds

22 October 2026. Original argument by the local-strengthening research subagent, independently audited mathematically by the construction subagent. No human check or Lean verification claimed. No repository records edited. Direct source for the new interpretation and conclusions: misc, this note.

## 1. Sources and exact claim

The definitions of Frege numerals, N_sigma, Sum_sigma and Prod_sigma are those in `topics/classicism/background.md`, lines 74–134. We use C's impredicative N-induction and the finite-cardinality exclusivity lemma in `topics/classicism/writeups/pure-possibility-implies-axiom-of-infinity-t.md`, section 1, Lemma 4: two N-cardinalities with a common actual instance are identical. Those are recorded background results, not new results of this note.

The external arithmetic input is the essential undecidability of Tarski–Mostowski–Robinson's theory R. Its exact five axiom schemata and the essential-undecidability statement are displayed in Juvenal Murwanashyaka, “Weak essentially undecidable theories of concatenation,” *Archive for Mathematical Logic* 61 (2022), 939–976, section 1, pp. 939–940: https://link.springer.com/article/10.1007/s00153-022-00820-y . The primary article was inspected in this session. The order relation in R is primitive; it need not be defined from the interpreted addition operation.

**Theorem.** Let T be a consistent recursively enumerable extension of C that is complete for closed pure sentences. For every admitted type sigma, there is a positive external standard integer b_sigma such that

    T proves Box(not AtLeast_(b_sigma)(sigma)).

Here AtLeast_n(sigma) is the ordinary finite sentence asserting n pairwise distinct entities of type sigma. Thus T bounds the size of each type by a standard finite number throughout its accessible worlds. The bound may depend on the type and the theory.

In particular, the theorem applies to C+A whenever A is a closed pure sentence and C+A is consistent and complete. It therefore applies to every pointed-complete cell in the profile-root atomicity criterion. It does NOT classify these cells as the finite rigid B_(n,k) cells: bounded domains can still have nonrigid transports.

## 2. Notation and the theory to be interpreted

Fix sigma. Put nu=(sigma t)t. Write N for N_sigma, S for Suc_sigma, and bar(n)=S^n 0 for each external standard n. All arithmetical quantifiers below are restricted to N. In particular, the domain used in the first-order interpretation is the definable, nonempty subset N of the nu-domain.

Let

    U_sigma = C + {AtLeast_n(sigma): n is a positive standard integer}.

This is a recursively enumerable theory. We will give an effective first-order interpretation of R in U_sigma. We do not assume I_sigma or I-star_sigma. We do not infer the quantified Infinity_sigma axiom from this schema.

In a language with standard numerals, addition, multiplication and primitive order, R has these schemata:

1. bar(m)+bar(n)=bar(m+n).
2. bar(m)*bar(n)=bar(m*n).
3. bar(m)!=bar(n), for distinct standard m,n.
4. For every standard n, all x satisfy x<=bar(n) implies x=bar(0) or ... or x=bar(n).
5. For every standard n, all x satisfy x<=bar(n) or bar(n)<=x.

The numeral successor is interpreted by S, which is a total function on N by the defining induction principle. If a presentation forms numerals by repeated addition of 1, axiom 1 identifies those numerals with the same S-numerals, by external finite induction.

## 3. Standard finite separation and predecessor uniqueness

For every standard n, C proves that AtLeast_n(sigma) makes bar(0),...,bar(n) pairwise distinct. Choose n actual distinct sigma-entities and, for each j<=n, abstract the property containing exactly the first j. Expanding the finitely iterated successor definition shows that bar(j) holds of that property and that each other numeral in the displayed list does not. Equal cardinality entities would agree on that argument, a contradiction.

The same finite expansion shows that any property with exactly j actual members is an instance of bar(j). These are external finite proofs for each standard j; there is no inference from a schema to a quantified infinity assertion.

**Bounded predecessor lemma.** For each positive standard h, U_sigma proves

    for all z in N, S(z)=bar(h) implies z=bar(h-1).

Choose an actual h-element property X, available by AtLeast_h(sigma). Since bar(h)X, the assumed identity gives (S z)X. Unfolding S supplies y with Xy and z(X-y). The property X-y has exactly h-1 actual members, so bar(h-1)(X-y). Both z and bar(h-1) are N-cardinalities. Their common instance identifies them by recorded exclusivity.

Also C proves S(z)!=0 for every z: 0 and any successor differ at the empty property. Thus no N-entity outside the finite prefix {bar(0),...,bar(n)} can have its successor inside that prefix. Only finitely many AtLeast_h assumptions are used for each fixed prefix.

## 4. Sum is uniquely correct on standard inputs

From the definition of Sum, C proves its base and successor rules:

    Sum(m,0,m),
    N m and N i and N j and Sum(m,i,j) imply Sum(m,S i,S j).

For the successor rule, instantiate an arbitrary relation satisfying Sum's base and closure clauses and apply its closure once. External finite iteration gives

    Sum(bar(m),bar(n),bar(m+n))

for every standard m,n.

To prove uniqueness for these inputs, fix standard m,n and instantiate Sum's quantified relation with

    R(i,j) := AND_(0<=h<=n) (i=bar(h) -> j=bar(m+h)).

This relation contains (0,bar(m)), by standard numeral separation. It is successor-closed on N. Indeed, if S i=bar(h), h=0 is impossible; for h>=1 the bounded predecessor lemma gives i=bar(h-1). The corresponding clause of R then gives j=bar(m+h-1), hence S j=bar(m+h). These are all clauses required for R(S i,S j); if S i is outside the prefix, they are vacuous.

Consequently Sum(bar(m),bar(n),o), with o in N, implies R(bar(n),o), hence o=bar(m+n). Therefore U_sigma proves that Sum on each pair of standard inputs has exactly one N-output, and that output is the correct standard numeral.

## 5. Prod is uniquely correct on standard inputs

The definition of Prod similarly gives its base rule and its step rule using Sum:

    Prod(m,0,0),
    Prod(m,i,j) and Sum(m,j,k) imply Prod(m,S i,k)

for numerical arguments. The standard Sum instances and external finite iteration yield

    Prod(bar(m),bar(n),bar(m*n)).

For uniqueness fix standard m,n and use

    R(i,j) := AND_(0<=h<=n) (i=bar(h) -> j=bar(m*h)).

The base pair (0,0) satisfies R. Suppose R(i,j), Sum(bar(m),j,k), and S i=bar(h) with h<=n. The zero case is impossible. Otherwise bounded predecessor uniqueness gives i=bar(h-1), and R gives j=bar(m*(h-1)). Section 4 makes the Sum output uniquely k=bar(m*h). Thus R(S i,k). Instantiating Prod's defining universal relation with this R forces any numerical output at inputs bar(m),bar(n) to equal bar(m*n).

## 6. Total arithmetic functions by definable default graphs

The interpretation of first-order functions does NOT require admitted typed operations returning a selected number. First-order interpretations may use definable total single-valued graphs.

Let UniqueSum(m,n) assert that there exists exactly one o in N with Sum(m,n,o). Define

    AddGraph(m,n,o) := N o and
      ((UniqueSum(m,n) and Sum(m,n,o))
       or (not UniqueSum(m,n) and o=0)).

For m,n in N, classical logic proves that this graph has exactly one numerical output: select the unique Sum output when it exists, and otherwise use 0. This is a logical existence-and-uniqueness proof, not a Choice or Plenitude assumption. The same definition using Prod gives MulGraph.

Sections 4–5 show that on standard input numerals the default case is not used. These graphs therefore validate R's addition and multiplication schemata. Section 3 validates its numeral-distinctness schema. Nested arithmetic function terms are translated in the usual way by composing these functional graph formulas; this translation is effective.

## 7. Primitive order and the two bounded-order schemata

Interpret

    m<=n  iff  exists k in N, Sum(m,k,n).

No claim is made that this relation is a global linear order in U_sigma. Only R's two fixed-standard-bound schemata are needed.

**Bounded initial segment.** Fix standard n and suppose m<=bar(n). If m were distinct from all bar(0),...,bar(n), use in Sum the relation

    R(i,j) := j!=bar(0) and ... and j!=bar(n).

It contains (0,m). It is successor-closed: section 3 proves that the successor of an N-entity outside the prefix remains outside the prefix. Thus Sum(m,k,bar(n)) would force R(k,bar(n)), a contradiction. Hence m equals one of the standard prefix numerals. This is R4.

**Comparison with a standard bound.** For every fixed standard n, C's N-induction proves

    every x in N is one of bar(0),...,bar(n),
    or x=S^(n+1) k for some k in N.

The property contains 0. Its successor step moves a prefix value to the next one; at bar(n) it enters the tail with witness 0; and a tail witness k is replaced by S k. This is an ordinary impredicative induction instance.

If x=bar(h) with h<=n, the standard Sum instance with witness bar(n-h) gives x<=bar(n). In the tail case x=S^(n+1)k, C's N-induction on l proves

    Sum(bar(n),l,S^n l).

The base is Sum(bar(n),0,bar(n)); the step is Sum's successor rule, using S(S^n l)=S^n(S l). Set l=S k to obtain Sum(bar(n),S k,x), hence bar(n)<=x. This is R5.

We have now interpreted all five R schemata in U_sigma, without I, I-star, Choice, Plenitude, or an illicit use of modal necessitation.

## 8. Complete effective extensions must have standard finite current bounds

Let T be as in section 1. Suppose for some sigma it proved no standard finite upper bound. Completeness for each closed pure AtLeast_n(sigma) then makes T prove every AtLeast_n(sigma), so T contains U_sigma.

The arithmetic sentences whose translations T proves form a consistent recursively enumerable complete theory extending R. Consistency and completeness pass through the interpretation because its domain is provably nonempty and its function graphs provably total and single-valued. Recursive enumerability follows from the effective translation and enumeration of T-proofs. This contradicts essential undecidability of R, equivalently the absence of a consistent recursively enumerable complete extension of R.

Thus for every sigma there is a standard n such that T proves not AtLeast_n(sigma). Since C has nonempty type domains, n can be taken at least 2. This is an actual standard finite bound, not merely internal finiteness.

## 9. The bounds can be made necessary

Apply section 8 to nu_sigma=(sigma t)t. For some standard m, T proves that the nu_sigma-domain has at most m entities. Among the m+1 standard cardinality terms bar(0),...,bar(m), finite pigeonhole then gives a disjunction of identities bar(i)=bar(j), with i<j<=m.

Each such identity is necessary by NI. Section 3 gives the C-theorem

    AtLeast_m(sigma) implies bar(i)!=bar(j).

Necessitate this C-theorem, then combine it with Box(bar(i)=bar(j)) to obtain Box(not AtLeast_m(sigma)). Every disjunct yields that same boxed bound, so the finite disjunction yields it as well.

No optional axiom of T was necessitated. The only boxing of a non-C fact was the legitimate NI consequence of an actual identity; the finite-separation implication that was necessitated is a C-theorem.

## 10. Consequences and limits for the atom search

If Max+Atom(A) is consistent for a closed pure A, the independently proved pointed-completeness criterion makes C+A complete. The theorem above therefore supplies standard finite necessary bounds on every type throughout every A-world. In particular A cannot be a cell with unbounded standard individual or propositional domain sizes. The simpler consequence A implies not I_sigma at every sigma also follows directly from arithmetic incompleteness, but the boxed standard bounds are stronger.

This does not assert that A-worlds have rigid transports, or that all pointed-complete cells are the B_(n,k) examples. Finite maps can collapse entities, and target domains can include new entities. A full classification still requires further work. No contradiction of pure Strong Possibility follows from this boundary alone.

# Prescribing the arithmetic of a Maximalist model

26 October 2026. Ordinary mathematical deduction by OpenAI Codex.
Direct source: `misc`, this note, §§1–4. Self-checked; no independent
audit or Lean verification. Neither Strong Possibility target is settled.

## 1. Statement with the references kept separate

Fix either L equal to the pure language or L equal to exactly the language
with Σ={c:e→t}, with no individual names. Put M=Max(C_L). Use the fixed
Frege interpretation at e for ordinary first-order arithmetic. Let E₁ say
that there is exactly one individual.

**Theorem.** Every countable recursively saturated model A of true
first-order arithmetic is isomorphic to the actual Frege arithmetic of a
genuine model N of M+E₁.

The assertion applies independently to the two reference theories. The
construction can also make its expanded coding structure recursively
saturated. It does not identify N's algebra with the nonstandard term
algebra B(A) in the stronger truth-expansion construction.

Here is a more general version which isolates the role of arithmetic
soundness. Let P be any computably axiomatized collection of additional
sentences in the fixed language, and let A be countable, recursively
saturated, and a model of PA plus every standard-true Π₁ sentence. Then:

    A is isomorphic to the actual arithmetic of some N satisfying M+P
      iff
    A satisfies every ordinary arithmetic consequence of M+P.       (1)

The right side refers to the fixed Frege translation. No boxed version
of P is included unless it is expressly part of P. In (1) assume, as
holds for M here, that the interpreted arithmetic satisfies PA.

## 2. A recursive presentation of Max relative to correct proof arithmetic

Use the ordinary countable many-sorted first-order Henkin presentation of
C_L, including a truth predicate on propositions, literal identity, all
term operations, and the truth clauses for quantifiers. Its axioms are
computably enumerable: proof certificates handle the theoremhood side
condition of Logical Equivalence. This is the same presentation used in
the stronger truth-expansion criterion.

Introduce a disjoint arithmetic sort and an isomorphism j from it onto
the actual Frege number domain of the C structure. Require j to preserve
zero, successor, addition and multiplication. Addition and multiplication
on the C side are the already defined relations; this does not postulate
new entity-valued C operations.

For each standard closed L-identity S=T add the sentence

    not Pr_C_L(code(S=T))  ->  not Tr(Eq(S,T)).                    (2)

The antecedent is evaluated in the arithmetic sort. This is a computably
enumerated scheme: it lists all closed identities and tests no consistency
or nonprovability condition externally. The proof predicate uses the
effective, certificate-based original calculus.

If the arithmetic sort satisfies PA+TrueΠ₁, its answers about C_L
provability of standard sentences are correct. An actual finite proof
has a standard numerical witness recognized in PA. If no proof exists,
the corresponding no-proof sentence is a standard-true Π₁ sentence.
Consequently, on such a structure, (2) is exactly the original Max
distinctness schema. It neither strengthens its reference to M nor
introduces a new original signature constant.

Add P. Call this expanded, computably axiomatized theory Q. When invoking
resplendency, replace an enumerable axiom set by an equivalent recursive
one using proof-index padding (Craig's trick).

## 3. Proof of the lifting criterion

The forward implication in (1) is soundness. For the reverse suppose A
satisfies all arithmetic consequences of M+P. The many-sorted theory

    M + P + Th(A), with the arithmetic sort linked by j,

is consistent. Otherwise a finite conjunction δ of sentences in Th(A)
would give M+P ⊢ not δ under the arithmetic translation. Then not δ
would be an arithmetic consequence of M+P false in A, a contradiction.

Take a countable model of this joint theory. Its arithmetic sort satisfies
PA+TrueΠ₁, so it also satisfies Q by §2. Translate this countable
many-sorted model into an expansion of its arithmetic universe: represent
each C sort by a unary subset of that universe and its operations and
truth by additional functions or relations. Each C sort is countable;
arbitrary injections into the infinite arithmetic universe supply these
representations. Different represented sorts may overlap because they
have distinct sort predicates and separately typed operations. Include
the usual domain and typing axioms. This coding uses a recursive
countable expanded language.

In particular the resulting one-sorted recursive theory Q* is consistent
with Th(A). Resplendency of the specified countable recursively saturated
A now gives an expansion of A satisfying Q*. Decode its C sorts. The
link j makes its actual Frege arithmetic isomorphic to A, and correctness
of the standard proof predicate makes the decoded model satisfy the
original M+P. This proves (1).

The resplendency theorem also allows the expansion to be recursively
saturated. The coding predicates and j belong only to the external
first-order presentation. They are not added entities, relations, or
choice operations in the original C language.

The standard external input is the Barwise–Schlipf–Ressayre resplendency
theorem in its recursive expanded-theory form: Fredrik Engström,
*Expansions, omitting types, and standard systems* (2004), §1.6,
Definition 1.22 and Theorem 1.23, printed pp.17–18. The recursive-axiom
replacement also appears in its proof on p.18.
[Checked primary source](https://engstrom.morot.org/material/docthesis.pdf).

## 4. Application and the remaining gap

For each assigned language the earlier singleton profile model R_L
satisfies M+E₁ and has standard actual Frege arithmetic. Its number domain
is exactly the external numeral orbit, because every root subset is an
admitted predicate extension; component profiles distinguish all numerals.
The arithmetic graphs have their standard values. Therefore every
arithmetic consequence of M+E₁ is true in the standard natural numbers.
Any A satisfying true arithmetic meets the right side of (1), with
P={E₁}, proving the theorem in §1.

Construction inputs: [profile root, §§1–5 and 11](../../../classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/profile-root-construction-20261022.md),
and the [unary-signature reference audit, §§2–3](../../../classicism-results-2026-10-24-v2/proofs/signature-sp-derivative.md).
The standard arithmetic identification is also checked in
the earlier fixed-domain construction analysis.

Thus a chosen countable recursively saturated arithmetic model does not,
by itself, obstruct a Maximalist expansion. The new expansion need not
preserve the complete algebraic theory of the common term algebra B.
Nor does lifting two arithmetic structures separately lift an embedding
between them to an injective map preserving all higher-type term
operations. Those are precisely the additional requirements in the
current SP construction routes. No such compatibility follows from this
theorem, and no SP truth expansion is being inferred from it.

# Arithmetic Necessitism and pure B imply Necessity of Arithmetic

Fix a type $\sigma$. Write $N$ for its Frege numbers, $I^*$ for their
Peano condition, and $I$ for $\Diamond I^*$. We use B only for the closed
pure sentence $I$. The arithmetic induction below is Goodsell's
[Theorem 9](countable-boolean-completeness-implies-necessity-of-arithmetic.html);
here its restricted quantifier step comes from Arithmetic Necessitism.

By the [equivalent forms of Potential Infinity](../index.html#background/arithmetic),
C proves $I\leftrightarrow I^*$. C also proves $\Diamond I\leftrightarrow I$,
since $I$ is a possibility and the accessibility relation is reflexive
and transitive. The B instance $I\to\Box\Diamond I$ now shows
$I\to\Box I$, hence $I\to\Box I^*$. If $I$ has no possible instance,
$\Box(I\to A)$ holds for every sentence $A$. Otherwise $I$ holds now
and $I^*$ holds necessarily.

In the latter case Arithmetic Necessitism supplies the rigidity of $N$
and necessary distinctness of its distinct current members. We claim
that for each arithmetical formula and each tuple of current number
parameters its present truth value is preserved at all accessible points.
The following induction uses necessary $I^*$ throughout.

- A variable, zero and a successor term with number parameters denote
  numbers. Their values transport as terms and numbers remain numbers.
  Equal number values remain equal by necessary identity, and distinct
  ones remain distinct by the given number distinctness.
- True sum and product equations on numbers persist in C by the
  induction defining their graphs. For a false equation, choose
  the actual result on the two inputs. Its graph instance persists.
  Under $I^*$ the graph is single-valued on numbers, and the true
  output remains distinct from the proposed output. Thus the original
  equation stays false. These are Goodsell's arithmetic Lemmas 3, 6
  and 7.
- Both signs of the Boolean connectives follow from the induction
  hypotheses for the constituents.
- If a universal sentence restricted to $N$ holds on the current
  parameters, each current number necessarily satisfies its matrix by
  the induction hypothesis. Weak inextensibility of $N$, applied to
  the matrix with those parameters, implies that every accessible
  number satisfies it there. If the universal is false, a current
  counterexample remains a number and continues to falsify its matrix.
  Existential quantification follows by negation.

For a sentence $A$ the claim gives $\Box A$ or $\Box\neg A$ in the
second case. Together with the first case this gives the required
$\Box(I\to A)\lor\Box(I\to\neg A)$ at every counting type.

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, obtained this combination
of the pure B instance with Arithmetic Necessitism's restricted
quantification on 26 November 2026, using Zachary Goodsell's arithmetic
persistence and formula induction. Two additional GPT-6 research agents
independently reviewed the argument.

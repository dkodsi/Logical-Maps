# Typed bracket abstraction in the relational grammar

Original mathematical argument, direct source misc; unpaginated.

Fixed framework
Types are e, relational types, and the metalanguage's opaque type variables.
An arrow has arbitrary input type and RELATIONAL output type. Consequently
a term of nonrelational type is a variable or constant: neither application
nor abstraction can produce it. This fact makes the missing e -> e type
manageable rather than an obstacle to abstraction elimination.

Use these fixed typed combinator schemata. Here sigma and tau are arbitrary
types, rho is relational, and nu is relational wherever S is used.

  I_rho : rho -> rho
    I x = x
  K_(sigma,rho) : rho -> sigma -> rho
    K a x = a
  S_(sigma,nu,rho) : (sigma -> nu -> rho) -> (sigma -> nu) -> sigma -> rho
    S f g x = f x (g x)
  C_(sigma,tau,rho) : (sigma -> tau -> rho) -> tau -> sigma -> rho
    C f a x = f x a
  W_(sigma,rho) : (sigma -> sigma -> rho) -> sigma -> rho
    W f x = f x x

Every displayed type belongs to the relational type system. In particular,
S never asks for an arrow with nonrelational output. I is only needed at
relational types, and could be defined as W K there; keeping it as a named
derived operation makes the algorithm easier to inspect. No minimality
claim about this basis is intended.

Algorithm
First eliminate inner lambdas. The body M of the remaining lambda x:sigma.M
is an applicative expression of relational type rho with no lambda nodes.
Its atoms can be variables, nonlogical constants, logical operator names,
or the fixed combinator names above. Define [x]M as follows.

1. M is x: use I. The output is relational, so x's type is relational here.
2. M is another variable or a constant: use K M, with x dropped from M's
   context by the actual de Bruijn renaming.
3. M is f a, where a has relational type nu: use S ([x]f) ([x]a).
4. M is f a, where a has nonrelational type tau:
   - a is x: tau=sigma, so use W ([x]f).
   - a is another variable or constant: use C ([x]f) a, dropping x from a.
   These exhaust the possible syntactic forms of a.

The algorithm terminates by structural recursion on M. It produces type
sigma -> rho and removes x; it never constructs an individual-valued map.
This works equally for e and opaque type variables in case 4.

Proof of the beta law
For any term b:sigma in the remaining context, prove

  ([x]M) b = M[b/x]

by structural induction. Cases 1 and 2 use I and K. Case 3 uses the S
identity followed by the two induction hypotheses and application
congruence. Case 4a uses W and the induction hypothesis for f; substitution
replaces a=x by b. Case 4b uses C and the induction hypothesis for f; a is
x-free. These are literal identities, not merely material biconditionals.

Obtaining the operations in the lambda-free calculus
For each required typed combinator, its right-hand side is an existing
finite applicative term with finitely many parameters and relational
output. Build the finite binder spine with Body.ofTerm at its terminal
output. Strong uniform comprehension supplies a closed representative;
all-type Intensionality supplies the literal application laws and uniqueness.
The existing modal-four derivation makes its boxed definition stable.
Thus the combinator definitions themselves are independent SC definitions:
their bodies contain no abstraction-template names or other combinators.
Logical operator objects can separately be named by their finite binder
bodies, as in the existing representation lemmas.

Why this helps
Instead of creating a different name for every lambda template and proving
coherence between those names after renaming and substitution, the source
compiler uses one fixed typed operation for each needed combinator instance.
Name allocation depends on types, not on arbitrary lambda bodies. Each
finite proof uses finitely many such instances; the finite conservative
definition theorem is the intended erasure mechanism.

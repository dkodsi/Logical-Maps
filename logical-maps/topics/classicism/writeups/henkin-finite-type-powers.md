# Finite power depths in the elementary Henkin presents

GPT-6 Astra, prompted by Daniel Kodsi, 30 October 2026. This uses the two constructions and full-present rigidity argument in [[elementary-henkin-presents]].

The continuum-closed model satisfies **SOAN but fails FTAN at host \(et\), height 1**. SOAN supplies every finite-arity relation on a real carrier. The failed FTAN clause asks for every subset of the **first power of that carrier** to be represented in its second canonical power. This is a further power depth, not a missing unary subset of the reals.

Both models also have the active arithmetic guard \(\Box I^*_e\). For the canonical e-number tower, the smaller model satisfies FTN height 0 and fails height 1; the larger satisfies heights 0 and 1 and fails height 2. These are fixed-source clauses, not positive full FTN schemas.

## 1. Exact-image rigidity

Write \(q:R\to H\) for the single projection of the full present. For a unary root relation \(G\) with current extension \(U\) and whole leaf extension \(V\),

\[
 \operatorname{Rigid}(G)\quad\Longleftrightarrow\quad V=q[U].
\tag{1}
\]

Persistence gives \(q[U]\subseteq V\). If \(b\in V\setminus q[U]\), use a root test with universal current row and leaf row \(H\setminus\{b\}\), admitted by singleton-complement comprehension. Every current \(G\)-member necessarily satisfies this test. Weak inextensibility would put \(G\) below it, contradicting \(b\in V\). Thus equality holds. This uses one test at a time, without assuming an aggregate code for \(q[U]\).

Conversely, exact-image transport gives current persistence and weak inextensibility against every root test. At terminal \(H\), both hold automatically, proving the leading boxes in native rigidity. The same argument applies to higher-type family predicates.

## 2. The entire canonical power transports bijectively

Let \(X\) be rigid, with current extension \(T\), and suppose \(q\) is injective on \(T\). Its leaf extension is \(X_H=q[T]\). A member of the actual canonical power

\[
 \mathsf P(X)=\lambda A\bigl(\operatorname{Rigid}(A)\land A\leq X\bigr)
\]

is exactly a pair \((U,h)\) with \(U\subseteq T\) and \(h\)'s leaf extension equal to \(q[U]\), by (1) and necessary support. Conversely every admitted leaf predicate supported on \(X_H\) has one such lift, using inverse image under the carrier bijection. Faithful extensionality of \(H\) and injectivity of \(q\) make that lift unique.

Projection therefore bijects the **whole canonical family**, not a selected subfamily, with all admitted leaf predicates supported on \(X_H\). Term naturality identifies the family's whole leaf component with the terminal canonical power, where all predicates are rigid. Its leaf extension is exactly its current image. Equation (1), one type higher, makes the family rigid; the bijection makes its current members necessarily distinct. This argument iterates through any specified finite height without assuming powerset fullness.

In particular each canonical power has at most as many current members as its leaf sort: at most \(\mathfrak c\) in the smaller model and at most \(\lambda=2^{\mathfrak c}\) in the larger.

## 3. Representation and its cardinal obstruction

For a carrier \(Y\) satisfying the preceding hypotheses, suppose every external subset of \(Y_H\) has an exact admitted leaf code. Every current predicate restriction to \(Y\) then has its canonical exact-image lift. At \(H\), any admitted predicate is represented by its intersection with \(Y_H\), using parameter comprehension. Together these local verifications prove the boxed universal-existential representation clause. They require no common choice of a witness across the two points. The canonical family is already rigid by section 2.

Hence if \(|Y(R)|=\mu\), this condition makes \(\mathsf P(Y)(R)\) the full external power, of size \(2^\mu\). It holds automatically when \(\mu\leq\aleph_0\) in the smaller construction and when \(\mu\leq\mathfrak c\) in the larger.

Conversely, if the canonical family has at most \(\kappa\) members while \(2^\mu>\kappa\), one subset of the current carrier has no representative. The root admits that missing subset as the current row of a predicate with leaf component bottom. The representation clause fails already now. This counts all canonical candidates, not merely the representatives used in one construction.

## 4. Failure at the next real-power depth

At host \(et\), both roots have

\[
 R_{et}=\mathcal P(\omega)\times\mathcal P(\omega),
 \qquad |R_{et}|=\mathfrak c.
\]

The seeded field makes the possible-Real antecedent active. Consider **any** proposed field for an FTAN consequent at this host. Full current predicates make its completeness external, so its real carrier has at least \(\mathfrak c\) points; the ambient domain bounds it by \(\mathfrak c\). Its rigid carrier and necessary distinctness give exact-image, injective transport. Thus all preceding lemmas apply to every candidate.

In the smaller root its first canonical power has at most \(\mathfrak c\) members, so cannot represent all \(2^{\mathfrak c}\) subsets of the real carrier. FTAN height 0 fails, as already follows from this model's SOAN failure.

In the larger root, every subset of the leaf real carrier has size at most \(\mathfrak c\) and has a code. Its first canonical power is therefore full of size \(\lambda\). The whole second canonical power, however, injects into a leaf sort of size at most \(\lambda\). It cannot represent all \(2^\lambda\) subsets of the first power. This directly refutes

\[
 \operatorname{RepPower}_1(\mathsf P^2(X),\mathsf P(X)),
\]

which is the height-1 FTAN clause. Every proposed field is defeated; allowing a different field at this height does not help. All powers stay at their correct higher types. Hence [[full-present-continuum-closed-henkin]] witnesses SOAN without FTAN. FTN also fails there, by AN and the recorded implication FTN + AN \(\to\) FTAN.

No necessary failure is asserted. Terminal \(H\) has its local canonical powers by comprehension, although its external powersets may be missing.

## 5. The active arithmetic tower

At the root the canonical e-numbers are precisely the standard successor orbit, as the full current orbit is an admitted inductive predicate. In \(F\) the canonical numbers are the ordinary Frege numerals; elementarity gives the same trace in \(H\), with every numeral term retained. Term naturality sends each root numeral to that same leaf numeral. The numerals are distinct, successor is injective and zero is not a successor at both points. Thus \(\Box I^*_e\) holds.

Projection bijects the number carriers, making numberhood rigid by (1). The preceding power lemmas now apply.

| Leaf closure | Canonical number carrier | Represented power sizes | First failed e-FTN height |
| --- | --- | --- | --- |
| Countable | \(\aleph_0\) | First power \(\mathfrak c\); second power has at most \(\mathfrak c\) members | 1: cannot represent all subsets of the first power |
| Continuum | \(\aleph_0\) | First power \(\mathfrak c\), second power \(\lambda=2^{\mathfrak c}\); third has at most \(\lambda\) members | 2: cannot represent all subsets of the second power |

Countable subset closure gives the positive height-0 clause in each model. Continuum subset closure additionally gives the larger model's height-1 clause. All include canonical-family rigidity and the full boxed representation condition, and the stated failures have the true necessary-infinity guard. The obstruction is a shortage of represented current subsets even though the canonical carriers remain rigid and transport injectively.

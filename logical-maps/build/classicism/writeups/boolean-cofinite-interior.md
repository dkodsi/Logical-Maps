# Boolean nonexpansive model: cofinite interior

Ordinary construction and proof from OpenAI Codex, prompted by Daniel Kodsi, *Observer separation with propositional completeness and divergent possibilities*, 25 October 2026, §4, independently expanded for integration on 28 October 2026. The scope is fixed C, at the first-coordinate evaluation. Metatheory: ZFC. No Lean or human certification is asserted.

The model has current propositional Atomicity and Boolean Completeness, full Barcan and full Relational Choice, while both necessary propositional Boolean Completeness and necessary propositional Barcan fail. It additionally has full logical observer separation, proved directly below; that principle has no native node yet. This is a current-versus-necessary separation, not a C5 model.

## 1. The complete Boolean algebra and its interior

Let $B=2\times\mathcal P(\mathbb N)$, with coordinatewise Boolean operations, and set

\[
j(\epsilon,A)=\left(\mathbf1_{(\epsilon,A)=\top},
 \begin{cases} A,&A\text{ cofinite},\\\varnothing,&\text{otherwise}.\end{cases}\right).
\tag{1}
\]

This preserves Top and finite meets, lies below its argument, and is idempotent. Its fixed points form the frame $O$ of opens: Bottom, Top, and $(0,A)$ for cofinite $A$. Opens are closed under arbitrary joins and finite meets; their meet is $j$ of the Boolean meet. At $t$ put

\[
\delta_t(p,q)=j(p\leftrightarrow q).
\tag{2}
\]

This is a separated $O$-valued equality: reflexive, symmetric and transitive, with $\delta_t(p,q)=\top$ iff $p=q$. At $e$ use a singleton with equality Top.

## 2. Admitted higher types and C soundness

Inductively let $D_{\sigma\tau}$ consist of **all** nonexpansive maps $f:D_\sigma\to D_\tau$:

\[
\delta_\sigma(x,y)\le\delta_\tau(fx,fy).
\]

Equip it with the open meet of the pointwise output equalities. Equivalently, at flattened relational type $\rho=\bar\sigma t$,

\[
\delta_\rho(f,g)=j\bigwedge_{\bar x}
      (f[\bar x]\leftrightarrow g[\bar x]). \tag{3}
\]

The two descriptions agree because inserting additional $j$ operations before an outer open meet does not change it. Evaluation is nonexpansive: an open bound on both the function and argument equalities bounds the output equality by transitivity. Currying is nonexpansive for the same reason, and uncurrying is nonexpansive by evaluation. Thus lambda abstraction and substitution remain within the admitted spaces.

Boolean operations are nonexpansive. Define quantifiers by the actual $B$-meet and $B$-join of an admitted predicate's range. If an open $u$ lies below every $F(x)\leftrightarrow G(x)$, it lies below the equivalence of their meets and of their joins; since $u$ is open it also lies below $j$ of those equivalences. Consequently the quantifier operations themselves are admitted nonexpansive maps.

The admitted predicate $z\mapsto\delta_\sigma(z,a)$ is nonexpansive by transitivity. Every predicate preserves the lower bound $\delta_\sigma(x,y)$, and this haecceity supplies the reverse bound. The defined Leibniz identity is therefore exactly $\delta_\sigma$, not an independently added crisp equality.

Truth at the initial evaluation is the first coordinate; truth at coordinate $n$ is membership of $n$ in the second coordinate. Each of these Boolean characters preserves every meet and join, so all typed quantifiers have their ordinary classical truth clauses. At each character, quotient each type by its true $\delta$-identity. Application and predicates descend by nonexpansivity, and the haecceities verify the identity clauses. These are ordinary H interpretations, including all admitted lambda terms. Their truth characters jointly separate $B$. Hence every H-provable equivalence has equal Boolean values at every assignment, and every H-provable coextension gives pointwise equal functions and thus identity Top by (3). This proves precisely C's theoremhood-restricted Logical Equivalence rule. It does not assume a dynamically enlarged rule.

At the initial evaluation, $\delta(x,y)$ is true iff $x=y$ as actual entities. Native necessity $p=\top$ is the operation $j(p)$. Thus all claims below use the native modality and identities.

## 3. The current structural package and observers

The current native order on propositions is exactly the Boolean order of $B$. This algebra is externally complete and atomic, with atoms $(1,\varnothing)$ and $(0,\{n\})$. Every actual extension of an admitted family has a Boolean meet; the quantifier truth clauses turn that witness into current BC_t. The same clauses give current Atomicity_t. The true atom $a_*=(1,\varnothing)$ witnesses Actuality.

Current BF holds at every type directly. If every $F(x)$ is necessary at the initial evaluation, each $j(Fx)$ has first coordinate 1 and hence each $Fx$ is Top. Their meet is Top, so $\forall x Fx$ is necessary. This checks the full Barcan schema without inferring any necessary version.

Every external current relation on any finite tuple of domains is represented by the function with value $a_*$ on that relation and Bottom elsewhere. To verify admission, observe that a change in its output is permitted only when its input tuple changes. Then the open equality of the input tuple has first coordinate 0 and lies below $(0,\mathbb N)=\delta_t(a_*,\bot)$. This proves nonexpansivity, including the curried formulation. An externally chosen selector graph for any current serial relation is consequently admitted. This proves full current Relational Choice, also for individual outputs; no individual-valued operation type is used.

For each $n$, the map

\[
E_n(\epsilon,A)=(\mathbf1_{n\in A},A) \tag{4}
\]

is an admitted nonexpansive Boolean map. Indeed equality of the inputs implies equality of the outputs; and whenever their tail sets differ finitely and agree at a coordinate $m$, the output tails do so too. It preserves arbitrary Boolean meets and joins, therefore every admitted typed quantifier. Function-space equality (3) turns these equalities into the required whole-operation identities. Identity distinguishes different first coordinates and the $E_n$ distinguish different tail sets. Actual functionality and repeated application lift this separation to arbitrary relational types. Thus full logical observer separation holds for every finite qualification list.

## 4. Failure of necessary propositional completeness

At coordinate $n$, two propositions are identical iff their tail sets differ finitely and agree in membership at $n$; their original first bits are immaterial. The quotient proposition algebra is

\[
2\times\bigl(\mathcal P(\mathbb N\setminus\{n\})/\mathrm{Fin}\bigr). \tag{5}
\]

Partition $\mathbb N\setminus\{n\}$ into infinitely many infinite blocks $A_i$. The classes $(0,[A_i])$ have no least upper bound. Any upper bound contains all but finitely many members of each $A_i$. Delete one point from its intersection with each block. The result is still an upper bound, but is strictly smaller modulo finite difference.

Crucially this is an **admitted** family at coordinate $n$. Let $S$ be exactly that set of quotient classes, and define $X_S(p)=(0,\{n\})$ when the local class of $p$ belongs to $S$, and Bottom otherwise. If two inputs are locally identical at $n$, their outputs agree. At any other coordinate the two possible outputs are locally identical, since $\delta_t((0,\{n\}),\bot)=(0,\mathbb N\setminus\{n\})$. Literal equality of inputs also preserves outputs. These coordinatewise facts give nonexpansivity, hence admission of $X_S$.

The local quantifier and identity clauses from §2 identify its upper bounds with the bounds in (5). Native BC is stated using greatest lower bounds: use the admitted complement-transformed family $Y(p)=X_S(\neg p)$. A greatest lower bound of $Y$ would complement to a least upper bound of $X_S$, which does not exist. Thus BC_t is false at coordinate $n$. If BC_t were necessary at the initial evaluation, its Boolean value would be Top by (1), which it is not. This proves $\neg\Box\mathrm{BC}_t$ there. We do not claim that $B$ itself lacks external joins: the failure occurs after passing to the local equality quotient.

## 5. Failure of necessary BF, and why the model is not C5

Fix $n$ and define an admitted predicate on propositions by

\[
F(\epsilon,A)=(1,f_n(A)),\qquad
f_n(A)=\begin{cases}
\mathbb N\setminus(A\setminus\{n\}),&A\text{ finite},\\
\mathbb N,&A\text{ infinite}.
\end{cases} \tag{6}
\]

For inputs locally identical at $m$, finiteness agrees, their output tails differ finitely, and those tails agree at $m$ (at $n$ both always contain $n$). Actual equality is also respected. Thus $F$ is nonexpansive. Every value $F(p)$ has cofinite tail containing $n$, so $j(Fp)$ is true at $n$. But $\bigwedge_p Fp=(1,\{n\})$, whose $j$-value is Bottom. Hence $\forall p\Box Fp$ is true and $\Box\forall p Fp$ false at coordinate $n$. As in §4, this refutes necessary BF_t at the initial evaluation.

Finally $a_*$ is distinct from Bottom at the initial evaluation, while $\delta_t(a_*,\bot)=(0,\mathbb N)$ is true at every tail coordinate. Current ND_t therefore fails. This is compatible with current BF and Atomicity_t; neither has been silently promoted to its necessary form.

The construction thus separates current BC_t from its necessary version even with current Atomicity_t, full BF, full Relational Choice, Actuality, and full logical observer separation. The last observer verdict is retained in this proof pending its native principle definition; no stronger observer or C5 flag is inferred.

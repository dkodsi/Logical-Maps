# Current completeness gives necessary transversals under Modalized Choice

Over C,
\[
BC_{\rm all}+MRC_{\rm all}\quad\Longrightarrow\quad\Box TC_{\rm all}.
\]
The completeness premise is current. At a fixed \(\sigma\), it suffices
to use \(BC_{\sigma t}\), \(MRC_{\sigma t,\sigma}\), and
\(IC_{\sigma\sigma t}\). Full MRC supplies the last instance by the
[universal-modal-selector theorem](modalized-relational-choice-implies-necessary-modalized-relational-choice.html).
In particular, the propositional target uses BC_tt, not BC_t.

## 1. Construct modal witnesses for current equivalences

First suppose \(\Box\operatorname{Equiv}(R)\). Call a property X
separated when
\[
\Box\forall x y(Xx\land Xy\land(Rx)y\to x=y).
\]
Define \((\Gamma B)x:=\forall y(By\land(Rx)y\to x=y)\). Algebraic
order gives
\[
A\le\Gamma B\quad\longleftrightarrow\quad
\Box\forall x y(Ax\land By\land(Rx)y\to x=y).
\]
Necessary symmetry of R therefore gives \(A\le\Gamma B\) iff
\(B\le\Gamma A\); separation of X is \(X\le\Gamma X\).
No optional equivalence is used as an input to Logical Equivalence.

The separated properties form a represented chain-complete poset under
algebraic order. Indeed, let J be the current Boolean join of a represented
chain D, using BC_(sigma t). For A,B in D, comparison and separation give
\(A\le\Gamma B\). Taking the join in A gives \(J\le\Gamma B\);
the displayed symmetry gives \(B\le\Gamma J\), and taking the join
in B gives \(J\le\Gamma J\). Thus J is separated. The empty join is
zero. Neither the family nor its join is assumed to remain a chain/join
at later evaluations; the final algebraic bound already asserts necessary
separation.

MRC_(sigma t,sigma) gives the universal necessarily functional membership
selector S from the cited theorem. Set
\[
M_X(y):=\neg\exists x(Xx\land(Rx)y),\quad
D_X(y):=M_X(y)\land(SM_X)y,\quad \Phi(X):=X\lor D_X.
\]
Necessarily D_X has at most one member and exactly one when M_X is
inhabited. Its members are unrelated to X. Hence Phi preserves separated
properties and is progressive in their algebraic order.

The [represented canonical-chain lemma](boolean-completeness-and-modalized-relational-choice-imply-necessary-transversal-choice.html#canonical-chain-lemma), applies to this chain-complete poset and the admitted operation
Phi. It uses only internal represented chains and entity-antisymmetric
order, so it requires no further choice. Obtain the entity identity
\(\Phi(X)=X\). Then \(D_X\le X\) and \(D_X\le M_X\), while
necessary reflexivity of R gives \(X\land M_X=0\). Thus D_X is
necessarily empty. Its necessary selection law makes M_X necessarily
empty too. Combined with separation, this says
\(\Box\operatorname{Tr}_R(X)\).

The fixed-point identity, rather than current coextension, is what rules
out a missed class at a later evaluation.

## 2. Remove the necessary-equivalence qualification

For arbitrary R define the admitted relation
\[
(\widehat R x)y:=
 (\operatorname{Equiv}(R)\land(Rx)y)
 \lor(\neg\operatorname{Equiv}(R)\land x=y).
\]
H proves it is an equivalence; its necessity is unconditional. Applying
§1 gives one X such that
\[
\Box(\operatorname{Equiv}(R)\to\operatorname{Tr}_R(X)). \tag{1}
\]
This uses only material agreement of R and its qualified replacement
where R is an equivalence, not their identity as entities.

## 3. Cover future inputs without Barcan

Use the following general profile argument. Let A have relational type
theta and suppose a formula Psi(A,b) is invariant under current
coextension of A by a C theorem. Under IC_theta,
\[
\forall A\exists b\Box\Psi(A,b)
\quad\Longrightarrow\quad\Box\forall A\exists b\Psi(A,b). \tag{2}
\]
Put Bad(A):=not exists b Psi(A,b), and totalize the property of bad inputs:
P(A):=Bad(A) or not exists A' Bad(A'). P is necessarily inhabited. IC
gives a necessarily singleton property G entailing P. Its admitted
relational profile is
\(\widehat A[\bar x]:=\exists A(GA\land A[\bar x])\).
At every accessible evaluation this is coextensive with G's unique
instance. Apply the left side of (2) once, to this current profile, and
obtain b with necessary Psi(hat A,b). At any accessible evaluation with
a bad input, G selects a bad A, but profile coextension and Psi(hat A,b)
contradict Bad(A). This proves (2). It selects no current entity preimage
for arbitrary future A and uses no BF.

Take theta=sigma sigma t and
Psi(R,X):=Equiv(R) implies Tr_R(X). This is extensionally invariant in R
by H. Apply (2) to (1), using precisely IC_(sigma sigma t), obtaining
necessary TC_sigma as asserted.

## 4. Consequences and preserved type bounds

Existing arrows give necessary Well-Ordering from necessary TC and Modal
Well-Ordering from necessary Well-Ordering plus IC. Thus, over C plus
current full BC, MRC and Modal Well-Ordering are equivalent. Only the
stronger necessary-TC edge is needed in the database.

The source also gives the sharper isolated bound
\(MRC_{(\sigma t)t,\sigma t}+BC_{(\sigma t)t}\to MWO_\sigma\):
apply §1 to coextension of sigma-properties to obtain a necessarily valid
representative predicate; use the same universal modal selector on
haecceity codes to select an object of each inhabited sigma-property.
The resulting relation chooses outside each nonfull predecessor property
and is necessarily coherent on coextensive predecessors. The material
union of its conforming well-orders is a necessarily valid well-order.
This sharp construction is retained with full details in the direct
source, §4; it is not needed as an additional database arrow or assumed
in §§1–3 above.

Neither current BC_t alone nor unrestricted MRC → Modal Well-Ordering is
established. The completeness premise has never been necessitated.

## Sources and review

Direct sources: OpenAI Codex, prompted by Daniel Kodsi, *Modal transversals from current Boolean
completeness*, 26 October 2026, §§1–4, and *Transferring modal witnesses
through relational profiles*, 26 October 2026, §§1–3; unpaginated.
The represented canonical-chain lemma is independently supplied in the
separate supporting note. Dorr's chooser-of-orders theorem and the
existing TC/Well-Ordering arrows keep their original attribution. This
consolidation independently checks the separation adjunction, current
chain joins, modal selector and profile-transfer proof. Ordinary AI
review, not human or Lean certification.


<a id="canonical-chain-lemma"></a>

## Appendix: represented canonical-chain lemma

The supporting proof below retains its original internal section numbering.

**Lemma.** Let P^{ρt} carry a represented antisymmetric partial order, have a least element 0, and have a LUB in P for every represented chain, including the empty chain. Let f be a represented total single-valued graph from P to P with x≤f(x) for every x∈P. Then f has a fixed point.

The proof uses only predicate comprehension and ordinary quantification admitted in C. In particular it does not assume an external set of ordinals, standard finiteness, an operation representing f, or extensionality of property entities.

Call a predicate C^{ρt} an **f-chain** when:

1. C⊆P and the inherited order well-orders C: every admitted nonempty subproperty of C has a least member.
2. For each x∈C, x is the LUB in P of the graph image

       { f(y): y∈C and y<x }.                          (6)

Condition 2 is a formula about being a LUB; it does not presume this image has a LUB before the condition is asserted. The singleton {0} is an f-chain. If x<y lie in an f-chain, then f(x)≤y by (6).

**Comparison.** Any two f-chains C,D are comparable by initial segment. Define I to consist of those common members x for which the C- and D-predecessor properties below x are coextensive. I is an initial segment of both C and D: if x∈I and y<x lies in either chain, then y lies in both, and the predecessor properties below y are equal in extension as subsets of their common predecessor property below x.

If both C\I and D\I were nonempty, let c,d be their respective least members. Their predecessor properties are each coextensive with I. The graph images in (6) are therefore coextensive. Since an antisymmetric poset has at most one LUB for a given actual family, c=d. This equality and equality of their predecessor extensions place c in I, contradiction. Hence C≡I or D≡I (actual coextension), proving comparison by initial segment. Notice that equality of predicate codes was never inferred from coextension; only uniqueness of their order-theoretic LUB was used.

**Union.** Define the admitted property

    A(x):=∃C^{ρt}(C is an f-chain ∧ Cx).

Comparison makes A a chain. It is internally well-ordered: given any nonempty represented X⊆A, choose x∈X and an f-chain C containing x. Let m be the least member of X∩C. For any z∈X, choose an f-chain D containing z. If D is an initial segment of C, then z∈C and m≤z. If C is an initial segment of D, then either z∈C, giving the same conclusion, or z lies strictly above every member of C, including m. Thus m is least in X.

For x∈A choose an f-chain C containing x. Comparison shows that A and C have the same predecessor extension below x. Condition (6) for C therefore gives it for A, again using only actual coextension of the represented images. Hence A is itself an f-chain, and it contains every f-chain by definition.

**The supremum is a fixed point.** Let u be the LUB of A in P. If u∉A, then A has no largest member. For every x∈A choose y∈A with x<y; (6) gives f(x)≤y≤u. Conversely x≤f(x) for each x, so any upper bound of f[A] bounds A. Therefore u is the LUB of f[A]. Adjoining u at the end of A gives another f-chain: its new predecessor property is A, and the defining LUB condition is the one just proved. This contradicts the definition of A, which would then contain u. Thus u∈A.

If u<f(u), adjoining f(u) at the end of A again gives an f-chain. Its new LUB condition holds because f(u) is the greatest member of f[A]: for x<u in A, (6) gives f(x)≤u≤f(u), and f(u) itself is in that image. Again the definition of A would put f(u) into A, contradicting u being an upper bound. Progressivity leaves f(u)=u. This proves the lemma.


Source: OpenAI Codex, prompted by Daniel Kodsi, represented canonical-chain proof of 22 October 2026, §5, unpaginated; expanded comparison proof of 28 October 2026. Ordinary mathematical proof; no new Lean certification.

# Finite-support action model: single-flip sections and projection

Direct source: OpenAI Codex, prompted by Daniel Kodsi, *Admissible replacement witnesses for four completeness separations*, 28 October 2026, §§1–3 and 5, unpaginated. Independently checked and simplified for integration the same day. The semantic framework is Bacon and Dorr, *Classicism*, Appendix D, Definitions D.1–D.3 and Proposition D.4, pp. 73–74, as in the native sections-and-projection model. The restricted category below is a new construction; no preservation theorem for arbitrarily deleting worlds is assumed. No human or Lean certification is claimed.

## 1. The category

Take $W_0=\mathbb N$ and $W_1=\mathbb N\times\{0,1\}$ as individual domains. Let $f_*(n)=(n,0)$ and let $f_k$ differ from $f_*$ only at $k$, where it takes value $(k,1)$. Put $\pi(n,i)=n$ and $e_j=f_j\pi$, with $j\in\{*\}\cup\mathbb N$. The arrows are

- $W_0\to W_0$: identity;
- $W_0\to W_1$: all $f_j$;
- $W_1\to W_0$: only $\pi$;
- $W_1\to W_1$: identity and all $e_j$.

They are closed under composition because $\pi f_j=1$, $e_i f_j=f_i$, $e_i e_j=e_i$ and $\pi e_j=\pi$. Use the ideally-full hierarchy of all finitely pinned intensions, with no extra symmetry restriction, and evaluate at $1_{W_0}$. Each object has the finite-set ideal, so the standard soundness theorem applies to this category at every original relational type.

Pinning is equality of **whole transports** along parallel arrows agreeing on the finite pin. For an intension $F$, $(h\cdot F)_k=F_{kh}$; the computations below check every possible $k$, not merely the first extension row.

## 2. Full current ND and propositional Atomicity

Every arrow out of $W_0$ has a left inverse: $\pi$ retracts every $f_j$. By functoriality at every type, equality of $f_j\cdot X$ and $f_j\cdot Y$ implies $X=Y$. Thus full current ND holds.

A root proposition is an independently chosen truth value at $1_{W_0}$ together with one of these section parts:

- a finite set of single-flip arrows $f_k$, excluding $f_*$;
- $f_*$ together with a cofinite set of the single-flip arrows.

Indeed, outside a finite pin $S$, every $f_k$ agrees with $f_*$ on $S$, so they have the same truth value. Conversely the finite set of exceptions pins a displayed pattern. If two sections agree there, postcomposition by identity tests their displayed values, postcomposition by $\pi$ sends both to $1_{W_0}$, and postcomposition by $e_i$ sends both to $f_i$. These exhaust all whole-transport comparisons.

The atoms are therefore $a_0=\{1_{W_0}\}$ and $b_k=\{f_k\}$. Every nonzero proposition contains one of them, proving Atomicity_t. This Boolean algebra is $2$ times the finite/cofinite algebra on $\mathbb N$; the limit section $f_*$ is not an additional isolated atom.

## 3. The missing join is an admitted family

Define $X:tt$ by the root row $X_1=\{b_{2n}:n\in\mathbb N\}$ and empty rows at every section. This is **empty-pinned**. For any two sections $f_i,f_j$, their transported $X$ rows agree at every tail arrow: both are empty at identity; both are the even-atom family at $\pi$ because $\pi f_i=\pi f_j=1$; and both are empty at every $e_k$ because $e_k f_i=e_k f_j=f_k$. All comparisons have the same target-domain arguments. There is only one root-target arrow. Ideal fullness therefore admits this higher-type family.

Every upper bound for its current members contains infinitely many even sections, so its section part is cofinite and contains $f_*$. It contains an odd section $f_{2m+1}$. Deleting the admitted singleton $b_{2m+1}$ gives a strictly smaller upper bound. Thus $X$ has no least upper bound. The admitted family $Y(p)=X(\neg p)$ has no greatest lower bound, since such a bound would complement to a join of $X$. This is failure of native BC_t.

It also refutes full Boolean Completeness and full Weak Rigid Comprehension, by the existing typed implications; in particular the native [Weak Rigid Comprehension implies Boolean Completeness](weak-rigid-comprehension-r-implies-boolean-completeness-r.html) theorem proves the propositional join form using its $tt$ comprehension instance. No conjecture is used.

## 4. Modal scope and an additional checked flag

The tail singleton $c=\{1_{W_1}\}$ is admitted, pinned by $\{(0,0),(0,1)\}$: no $e_j$ agrees with identity on both points. Whole pinning follows because equal section patterns on the first-coordinate projections remain equal under postcomposition; the identity case is isolated by that pair. It is nonzero but becomes Bottom along $\pi$. Thus ND_t fails at $W_1$ and necessary ND_t fails at the root. Current ND has not been upgraded to C5.

Strong Actuality nevertheless holds at both objects. The true root singleton $a_0$ becomes $\{\pi\}$ along any section. This is an atom at $W_1$, the only arrow there with target $W_0$; its further shifts are $a_0$ along $\pi$ and itself along each $e_j$. The true tail singleton $c$ becomes Bottom along every nonidentity arrow out of $W_1$. Hence both true singletons necessarily decide every proposition. This independently checked consequence gives necessary Strong Actuality at the root, strengthening the replacement witness without altering its completeness failure.

The proof restores the lost Atomicity_t + ND_t separations using this new model. It does not restore the withdrawn full-completeness failure at the old/new model's original $E$ evaluation.

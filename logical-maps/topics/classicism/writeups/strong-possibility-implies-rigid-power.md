# Pure Strong Possibility forces rigid relations to be Frege-finite

At a pure Strong Possibility point, the current extension of every rigid relation has a Frege finite cardinality. Consequently Rigid Power holds. If Tame Rigidity also holds there, then Weakly Rigid Power holds. The count can be nonstandard. The argument applies to every finite argument tuple, including the empty tuple.

Write $\mathrm{SA}$ for Strong Actuality. For a relation $F$ on a tuple of types $\bar\sigma$, write $\mathrm{Fin}(F)$ for the assertion that some current Frege number counts the property of being the tuple-haecceity of an $F$-tuple. This is one formula for each fixed arity. Tuple-haecceities are necessarily injective in their coordinates. [Internally finite bounds](../index.html#background/rigidity/internally-finite-rigid-power)

## A pure sentence consistent with ordinary Maximalism

Fix $\bar\sigma$ and consider the closed pure sentence
$$
 \Psi_{\bar\sigma} =
 \forall F^{\bar\sigma t}\bigl(\mathrm{Rigid}(F)\to
             \Box(\neg\mathrm{SA}\to\mathrm{Fin}(F))\bigr).
$$
The coalesced Maximalist point with finite descriptor support satisfies this sentence. Its only root loop is the identity. The proposition true just at that identity is a true strong atom, so $\mathrm{SA}$ holds there. For every weakly rigid $F$ at that root there are finitely many actual tuples $\bar a_1,\ldots,\bar a_m$ such that at every proper arrow $h$ the entire relation $hF$ is the union of the tuple-haecceities of $h\bar a_1,\ldots,h\bar a_m$. This includes old postcomposites. The current extension at such an arrow therefore has an ordinary finite number of tuples, possibly fewer than $m$ through coincidences. Its tuple codes have an actual Frege count. These two cases give the box in $\Psi_{\bar\sigma}$. The auxiliary symbols used to construct the point do not occur in $\Psi_{\bar\sigma}$. [Maximalist finite-descriptor model](coalesced-finite-support-rigid-root.html)

## The return

Let $r$ satisfy pure Strong Possibility. The strong-atom obstruction gives $r\models\neg\mathrm{SA}$. Suppose $F$ is rigid at $r$ and has no current Frege finite count. Then $q=\neg\mathrm{SA}\land\neg\mathrm{Fin}(F)$ is a true proposition at $r$. The schema applies to the closed pure $\Psi_{\bar\sigma}$ and gives $\Diamond_{\ne}\Psi_{\bar\sigma}$. Testing with this particular $q$ gives arrows $r\to v\to z$ such that $\Psi_{\bar\sigma}$ holds at $v$ and the transported $q$ holds at $z$. Rigidity persists, so the image of $F$ at $v$ is rigid. Since $\mathrm{SA}$ fails at $z$, the box in $\Psi_{\bar\sigma}$ gives $\mathrm{Fin}(F)$ there for the very same transported relation. This contradicts $q$. [Strong-atom obstruction](../index.html#result/strong-possibility-and-strong-actuality-incompatible)

The internally finite bound theorem now gives $\Box\mathrm{Fin}(F)$ and the identity and rigidity of the canonical full and weak powers of $F$. This proves Rigid Power. Under local Tame Rigidity it also applies to every current weakly rigid $F$, proving Weakly Rigid Power. Thus at a pure Strong Possibility point Tame Rigidity and Weakly Rigid Power are equivalent, using the established converse in C. [Finite-bound induction and tuple coding](../index.html#background/rigidity/internally-finite-rigid-power)

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, found the argument on 27 November 2026. Two other GPT-6 research agents independently reviewed it.

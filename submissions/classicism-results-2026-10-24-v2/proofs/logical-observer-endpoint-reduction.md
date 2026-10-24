# Omitting endpoint-fixing clauses from logical observer separation

Ordinary mathematical argument by OpenAI Codex, 24 October 2026. Direct source: misc, this note, §§1–4, unpaginated. This supplies an equivalence with the earlier definition; it is not a new formal certificate. Earlier source proofs and certificate statements retain their original scope.

## 1. The revised qualification

Let $\mathrm{Good}^{+}_{\Delta}(E)$ be the qualification in [Logical Observer Separation](logical-observers.md), §1. Define $\mathrm{Good}_{\Delta}(E)$ by deleting only

$$
E\top=\top,\qquad E\bot=\bot.
$$

Retain the full operation identities for negation, conjunction, disjunction, and both quantifiers at every type in the finite list $\Delta$. Retain translated reflexivity and Leibniz substitution at those types. This change does not remove the separate range restriction $\mathrm{End}(E)$ used for endpoint-valued observers.

Use the fixed H abbreviations $a:=\forall p^t p$, $\top:=a\lor\neg a$, and $\bot:=a\land\neg a$. Boolean preservation gives

$$
E\top=Ea\lor\neg Ea,\qquad E\bot=Ea\land\neg Ea.
$$

Consequently H proves that every newly qualified observer makes $E\top$ true and $E\bot$ false. These are truth claims; H alone need not identify the outputs with the endpoints.

Over C, the Boolean identities identify the right sides with $\top$ and $\bot$. Hence C proves $\mathrm{Good}_{\Delta}(E)\leftrightarrow\mathrm{Good}^{+}_{\Delta}(E)$. This derivation needs no BF. Already over H, adding $\mathrm{End}(E)$ gives the same equivalence: each output at an endpoint must itself be an endpoint, and its truth value rules out the wrong one.

## 2. Full separation over H is unchanged

Let OS use the revised qualification and let $\mathrm{OS}^{+}$ use the earlier qualification. Both are full typed schemas, with each tested type list finite.

The H-proof transport argument in [Logical Observer Separation](logical-observers.md), §3, still applies to the revised qualification. Propositional tautologies are transported using Boolean commutation; the quantifier axioms and rules use the corresponding quantifier identities; reflexivity and Leibniz steps use the retained equality clauses. Conversion steps use translated reflexivity and ordinary H substitution. The endpoint truth facts in §1 suffice wherever the fixed abbreviations for truth or falsity occur. No step needs their outputs to be identical to the endpoints.

Thus, for every H theorem $P$, a finite list $\Delta$ containing the types used in its proof suffices to establish $\mathrm{Good}_{\Delta}(E)\to EP$, with $E$ fresh. If H proves $P\leftrightarrow Q$, all such observers agree in truth on $P$ and $Q$. Applying full typed separation to the corresponding abstractions gives

$$
(\lambda\bar z.P)=(\lambda\bar z.Q).
$$

These are the Logical Equivalence instances defining C. Therefore H + OS yields C. Section 1 now identifies the old and new qualifications, so it also yields $\mathrm{OS}^{+}$.

Conversely, $\mathrm{Good}^{+}_{\Delta}$ is a subclass of $\mathrm{Good}_{\Delta}$ already over H. Agreement under every newly qualified observer implies agreement under every old one; $\mathrm{OS}^{+}$ therefore gives OS. The two full theories over H are equivalent.

This does not identify the two observer classes in bare H. Nor does the argument recover C from a single propositional separation instance.

## 3. The BF proof uses endpoint acceptance and quantifier commutation

Fix $\sigma$ in the tested list and suppose $\forall x^\sigma(Fx=\top)$. For each qualified $E$, substitution gives $E(Fx)=E\top$ for every $x$. Section 1 makes $E\top$ true, so $\forall x\,E(Fx)$ is true. Universal commutation makes $E(\forall x\,Fx)$ true as well.

Every eligible observer therefore agrees in truth on $\forall x\,Fx$ and $\top$. Propositional separation identifies them, giving BF at $\sigma$ after discharging the supposition.

No equality clause is needed for this BF argument. Universal commutation is needed: fixing or accepting $\top$ alone gives no inference from $\forall x\,E(Fx)$ to $E(\forall x\,Fx)$. No optional hypothesis has been necessitated.

## 4. Scope of the retained results

All established full restricted separation schemas imply ordinary OS by inclusion of observer classes. They therefore recover C, where the two qualifications agree. This preserves the endpoint, reversible, involutive, idempotent, finite-image and identity-fixing separation results, including definitions of reversibility that require a qualified inverse. The same argument preserves the separately boxed schema comparisons by necessitating the discharged finite implication proofs.

The fixed-type factive-separation argument over H uses negation preservation and the identity observer and remains unchanged. Its Fregean/universal-factivity converse needs only the endpoint truth facts from §1. Full OS with uniqueness still gives Extensionality; conversely Extensionality upgrades those endpoint truth facts to endpoint identities and identifies every qualified observer with identity.

The restriction $\mathrm{End}$ itself is unchanged, and even its qualified observer class agrees with the earlier one over H. Other standalone qualification claims over bare H must retain the distinction between $\mathrm{Good}$ and $\mathrm{Good}^{+}$.

The original source proofs, saved manifests and exact certificate maps are preserved. Existing certificates refer to $\mathrm{Good}^{+}$; the shorter current definition is connected to them by this ordinary mathematical equivalence proof.

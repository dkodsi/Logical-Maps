# Tame Rigidity ∧ Rigid Power ⇒ Weakly Rigid Power

<p class='cert'>Conjecture — Source: Misc.; produced by Cian Dorr, question of 10 October 2026; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 10 October 2026.</p>

## Premises

- **Tame Rigidity.** Every weakly rigid relation, including a proposition, is rigid.
- **Rigid Power.** If a relation is rigid, so is the property of being a rigid relation that entails it.

## Conclusion

- **Weakly Rigid Power.** If a relation is weakly rigid, so is the property of being a weakly rigid relation that entails it.

## Notes

The converse of weakly-rigid-power-implies-tame-rigidity and weakly-rigid-power-implies-rigid-power. With □Tame Rigidity in place of Tame Rigidity it is proved (necessary-tame-rigidity-and-rigid-power-imply-weakly-rigid-power). The unboxed argument fails at weak inextensibility: for weakly rigid $F$, $P_F:=\lambda X\, .\,\operatorname{WeaklyRigid}(X)\land X\le F$ is weakly persistent, but $Z:=\lambda X\, .\,\operatorname{Rigid}(X)\land X\le F$ satisfies $\forall X\, .\,P_FX\to\Box ZX$, so the weak inextensibility of $P_F$ requires $P_F\le Z$, which is Tame Rigidity below $F$ at every accessible world. Weakly Rigid Power implies □Tame Rigidity at type $t$ (and, with BF, at every type: barcan-and-weakly-rigid-power-imply-necessary-tame-rigidity), so the conjecture would follow from Tame Rigidity + Rigid Power ⇒ □Tame Rigidity, and a countermodel must satisfy Tame Rigidity and Rigid Power while failing □Tame Rigidity at type $t$. No recorded model yet separates Tame Rigidity from □Tame Rigidity.

Research update of 23 October 2026: the FULL all-type unboxed TR+RP⇒WRP question remains unresolved. The completed ColourCollapse central_countermodel satisfies full root TR, full boxed BF and boxed RP_et, and fails WRP_et; its power properties have type (et)t. No all-type RP premise is supplied. This supersedes the earlier claim that no separation between root and future tameness was known, but does not settle this record. The obstruction is bounded future tameness: below a transported rigid universal unary relation a weakly rigid, nonrigid relation appears at B; the weak-power property at A cannot satisfy weak inextensibility. The displayed completion establishes an et failure, not a t failure. Any use of the older t-specific guidance must retain that distinction. The finite/cofinite or Boolean-fragment arguments do not supply rigidity of the property collecting all higher-type subrelations. See the matching write-up for the exact completed certificate and remaining all-type obligation. New research attribution is misc; Dorr’s original question and date are retained.

## Revisions

- **2026-10-23** (Codex (OpenAI), prompted by Daniel Kodsi) — Updated the stale countermodel guidance using the completed full-TR/full-boxed-BF/boxed-RP_et/not-WRP_et certificate. The full all-type RP premise remains unverified, so the original conjecture is unchanged.

## Sources

- **Dorr 10 Oct** — Cian Dorr, question of 10 October 2026.
- **Kodsi research handoff 23 Oct** — Original research by Codex (OpenAI), prompted by Daniel Kodsi, 22–23 October 2026, notes/colour-collapse-entrance.md, §§1–7, and notes/rigidity-by-joins-and-boolean-closure.md, §§5–6 (unpaginated); final verification-updates/colourcollapse_completion.json, completed 23 October 2026.

<p class='cert'>Record: <code>topics/classicism/results/tame-rigidity-and-rigid-power-imply-weakly-rigid-power.yaml</code></p>

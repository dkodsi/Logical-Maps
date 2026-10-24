import Classicism.Results.Research.RelationalLambdaDecodingLaws

/-!
# The C-side syntactic roundtrip of relational bracket compilation

Original research, misc, Codex (OpenAI), prompted by Daniel Kodsi,
23 October 2026. Direct source: the typed reconstruction argument in
`research/2026-10-23/operator-characterizations/lambda-free-classicism-reconstruction-proof.txt`,
sections 3 and 8 (unpaginated).

The decoder interprets the five combinators by actual typed lambda terms
and restores each source logical/nonlogical atom to its original constructor.
Its interpretation of raw combinator equality is actual `Meta.Conv`, proved
from beta steps and congruence. Fresh-argument bracket beta, lambda
congruence, and eta therefore give the abstraction case of the roundtrip.

The final theorem covers every actual `Meta.Term` constructor, at every
signature and free-variable context, with all types unchanged. It neither
postulates a C-derivability interface nor uses an e-valued arrow. In this
roundtrip the type-indexed logical constants are restored literally; no
delta equation is needed. Full C proof transport, the opposite B-side
object-identity roundtrip, and finite-name erasure are separate modules.
Identifying this opaque-atom decoder with independently reconstructed
logical-operation witnesses in the full dossier's j+ is a separate obligation.

Prepared for the shared verification runner; this source file does not
claim compiler acceptance or a generated database certificate.
-/

namespace Classicism.Research.RelationalLambdaDecoding
open Classicism.Meta (Ty RTy Ctx Signature Conv)
open RelationalLambdaCompilation (Atoms compile)

variable {Sig : Signature}

/-- The raw bracket beta law becomes a beta conversion of actual source
terms, with capture-avoiding instantiation interpreted literally. -/
theorem decode_bracket_beta {Γ : Ctx} {σ : Ty} {ρ : RTy}
    (M : RelationalBracketAbstraction.Term (Atoms Sig) (σ :: Γ) ρ)
    (a : RelationalBracketAbstraction.Term (Atoms Sig) Γ σ) :
    Conv (.app (decode M.bracket) (decode a))
      ((decode M).instantiate (decode a)) := by
  have h := equal_conv (RelationalBracketAbstraction.Term.bracket_beta M a)
  simp only [decode] at h
  rw [decode_inst] at h
  exact h

/-- Decoding implemented bracket abstraction recovers actual lambda
abstraction up to beta/eta conversion. The proof uses the proved fresh-
argument identity, not a local extensionality or derivability assumption. -/
theorem decode_bracket {Γ : Ctx} {σ : Ty} {ρ : RTy}
    (M : RelationalBracketAbstraction.Term (Atoms Sig) (σ :: Γ) ρ) :
    Conv (decode M.bracket) (.lam (decode M)) := by
  have h := equal_conv (RelationalBracketAbstraction.Term.bracket_fresh_beta M)
  simp only [decode] at h
  rw [decode_wk] at h
  exact Conv.trans (Conv.symm (Conv.eta (decode M.bracket))) (Conv.lam_congr h)

/-- The C-side syntactic roundtrip, for every original typed term.
All original constants, including unsaturated logical and type-indexed
ones, return literally. Only the lambda case needs beta/eta conversion. -/
theorem decode_compile {Γ : Ctx} {σ : Ty}
    (M : Classicism.Meta.Term Sig Γ σ) :
    Conv (decode (compile M)) M := by
  induction M with
  | var v =>
      simp only [compile, decode]
      exact Conv.refl _
  | const c =>
      simp only [compile, decode, decodeBasis, decodeAtom]
      exact Conv.refl _
  | app f a ihf iha =>
      simpa only [compile, decode] using Conv.app_congr ihf iha
  | lam b ih =>
      simpa only [compile] using
        Conv.trans (decode_bracket (compile b)) (Conv.lam_congr ih)
  | and =>
      simp only [compile, decode, decodeBasis, decodeAtom]
      exact Conv.refl _
  | or =>
      simp only [compile, decode, decodeBasis, decodeAtom]
      exact Conv.refl _
  | not =>
      simp only [compile, decode, decodeBasis, decodeAtom]
      exact Conv.refl _
  | all σ =>
      simp only [compile, decode, decodeBasis, decodeAtom]
      exact Conv.refl _
  | ex σ =>
      simp only [compile, decode, decodeBasis, decodeAtom]
      exact Conv.refl _
  | eq σ =>
      simp only [compile, decode, decodeBasis, decodeAtom]
      exact Conv.refl _
  | constR ρ =>
      simp only [compile, decode, decodeBasis, decodeAtom]
      exact Conv.refl _
  | negR ρ =>
      simp only [compile, decode, decodeBasis, decodeAtom]
      exact Conv.refl _
  | andR ρ =>
      simp only [compile, decode, decodeBasis, decodeAtom]
      exact Conv.refl _
  | orR ρ =>
      simp only [compile, decode, decodeBasis, decodeAtom]
      exact Conv.refl _
  | coextR ρ =>
      simp only [compile, decode, decodeBasis, decodeAtom]
      exact Conv.refl _
  | boxR ρ =>
      simp only [compile, decode, decodeBasis, decodeAtom]
      exact Conv.refl _
  | inclR ρ =>
      simp only [compile, decode, decodeBasis, decodeAtom]
      exact Conv.refl _

#print axioms decode_bracket_beta
#print axioms decode_bracket
#print axioms decode_compile

end Classicism.Research.RelationalLambdaDecoding

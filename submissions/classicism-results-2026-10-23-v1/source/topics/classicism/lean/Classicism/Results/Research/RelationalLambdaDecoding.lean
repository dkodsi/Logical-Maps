import Classicism.Results.Research.RelationalLambdaCompilation
import Classicism.Syntax.Conversion

/-!
# Decoding relational bracket terms into the original lambda syntax

Original research implementation, misc, 23 October 2026, by Codex (OpenAI),
prompted by Daniel Kodsi. Original logical and nonlogical atoms decode to
their exact source constructors. The five typed basis constants decode to
closed lambda terms admitted by the relational type system.

The coherence results below are literal equalities of syntax. They do not
assume an interpretation of the combinator laws or an object-level rule
of abstraction congruence. Conversion laws and the compiler round trip are
separate consumers of this decoder.
-/

namespace Classicism.Research.RelationalLambdaDecoding

open Classicism.Meta (Ty RTy Ctx Signature Ren)
open RelationalLambdaCompilation (Atoms)
open RelationalBracketAbstraction (BasisConst)

variable {Sig : Signature}

/-- Recover the original constant constructor, without introducing a new
nonlogical name for a logical constant. -/
def decodeAtom {Γ : Ctx} : {σ : Ty} → Atoms Sig σ → Classicism.Meta.Term Sig Γ σ
  | _, .nonlogical c => .const c
  | _, .and => .and
  | _, .or => .or
  | _, .not => .not
  | _, .all σ => .all σ
  | _, .ex σ => .ex σ
  | _, .eq σ => .eq σ
  | _, .constR ρ => .constR ρ
  | _, .negR ρ => .negR ρ
  | _, .andR ρ => .andR ρ
  | _, .orR ρ => .orR ρ
  | _, .coextR ρ => .coextR ρ
  | _, .boxR ρ => .boxR ρ
  | _, .inclR ρ => .inclR ρ

/-- Closed lambda realizations of I, K, S, C and W. In particular, the
unrestricted input types of C and W never create an individual-valued
operation: every lambda body has a relational output type. -/
def decodeBasis {Γ : Ctx} : {σ : Ty} → BasisConst (Atoms Sig) σ →
    Classicism.Meta.Term Sig Γ σ
  | _, .original a => decodeAtom a
  | _, .I _ => .lam (.var .zero)
  | _, .K _ _ => .lam (.lam (.var (.succ .zero)))
  | _, .S _ _ _ =>
      .lam (.lam (.lam
        (.app (.app (.var (.succ (.succ .zero))) (.var .zero))
          (.app (.var (.succ .zero)) (.var .zero)))))
  | _, .C _ _ _ =>
      .lam (.lam (.lam
        (.app (.app (.var (.succ (.succ .zero))) (.var .zero))
          (.var (.succ .zero)))))
  | _, .W _ _ =>
      .lam (.lam
        (.app (.app (.var (.succ .zero)) (.var .zero)) (.var .zero)))

/-- Decode raw applicative syntax, preserving its variables and applications. -/
def decode : {Γ : Ctx} → {σ : Ty} →
    RelationalBracketAbstraction.Term (Atoms Sig) Γ σ →
    Classicism.Meta.Term Sig Γ σ
  | _, _, .var v => .var v
  | _, _, .const c => decodeBasis c
  | _, _, .app f a => .app (decode f) (decode a)

/-- Decode each value of a raw simultaneous substitution. -/
def decodeSub {Γ Δ : Ctx}
    (s : RelationalBracketAbstraction.Sub (Atoms Sig) Γ Δ) :
    Classicism.Meta.Sub Sig Γ Δ :=
  fun σ v => decode (s σ v)

@[simp] theorem decodeAtom_rename {Γ Δ : Ctx} {σ : Ty}
    (r : Ren Γ Δ) (a : Atoms Sig σ) :
    (decodeAtom (Γ := Γ) a).rename r = decodeAtom (Γ := Δ) a := by
  cases a <;> rfl

@[simp] theorem decodeAtom_subst {Γ Δ : Ctx} {σ : Ty}
    (s : Classicism.Meta.Sub Sig Γ Δ) (a : Atoms Sig σ) :
    (decodeAtom (Γ := Γ) a).subst s = decodeAtom (Γ := Δ) a := by
  cases a <;> rfl

@[simp] theorem decodeBasis_rename {Γ Δ : Ctx} {σ : Ty}
    (r : Ren Γ Δ) (c : BasisConst (Atoms Sig) σ) :
    (decodeBasis (Γ := Γ) c).rename r = decodeBasis (Γ := Δ) c := by
  cases c with
  | original a => exact decodeAtom_rename r a
  | I ρ => rfl
  | K σ ρ => rfl
  | S σ τ ρ => rfl
  | C σ τ ρ => rfl
  | W σ ρ => rfl

@[simp] theorem decodeBasis_subst {Γ Δ : Ctx} {σ : Ty}
    (s : Classicism.Meta.Sub Sig Γ Δ) (c : BasisConst (Atoms Sig) σ) :
    (decodeBasis (Γ := Γ) c).subst s = decodeBasis (Γ := Δ) c := by
  cases c with
  | original a => exact decodeAtom_subst s a
  | I ρ => rfl
  | K σ ρ => rfl
  | S σ τ ρ => rfl
  | C σ τ ρ => rfl
  | W σ ρ => rfl

/-- Literal renaming coherence; no conversion relation is needed. -/
theorem decode_rename {Γ Δ : Ctx} {σ : Ty} (r : Ren Γ Δ)
    (M : RelationalBracketAbstraction.Term (Atoms Sig) Γ σ) :
    decode (M.rename r) = (decode M).rename r := by
  induction M with
  | var v =>
      simp only [RelationalBracketAbstraction.Term.rename, decode,
        Classicism.Meta.Term.rename_var]
  | const c =>
      simp only [RelationalBracketAbstraction.Term.rename, decode, decodeBasis_rename]
  | app f a ihf iha =>
      simp only [RelationalBracketAbstraction.Term.rename, decode,
        Classicism.Meta.Term.rename_app, ihf, iha]

theorem decode_wk {Γ : Ctx} {σ τ : Ty}
    (M : RelationalBracketAbstraction.Term (Atoms Sig) Γ τ) :
    decode (M.wk (σ := σ)) = (decode M).weaken (τ := σ) :=
  decode_rename Classicism.Meta.Ren.shift M

/-- Literal simultaneous-substitution coherence. -/
theorem decode_subst {Γ Δ : Ctx} {σ : Ty}
    (s : RelationalBracketAbstraction.Sub (Atoms Sig) Γ Δ)
    (M : RelationalBracketAbstraction.Term (Atoms Sig) Γ σ) :
    decode (M.subst s) = (decode M).subst (decodeSub s) := by
  induction M with
  | var v =>
      simp only [RelationalBracketAbstraction.Term.subst, decode,
        Classicism.Meta.Term.subst_var, decodeSub]
  | const c =>
      simp only [RelationalBracketAbstraction.Term.subst, decode, decodeBasis_subst]
  | app f a ihf iha =>
      simp only [RelationalBracketAbstraction.Term.subst, decode,
        Classicism.Meta.Term.subst_app, ihf, iha]

theorem decodeSub_cons_id {Γ : Ctx} {σ : Ty}
    (a : RelationalBracketAbstraction.Term (Atoms Sig) Γ σ) :
    decodeSub (RelationalBracketAbstraction.Sub.cons a
      RelationalBracketAbstraction.Sub.id) =
      Classicism.Meta.Sub.cons (decode a) Classicism.Meta.Sub.id := by
  funext τ v
  cases v <;>
    simp only [decodeSub, RelationalBracketAbstraction.Sub.cons,
      RelationalBracketAbstraction.Sub.id, decode,
      Classicism.Meta.Sub.cons, Classicism.Meta.Sub.id]

/-- The one-variable coherence statement uses the original capture-avoiding
instantiation operation. -/
theorem decode_inst {Γ : Ctx} {σ τ : Ty}
    (M : RelationalBracketAbstraction.Term (Atoms Sig) (σ :: Γ) τ)
    (a : RelationalBracketAbstraction.Term (Atoms Sig) Γ σ) :
    decode (M.inst a) = (decode M).instantiate (decode a) := by
  simpa only [RelationalBracketAbstraction.Term.inst,
    Classicism.Meta.Term.instantiate, decodeSub_cons_id] using
    decode_subst (RelationalBracketAbstraction.Sub.cons a
      RelationalBracketAbstraction.Sub.id) M

#print axioms decodeAtom_rename
#print axioms decodeAtom_subst
#print axioms decodeBasis_rename
#print axioms decodeBasis_subst
#print axioms decode_rename
#print axioms decode_wk
#print axioms decode_subst
#print axioms decodeSub_cons_id
#print axioms decode_inst

end Classicism.Research.RelationalLambdaDecoding

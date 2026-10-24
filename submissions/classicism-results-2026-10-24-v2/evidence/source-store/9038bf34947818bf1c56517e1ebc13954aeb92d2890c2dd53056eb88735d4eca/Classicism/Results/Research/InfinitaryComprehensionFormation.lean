import Classicism.Results.Research.InfinitaryComprehensionGrounding

/-!
# The original closed-type infinitary language

This syntactic predicate checks the types that actually occur in a term,
including bound-variable and parameter occurrences. It imposes no condition
on unused entries of its parameter family. Thus arbitrary simultaneous
assignments remain available without enlarging the original object types.
Grounding sends every concrete term into this original language.

Source: the main Infinitary Comprehension note, sections 1 and 4 (misc,
23 October 2026, unpaginated). Source-only; compilation is held.
-/

namespace Classicism.Research.InfinitaryComprehension.Formation

open Classicism.Meta Grounding

universe u

def ContextClosed (Γ : Ctx) : Prop := ∀ σ ∈ Γ, σ.Closed

theorem ground_context_closed (Γ : Ctx) : ContextClosed (groundCtx Γ) :=
  groundCtx_closed Γ

theorem context_nil : ContextClosed [] := by
  intro σ h
  cases h

theorem context_cons {σ : Ty} {Γ : Ctx} :
    ContextClosed (σ :: Γ) ↔ σ.Closed ∧ ContextClosed Γ := by
  constructor
  · intro h
    exact ⟨h σ (List.mem_cons_self), fun τ hτ => h τ (List.mem_cons_of_mem σ hτ)⟩
  · rintro ⟨hσ, hΓ⟩ τ hτ
    rcases List.mem_cons.mp hτ with rfl | hτ
    · exact hσ
    · exact hΓ τ hτ

/-- Every type written in the actual syntax is an original closed type. -/
def formed {Param : Ty → Type u} : {Γ : Ctx} → {σ : Ty} → Term Param Γ σ → Prop
  | _, σ, .var _ => σ.Closed
  | _, σ, .param _ => σ.Closed
  | _, _, .app f a => formed f ∧ formed a
  | _, _, .top => True
  | _, _, .bot => True
  | _, _, .neg p => formed p
  | _, _, .conj p q => formed p ∧ formed q
  | _, _, .disj p q => formed p ∧ formed q
  | _, _, .imp p q => formed p ∧ formed q
  | _, _, .iff p q => formed p ∧ formed q
  | _, _, .eq a b => formed a ∧ formed b
  | _, _, .boxOp => True
  | _, _, .all (σ := σ) p => σ.Closed ∧ formed p
  | _, _, .ex (σ := σ) p => σ.Closed ∧ formed p
  | _, _, .iAnd I p => ∀ i : I, formed (p i)
  | _, _, .iOr I p => ∀ i : I, formed (p i)

theorem formed_result_type {Param : Ty → Type u} {Γ σ} (p : Term Param Γ σ)
    (hp : formed p) : σ.Closed := by
  induction p with
  | var => exact hp
  | param => exact hp
  | app f a ihf _ => exact (ihf hp.1).2
  | top | bot | neg | conj | disj | imp | iff | eq | all | ex | iAnd | iOr => trivial
  | boxOp => exact ⟨trivial, trivial⟩

theorem groundTerm_formed {Param Param' : Ty → Type u}
    (mapParam : ∀ {σ}, Param σ → Param' (groundTy σ))
    {Γ σ} (p : Term Param Γ σ) : formed (groundTerm mapParam p) := by
  induction p with
  | var => exact groundTy_closed _
  | param => exact groundTy_closed _
  | app f a ihf iha => exact ⟨ihf, iha⟩
  | top | bot | boxOp => trivial
  | neg p ih => exact ih
  | conj p q ihp ihq => exact ⟨ihp, ihq⟩
  | disj p q ihp ihq => exact ⟨ihp, ihq⟩
  | imp p q ihp ihq => exact ⟨ihp, ihq⟩
  | iff p q ihp ihq => exact ⟨ihp, ihq⟩
  | eq a b iha ihb => exact ⟨iha, ihb⟩
  | all p ih => exact ⟨groundTy_closed _, ih⟩
  | ex p ih => exact ⟨groundTy_closed _, ih⟩
  | iAnd I p ih => exact ih
  | iOr I p ih => exact ih

theorem formed_rename_iff {Param : Ty → Type u} {Γ σ} (p : Term Param Γ σ) :
    ∀ {Δ} (r : Ren Γ Δ), formed (p.rename r) ↔ formed p := by
  induction p with
  | var | param | top | bot | boxOp => intros; rfl
  | app f a ihf iha => intro Δ r; exact and_congr (ihf r) (iha r)
  | neg p ih => intro Δ r; exact ih r
  | conj p q ihp ihq => intro Δ r; exact and_congr (ihp r) (ihq r)
  | disj p q ihp ihq => intro Δ r; exact and_congr (ihp r) (ihq r)
  | imp p q ihp ihq => intro Δ r; exact and_congr (ihp r) (ihq r)
  | iff p q ihp ihq => intro Δ r; exact and_congr (ihp r) (ihq r)
  | eq a b iha ihb => intro Δ r; exact and_congr (iha r) (ihb r)
  | all p ih => intro Δ r; exact and_congr Iff.rfl (ih (Ren.lift r))
  | ex p ih => intro Δ r; exact and_congr Iff.rfl (ih (Ren.lift r))
  | iAnd I p ih => intro Δ r; exact forall_congr' (fun i => ih i r)
  | iOr I p ih => intro Δ r; exact forall_congr' (fun i => ih i r)

theorem ofArgs_closed (Γ : Ctx) (hΓ : ContextClosed Γ) : (RTy.ofArgs Γ).Closed := by
  induction Γ with
  | nil => trivial
  | cons σ Γ ih =>
      obtain ⟨hσ, hΓ⟩ := context_cons.mp hΓ
      exact ⟨hσ, ih hΓ⟩

theorem var_type_closed {Γ σ} (hΓ : ContextClosed Γ) (v : Var Γ σ) : σ.Closed := by
  induction v with
  | zero => exact (context_cons.mp hΓ).1
  | succ v ih => exact ih (context_cons.mp hΓ).2

theorem formed_applyVars {Param : Ty → Type u} (Γ : Ctx) :
    ∀ {Δ} (F : Term Param Δ (RTy.ofArgs Γ))
      (xs : ∀ {σ}, Var Γ σ → Term Param Δ σ),
      formed F → (∀ {σ} (v : Var Γ σ), formed (xs v)) →
      formed (Term.applyVars Γ F xs) := by
  induction Γ with
  | nil => intro Δ F xs hF _; exact hF
  | cons σ Γ ih =>
      intro Δ F xs hF hxs
      exact ih (.app F (xs .zero)) (fun v => xs (.succ v))
        ⟨hF, hxs .zero⟩ (fun v => hxs (.succ v))

theorem formed_closeAll {Param : Ty → Type u} (Γ : Ctx)
    (hΓ : ContextClosed Γ) :
    ∀ {Δ} (p : Formula Param (Γ ++ Δ)), formed p → formed (Term.closeAll Γ p) := by
  induction Γ with
  | nil => intro Δ p hp; exact hp
  | cons σ Γ ih =>
      intro Δ p hp
      exact ih (context_cons.mp hΓ).2 (.all p) ⟨(context_cons.mp hΓ).1, hp⟩

theorem formed_compBody {Param : Ty → Type u} {Γ : Ctx}
    (p : Formula Param Γ) (hΓ : ContextClosed Γ) (hp : formed p) :
    formed p.compBody := by
  refine ⟨?_, (formed_rename_iff p (Ren.embed Γ _)).2 hp⟩
  apply formed_applyVars Γ
  · exact ofArgs_closed Γ hΓ
  · intro σ v
    exact var_type_closed hΓ v

theorem formed_comprehension {Param : Ty → Type u} {Γ : Ctx}
    (p : Formula Param Γ) (hΓ : ContextClosed Γ) (hp : formed p) :
    formed p.comprehension := by
  refine ⟨ofArgs_closed Γ hΓ, trivial, ?_⟩
  exact formed_closeAll Γ hΓ p.compBody (formed_compBody p hΓ hp)

#print axioms groundTerm_formed
#print axioms formed_comprehension

end Classicism.Research.InfinitaryComprehension.Formation

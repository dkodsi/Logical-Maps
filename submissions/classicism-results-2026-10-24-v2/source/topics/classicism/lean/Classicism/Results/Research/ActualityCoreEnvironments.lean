import Classicism.Results.Research.ActualityCoreAdmittedValues

/-!
# Core environments and admitted application

Direct source: `research/2026-10-22/notes/actuality-world-slice-core.md`,
sections 2--3 (misc, 22 October 2026, unpaginated).

Core environments have values in the actual admitted carriers. Their context
hypotheses are proved, not assumed as an extra closure property. The arbitrary
intensional model and current-world scope are retained throughout.
-/

open CategoryTheory

namespace Classicism.Meta.Intensional.ActualityCore
open Classicism.Meta.ActualityCoreSyntax

variable {Sig : Signature} {C : Type} [SmallCategory C]
variable (A : Premodel Sig C) (M : A.IsModel)
include M

theorem core_context {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W)
    (w : Formula Sig Γ) (g : IEnv (A.Dom W) Γ) (wv : A.Dom W Ty.t)
    (hwv : A.Incl Ty.t W wv = A.sem h w g)
    (hc : ∀ (σ : Ty) (v : Var Γ σ), InCore A h wv σ (g.get v)) :
    A.HoldsHyps h (context Γ w) g := by
  intro p hp
  obtain ⟨⟨σ, v⟩, _, rfl⟩ := List.mem_map.mp hp
  have hv := (value_core_iff A M h w (.var v) g wv (g.get v) hwv rfl).2 (hc σ v)
  unfold Premodel.Holds
  rw [A.sem_conv M (domain_app_conv σ w (.var v))]
  exact hv

def forgetEnv {W : C} (h : A.W₀ ⟶ W) (wv : A.Dom W Ty.t) {Γ : Ctx}
    (g : IEnv (Carrier A h wv) Γ) : IEnv (A.Dom W) Γ :=
  g.map (fun _ x => x.val)

theorem context_forgetEnv {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W)
    (wv : A.Dom W Ty.t) (w : Formula Sig Γ) (g : IEnv (Carrier A h wv) Γ)
    (hwv : A.Incl Ty.t W wv = A.sem h w (forgetEnv A h wv g)) :
    A.HoldsHyps h (context Γ w) (forgetEnv A h wv g) := by
  apply core_context A M h w _ wv hwv
  intro σ v
  change InCore A h wv σ ((g.map (fun _ x => x.val)).get v)
  rw [IEnv.get_map]
  exact (g.get v).property

/-- The actual finite assignment supplies all context bounds. Only the model
and current actual-world hypotheses remain; no external fullness is assumed. -/
theorem translated_value_in_environment {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W)
    (wv : A.Dom W Ty.t) (w : Formula Sig Γ) {σ : Ty} (a : Term Sig Γ σ)
    (g : IEnv (Carrier A h wv) Γ)
    (hwv : A.Incl Ty.t W wv = A.sem h w (forgetEnv A h wv g))
    (hw : A.Holds h (actualWorld w) (forgetEnv A h wv g)) :
    ∃! x : Carrier A h wv σ,
      A.Incl σ W x.val = A.sem h (translate w a) (forgetEnv A h wv g) :=
  translated_value A M h w a (forgetEnv A h wv g) wv hwv hw
    (context_forgetEnv A M h wv w g hwv)

/-- Applying actual admitted core values gives a unique actual admitted core
value at the relational output type. Individual arguments are included. -/
theorem application_value {W : C} (h : A.W₀ ⟶ W) (wv : A.Dom W Ty.t)
    (σ : Ty) (ρ : RTy) (F : Carrier A h wv (σ ⇒ ρ)) (x : Carrier A h wv σ) :
    ∃! y : Carrier A h wv ρ,
      A.Incl ρ W y.val = A.apply (A.Incl (σ ⇒ ρ) W F.val) (A.Incl σ W x.val) := by
  let g : IEnv (A.Dom W) [σ, σ ⇒ ρ, Ty.t] :=
    .cons x.val (.cons F.val (.cons wv .nil))
  let w : Formula Sig [σ, σ ⇒ ρ, Ty.t] := .v2
  let f : Term Sig [σ, σ ⇒ ρ, Ty.t] (σ ⇒ ρ) := .v1
  let a : Term Sig [σ, σ ⇒ ρ, Ty.t] σ := .v0
  have hf : A.Holds h (member (σ ⇒ ρ) w f) g :=
    (value_core_iff A M h w f g wv F.val rfl rfl).2 F.property
  have hd := application_member σ ρ [member (σ ⇒ ρ) w f] w f a Derivable.hyp₀
  have hb : A.Holds h (member ρ w (.app f a)) g :=
    A.sound M h (A.axioms_holds M h) hd g
      (fun p hp => (List.mem_cons.mp hp).elim (fun he => he.symm ▸ hf)
        (fun hn => False.elim (List.not_mem_nil hn)))
  obtain ⟨y, hy⟩ := M h (.app f a) g
  refine ⟨⟨y, value_in_core A M h w (.app f a) g wv y rfl hy hb⟩, hy, ?_⟩
  intro z hz
  apply Subtype.ext
  exact A.Incl_injective ρ W (hz.trans hy.symm)

end Classicism.Meta.Intensional.ActualityCore

#print axioms Classicism.Meta.Intensional.ActualityCore.translated_value_in_environment
#print axioms Classicism.Meta.Intensional.ActualityCore.application_value

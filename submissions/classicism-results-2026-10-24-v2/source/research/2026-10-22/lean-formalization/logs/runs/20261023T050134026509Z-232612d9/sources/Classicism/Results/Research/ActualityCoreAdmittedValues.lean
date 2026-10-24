import Classicism.Results.Research.ActualityCoreConversion
import Classicism.Semantics.IntensionalSoundness

/-!
# Actual-core values in an arbitrary admitted intensional hierarchy

Direct source: `research/2026-10-22/notes/actuality-world-slice-core.md`,
sections 2--3 (misc, 22 October 2026, unpaginated).

This is ordinary model metatheory. The carriers below are subtypes of the
ambient model's actual inner domains. They are not external function spaces.
The main theorem uses the C derivation of recursive domain membership and
the ambient `IsModel` condition to obtain a unique admitted core value for
every translated term. It does not assume that all external functions or
predicates have representatives.
-/

open CategoryTheory

namespace Classicism.Meta.Intensional.ActualityCore
open Classicism.Meta.ActualityCoreSyntax

variable {Sig : Signature} {C : Type} [SmallCategory C]

def coreFormula (σ : Ty) : Formula Sig [σ, Ty.t] :=
  .app (domain σ .v1) .v0

def InCore (A : Premodel Sig C) {W : C} (h : A.W₀ ⟶ W)
    (w : A.Dom W Ty.t) (σ : Ty) (x : A.Dom W σ) : Prop :=
  A.Holds h (coreFormula σ) (.cons x (.cons w .nil))

abbrev Carrier (A : Premodel Sig C) {W : C} (h : A.W₀ ⟶ W)
    (w : A.Dom W Ty.t) (σ : Ty) : Type :=
  {x : A.Dom W σ // InCore A h w σ x}

variable (A : Premodel Sig C) (M : A.IsModel)

/-- A represented term satisfying the syntactic membership predicate has
its actual admitted value in the corresponding semantic carrier. -/
theorem value_in_core {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W)
    (w : Formula Sig Γ) {σ : Ty} (a : Term Sig Γ σ) (g : IEnv (A.Dom W) Γ)
    (wv : A.Dom W Ty.t) (x : A.Dom W σ)
    (hw : A.Incl Ty.t W wv = A.sem h w g)
    (hx : A.Incl σ W x = A.sem h a g)
    (ha : A.Holds h (member σ w a) g) : InCore A h wv σ x := by
  let s : Sub Sig [σ, Ty.t] Γ :=
    Sub.cons a (Sub.cons w (fun _ v => nomatch v))
  have hs : (coreFormula (Sig := Sig) σ).subst s = .app (domain σ w) a := by
    simp only [coreFormula, Term.subst_app, domain_subst, Term.subst_var,
      s, Term.v0, Term.v1, Sub.cons]
  have he : A.subEnv M h s g = .cons x (.cons wv .nil) := by
    apply IEnv.ext
    intro τ v
    apply A.Incl_injective τ W
    rw [A.Incl_subEnv_get]
    cases v with
    | zero => exact hx.symm
    | succ v =>
      cases v with
      | zero => exact hw.symm
      | succ v => exact nomatch v
  have hc : A.Holds h (.app (domain σ w) a) g := by
    unfold Premodel.Holds
    rw [A.sem_conv M (domain_app_conv σ w a)]
    exact ha
  unfold InCore Premodel.Holds
  rw [← he, ← A.sem_subst M s h (coreFormula σ) g, hs]
  exact hc

/-- Every translated term has exactly one value in the actual admitted core,
under precisely the translated context and actual-world hypotheses. -/
theorem translated_value {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W)
    (w : Formula Sig Γ) {σ : Ty} (a : Term Sig Γ σ) (g : IEnv (A.Dom W) Γ)
    (wv : A.Dom W Ty.t) (hwv : A.Incl Ty.t W wv = A.sem h w g)
    (hw : A.Holds h (actualWorld w) g)
    (hg : A.HoldsHyps h (context Γ w) g) :
    ∃! x : Carrier A h wv σ, A.Incl σ W x.val = A.sem h (translate w a) g := by
  have hb : A.Holds h (member σ w (translate w a)) g :=
    A.sound M h (A.axioms_holds M h) (translate_typing w a) g
      (fun p hp => (List.mem_cons.mp hp).elim (fun he => he.symm ▸ hw) (hg p))
  obtain ⟨x, hx⟩ := M h (translate w a) g
  refine ⟨⟨x, value_in_core A M h w (translate w a) g wv x hwv hx hb⟩, hx, ?_⟩
  intro y hy
  apply Subtype.ext
  exact A.Incl_injective σ W (hy.trans hx.symm)

end Classicism.Meta.Intensional.ActualityCore

#print axioms Classicism.Meta.Intensional.ActualityCore.translated_value

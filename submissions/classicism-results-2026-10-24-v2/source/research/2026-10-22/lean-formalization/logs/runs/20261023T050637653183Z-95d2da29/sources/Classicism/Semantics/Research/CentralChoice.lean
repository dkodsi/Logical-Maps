import Classicism.Semantics.Research.CentralSupport
import Classicism.Semantics.FullModels

/-!
# Extensional fullness of externally supported models

Existing argument: `research/2026-10-22/followup/central-map.md`, §§1–2.
A raw relation independent of the arrow has empty support even when the
members of its extension do not share any bounded support. This proves the
choice part of the construction independently of the concrete free monoid.
Ordinary classical metatheory; this is not the Logical Necessity separator.
-/

namespace Classicism.Meta.Intensional.Central
open CategoryTheory

variable {C : Type} [SmallCategory C] (Q : Control C) (De : C ⥤ Type)

/-- Any family of extensions has an admitted arrow-independent profile. -/
noncomputable def constantProfile (ρ : RTy) (W : C)
    (E : ∀ V : C, Set (Args (Domain Q De) ρ V)) :
    (Domain Q De (.rel ρ)).obj W :=
  ⟨{p | args' Q De ρ p.1 p.2.1 ∈ E p.1}, Q.zero W, by
    intro V h i _
    ext ⟨U, a, r⟩
    rfl⟩

theorem constantProfile_extension (ρ : RTy) (W : C)
    (E : ∀ V : C, Set (Args (Domain Q De) ρ V)) :
    (incl Q De ρ W (constantProfile Q De ρ W E)).ext' (Domain Q De) = E W := by
  ext a
  change args' Q De ρ W (args Q De ρ W a) ∈ E W ↔ a ∈ E W
  rw [args'_args]

variable {Sig : Signature} (W₀ : C) (hne : ∀ W, Nonempty (De.obj W))
  (I : ∀ c : Sig.Const, (Domain Q De (Sig.typeOf c)).obj W₀)

/-- Extensional fullness does not require a common support for an extension's
members, nor a one-object category. -/
theorem model_extFull : (model Q De W₀ hne I).ExtFull := by
  classical
  intro ρ W E
  let E' : ∀ V : C, Set (Args (Domain Q De) ρ V) :=
    fun V => {a | ∃ h : V = W, h ▸ a ∈ E}
  refine ⟨constantProfile Q De ρ W E', ?_⟩
  change (incl Q De ρ W (constantProfile Q De ρ W E')).ext' (Domain Q De) = E
  rw [constantProfile_extension]
  ext a
  change (∃ h : W = W, h ▸ a ∈ E) ↔ a ∈ E
  simp

end Classicism.Meta.Intensional.Central

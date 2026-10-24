import Classicism.Semantics.Research.CentralSupport
import Classicism.Semantics.IntensionalFacts
import Mathlib.CategoryTheory.SingleObj
import Classicism.Semantics.Research.CentralWords
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Set.Countable

/-!
# The actual countably supported product model

New research construction, 22 October 2026; ordinary classical metatheory.
Source: `research/2026-10-22/followup/central-map.md`, §§1, 3, 6.
The base domain is a singleton. Relational domains are the recursively built
intensions supported on countably many coordinates of a full product of free
monoids. Nothing restricts the support of an arrow or of a quantified tuple.
This file is an uncompiled author draft, not a completed model certificate.
-/

namespace Classicism.Meta.Intensional.Central.Product
open CategoryTheory

variable (I L : Type)

abbrev Arrow := I → Word L
abbrev World := SingleObj (Arrow I L)
abbrev star : World I L := SingleObj.star _

def control : Control (World I L) where
  Key _ := {S : Set I // S.Countable}
  zero _ := ⟨∅, Set.countable_empty⟩
  join s t := ⟨s.1 ∪ t.1, s.2.union t.2⟩
  Agree s h k := ∀ j ∈ s.1, h j = k j
  join_left _ _ _ _ h j hj := h j (Or.inl hj)
  join_right _ _ _ _ h j hj := h j (Or.inr hj)
  push _ s := s
  comp h _ k r hk j hj := congrArg (fun u => u * h j) (hk j hj)

abbrev individuals : World I L ⥤ Type := pointAction
noncomputable abbrev domain (σ : Ty) := Domain (control I L) (individuals I L) σ
noncomputable abbrev arguments (ρ : RTy) := Arguments (control I L) (individuals I L) ρ
abbrev raw (ρ : RTy) (W : World I L) := Raw (control I L) (individuals I L) ρ W

theorem individuals_supported (W : World I L) (x : (individuals I L).obj W) :
    Supported (control I L) (individuals I L) x :=
  ⟨⟨∅, Set.countable_empty⟩, fun _ _ _ _ => rfl⟩

noncomputable def model {Sig : Signature}
    (J : ∀ c : Sig.Const, (domain I L (Sig.typeOf c)).obj (star I L)) :
    Premodel Sig (World I L) :=
  Central.model (control I L) (individuals I L) (star I L) (fun _ => ⟨PUnit.unit⟩) J

theorem model_isModel {Sig : Signature}
    (J : ∀ c : Sig.Const, (domain I L (Sig.typeOf c)).obj (star I L)) :
    (model I L J).IsModel :=
  Central.model_isModel (control I L) (individuals I L) (individuals_supported I L)

/-- Dependence of a complete profile on the arrow coordinates in S. The
argument tuple is held fixed, and may have completely unrelated support. -/
def ProfileSupport {ρ : RTy} {W : World I L} (S : Set I) (F : raw I L ρ W) : Prop :=
  ∀ (V : World I L) (a : (arguments I L ρ).obj V) (h k : W ⟶ V),
    (∀ j ∈ S, h j = k j) →
      ((⟨V, a, h⟩ : Σ V, (arguments I L ρ).obj V × (W ⟶ V)) ∈ F ↔
       (⟨V, a, k⟩ : Σ V, (arguments I L ρ).obj V × (W ⟶ V)) ∈ F)

theorem supported_of_profile {ρ : RTy} {W : World I L} {S : Set I}
    (hS : S.Countable) {F : raw I L ρ W} (hF : ProfileSupport I L S F) :
    Supported (control I L) (intensionAction (arguments I L ρ)) F := by
  refine ⟨⟨S, hS⟩, fun V h k hk => ?_⟩
  ext ⟨U, a, r⟩
  exact hF U a (h ≫ r) (k ≫ r)
    (fun j hj => congrArg (fun u => r j * u) (hk j hj))

theorem profile_of_supportedBy {ρ : RTy} {W : World I L}
    {S : (control I L).Key W} {F : raw I L ρ W}
    (hF : SupportedBy (control I L) (intensionAction (arguments I L ρ)) S F) :
    ProfileSupport I L S.1 F := by
  intro V a h k hk
  have e := hF V h k hk
  have e' := congrArg (fun E => (⟨V, a, 𝟙 V⟩ :
    Σ U, (arguments I L ρ).obj U × (V ⟶ U)) ∈ E) e
  simpa only [intensionAction, Category.comp_id] using iff_of_eq e'

theorem profile_support {ρ : RTy} {W : World I L}
    (F : (domain I L (.rel ρ)).obj W) :
    ∃ S : Set I, S.Countable ∧ ProfileSupport I L S F.1 := by
  obtain ⟨S, hS⟩ := F.2
  exact ⟨S.1, S.2, profile_of_supportedBy I L hS⟩

/-- An arbitrary extension admits a constant profile. In particular, its
members are not required to have a common countable support. -/
noncomputable def constantProfile (ρ : RTy) (W : World I L)
    (E : ∀ V : World I L, Set ((arguments I L ρ).obj V)) :
    (domain I L (.rel ρ)).obj W :=
  ⟨{z | z.2.1 ∈ E z.1}, supported_of_profile I L Set.countable_empty
    (fun _ _ _ _ _ => Iff.rfl)⟩

theorem constantProfile_map (ρ : RTy) {W V : World I L} (h : W ⟶ V)
    (E : ∀ U : World I L, Set ((arguments I L ρ).obj U)) :
    (domain I L (.rel ρ)).map h (constantProfile I L ρ W E) =
      constantProfile I L ρ V E := by
  apply Subtype.ext
  rfl

/-- Prefixes are existentially quantified only in metatheory; this is a
fully specified intension, not an extra logical constant or choice axiom. -/
def suffixRaw {ρ : RTy} {W V : World I L} (S : Set I) (h : W ⟶ V)
    (F : raw I L ρ V) : raw I L ρ W :=
  {z | ∃ r : V ⟶ z.1, (∀ j ∈ S, z.2.2 j = r j * h j) ∧
    (⟨z.1, z.2.1, r⟩ : Σ U, (arguments I L ρ).obj U × (V ⟶ U)) ∈ F}

theorem suffixRaw_supported {ρ : RTy} {W V : World I L} {S : Set I}
    (hS : S.Countable) (h : W ⟶ V) (F : raw I L ρ V) :
    Supported (control I L) (intensionAction (arguments I L ρ)) (suffixRaw I L S h F) := by
  apply supported_of_profile I L hS
  intro U a k l hkl
  constructor <;> rintro ⟨r, hr, hFr⟩ <;> refine ⟨r, ?_, hFr⟩
  · exact fun j hj => (hkl j hj).symm.trans (hr j hj)
  · exact fun j hj => (hkl j hj).trans (hr j hj)

theorem suffixRaw_map {ρ : RTy} {W V : World I L} {S : Set I}
    (h : W ⟶ V) (F : raw I L ρ V) (hF : ProfileSupport I L S F) :
    (intensionAction (arguments I L ρ)).map h (suffixRaw I L S h F) = F := by
  ext ⟨U, a, k⟩
  change (∃ r : V ⟶ U, (∀ j ∈ S, k j * h j = r j * h j) ∧
    (⟨U, a, r⟩ : Σ U, (arguments I L ρ).obj U × (V ⟶ U)) ∈ F) ↔ _
  constructor
  · rintro ⟨r, hr, hFr⟩
    exact (hF U a r k (fun j hj => (Word.mul_right_cancel (hr j hj)).symm)).1 hFr
  · intro hk
    exact ⟨k, fun _ _ => rfl, hk⟩

/-- Onto maps at every admitted type, including individuals and type variables. -/
theorem domain_surjective (σ : Ty) {W V : World I L} (h : W ⟶ V) :
    Function.Surjective ((domain I L σ).map h) := by
  cases σ with
  | e => exact fun x => ⟨x, rfl⟩
  | var _ => exact fun x => ⟨x, rfl⟩
  | rel ρ =>
    intro F
    obtain ⟨S, hS, hF⟩ := profile_support I L F
    refine ⟨⟨suffixRaw I L S h F.1, suffixRaw_supported I L hS h F.1⟩, ?_⟩
    apply Subtype.ext
    exact suffixRaw_map I L h F.1 hF

/-- Exact object-language boxed Barcan instances in the constructed model. -/
theorem holds_box_bf {Sig : Signature}
    (J : ∀ c : Sig.Const, (domain I L (Sig.typeOf c)).obj (star I L)) (σ : Ty) :
    (model I L J).HoldsSentence (Term.box (Sentence.bf σ)) := by
  let B := model I L J
  have M := model_isModel I L J
  apply (B.holds_box M _ _ _).2
  intro V k
  rw [IEnv.nil_eq (B.push k IEnv.nil)]
  exact B.holds_bf_of_surjective M σ _ (fun r => domain_surjective I L σ r)

end Classicism.Meta.Intensional.Central.Product

import Classicism.Results.Research.ActualityCore
import Classicism.Results.Research.CoreNumberIsomorphism

/-!
# Internal numbers in the supported core of an actual world

Direct sources (unpaginated, original research, `misc`):
`research/2026-10-22/notes/actuality-world-slice-core.md`, §5;
`research/2026-10-22/proof-refinements/infinity-core-number-isomorphism.md`, §§1–3.

The target number predicate is defined here by the represented supported-core
induction formula. Its zero, successor, image and subset predicates are concrete.
No representation, coverage or surjectivity premise is left to a core owner.
All conclusions are current and conditional on the displayed actual-world witness.
This is a numerical interpretation, not a proof of a truth lemma for arbitrary
higher-order syntax, a Gallin interpretation, or external numerical standardness.
-/

namespace Classicism.Research.ActualityCoreNumbers
open Classicism.Paper Classicism.P Classicism.Research.ActualityCore

variable {σ : Type} [Ty σ]

def BaseTop (w : Prop) : σ → Prop := fun _ => w

def Properties (w : Prop) : (σ → Prop) → Prop :=
  Domain w (BaseTop w)

def Cardinals (w : Prop) : ((σ → Prop) → Prop) → Prop :=
  Domain w (Properties w)

def numberMap (w : Prop) (n : (σ → Prop) → Prop) : (σ → Prop) → Prop :=
  Cut (Properties w) n

def coreZero (w : Prop) : (σ → Prop) → Prop := numberMap w (ZeroCard σ)

def coreSuc (w : Prop) (n : (σ → Prop) → Prop) : (σ → Prop) → Prop :=
  fun X => Properties w X ∧ ∃ a, X a ∧ n (fun u => X u ∧ u ≠ a)

/-- The actual Frege induction formula over admitted predicates on core cardinals. -/
def Numbers (w : Prop) (y : (σ → Prop) → Prop) : Prop :=
  Cardinals w y ∧ ∀ V : ((σ → Prop) → Prop) → Prop,
    Domain w (Cardinals w) V → V (coreZero w) →
    (∀ z, Cardinals w z → V z → V (coreSuc w z)) → V y

theorem numbers_admitted (w : Prop) (hw : ActualWorld w) :
    Domain w (Cardinals (σ := σ) w) (Numbers w) :=
  ⟨hw.1, le_of_box_incl
    (nec% (fun (y : (σ → Prop) → Prop) (h : Numbers w y) => h.1))⟩

theorem properties_cover (w : Prop) (hw : ActualWorld w) :
    PropertyFieldCovers (Properties (σ := σ) w) := by
  intro X
  exact ⟨Cut (BaseTop w) X, cut_in_domain w hw _ _, fun u =>
    ⟨fun hu => ⟨hw.1, hu⟩, fun hu => hu.2⟩⟩

theorem numberMap_tests (w : Prop) :
    NumberMapTests (Properties (σ := σ) w) (numberMap w) :=
  fun _ _ _ hP => ⟨And.right, fun hn => ⟨hP, hn⟩⟩

theorem numberMap_in_cardinals (w : Prop) (hw : ActualWorld w)
    (n : (σ → Prop) → Prop) : Cardinals w (numberMap w n) :=
  cut_in_domain w hw (Properties w) n

theorem coreSuc_below (w : Prop) (n : (σ → Prop) → Prop) :
    coreSuc w n ≤ Properties w :=
  le_of_box_incl (nec% (fun (X : σ → Prop) (h : coreSuc w n X) => h.1))

theorem coreSuc_in_cardinals (w : Prop) (hw : ActualWorld w)
    (n : (σ → Prop) → Prop) : Cardinals w (coreSuc w n) :=
  ⟨hw.1, coreSuc_below w n⟩

theorem deletion_in_properties (w : Prop) (hw : ActualWorld w)
    (X : σ → Prop) (hX : Properties w X) (a : σ) :
    Properties w (fun u => X u ∧ u ≠ a) :=
  ⟨hw.1, le_trans_rel _ _ _
    (le_of_box_incl (nec% (fun (u : σ) (h : X u ∧ u ≠ a) => h.1))) hX.2⟩

/-- The successor equation is literal identity, licensed by world support. -/
theorem numberMap_suc (w : Prop) (hw : ActualWorld w)
    (n : (σ → Prop) → Prop) :
    numberMap w (SucCard n) = coreSuc w (numberMap w n) := by
  apply localized_eq w hw
  · exact cut_supported w (Properties w) (SucCard n)
      (domain_supported w (BaseTop w))
  · exact le_trans_rel _ _ _ (coreSuc_below w (numberMap w n))
      (domain_supported w (BaseTop w))
  · intro X
    constructor
    · intro h
      obtain ⟨a, ha, hn⟩ := h.2
      exact ⟨h.1, a, ha, deletion_in_properties w hw X h.1 a, hn⟩
    · intro h
      obtain ⟨a, ha, hn⟩ := h.2
      exact ⟨h.1, a, ha, hn.2⟩

theorem coreZero_current (w : Prop) (X : σ → Prop) (hX : Properties w X) :
    coreZero w X ↔ ∀ u, ¬ X u :=
  ⟨And.right, fun h => ⟨hX, h⟩⟩

theorem coreSuc_current (w : Prop) (n : (σ → Prop) → Prop)
    (X : σ → Prop) (hX : Properties w X) :
    coreSuc w n X ↔ ∃ a, X a ∧ n (fun u => X u ∧ u ≠ a) :=
  ⟨And.right, fun h => ⟨hX, h⟩⟩

theorem numbers_zero (w : Prop) (hw : ActualWorld w) :
    Numbers (σ := σ) w (coreZero w) :=
  ⟨numberMap_in_cardinals w hw (ZeroCard σ), fun _ _ hzero _ => hzero⟩

theorem numbers_suc (w : Prop) (hw : ActualWorld w)
    (y : (σ → Prop) → Prop) (hy : Numbers w y) : Numbers w (coreSuc w y) :=
  ⟨coreSuc_in_cardinals w hw y, fun V hV hzero hstep =>
    hstep y hy.1 (hy.2 V hV hzero hstep)⟩

theorem numberMap_forward (w : Prop) (hw : ActualWorld w)
    (n : (σ → Prop) → Prop) (hn : FiniteCardinality n) :
    Numbers w (numberMap w n) := by
  apply hn (fun z => Numbers w (numberMap w z))
  refine ⟨numbers_zero w hw, ?_⟩
  intro z hz
  exact (numberMap_suc w hw z).symm ▸ numbers_suc w hw (numberMap w z) hz

/-- The induction image is an admitted supported predicate, without C5 or BF. -/
def NumberImage (w : Prop) (y : (σ → Prop) → Prop) : Prop :=
  Cardinals w y ∧ ∃ n, FiniteCardinality n ∧ numberMap w n = y

theorem numberImage_admitted (w : Prop) (hw : ActualWorld w) :
    Domain w (Cardinals (σ := σ) w) (NumberImage w) :=
  ⟨hw.1, le_of_box_incl
    (nec% (fun (y : (σ → Prop) → Prop) (h : NumberImage w y) => h.1))⟩

theorem numberMap_onto (w : Prop) (hw : ActualWorld w)
    (y : (σ → Prop) → Prop) (hy : Numbers w y) :
    ∃ n, FiniteCardinality n ∧ numberMap w n = y := by
  have himage : NumberImage w y := by
    apply hy.2 (NumberImage w) (numberImage_admitted w hw)
    · exact ⟨numberMap_in_cardinals w hw (ZeroCard σ),
        ZeroCard σ, finiteCardinality_zero, rfl⟩
    · intro z _ hz
      obtain ⟨n, hn, he⟩ := hz.2
      exact ⟨coreSuc_in_cardinals w hw z, SucCard n, finiteCardinality_suc n hn,
        (numberMap_suc w hw n).trans (congrArg (coreSuc w) he)⟩
  exact himage.2

theorem quantified_infinity_iff (w : Prop) (hw : ActualWorld w) :
    Classicism.P.AxiomOfInfinity σ ↔
      ¬ ∃ y, Numbers w y ∧ y (BaseTop (σ := σ) w) :=
  core_quantified_infinity_iff (Properties w) (numberMap w) (Numbers w) (BaseTop w)
    (numberMap_tests w) (domain_contains_top w hw (BaseTop w)) (fun _ => hw.1)
    (numberMap_forward w hw) (numberMap_onto w hw)

theorem numberMap_injective (w : Prop) (hw : ActualWorld w)
    (hInf : Classicism.P.AxiomOfInfinity σ)
    (n m : (σ → Prop) → Prop) (hn : FiniteCardinality n)
    (hm : FiniteCardinality m) (he : numberMap w n = numberMap w m) : n = m :=
  core_number_injective hInf (Properties w) (numberMap w)
    (properties_cover w hw) (numberMap_tests w) n m hn hm he

theorem numberMap_identity_iff (w : Prop) (hw : ActualWorld w)
    (hInf : Classicism.P.AxiomOfInfinity σ)
    (n m : (σ → Prop) → Prop) (hn : FiniteCardinality n)
    (hm : FiniteCardinality m) : numberMap w n = numberMap w m ↔ n = m :=
  ⟨numberMap_injective w hw hInf n m hn hm, congrArg (numberMap w)⟩

theorem numberMap_inverse_graph (w : Prop) (hw : ActualWorld w)
    (hInf : Classicism.P.AxiomOfInfinity σ) :
    ∀ y : (σ → Prop) → Prop, Numbers w y → ∃ n, NumberInverse (Numbers w) (numberMap w) y n ∧
      ∀ m, NumberInverse (Numbers w) (numberMap w) y m → m = n :=
  core_number_inverse_graph hInf (Properties w) (numberMap w) (Numbers w)
    (properties_cover w hw) (numberMap_tests w) (numberMap_onto w hw)

theorem numberMap_successor_iff (w : Prop) (hw : ActualWorld w)
    (hInf : Classicism.P.AxiomOfInfinity σ)
    (n m : (σ → Prop) → Prop) (hn : FiniteCardinality n)
    (hm : FiniteCardinality m) :
    numberMap w n = coreSuc w (numberMap w m) ↔ n = SucCard m :=
  core_number_successor_iff hInf (Properties w) (numberMap w) (coreSuc w)
    (properties_cover w hw) (numberMap_tests w)
    (fun n _ => numberMap_suc w hw n) n m hn hm

/-- Every ambient numerical subset has a concrete admitted core representative. -/
def SubsetPush (w : Prop) (V : ((σ → Prop) → Prop) → Prop)
    (y : (σ → Prop) → Prop) : Prop :=
  Cardinals w y ∧ NumberPush (numberMap w) V y

theorem subsetPush_admitted (w : Prop) (hw : ActualWorld w)
    (V : ((σ → Prop) → Prop) → Prop) :
    Domain w (Cardinals w) (SubsetPush w V) :=
  ⟨hw.1, le_of_box_incl (nec% (fun (y : (σ → Prop) → Prop)
    (h : SubsetPush w V y) => h.1))⟩

theorem subset_push_pull (w : Prop) (hw : ActualWorld w)
    (hInf : Classicism.P.AxiomOfInfinity σ)
    (V : ((σ → Prop) → Prop) → Prop)
    (n : (σ → Prop) → Prop) (hn : FiniteCardinality n) :
    SubsetPush w V (numberMap w n) ↔ V n := by
  have h := core_number_push_pull hInf (Properties w) (numberMap w)
    (properties_cover w hw) (numberMap_tests w) V n hn
  exact ⟨fun hv => h.1 hv.2,
    fun hv => ⟨numberMap_in_cardinals w hw n, h.2 hv⟩⟩

theorem subset_pull_push (w : Prop) (hw : ActualWorld w)
    (V : ((σ → Prop) → Prop) → Prop)
    (y : (σ → Prop) → Prop) (hy : Numbers w y) :
    SubsetPush w (fun n => V (numberMap w n)) y ↔ V y := by
  have h := core_number_pull_push (numberMap w) (Numbers w) V
    (numberMap_onto w hw) y hy
  exact ⟨fun hv => h.1 hv.2, fun hv => ⟨hy.1, h.2 hv⟩⟩

end Classicism.Research.ActualityCoreNumbers

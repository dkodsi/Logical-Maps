import Classicism.Results.Research.ActualityCoreArithmetic

/-!
# Represented numerical predicates and relations in an actual world

Direct source: `research/2026-10-22/proof-refinements/infinity-core-number-isomorphism.md`,
§3 (unpaginated original research, `misc`). The representations below are supported
on the number field itself. Current localization, not necessitation of Actuality,
upgrades the image-support proof to the required order statement.

The target round trips are literal identities of supported representatives. The
ambient subset comparison is only on internal numbers; arbitrary ambient
coextensive predicates are not identified. No external subsets are quantified over.
-/

namespace Classicism.Research.ActualityNumericalRelations
open Classicism.Paper Classicism.P Classicism.Research.ActualityCore
open Classicism.Research.ActualityCoreNumbers
open Classicism.Research.ActualityCoreArithmetic

variable {σ : Type} [Ty σ]

theorem numbers_supported (w : Prop) : Supported w (Numbers (σ := σ) w) :=
  le_of_box_incl (nec% (fun (y : (σ → Prop) → Prop) (h : Numbers w y) => h.1.1))

theorem subsetPush_supported (w : Prop) (V : ((σ → Prop) → Prop) → Prop) :
    Supported w (SubsetPush w V) :=
  le_of_box_incl (nec% (fun (y : (σ → Prop) → Prop) (h : SubsetPush w V y) => h.1.1))

theorem subsetPush_numbers_admitted (w : Prop) (hw : ActualWorld w)
    (V : ((σ → Prop) → Prop) → Prop) : Domain w (Numbers w) (SubsetPush w V) := by
  refine ⟨hw.1, localized_le w hw _ _ (subsetPush_supported w V) ?_⟩
  intro y hy
  obtain ⟨n, hn, he, _⟩ := hy.2
  exact he ▸ numberMap_forward w hw n hn

theorem subset_roundtrip (w : Prop) (hw : ActualWorld w)
    (V : ((σ → Prop) → Prop) → Prop) (hV : Domain w (Numbers w) V) :
    SubsetPush w (fun n => V (numberMap w n)) = V := by
  apply localized_eq w hw
  · exact subsetPush_supported w _
  · exact le_trans_rel _ _ _ hV.2 (numbers_supported w)
  · intro y
    constructor
    · intro hy
      obtain ⟨n, _, he, hv⟩ := hy.2
      exact he ▸ hv
    · intro hy
      exact (subset_pull_push w hw V y (incl_of_le hV.2 y hy)).2 hy

theorem subset_image_identity_iff (w : Prop) (hw : ActualWorld w)
    (hInf : Classicism.P.AxiomOfInfinity σ)
    (U V : ((σ → Prop) → Prop) → Prop) :
    SubsetPush w U = SubsetPush w V ↔
      ∀ n, FiniteCardinality n → (U n ↔ V n) := by
  constructor
  · intro he n hn
    have hu := subset_push_pull w hw hInf U n hn
    have hv := subset_push_pull w hw hInf V n hn
    exact ⟨fun h => hv.1 (Eq.mp (congrFun he (numberMap w n)) (hu.2 h)),
      fun h => hu.1 (Eq.mpr (congrFun he (numberMap w n)) (hv.2 h))⟩
  · intro h
    apply localized_eq w hw _ _ (subsetPush_supported w U) (subsetPush_supported w V)
    intro y
    constructor
    · intro hy
      obtain ⟨n, hn, he, hu⟩ := hy.2
      exact ⟨hy.1, n, hn, he, (h n hn).1 hu⟩
    · intro hy
      obtain ⟨n, hn, he, hv⟩ := hy.2
      exact ⟨hy.1, n, hn, he, (h n hn).2 hv⟩

def NumberBinarySupport (w : Prop) :
    ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop :=
  fun x y => Numbers w x ∧ Numbers w y

def NumberTernarySupport (w : Prop) : ((σ → Prop) → Prop) →
    ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop :=
  fun x y z => Numbers w x ∧ Numbers w y ∧ Numbers w z

theorem numberBinarySupport_supported (w : Prop) :
    Supported w (NumberBinarySupport (σ := σ) w) :=
  le_of_box_incl (nec% (fun (x y : (σ → Prop) → Prop)
    (h : NumberBinarySupport w x y) => h.1.1.1))

theorem binaryPush_supported (w : Prop)
    (R : ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop) :
    Supported w (BinaryPush w R) :=
  le_of_box_incl (nec% (fun (x y : (σ → Prop) → Prop)
    (h : BinaryPush w R x y) => h.1.1))

theorem binaryPush_numbers_admitted (w : Prop) (hw : ActualWorld w)
    (R : ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop) :
    Domain w (NumberBinarySupport w) (BinaryPush w R) := by
  refine ⟨hw.1, localized_le w hw _ _ (binaryPush_supported w R) ?_⟩
  intro x y h
  obtain ⟨i, j, hi, hj, hie, hje, _⟩ := h.2.2
  exact ⟨hie ▸ numberMap_forward w hw i hi, hje ▸ numberMap_forward w hw j hj⟩

theorem binary_roundtrip (w : Prop) (hw : ActualWorld w)
    (R : ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop)
    (hR : Domain w (NumberBinarySupport w) R) :
    BinaryPush w (fun i j => R (numberMap w i) (numberMap w j)) = R := by
  apply localized_eq w hw
  · exact binaryPush_supported w _
  · exact le_trans_rel _ _ _ hR.2 (numberBinarySupport_supported w)
  · intro x y
    constructor
    · intro h
      obtain ⟨i, j, _, _, hie, hje, hij⟩ := h.2.2
      exact hje ▸ (hie ▸ hij)
    · intro h
      have hn : NumberBinarySupport w x y := incl_of_le hR.2 x y h
      exact (binary_pull_push w hw R x y hn.1 hn.2).2 h

theorem coreAdd_numbers_admitted (w : Prop) (hw : ActualWorld w) :
    Domain w (NumberTernarySupport (σ := σ) w) (CoreAdd w) :=
  ⟨hw.1, le_of_box_incl (nec% (fun (a b c : (σ → Prop) → Prop)
    (h : CoreAdd w a b c) => ⟨h.1, h.2.1, h.2.2.1⟩))⟩

theorem coreMul_numbers_admitted (w : Prop) (hw : ActualWorld w) :
    Domain w (NumberTernarySupport (σ := σ) w) (CoreMul w) :=
  ⟨hw.1, le_of_box_incl (nec% (fun (a b c : (σ → Prop) → Prop)
    (h : CoreMul w a b c) => ⟨h.1, h.2.1, h.2.2.1⟩))⟩

theorem coreLe_numbers_admitted (w : Prop) (hw : ActualWorld w) :
    Domain w (NumberBinarySupport (σ := σ) w) (CoreLe w) :=
  ⟨hw.1, le_of_box_incl (nec% (fun (a b : (σ → Prop) → Prop)
    (h : CoreLe w a b) => h.elim fun _ hc => ⟨hc.1, hc.2.2.1⟩))⟩

theorem core_number_induction (w : Prop) (hw : ActualWorld w)
    (V : ((σ → Prop) → Prop) → Prop) (hV : Domain w (Numbers w) V)
    (hzero : V (coreZero w))
    (hstep : ∀ y, Numbers w y → V y → V (coreSuc w y)) :
    ∀ y, Numbers w y → V y := by
  intro y hy
  exact hy.2 V ⟨hw.1, le_trans_rel _ _ _ hV.2 (numbers_admitted w hw).2⟩
    hzero (fun z _ hz => hstep z (incl_of_le hV.2 z hz) hz)

theorem core_zero_ne_suc (w : Prop) (hw : ActualWorld w)
    (hInf : Classicism.P.AxiomOfInfinity σ)
    (y : (σ → Prop) → Prop) (hy : Numbers w y) : coreZero w ≠ coreSuc w y := by
  intro he
  obtain ⟨n, hn, hne⟩ := numberMap_onto w hw y hy
  have hq : numberMap w (ZeroCard σ) = numberMap w (SucCard n) :=
    he.trans ((congrArg (coreSuc w) hne.symm).trans (numberMap_suc w hw n).symm)
  exact frege_zero_ne_suc n (numberMap_injective w hw hInf (ZeroCard σ) (SucCard n)
    finiteCardinality_zero (finiteCardinality_suc n hn) hq)

theorem core_suc_injective (w : Prop) (hw : ActualWorld w)
    (hInf : Classicism.P.AxiomOfInfinity σ)
    (y z : (σ → Prop) → Prop) (hy : Numbers w y) (hz : Numbers w z)
    (he : coreSuc w y = coreSuc w z) : y = z := by
  obtain ⟨n, hn, hne⟩ := numberMap_onto w hw y hy
  obtain ⟨m, hm, hme⟩ := numberMap_onto w hw z hz
  have hq : numberMap w (SucCard n) = numberMap w (SucCard m) :=
    (numberMap_suc w hw n).trans ((congrArg (coreSuc w) hne).trans
      (he.trans ((congrArg (coreSuc w) hme.symm).trans (numberMap_suc w hw m).symm)))
  have hnm : n = m := frege_infinity_suc_injective hInf n m hn hm
    (numberMap_injective w hw hInf (SucCard n) (SucCard m)
      (finiteCardinality_suc n hn) (finiteCardinality_suc m hm) hq)
  exact hne.symm.trans ((congrArg (numberMap w) hnm).trans hme)

end Classicism.Research.ActualityNumericalRelations

import Classicism.Results.Research.ActualityCoreGraphs
import Classicism.Results.Research.AtomicProbabilityCuts

/-!
# Concrete supported Dedekind-cut codes and their supremum operation

This discharges the previously assumed extensional-code and union-representative
interfaces using the submitted Actuality core. The input domain D and comparison
lt are represented relations at one fixed admitted type. Cut axioms are genuinely
relativized to D, including the nonmember witness. No external reals or Nat occur.

The construction proves bounded completeness of these supported cut codes from
Actuality alone. It does not assert that D is already a rational field; arithmetic
on D and the Archimedean small-gap theorem remain separate constructions.
All conclusions are current. No Choice, Plenitude, BF or boxed Actuality is used.

Source: proof-refinements/local-propositional-probability.md, internal-real bridge;
choice-free-faithful-probability.md, section 4 (unpaginated local research).
-/

namespace Classicism.Research.ProbabilitySupportedReals
open Classicism.Paper Classicism.P
open Classicism.Research.ActualityCore
open Classicism.Research.ProbabilityCuts

variable {σ : Type} [Ty σ]

def FieldCut (D : σ → Prop) (lt : σ → σ → Prop) (P : σ → Prop) : Prop :=
  (∀ q, P q → D q) ∧
  (∃ q, P q) ∧ (∃ q, D q ∧ ¬ P q) ∧
  (∀ p q, D p → D q → lt p q → P q → P p) ∧
  (∀ p, P p → ∃ q, P q ∧ lt p q)

/-- A concrete field of supported cut predicates; properness is inside D. -/
def RealCode (w : Prop) (D : σ → Prop) (lt : σ → σ → Prop) (P : σ → Prop) : Prop :=
  P ≤ BaseSupport w D ∧ FieldCut D lt P

/-- The admitted predicate defining the local real-code field. -/
def Reals (w : Prop) (D : σ → Prop) (lt : σ → σ → Prop) : (σ → Prop) → Prop :=
  fun P => w ∧ RealCode w D lt P

theorem reals_supported (w : Prop) (D : σ → Prop) (lt : σ → σ → Prop) :
    Supported w (Reals w D lt) :=
  le_of_box_incl (nec% (fun (P : σ → Prop) (h : Reals w D lt P) => h.1))

theorem reals_current (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (lt : σ → σ → Prop) (P : σ → Prop) :
    Reals w D lt P ↔ RealCode w D lt P :=
  ⟨And.right, fun h => ⟨hw.1, h⟩⟩

def BoundedFamily (w : Prop) (D : σ → Prop) (lt : σ → σ → Prop)
    (F : (σ → Prop) → Prop) : Prop :=
  (∃ P, F P) ∧ (∀ P, F P → RealCode w D lt P) ∧
  ∃ U, RealCode w D lt U ∧ ∀ P, F P → Included P U

/-- This is an actual admitted operation, not an assumed representative selector. -/
def supremum (w : Prop) (D : σ → Prop) (F : (σ → Prop) → Prop) : σ → Prop :=
  fun q => w ∧ D q ∧ ∃ P, F P ∧ P q

theorem baseSupport_supported (w : Prop) (D : σ → Prop) :
    Supported w (BaseSupport w D) :=
  le_of_box_incl (nec% (fun (q : σ) (h : BaseSupport w D q) => h.1))

theorem realCode_supported (w : Prop) (D : σ → Prop) (lt : σ → σ → Prop)
    (P : σ → Prop) (hP : RealCode w D lt P) : Supported w P :=
  le_trans_rel _ _ _ hP.1 (baseSupport_supported w D)

theorem realCode_extensional (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (lt : σ → σ → Prop) (P Q : σ → Prop)
    (hP : RealCode w D lt P) (hQ : RealCode w D lt Q)
    (hPQ : SameCut P Q) : P = Q :=
  localized_eq w hw P Q (realCode_supported w D lt P hP)
    (realCode_supported w D lt Q hQ) hPQ

theorem supremum_below (w : Prop) (D : σ → Prop) (F : (σ → Prop) → Prop) :
    supremum w D F ≤ BaseSupport w D :=
  le_of_box_incl (nec% (fun (q : σ) (h : supremum w D F q) => ⟨h.1, h.2.1⟩))

theorem supremum_current (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (F : (σ → Prop) → Prop) :
    ∀ q, supremum w D F q ↔ D q ∧ ∃ P, F P ∧ P q :=
  fun q => ⟨fun h => h.2, fun h => ⟨hw.1, h⟩⟩

theorem supremum_is_real (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (lt : σ → σ → Prop) (F : (σ → Prop) → Prop)
    (hF : BoundedFamily w D lt F) : RealCode w D lt (supremum w D F) := by
  refine ⟨supremum_below w D F, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact hq.2.1
  · obtain ⟨P, hP⟩ := hF.1
    obtain ⟨q, hq⟩ := (hF.2.1 P hP).2.2.1
    exact ⟨q, hw.1, (hF.2.1 P hP).2.1 q hq, P, hP, hq⟩
  · obtain ⟨U, hU, hbound⟩ := hF.2.2
    obtain ⟨q, hDq, hnq⟩ := hU.2.2.2.1
    refine ⟨q, hDq, ?_⟩
    intro hq
    obtain ⟨P, hP, hPq⟩ := hq.2.2
    exact hnq (hbound P hP q hPq)
  · intro p q hDp hDq hpq hq
    obtain ⟨P, hP, hPq⟩ := hq.2.2
    exact ⟨hw.1, hDp, P, hP,
      (hF.2.1 P hP).2.2.2.2.1 p q hDp hDq hpq hPq⟩
  · intro p hp
    obtain ⟨P, hP, hPp⟩ := hp.2.2
    obtain ⟨q, hPq, hpq⟩ := (hF.2.1 P hP).2.2.2.2.2 p hPp
    exact ⟨q, ⟨hw.1, (hF.2.1 P hP).2.1 q hPq, P, hP, hPq⟩, hpq⟩

theorem supremum_is_lub (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (lt : σ → σ → Prop) (F : (σ → Prop) → Prop)
    (hF : BoundedFamily w D lt F) : CutLub F (supremum w D F) := by
  refine ⟨?_, ?_⟩
  · intro P hP q hq
    exact ⟨hw.1, (hF.2.1 P hP).2.1 q hq, P, hP, hq⟩
  · intro V hV q hq
    obtain ⟨P, hP, hPq⟩ := hq.2.2
    exact hV P hP q hPq

theorem real_lub_unique (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (lt : σ → σ → Prop) (F : (σ → Prop) → Prop)
    (P Q : σ → Prop) (hP : RealCode w D lt P) (hQ : RealCode w D lt Q)
    (hPl : CutLub F P) (hQl : CutLub F Q) : P = Q :=
  realCode_extensional w hw D lt P Q hP hQ
    (lub_unique_coextension F P Q hPl hQl)

/-- Literal unique existence, with both old representation premises discharged. -/
theorem represented_real_supremum (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (lt : σ → σ → Prop) (F : (σ → Prop) → Prop)
    (hF : BoundedFamily w D lt F) :
    ∃ U, RealCode w D lt U ∧ CutLub F U ∧
      ∀ V, RealCode w D lt V → CutLub F V → U = V :=
  ⟨supremum w D F, supremum_is_real w hw D lt F hF,
    supremum_is_lub w hw D lt F hF,
    fun V hV hl => real_lub_unique w hw D lt F (supremum w D F) V
      (supremum_is_real w hw D lt F hF) hV (supremum_is_lub w hw D lt F hF) hl⟩

def SupGraph (w : Prop) (D : σ → Prop) (lt : σ → σ → Prop) :
    ((σ → Prop) → Prop) → (σ → Prop) → Prop :=
  Graph w (BoundedFamily w D lt) (RealCode w D lt) (fun F U => CutLub F U)

theorem supGraph_supported (w : Prop) (D : σ → Prop) (lt : σ → σ → Prop) :
    Supported w (SupGraph w D lt) :=
  graph_supported w (BoundedFamily w D lt) (RealCode w D lt) (fun F U => CutLub F U)

theorem supGraph_total_unique (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (lt : σ → σ → Prop) :
    ∀ F, BoundedFamily w D lt F →
      SupGraph w D lt F (supremum w D F) ∧
      ∀ U, SupGraph w D lt F U → U = supremum w D F := by
  intro F hF
  refine ⟨⟨hw.1, hF, supremum_is_real w hw D lt F hF,
    supremum_is_lub w hw D lt F hF⟩, ?_⟩
  intro U hU
  exact real_lub_unique w hw D lt F U (supremum w D F) hU.2.2.1
    (supremum_is_real w hw D lt F hF) hU.2.2.2 (supremum_is_lub w hw D lt F hF)

theorem real_order_iff (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (lt : σ → σ → Prop) (P Q : σ → Prop)
    (hP : RealCode w D lt P) : P ≤ Q ↔ Included P Q :=
  localized_le_iff w hw P Q (realCode_supported w D lt P hP)

end Classicism.Research.ProbabilitySupportedReals

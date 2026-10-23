import Classicism.Core

/-!
# Current cut unions at a fixed admitted code type

This is a shallow C-language development, unlike the external scalar modules.
Every carrier parameter is guarded by `Ty`; all formed types end in Prop.
All hypotheses and quantifiers below are CURRENT, not boxed. No function
returning an individual, external Nat/List, quotient or unrestricted
extensionality is used.

The code type and comparison relation have NOT been identified with the
internal rationals. These are the logical cut-union and code-uniqueness steps
needed by the graph-valued real construction, not an ordered real-field proof.
Source: proof-refinements/choice-free-faithful-probability.md, section 4;
local-propositional-probability.md, internal-real bridge (unpaginated research).
The companion certificate module requests gate/type/object-language checks.
-/

namespace Classicism.Research.ProbabilityCuts

variable {σ : Type} [Ty σ]

def Included (P Q : σ → Prop) : Prop := ∀ q, P q → Q q

def SameCut (P Q : σ → Prop) : Prop := ∀ q, P q ↔ Q q

/-- Nonempty, proper, downward closed and rounded; the comparison is a relation. -/
def LowerCut (lt : σ → σ → Prop) (P : σ → Prop) : Prop :=
  (∃ q, P q) ∧ (∃ q, ¬ P q) ∧
  (∀ p q, lt p q → P q → P p) ∧
  (∀ p, P p → ∃ q, P q ∧ lt p q)

def unionCut (F : (σ → Prop) → Prop) : σ → Prop :=
  fun q => ∃ P, F P ∧ P q

def BoundedCutFamily (lt : σ → σ → Prop) (F : (σ → Prop) → Prop) : Prop :=
  (∃ P, F P) ∧ (∀ P, F P → LowerCut lt P) ∧
  ∃ U, LowerCut lt U ∧ ∀ P, F P → Included P U

/-- Least upper bound for current inclusion, not for literal intensional identity. -/
def CutLub (F : (σ → Prop) → Prop) (U : σ → Prop) : Prop :=
  (∀ P, F P → Included P U) ∧
  (∀ V, (∀ P, F P → Included P V) → Included U V)

theorem union_is_lub (F : (σ → Prop) → Prop) : CutLub F (unionCut F) := by
  refine ⟨?_, ?_⟩
  · intro P hP q hq
    exact ⟨P, hP, hq⟩
  · intro V hV q hq
    exact hq.elim (fun P hP => hV P hP.1 q hP.2)

theorem union_is_cut (lt : σ → σ → Prop) (F : (σ → Prop) → Prop)
    (h : BoundedCutFamily lt F) : LowerCut lt (unionCut F) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨P, hP⟩ := h.1
    obtain ⟨q, hq⟩ := (h.2.1 P hP).1
    exact ⟨q, P, hP, hq⟩
  · obtain ⟨U, hU, hbound⟩ := h.2.2
    obtain ⟨q, hq⟩ := hU.2.1
    refine ⟨q, ?_⟩
    intro hu
    exact hu.elim (fun P hP => hq (hbound P hP.1 q hP.2))
  · intro p q hpq hq
    obtain ⟨P, hP, hPq⟩ := hq
    exact ⟨P, hP, (h.2.1 P hP).2.2.1 p q hpq hPq⟩
  · intro p hp
    obtain ⟨P, hP, hPp⟩ := hp
    obtain ⟨q, hPq, hpq⟩ := (h.2.1 P hP).2.2.2 p hPp
    exact ⟨q, ⟨P, hP, hPq⟩, hpq⟩

theorem cut_sup_exists (lt : σ → σ → Prop) (F : (σ → Prop) → Prop)
    (h : BoundedCutFamily lt F) : ∃ U, LowerCut lt U ∧ CutLub F U :=
  ⟨unionCut F, union_is_cut lt F h, union_is_lub F⟩

theorem lub_unique_coextension (F : (σ → Prop) → Prop) (U V : σ → Prop)
    (hU : CutLub F U) (hV : CutLub F V) : SameCut U V :=
  fun q => ⟨fun hq => hU.2 V hV.1 q hq, fun hq => hV.2 U hU.1 q hq⟩

theorem lowerCut_transport (lt : σ → σ → Prop) (P Q : σ → Prop)
    (hP : LowerCut lt P) (hPQ : SameCut P Q) : LowerCut lt Q := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hP.1.elim (fun q hq => ⟨q, (hPQ q).1 hq⟩)
  · exact hP.2.1.elim (fun q hq => ⟨q, fun hQ => hq ((hPQ q).2 hQ)⟩)
  · intro p q hpq hq
    exact (hPQ p).1 (hP.2.2.1 p q hpq ((hPQ q).2 hq))
  · intro p hp
    obtain ⟨q, hq, hpq⟩ := hP.2.2.2 p ((hPQ p).2 hp)
    exact ⟨q, (hPQ q).1 hq, hpq⟩

theorem lub_transport (F : (σ → Prop) → Prop) (U V : σ → Prop)
    (hU : CutLub F U) (hUV : SameCut U V) : CutLub F V := by
  refine ⟨?_, ?_⟩
  · intro P hP q hq
    exact (hUV q).1 (hU.1 P hP q hq)
  · intro W hW q hq
    exact hU.2 W hW q ((hUV q).2 hq)

/-- The specific extensional-code interface still needed from a supported core. -/
def ExtensionalCutCodes (K : (σ → Prop) → Prop) : Prop :=
  ∀ P Q, K P → K Q → SameCut P Q → P = Q

def CodedCutSup (K : (σ → Prop) → Prop) (lt : σ → σ → Prop)
    (F : (σ → Prop) → Prop) (U : σ → Prop) : Prop :=
  K U ∧ LowerCut lt U ∧ CutLub F U

theorem coded_sup_unique (K : (σ → Prop) → Prop) (lt : σ → σ → Prop)
    (F : (σ → Prop) → Prop) (he : ExtensionalCutCodes K) (U V : σ → Prop)
    (hU : CodedCutSup K lt F U) (hV : CodedCutSup K lt F V) : U = V :=
  he U V hU.1 hV.1 (lub_unique_coextension F U V hU.2.2 hV.2.2)

/-- The representative is supplied only for this family, with current coextension.

This theorem does NOT infer supported representatives from bare C, nor does it
identify globally rigid codes with actual-world-local codes.
-/
theorem coded_sup_exists (K : (σ → Prop) → Prop) (lt : σ → σ → Prop)
    (F : (σ → Prop) → Prop) (h : BoundedCutFamily lt F)
    (hr : ∃ U, K U ∧ SameCut (unionCut F) U) : ∃ U, CodedCutSup K lt F U := by
  obtain ⟨U, hU, hrep⟩ := hr
  exact ⟨U, hU, lowerCut_transport lt (unionCut F) U (union_is_cut lt F h) hrep,
    lub_transport F (unionCut F) U (union_is_lub F) hrep⟩

theorem coded_sup_graph_total_functional (K : (σ → Prop) → Prop)
    (lt : σ → σ → Prop) (he : ExtensionalCutCodes K)
    (hr : ∀ F, BoundedCutFamily lt F → ∃ U, K U ∧ SameCut (unionCut F) U) :
    ∀ F, BoundedCutFamily lt F → ∃ U, CodedCutSup K lt F U ∧
      ∀ V, CodedCutSup K lt F V → U = V := by
  intro F hF
  obtain ⟨U, hU⟩ := coded_sup_exists K lt F hF (hr F hF)
  exact ⟨U, hU, fun V hV => coded_sup_unique K lt F he U V hU hV⟩

end Classicism.Research.ProbabilityCuts

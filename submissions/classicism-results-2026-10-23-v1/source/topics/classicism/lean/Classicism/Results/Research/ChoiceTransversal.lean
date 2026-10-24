import Classicism.Results.Research.ChoiceCompleteness
import Classicism.Results.Research.ChoiceCountable

/-!
# The direct type-local Transversal theorem

Direct source: `research/2026-10-22/notes/relational-choice-boolean-completeness-transversal-proof.md`,
§§2–6, and `notes/relational-choice-countable-completeness-ccc.md`, statement
(`misc`, original research, 22 October 2026; unpaginated).

This route uses `RC_(sigma t,sigma t)` and `BC_(sigma t)` to prove `TC_sigma`.
It does not pass through Actuality or assume completeness at `tt`. Equivalence
of the given relation is actual, not necessary. The selected graph is actual
and is never represented by a choice operation.
-/
namespace Classicism.Research.Choice
open Classicism.Paper Classicism.P

section
variable {σ : Type} [Ty σ]

def PartialRep (R : σ → σ → Prop) (F : σ → Prop) : Prop :=
  ∀ x y, (F x ∧ F y) ≤ (R x y → x = y)

def FullRep (R : σ → σ → Prop) (F : σ → Prop) : Prop :=
  ∀ x, ∃ y, R x y ∧ F y

theorem partialRep_chain_lub (R : σ → σ → Prop) (C : (σ → Prop) → Prop)
    (J : σ → Prop) (hJ : LUB J C) (hC : ∀ F, C F → PartialRep R F)
    (hc : TotalOrderOn (fun F G : σ → Prop => F ≤ G) C) : PartialRep R J := by
  intro x y
  apply lub_pair_closed C J hJ x y
  intro F G hF hG
  rcases hc.2.2 F G hF hG with hFG | hGF
  · exact le_trans_prop _ _ _
      (le_and_prop _ _ _
        (le_trans_prop _ _ _ (and_le_left_prop _ _) (le_apply_of_le F G x hFG))
        (and_le_right_prop _ _)) (hC G hG x y)
  · exact le_trans_prop _ _ _
      (le_and_prop _ _ _ (and_le_left_prop _ _)
        (le_trans_prop _ _ _ (and_le_right_prop _ _) (le_apply_of_le G F y hGF)))
      (hC F hF x y)

theorem partialRep_chain_complete (R : σ → σ → Prop)
    (bc : BooleanCompleteness (σ → Prop)) :
    DomainChainComplete (PartialRep R) (fun F G : σ → Prop => F ≤ G) := by
  intro C hC hc
  obtain ⟨J, hJ⟩ := BooleanCompleteness.to_lub bc C
  exact ⟨J, partialRep_chain_lub R C J hJ hC hc,
    (hJ J).2 (le_refl_arrow_prop J), fun G _ hu => (hJ G).1 hu⟩

def RepGuard (R : σ → σ → Prop) (F : σ → Prop) (x : σ) : Prop :=
  ∀ z, F z ∧ (R x z ∨ R z x) → z = x

def AdjoinRep (R : σ → σ → Prop) (F : σ → Prop) (x : σ) : σ → Prop :=
  fun y => F y ∨ (y = x ∧ RepGuard R F x)

theorem adjoinRep_pair_imp (R : σ → σ → Prop) (F : σ → Prop) (x a b : σ) :
    (F a ∧ F b → R a b → a = b) →
    (AdjoinRep R F x a ∧ AdjoinRep R F x b → R a b → a = b) := by
  intro h hab hr
  rcases hab.1 with ha | ha <;> rcases hab.2 with hb | hb
  · exact h ⟨ha, hb⟩ hr
  · exact (hb.2 a ⟨ha, Or.inr (hb.1 ▸ hr)⟩).trans hb.1.symm
  · exact ha.1.trans (ha.2 b ⟨hb, Or.inl (ha.1 ▸ hr)⟩).symm
  · exact ha.1.trans hb.1.symm

theorem adjoinRep_partial (R : σ → σ → Prop) (F : σ → Prop) (x : σ)
    (hF : PartialRep R F) : PartialRep R (AdjoinRep R F x) := fun a b =>
  le_of_box_incl (modal_K _ _ (nec% (adjoinRep_pair_imp R F x a b))
    ((le_iff_prop _ _).1 (hF a b)))

theorem adjoinRep_above (R : σ → σ → Prop) (F : σ → Prop) (x : σ) :
    F ≤ AdjoinRep R F x :=
  le_of_box_incl (nec% (fun (y : σ) (hy : F y) =>
    (Or.inl hy : AdjoinRep R F x y)))

theorem partialRep_step (R : σ → σ → Prop) (hR : EquivRel R) (F : σ → Prop)
    (hF : PartialRep R F) (hn : ¬ FullRep R F) :
    ∃ G, PartialRep R G ∧ F ≤ G ∧ F ≠ G := by
  have hex : ∃ x, ¬ ∃ y, R x y ∧ F y :=
    (em (∃ x, ¬ ∃ y, R x y ∧ F y)).elim id fun h =>
      (hn fun x => (em (∃ y, R x y ∧ F y)).elim id
        (fun hn' => (h ⟨x, hn'⟩).elim)).elim
  obtain ⟨x, hm⟩ := hex
  have hq : RepGuard R F x := fun z hz =>
    (hm ⟨z, hz.2.elim id (hR.2.1 z x), hz.1⟩).elim
  have hnx : ¬ F x := fun hx => hm ⟨x, hR.1 x, hx⟩
  have hg : AdjoinRep R F x x := Or.inr ⟨rfl, hq⟩
  exact ⟨AdjoinRep R F x, adjoinRep_partial R F x hF, adjoinRep_above R F x,
    fun e => hnx (congrFun e.symm x ▸ hg)⟩

theorem full_partial_transversal (R : σ → σ → Prop) (hR : EquivRel R)
    (F : σ → Prop) (hp : PartialRep R F) (hf : FullRep R F) :
    ∀ x, ∃ y, R x y ∧ F y ∧ ∀ z, (R x z ∧ F z) → y = z := by
  intro x
  obtain ⟨y, hxy, hFy⟩ := hf x
  refine ⟨y, hxy, hFy, fun z hz => ?_⟩
  exact (imp_of_le_prop _ _ (hp y z) ⟨hFy, hz.2⟩)
    (hR.2.2 y x z (hR.2.1 x y hxy) hz.1)

theorem local_choice_completeness_transversal :
    RelationalChoice (σ → Prop) (σ → Prop) → BooleanCompleteness (σ → Prop) →
      TransversalChoice σ := by
  intro rc bc R hR
  let P := PartialRep R
  let U : (σ → Prop) → (σ → Prop) → Prop := fun F G =>
    ((P F ∧ ¬ FullRep R F) → P G ∧ F ≤ G ∧ F ≠ G) ∧
    (¬ (P F ∧ ¬ FullRep R F) → G = F)
  have hs : Serial U := by
    intro F
    refine (em (P F ∧ ¬ FullRep R F)).elim (fun h => ?_) (fun hn => ?_)
    · obtain ⟨G, hG⟩ := partialRep_step R hR F h.1 h.2
      exact ⟨G, (fun _ => hG), (fun hn => (hn h).elim)⟩
    · exact ⟨F, (fun h => (hn h).elim), (fun _ => rfl)⟩
  obtain ⟨f, hff, hfU⟩ := rc U hs
  have fs : ∀ F, P F → ∃ G, f F G := fun F _ =>
    (hff F).elim fun G hG => ⟨G, hG.1⟩
  have fc : ∀ F G, P F → f F G → P G := by
    intro F G hF hFG
    refine (em (FullRep R F)).elim (fun hfull => ?_) (fun hnfull => ?_)
    · have e := (hfU F G hFG).2 (fun h => h.2 hfull)
      exact e.symm ▸ hF
    · exact ((hfU F G hFG).1 ⟨hF, hnfull⟩).1
  have fp : ∀ F G, P F → f F G → F ≤ G := by
    intro F G hF hFG
    refine (em (FullRep R F)).elim (fun hfull => ?_) (fun hnfull => ?_)
    · have e := (hfU F G hFG).2 (fun h => h.2 hfull)
      exact e.symm ▸ le_refl_arrow_prop F
    · exact ((hfU F G hFG).1 ⟨hF, hnfull⟩).2.1
  have fu : ∀ F G H, P F → f F G → f F H → G = H := fun F G H _ hFG hFH =>
    (hff F).elim fun V hV => (hV.2 G hFG).symm.trans (hV.2 H hFH)
  obtain ⟨F, hF, hfix⟩ := domain_graph_fixedpoint P
    (fun F G : σ → Prop => F ≤ G) f (fun _ => False)
    le_refl_arrow_prop le_trans_arrow le_antisymm_arrow
    (partialRep_chain_complete R bc) fs fc fp fu
  have hfull : FullRep R F := (em (FullRep R F)).elim id fun hn =>
    (((hfU F F hfix).1 ⟨hF, hn⟩).2.2 rfl).elim
  exact ⟨F, full_partial_transversal R hR F hF hfull⟩

/-- The original type-local countable-completeness descendant. -/
theorem local_choice_countable_ccc_transversal {κ : Type} [Ty κ] :
    RelationalChoice (σ → Prop) (σ → Prop) →
    CountableBooleanCompleteness κ (σ → Prop) → BooleanCCC κ (σ → Prop) →
      TransversalChoice σ := fun rc cbc ccc =>
  local_choice_completeness_transversal rc (choice_countable_ccc_completeness rc cbc ccc)

end
end Classicism.Research.Choice

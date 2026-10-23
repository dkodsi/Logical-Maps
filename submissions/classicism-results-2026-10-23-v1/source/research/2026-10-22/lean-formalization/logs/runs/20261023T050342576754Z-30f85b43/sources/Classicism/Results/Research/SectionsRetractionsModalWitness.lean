import Classicism.Results.Research.SectionsRetractionsStableGraphs
import Classicism.Results.Records.Extensionality

/-!
# Uniform modal witnesses collapse to Extensionality

Direct source: `research/2026-10-22/notes/choice-uniformization.md`, §1,
Theorems 1–2 (`misc`, original research, 22 October 2026; unpaginated).
`ModalPlenitude` below has an existential operation outside the box. It is
not the existing C-theorem named `P.ModalizedPlenitude`.
-/
namespace Classicism.Research.Splitting
open Classicism.Paper Classicism.P

def NecessaryUniqueWitness : Prop :=
  ∀ F : Prop → Prop, (□ (∃ q, F q ∧ ∀ r, F r → r = q)) → ∃ q, □ (F q)

def NecessaryWitness : Prop :=
  ∀ F : Prop → Prop, (□ (∃ q, F q)) → ∃ q, □ (F q)

def ModalPlenitude (σ τ : Type) [Ty σ] [Rel τ] : Prop :=
  ∀ U : σ → τ → Prop, (□ (Functional U)) → ∃ f : σ → τ, □ (∀ x, U x (f x))

def ModalFunctionalChoice (σ τ : Type) [Ty σ] [Rel τ] : Prop :=
  ∀ U : σ → τ → Prop, (□ (Serial U)) → ∃ f : σ → τ, □ (∀ x, U x (f x))

def truthSwitch (p q : Prop) : Prop := (p ∧ q = True) ∨ (¬ p ∧ q = False)

theorem truthSwitch_unique (p : Prop) :
    ∃ q, truthSwitch p q ∧ ∀ r, truthSwitch p r → r = q :=
  (em p).elim
    (fun hp => ⟨True, Or.inl ⟨hp, rfl⟩,
      fun _ h => h.elim And.right (fun h => (h.1 hp).elim)⟩)
    (fun hn => ⟨False, Or.inr ⟨hn, rfl⟩,
      fun _ h => h.elim (fun h => (hn h.1).elim) And.right⟩)

theorem truthSwitch_top (p q : Prop) : p → truthSwitch p q → q = True :=
  fun hp h => h.elim And.right (fun h => (h.1 hp).elim)

theorem truthSwitch_recovers (p q : Prop) : truthSwitch p q → q = True → p :=
  fun h he => h.elim And.left
    (fun h => (Eq.mp (he.symm.trans h.2) trivial).elim)

theorem unique_witness_collapse (nuw : NecessaryUniqueWitness) : ∀ p : Prop, p → □ p := by
  intro p hp
  obtain ⟨q, hq⟩ := nuw (truthSwitch p) (nec% (truthSwitch_unique p))
  have he : q = True := truthSwitch_top p q hp (box_elim hq)
  exact modal_K _ _ (modal_K _ _ (nec% (truthSwitch_recovers p q)) hq)
    (necessity_of_identity _ _ he)

theorem unique_witness_extensionality {τ : Type} [Rel τ] :
    NecessaryUniqueWitness → Extensionality τ :=
  fun nuw X Y h => intensionality X Y (unique_witness_collapse nuw (X ≡ Y) h)

theorem extensionality_necessary_witness : Extensionality Prop → NecessaryWitness :=
  fun ext F hf => (box_elim hf).elim fun q hq =>
    ⟨q, Proofs.box_of_fregean (Proofs.extensionality_r_implies_fregean_axiom ext) _ hq⟩

theorem witness_unique_witness : NecessaryWitness → NecessaryUniqueWitness :=
  fun nw F hf => nw F (modal_K _ _
    (nec% (fun (h : ∃ q, F q ∧ ∀ r, F r → r = q) =>
      h.elim fun q hq => (⟨q, hq.1⟩ : ∃ q, F q))) hf)

theorem extensionality_unique_witness : Extensionality Prop → NecessaryUniqueWitness :=
  fun ext => witness_unique_witness (extensionality_necessary_witness ext)

theorem necessary_unique_witness_iff_extensionality :
    NecessaryUniqueWitness ↔ Extensionality Prop :=
  ⟨unique_witness_extensionality, extensionality_unique_witness⟩

theorem modal_plenitude_unique_witness : ModalPlenitude Prop Prop → NecessaryUniqueWitness := by
  intro mp F hf
  have hu : □ (Functional (fun (_ : Prop) q => F q)) := modal_K _ _
    (nec% (fun (h : ∃ q, F q ∧ ∀ r, F r → r = q) (_ : Prop) =>
      h.elim fun q hq => (⟨q, hq.1, fun r hr => (hq.2 r hr).symm⟩ :
        ∃ q, F q ∧ ∀ r, F r → q = r))) hf
  obtain ⟨f, h⟩ := mp (fun (_ : Prop) q => F q) hu
  exact ⟨f True, converse_barcan (fun x => F (f x)) h True⟩

theorem modal_plenitude_extensionality {τ : Type} [Rel τ] :
    ModalPlenitude Prop Prop → Extensionality τ :=
  fun mp => unique_witness_extensionality (modal_plenitude_unique_witness mp)

theorem extensionality_modal_plenitude {ν σ : Type} [Ty ν] [Ty σ] :
    Extensionality Prop → ModalPlenitude σ (ν → Prop) := by
  intro ext U hu
  have fa := Proofs.extensionality_r_implies_fregean_axiom ext
  have hf : ∀ x, U x (decodePair U x) := by
    intro x
    obtain ⟨y, hy, huniq⟩ := box_elim hu x
    have he : decodePair U x = y :=
      Proofs.fregean_axiom_implies_extensionality_r fa _ _
        (unique_decode_coext U x y ⟨hy, fun z hz => (huniq z hz).symm⟩)
    exact Eq.mpr (congrArg (U x) he) hy
  exact ⟨decodePair U, Proofs.box_of_fregean fa _ hf⟩

theorem modal_functional_choice_plenitude {σ τ : Type} [Ty σ] [Rel τ] :
    ModalFunctionalChoice σ τ → ModalPlenitude σ τ :=
  fun mfc U hu => mfc U (modal_K _ _
    (nec% (fun (h : Functional U) x =>
      (h x).elim fun y hy => (⟨y, hy.1⟩ : ∃ y, U x y))) hu)

theorem functional_choice_modal_of_extensionality {σ τ : Type} [Ty σ] [Rel τ] :
    Extensionality Prop → FunctionalChoice σ τ → ModalFunctionalChoice σ τ :=
  fun ext fc U hu => (fc U (box_elim hu)).elim fun f hf =>
    ⟨f, Proofs.box_of_fregean (Proofs.extensionality_r_implies_fregean_axiom ext) _ hf⟩

theorem modal_choice_ordinary_of_extensionality {σ τ : Type} [Ty σ] [Rel τ] :
    Extensionality Prop → ModalFunctionalChoice σ τ → FunctionalChoice σ τ :=
  fun ext mfc U hu => (mfc U
    (Proofs.box_of_fregean (Proofs.extensionality_r_implies_fregean_axiom ext) _ hu)).elim
      fun f hf => ⟨f, box_elim hf⟩

end Classicism.Research.Splitting

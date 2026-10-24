import Classicism.Results.Research.FregeNoncollapse
import Classicism.Principles.Choice

/-!
# Pure Maximalism and numerical predecessor operations: the C argument

Direct source: research/2026-10-22/notes/relational-coding-recursion-20261022.md
§38 (original research, unpaginated, misc). The separate metalogical certificate
discharges the finite-model and pure-Max side conditions. This module assumes
neither Max nor consistency as a new shallow axiom.
-/

namespace Classicism.Research.MaxPredecessor
open Classicism.Research.FregeNoncollapse

variable {σ : Type} [Ty σ]

def PredOp (σ : Type) [Ty σ] : Prop :=
  ∃ f : ((σ → Prop) → Prop) → (σ → Prop) → Prop,
    ∀ n, FiniteCardinality n → f (SucCard n) = n

def One (σ : Type) [Ty σ] : (σ → Prop) → Prop := SucCard (ZeroCard σ)
def Two (σ : Type) [Ty σ] : (σ → Prop) → Prop := SucCard (One σ)
def Three (σ : Type) [Ty σ] : (σ → Prop) → Prop := SucCard (Two σ)

def Collision (σ : Type) [Ty σ] : Prop := Two σ = Three σ ∧ One σ ≠ Two σ

theorem one_number : FiniteCardinality (One σ) :=
  finiteCardinality_suc _ finiteCardinality_zero

theorem two_number : FiniteCardinality (Two σ) :=
  finiteCardinality_suc _ one_number

theorem equations_exclude_collision
    (f : ((σ → Prop) → Prop) → (σ → Prop) → Prop)
    (a b : (σ → Prop) → Prop)
    (ha : f (SucCard a) = a) (hb : f (SucCard b) = b) :
    ¬ (SucCard a = SucCard b ∧ a ≠ b) :=
  fun h => h.2 (ha.symm.trans ((congrArg f h.1).trans hb))

/-- Only the two operation equations are made necessary. Neither the universal
predecessor law nor either optional hypothesis is necessitated. -/
theorem collision_excludes_predecessor (a b : (σ → Prop) → Prop)
    (ha : FiniteCardinality a) (hb : FiniteCardinality b) :
    ◇ (SucCard a = SucCard b ∧ a ≠ b) → ¬ PredOp σ := by
  intro hd hp
  obtain ⟨f, hf⟩ := hp
  exact not_dia_of_box_not _
    (modal_K _ _ (modal_K _ _ (nec% (equations_exclude_collision f a b))
      (necessity_of_identity _ _ (hf a ha)))
      (necessity_of_identity _ _ (hf b hb))) hd

theorem possible_collision_excludes_predecessor : ◇ (Collision σ) → ¬ PredOp σ :=
  collision_excludes_predecessor (One σ) (Two σ) one_number two_number

theorem predecessor_implies_noncollapse (h : PredOp σ) : Noncollapse σ := by
  obtain ⟨f, hf⟩ := h
  intro m n hm hn he
  exact (hf m hm).symm.trans ((congrArg f he).trans (hf n hn))

theorem predecessor_implies_arithmeticI (h : PredOp σ) : ArithmeticI σ :=
  arithmeticI_iff_istar.2 (istar_iff_noncollapse.2 (predecessor_implies_noncollapse h))

/-- The canonical total predecessor graph, including nonnumbers and zero. -/
def PredGraph (x y : (σ → Prop) → Prop) : Prop :=
  (FiniteCardinality x ∧ x ≠ ZeroCard σ ∧ FiniteCardinality y ∧ x = SucCard y) ∨
    ((¬ FiniteCardinality x ∨ x = ZeroCard σ) ∧ y = ZeroCard σ)

theorem graph_successor (n : (σ → Prop) → Prop) (hn : FiniteCardinality n) :
    PredGraph (SucCard n) n :=
  Or.inl ⟨finiteCardinality_suc n hn,
    fun h => frege_zero_ne_suc n h.symm, hn, rfl⟩

theorem graph_total (x : (σ → Prop) → Prop) : ∃ y, PredGraph x y := by
  apply (em (FiniteCardinality x)).elim
  · intro hx
    apply (frege_cases x hx).elim
    · intro hz
      exact ⟨ZeroCard σ, Or.inr ⟨Or.inr hz, rfl⟩⟩
    · intro hs
      obtain ⟨y, hy, he⟩ := hs
      exact ⟨y, Or.inl ⟨hx, fun hz => frege_zero_ne_suc y (hz.symm.trans he), hy, he⟩⟩
  · intro hx
    exact ⟨ZeroCard σ, Or.inr ⟨Or.inl hx, rfl⟩⟩

theorem graph_single_valued (h : Noncollapse σ)
    (x y z : (σ → Prop) → Prop) (hy : PredGraph x y) (hz : PredGraph x z) : y = z := by
  apply hy.elim
  · intro hy
    apply hz.elim
    · intro hz
      exact h y z hy.2.2.1 hz.2.2.1 (hy.2.2.2.symm.trans hz.2.2.2)
    · intro hz
      exact (hz.1.elim (fun hn => hn hy.1) hy.2.1).elim
  · intro hy
    apply hz.elim
    · intro hz
      exact (hy.1.elim (fun hn => hn hz.1) hz.2.1).elim
    · intro hz
      exact hy.2.trans hz.2.symm

theorem graph_functional (h : ArithmeticI σ) :
    P.Functional (PredGraph (σ := σ)) := by
  intro x
  obtain ⟨y, hy⟩ := graph_total x
  exact ⟨y, hy, fun z hz => graph_single_valued
    (istar_iff_noncollapse.1 (arithmeticI_iff_istar.1 h)) x y z hy hz⟩

theorem plenitude_supplies_predecessor
    (hp : P.Plenitude ((σ → Prop) → Prop) ((σ → Prop) → Prop))
    (h : ArithmeticI σ) : PredOp σ := by
  obtain ⟨f, hf⟩ := hp PredGraph (graph_functional h)
  refine ⟨f, fun n hn => ?_⟩
  exact graph_single_valued
    (istar_iff_noncollapse.1 (arithmeticI_iff_istar.1 h))
    (SucCard n) (f (SucCard n)) n (hf (SucCard n)) (graph_successor n hn)

end Classicism.Research.MaxPredecessor

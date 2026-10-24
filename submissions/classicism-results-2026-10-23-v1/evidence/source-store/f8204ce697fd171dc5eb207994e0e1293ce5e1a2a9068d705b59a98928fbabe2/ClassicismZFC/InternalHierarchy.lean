import ClassicismZFC.Product
import ClassicismZFC.RawTranslation
import Classicism.Models.CoalescedInternalHierarchy
import Classicism.Models.CoalescedFirstOrder

/-!
# An actual typed component from an ordinary first-order ZFC model

Original formalization (misc), 23 October 2026. The input is satisfaction of
the source's explicit ZFC theory, together with an internally inhabited set
for the individual sort. Every primitive hierarchy law is proved from that
theory, and every typed comprehension instance is derived by translating its
finite syntax and applying the finite first-order Separation theorem.

No transitivity, external well-foundedness, standardness, term-closure field,
or truth-transfer field is assumed. The default omega component is only an
example of an inhabited base. It asserts neither that this base is a real
structure nor that a source CH sentence has been identified with typed CH.
-/

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open Erdos501.FOL (L memM)
open Classicism.Meta
open Classicism.Meta.Intensional.Coalesced (One)
open ClassicismZFC.SetLaws (emptyM unitSet pairM powerM omegaM)

namespace ClassicismZFC.InternalHierarchy

variable {M : Type} [L.Structure M]

/-- All fields are established set-theoretic laws. In particular the
Separation field is filled from the finite syntactic translation theorem. -/
noncomputable def internalUniverse (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM x E) : CoalescedInternalHierarchy.Universe where
  Carrier := M
  mem := memM
  ext := SetLaws.ext hZFC
  unit := emptyM
  unitSet := unitSet
  unit_mem := SetLaws.unit_mem hZFC
  pair := pairM
  pair_injective := SetLaws.pair_injective hZFC
  product := Product.product hZFC
  product_mem := Product.product_mem hZFC
  power := powerM
  power_mem := SetLaws.power_mem hZFC
  individuals := E
  individuals_nonempty := hE
  separation := by
    intro Γ φ g A
    obtain ⟨n, ψ, p, hψ⟩ := RawTranslation.unary_formula φ g
    obtain ⟨B, hB⟩ := Separation.separation hZFC n ψ p A
    refine ⟨B, fun x => ?_⟩
    have hψx : ψ.Realize default (Fin.snoc p x) ↔ φ.Realize memM pairM (.cons x g) := by
      exact Eq.mp (congrArg (fun v : Empty → M =>
        ψ.Realize v (Fin.snoc p x) ↔ φ.Realize memM pairM (.cons x g))
        (show (fun e : Empty => nomatch e) = (default : Empty → M)
          from Subsingleton.elim _ _)) (hψ x)
    exact (hB x).trans (and_congr Iff.rfl hψx)

noncomputable def typedStructure (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM x E) : ChoiceFirstOrder.Structure :=
  CoalescedInternalHierarchy.typedStructure (internalUniverse hZFC E hE)

theorem smallComprehension (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM x E) :
    ChoiceFirstOrder.SmallComprehension (typedStructure hZFC E hE) :=
  CoalescedInternalHierarchy.smallComprehension (internalUniverse hZFC E hE)

theorem firstOrder_isModel (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM x E) : (typedStructure hZFC E hE).model.IsModel :=
  CoalescedInternalHierarchy.isModel (internalUniverse hZFC E hE)

/-- The same concrete domains and profiles on the singleton category used
by the coalesced-model construction. -/
noncomputable def component (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM x E) : Intensional.Premodel Signature.pure One :=
  Intensional.Coalesced.FirstOrderBridge.model (typedStructure hZFC E hE)

theorem component_isModel (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM x E) : (component hZFC E hE).IsModel :=
  Intensional.Coalesced.FirstOrderBridge.isModel (typedStructure hZFC E hE)
    (smallComprehension hZFC E hE)

/-- Every sort is inhabited. At relational sorts this follows from the
derived empty-relation comprehension instance, not an extra domain premise. -/
theorem domain_nonempty (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM x E) (σ : Ty) : Nonempty ((typedStructure hZFC E hE).D σ) := by
  cases σ with
  | e => exact (typedStructure hZFC E hE).nonempty_e
  | var i =>
    obtain ⟨x, hx⟩ := hE
    exact ⟨⟨x, hx⟩⟩
  | rel ρ =>
    obtain ⟨X, _⟩ := smallComprehension hZFC E hE [] ρ
      ChoiceFirstOrder.SmallFormula.falsum IEnv.nil
    exact ⟨X⟩

theorem component_nonempty (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM x E) (W : One) (σ : Ty) :
    Nonempty ((component hZFC E hE).Dom W σ) :=
  domain_nonempty hZFC E hE σ

/-- Exact satisfaction of the explicitly translated finite membership
formula. Identifying a separate source-theory CH sentence is additional work. -/
theorem component_sentence (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM x E) (p : Classicism.Meta.Sentence Signature.pure) :
    (component hZFC E hE).HoldsSentence p ↔
      (CoalescedInternalHierarchy.translate (internalUniverse hZFC E hE)
        (ChoiceFirstOrder.smallSentenceTranslation p)).Realize
          (memM (M := M)) (pairM (M := M)) IEnv.nil :=
  (Intensional.Coalesced.FirstOrderBridge.holdsSentence_iff (typedStructure hZFC E hE) p).trans
    (CoalescedInternalHierarchy.sentence_correct (internalUniverse hZFC E hE) p).symm

/-- A concrete inhabited-base example, with no real-field or CH claim. -/
noncomputable def omegaComponent (hZFC : M ⊨ Erdos501.FOL.ZFC) :
    Intensional.Premodel Signature.pure One :=
  component hZFC omegaM (SetLaws.omega_nonempty hZFC)

theorem omegaComponent_isModel (hZFC : M ⊨ Erdos501.FOL.ZFC) :
    (omegaComponent hZFC).IsModel :=
  component_isModel hZFC omegaM (SetLaws.omega_nonempty hZFC)

#print axioms internalUniverse
#print axioms component_isModel
#print axioms component_nonempty
#print axioms component_sentence

end ClassicismZFC.InternalHierarchy

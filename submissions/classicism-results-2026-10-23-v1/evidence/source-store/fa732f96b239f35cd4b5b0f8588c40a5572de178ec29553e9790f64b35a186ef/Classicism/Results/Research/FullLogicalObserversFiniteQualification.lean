import Classicism.Results.Research.FullLogicalObserversCharacterization

/-!
# Combinators for simultaneous finite observer qualifications

Direct source: `research/2026-10-23/operator-characterizations/positive-operator-representation.txt`,
sections 1--3 (misc, original research, 23 October 2026, unpaginated).
The object predicate X is an additional qualification of one observer. Its
finite conjunctions will be built externally from a list of admitted types.
Every conjunct is proved for the same term `PatchedPrincipal a`.
-/

namespace Classicism.Research.FullLogicalObservers.FiniteQualification
open Classicism.P Classicism.Paper

def TrueQualification (_O : Prop → Prop) : Prop := True
def ConjoinQualification (X Y : (Prop → Prop) → Prop) (O : Prop → Prop) : Prop :=
  X O ∧ Y O
def QuantifierCondition (σ : Type) [Ty σ] (O : Prop → Prop) : Prop :=
  QuantifierFull σ O
def AtomQualification (X : (Prop → Prop) → Prop) : Prop :=
  ∀ a : Prop, Atom a → BoolFull (PatchedPrincipal a) ∧ X (PatchedPrincipal a)
def SeparationCondition (X : (Prop → Prop) → Prop) : Prop := SeparationBy X
def C5Condition : Prop := NecNecessityOfDistinctness Prop
def AtomicCondition : Prop := Atomicity Prop
def ActualCondition : Prop := Actuality

theorem c5_qualified_nil (c5 : C5Condition) : AtomQualification TrueQualification :=
  fun a ha => ⟨patched_boolFull a (Proofs.necessary_nd_implies_bf c5) ha, trivial⟩

theorem c5_qualified_cons {σ : Type} [Ty σ] (X : (Prop → Prop) → Prop)
    (c5 : C5Condition) (hX : AtomQualification X) :
    AtomQualification (ConjoinQualification (QuantifierCondition σ) X) :=
  fun a ha => ⟨(hX a ha).1,
    patched_quantifierFull a (hX a ha).1
      (Proofs.necessary_distinctness_necessary_r_implies_necessary_barcan_r c5),
    (hX a ha).2⟩

theorem qualified_separation (X : (Prop → Prop) → Prop)
    (hat : AtomicCondition) (hX : AtomQualification X) : SeparationCondition X :=
  atomicity_separation_by X hat hX

theorem c5_necessary_qualified_nil (c5 : C5Condition) :
    □ (AtomQualification TrueQualification) :=
  modal_K _ _ (nec% c5_qualified_nil) (modal_four _ c5)

theorem c5_necessary_qualified_cons {σ : Type} [Ty σ] (X : (Prop → Prop) → Prop)
    (c5 : C5Condition) (hX : □ (AtomQualification X)) :
    □ (AtomQualification (ConjoinQualification (QuantifierCondition σ) X)) :=
  modal_K _ _ (modal_K _ _ (nec% (c5_qualified_cons (σ := σ) X))
    (modal_four _ c5)) hX

theorem qualified_necessary_separation (X : (Prop → Prop) → Prop)
    (c5 : C5Condition) (hat : AtomicCondition) (hX : □ (AtomQualification X)) :
    □ (SeparationCondition X) :=
  modal_K _ _ (modal_K _ _ (nec% (qualified_separation X))
    (c5_atomicity_necessary_atomicity hat c5)) hX

theorem singleton_separation
    (hs : SeparationCondition
      (ConjoinQualification (QuantifierCondition Prop) TrueQualification)) :
    SeparationFull Prop := fun p q =>
  ⟨fun he O hO => (hs p q).1 he O ⟨hO.1, hO.2, trivial⟩,
    fun h => (hs p q).2 (fun O hO => h O ⟨hO.1, hO.2.1⟩)⟩

theorem c5_actuality_singleton_atomicity (c5 : C5Condition) (act : ActualCondition)
    (hs : SeparationCondition
      (ConjoinQualification (QuantifierCondition Prop) TrueQualification)) :
    AtomicCondition :=
  c5_actuality_full_separation_atomicity c5 act (singleton_separation hs)

theorem c5_actuality_necessary_singleton_atomicity
    (c5 : C5Condition) (act : ActualCondition)
    (hs : □ (SeparationCondition
      (ConjoinQualification (QuantifierCondition Prop) TrueQualification))) :
    AtomicCondition :=
  c5_actuality_singleton_atomicity c5 act (box_elim hs)

end Classicism.Research.FullLogicalObservers.FiniteQualification

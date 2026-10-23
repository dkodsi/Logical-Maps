import Classicism.Results.Research.MaxAtomicitySetCodeAbsoluteness
import Classicism.Results.Research.MaxAtomicityJechShelahSyntax

/-!
# Actual small function graphs in the canonical membership presentation

The graph is constructed by hereditary-small range and finite pairing.
Application, functionhood, domain, and injectivity are then proved for the
actual finite relational predicates. No graph or formula correctness premise
is assumed. Original coding proof (misc, 23 October 2026, unpaginated).
Compilation belongs to the designated serial checker.
-/

namespace Classicism.Meta.Research.MaxAtomicityCodedFunctions

open MaxAtomicityHereditaryCover MaxAtomicityHereditaryUniverse
open MaxAtomicityHereditaryGraphs MaxAtomicitySetCodeAbsoluteness
open MaxAtomicityJechShelahCylinders MaxAtomicitySetFormulaTools

noncomputable section

variable {A : Type}

def functionCode (e : A ↪ B) (f g : A → (B → B)) : B → B :=
  encode B (graphOf (fun a => present B (f a)) (fun a => present B (g a)))
    ((mem_universeSet B _).2
      (graphOf_hereditary B e _ _ (fun a => present_hereditary B (f a))
        (fun a => present_hereditary B (g a))))

@[simp] theorem present_functionCode (e : A ↪ B) (f g : A → (B → B)) :
    present B (functionCode e f g) =
      graphOf (fun a => present B (f a)) (fun a => present B (g a)) :=
  present_encode B _ _

theorem functionCode_app (e : A ↪ B) (f g : A → (B → B)) (x y : B → B) :
    Ordinary.GraphApp (codeRelation B) (functionCode e f g) x y ↔
      ∃ a, f a = x ∧ g a = y := by
  rw [graphApp_iff, present_functionCode, mem_graphOf]
  apply exists_congr
  intro a
  exact and_congr (equal_iff B (f a) x).symm (equal_iff B (g a) y).symm

theorem functionCode_onlyPairs (e : A ↪ B) (f g : A → (B → B)) :
    Ordinary.GraphOnlyPairs (codeRelation B) (functionCode e f g) := by
  intro p hp
  change present B p ∈ present B (functionCode e f g) at hp
  rw [present_functionCode, graphOf, ZFSet.mem_range] at hp
  obtain ⟨a, ha⟩ := hp
  exact ⟨f a, g a, (orderedPair_iff B _ _ _).2 ha.symm⟩

theorem functionCode_function (e : A ↪ B) (f g : A → (B → B))
    (hf : Function.Injective f) :
    Ordinary.FunctionGraph (codeRelation B) (functionCode e f g) := by
  refine ⟨functionCode_onlyPairs e f g, ?_⟩
  intro x y z h
  obtain ⟨a, hax, hay⟩ := (functionCode_app e f g x y).1 h.1
  obtain ⟨b, hbx, hbz⟩ := (functionCode_app e f g x z).1 h.2
  have hab : a = b := hf (hax.trans hbx.symm)
  subst b
  exact hay.symm.trans hbz

theorem functionCode_domain (e : A ↪ B) (f g : A → (B → B)) (d : B → B)
    (hd : ∀ x, codeRelation B x d ↔ ∃ a, f a = x) :
    Ordinary.GraphDomain (codeRelation B) (functionCode e f g) d := by
  intro x
  rw [hd x]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨g a, (functionCode_app e f g _ _).2 ⟨a, rfl, rfl⟩⟩
  · rintro ⟨y, hy⟩
    obtain ⟨a, ha, _⟩ := (functionCode_app e f g x y).1 hy
    exact ⟨a, ha⟩

theorem functionCode_injective (e : A ↪ B) (f g : A → (B → B))
    (hg : Function.Injective g) :
    MaxAtomicityJechShelahSyntax.Ordinary.InjectiveGraph (codeRelation B)
      (functionCode e f g) := by
  intro x y z h
  obtain ⟨a, hax, haz⟩ := (functionCode_app e f g x z).1 h.1
  obtain ⟨b, hby, hbz⟩ := (functionCode_app e f g y z).1 h.2
  have hab : a = b := hg (haz.trans hbz.symm)
  subst b
  exact hax.symm.trans hby

#print axioms functionCode_app
#print axioms functionCode_function
#print axioms functionCode_domain
#print axioms functionCode_injective

end

end Classicism.Meta.Research.MaxAtomicityCodedFunctions

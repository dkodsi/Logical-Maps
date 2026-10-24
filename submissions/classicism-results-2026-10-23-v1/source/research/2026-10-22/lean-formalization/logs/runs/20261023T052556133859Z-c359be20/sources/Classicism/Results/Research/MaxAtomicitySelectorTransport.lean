import Classicism.Results.Research.MaxAtomicitySetCodeAbsoluteness

/-!
# Transporting canonical formula adequacy to every successful universe code

Presentation transport is proved for an actual membership equivalence, including
the quantified subset and ordered-pair graph predicates. The previously proved
Mostowski canonicalChange then reduces the selector's complete adequacy
obligation to two concrete first-order facts in one fixed hereditary universe:
the displayed canonical triple satisfies phi, and every satisfying triple has
those same three values.

Those two formula-specific facts are explicit hypotheses here. No assertion
that JSCode satisfies them is made by this bridge, and no selector conclusion
is included among its hypotheses. Original formal proof: misc, 23 October 2026.
Source awaits the designated serial checker.
-/

namespace Classicism.Meta.Research.MaxAtomicitySelectorTransport

open MaxAtomicitySetSyntax MaxAtomicitySetSemantics MaxAtomicitySetFormulaTools
open MaxAtomicityHCodeSemantics MaxAtomicityHCodeExistence
open MaxAtomicityHCodeCharacterization MaxAtomicityHereditaryUniverse
open MaxAtomicityPureSelector MaxAtomicitySetCodeAbsoluteness
open MaxAtomicityJechShelahCylinders MaxAtomicityJechShelahIndexedGenerators

noncomputable section

theorem map_triple {D D' : Type*} (e : D → D') (a b c : D) :
    (fun i => e (triple a b c i)) = triple (e a) (e b) (e c) := by
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ Fin.elim0)) i <;> rfl

theorem subset_equiv {D D' : Type} (R : D → D → Prop) (R' : D' → D' → Prop)
    (e : D ≃ D') (he : ∀ a b, R a b ↔ R' (e a) (e b)) (a b : D) :
    Ordinary.Subset R a b ↔ Ordinary.Subset R' (e a) (e b) := by
  constructor
  · intro h z hz
    obtain ⟨d, rfl⟩ := e.surjective z
    exact (he d b).1 (h d ((he d a).2 hz))
  · intro h d hd
    exact (he d b).2 (h (e d) ((he d a).1 hd))

theorem graphApp_equiv {D D' : Type} (R : D → D → Prop) (R' : D' → D' → Prop)
    (e : D ≃ D') (he : ∀ a b, R a b ↔ R' (e a) (e b)) (G a b : D) :
    Ordinary.GraphApp R G a b ↔ Ordinary.GraphApp R' (e G) (e a) (e b) :=
  satisfies_equiv R R' e he (graphApp (0 : Fin 3) 1 2) (triple G a b)

section General

variable {A : Type} [CompleteBooleanAlgebra A]
variable {D D' : Type} {R : D → D → Prop} {R' : D' → D' → Prop}
variable {c w G : D} {g : ℕ → A}

/-- Pull every actual canonical datum back through a membership equivalence.
No standardness or graph-law assumption is added during transport. -/
def pullbackPresentation (e : D ≃ D') (he : ∀ a b, R a b ↔ R' (e a) (e b))
    (P : Presentation R' (e c) (e w) (e G) g) : Presentation R c w G g where
  carrier := P.carrier.trans e.symm.toEmbedding
  carrier_range := by
    intro a
    rw [he, P.carrier_range]
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨b, (congrArg e.symm hb).trans (e.symm_apply_apply a)⟩
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      have hh := congrArg e hb
      change e (e.symm (P.carrier b)) = e a at hh
      simpa only [e.apply_symm_apply] using hh
  carrier_order := by
    intro a b
    change Ordinary.Subset R (e.symm (P.carrier a)) (e.symm (P.carrier b)) ↔ a ≤ b
    rw [subset_equiv R R' e he, e.apply_symm_apply, e.apply_symm_apply]
    exact P.carrier_order a b
  number := P.number.trans e.symm.toEmbedding
  number_range := by
    intro a
    rw [he, P.number_range]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, (congrArg e.symm hk).trans (e.symm_apply_apply a)⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have hh := congrArg e hk
      change e (e.symm (P.number k)) = e a at hh
      simpa only [e.apply_symm_apply] using hh
  predecessor := by
    intro k a
    change R a (e.symm (P.number k)) ↔
      ∃ j, j < k ∧ e.symm (P.number j) = a
    rw [he, e.apply_symm_apply, P.predecessor]
    apply exists_congr
    intro j
    apply and_congr Iff.rfl
    constructor
    · intro hj
      exact (congrArg e.symm hj).trans (e.symm_apply_apply a)
    · intro hj
      have hh := congrArg e hj
      simpa only [e.apply_symm_apply] using hh
  graph := by
    intro k a
    change Ordinary.GraphApp R G (e.symm (P.number k)) a ↔
      a = e.symm (P.carrier (g k))
    rw [graphApp_equiv R R' e he, e.apply_symm_apply, P.graph]
    constructor
    · intro ha
      exact (e.symm_apply_apply a).symm.trans (congrArg e.symm ha)
    · intro ha
      simpa only [e.apply_symm_apply] using congrArg e ha

end General

/-- The two concrete formula facts still to be proved by the JS coding module.
They are stated in the one canonical code relation, not arbitrary BV models. -/
def CanonicalSound (phi : SetFormula 3) : Prop :=
  ∀ c w G : B → B,
    satisfies phi (codeRelation B) (triple c w G) →
      c = canonicalCarrier ∧ w = canonicalNaturals ∧ G = canonicalGraph

def CanonicalExists (phi : SetFormula 3) : Prop :=
  satisfies phi (codeRelation B)
    (triple canonicalCarrier canonicalNaturals canonicalGraph)

/-- Mostowski collapse and formula invariance supply the sound field for ALL
successful universe codes from the single canonical characterization. -/
theorem adequate_of_canonical (phi : SetFormula 3)
    (hsound : CanonicalSound phi) (hexists : CanonicalExists phi) :
    Adequate phi indexedGenerator := by
  classical
  refine ⟨?_, ?_⟩
  · intro E c w G hcode
    let R : (B → B) → (B → B) → Prop := fun a b => E a b = ⊤
    have hgood : GoodRelation (B := B) R := hcode.2.1
    let e := canonicalChange R hgood
    have he : ∀ a b, R a b ↔ codeRelation B (e a) (e b) :=
      canonicalChange_membership R hgood
    have hs : satisfies phi (codeRelation B) (triple (e c) (e w) (e G)) := by
      have h := (satisfies_canonicalChange R hgood phi (triple c w G)).1 hcode.2.2
      simpa only [map_triple] using h
    obtain ⟨hc, hw, hG⟩ := hsound (e c) (e w) (e G) hs
    have P : Presentation (codeRelation B) (e c) (e w) (e G) indexedGenerator := by
      rw [hc, hw, hG]
      exact canonicalPresentation
    exact ⟨pullbackPresentation e he P⟩
  · let E : (B → B) → (B → B) → B := fun a b => truth (codeRelation B a b)
    have hR : (fun a b => E a b = ⊤) = codeRelation B := by
      funext a b
      exact propext (truth_eq_top_iff (codeRelation B a b))
    refine ⟨E, canonicalCarrier, canonicalNaturals, canonicalGraph, ?_, ?_, ?_⟩
    · intro a b
      exact truth_predicate_crisp (fun z => codeRelation B a z) b
    · rw [hR]
      exact codeRelation_good
    · rw [hR]
      exact hexists

/-- Equivalent convenient interface if the formula author proves one iff. -/
theorem adequate_of_canonical_iff (phi : SetFormula 3)
    (h : ∀ c w G : B → B,
      satisfies phi (codeRelation B) (triple c w G) ↔
        c = canonicalCarrier ∧ w = canonicalNaturals ∧ G = canonicalGraph) :
    Adequate phi indexedGenerator :=
  adequate_of_canonical phi (fun c w G hs => (h c w G).1 hs)
    ((h canonicalCarrier canonicalNaturals canonicalGraph).2 ⟨rfl, rfl, rfl⟩)

#print axioms subset_equiv
#print axioms graphApp_equiv
#print axioms pullbackPresentation
#print axioms adequate_of_canonical
#print axioms adequate_of_canonical_iff

end

end Classicism.Meta.Research.MaxAtomicitySelectorTransport

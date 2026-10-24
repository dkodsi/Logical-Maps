import Classicism.Principles.Choice
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Translate

/-!
# Selector and Functional Choice reductions

Research source: `research/2026-10-22/followup/finite-functional-choice.md`,
§§5, 7 and 10. These are fixed-type formulas of C, not quantifiers over types.
All operation outputs are relational. The final commands request the gate, the
type check and actual object-language derivations. Until those commands have
successfully compiled, this is a proof submission, not a verified certificate.

No forcing model, choice axiom, Functionality or optional-premise equivalence is
used. The retraction hypotheses in the general transfer lemmas remain explicit.
-/

namespace Classicism.ChoiceHierarchy

/-- A local selector on one fixed relational type. -/
def Selector (τ : Type) [Rel τ] : Prop :=
  ∃ ε : (τ → Prop) → τ, ∀ P : τ → Prop, (∃ y, P y) → P (ε P)

theorem selector_of_functionalChoice {τ : Type} [Rel τ] :
    P.FunctionalChoice (τ → Prop) τ → Selector τ := by
  intro fc
  have hs : P.Serial (fun (Q : τ → Prop) (y : τ) => (∃ z, Q z) → Q y) := by
    intro Q
    exact (em (∃ z, Q z)).elim
      (fun h => h.elim fun y hy => ⟨y, fun _ => hy⟩)
      (fun h => ⟨Rel.top τ, fun hz => False.elim (h hz)⟩)
  exact fc _ hs

theorem functionalChoice_of_selector {σ τ : Type} [Ty σ] [Rel τ] :
    Selector τ → P.FunctionalChoice σ τ := by
  rintro ⟨ε, hε⟩ U hs
  exact ⟨fun x => ε (U x), fun x => hε (U x) (hs x)⟩

theorem selector_iff_functionalChoice {τ : Type} [Rel τ] :
    Selector τ ↔ P.FunctionalChoice (τ → Prop) τ :=
  ⟨functionalChoice_of_selector, selector_of_functionalChoice⟩

theorem boxed_selector_of_boxed_functionalChoice {τ : Type} [Rel τ] :
    P.NecFunctionalChoice (τ → Prop) τ → □ (Selector τ) :=
  fun h => modal_K _ _ (nec% (selector_of_functionalChoice (τ := τ))) h

theorem boxed_functionalChoice_of_boxed_selector {σ τ : Type} [Ty σ] [Rel τ] :
    □ (Selector τ) → P.NecFunctionalChoice σ τ :=
  fun h => modal_K _ _ (nec% (functionalChoice_of_selector (σ := σ) (τ := τ))) h

/-- Equality of haecceities implies identity; no Functionality is used. -/
theorem haecceity_injective {σ : Type} [Ty σ] (x y : σ) :
    (fun z : σ => z = x) = (fun z : σ => z = y) → x = y :=
  fun h => Eq.mp (congrFun h x) rfl

/-- Transfer a selector along an explicitly given retraction. -/
theorem selector_retract {α β : Type} [Rel α] [Rel β]
    (i : α → β) (r : β → α) :
    (∀ x, r (i x) = x) → Selector β → Selector α := by
  intro hr
  rintro ⟨ε, hε⟩
  refine ⟨fun Q => r (ε (fun z => ∃ y, Q y ∧ z = i y)), ?_⟩
  intro Q hQ
  have himage : ∃ z, ∃ y, Q y ∧ z = i y :=
    hQ.elim fun y hy => ⟨i y, y, hy, rfl⟩
  obtain ⟨y, hy, hz⟩ := hε (fun z => ∃ y, Q y ∧ z = i y) himage
  change Q (r (ε (fun z => ∃ y, Q y ∧ z = i y)))
  rw [hz, hr y]
  exact hy

/-- The analogous output transfer for one fixed input type. -/
theorem functionalChoice_output_retract {σ α β : Type} [Ty σ] [Rel α] [Rel β]
    (i : α → β) (r : β → α) :
    (∀ x, r (i x) = x) → P.FunctionalChoice σ β → P.FunctionalChoice σ α := by
  intro hr fc U hs
  have hs' : P.Serial (fun x z => U x (r z)) := by
    intro x
    obtain ⟨y, hy⟩ := hs x
    refine ⟨i y, ?_⟩
    change U x (r (i y))
    rw [hr y]
    exact hy
  obtain ⟨f, hf⟩ := fc _ hs'
  exact ⟨fun x => r (f x), hf⟩

/-- Input raising by haecceity codes, including individual inputs. -/
theorem functionalChoice_input_haecceity {σ τ : Type} [Ty σ] [Rel τ] :
    P.FunctionalChoice (σ → Prop) τ → P.FunctionalChoice σ τ := by
  intro fc U hs
  have hs' : P.Serial (fun (Q : σ → Prop) (y : τ) =>
      (∃ x, Q = (fun z => z = x) ∧ U x y) ∨ ¬ ∃ x, Q = (fun z => z = x)) := by
    intro Q
    exact (em (∃ x : σ, Q = (fun z => z = x))).elim
      (fun h => h.elim fun x hx => (hs x).elim fun y hy =>
        ⟨y, Or.inl ⟨x, hx, hy⟩⟩)
      (fun h => ⟨Rel.top τ, Or.inr h⟩)
  obtain ⟨f, hf⟩ := fc _ hs'
  refine ⟨fun x => f (fun z => z = x), ?_⟩
  intro x
  rcases hf (fun z => z = x) with h | h
  · obtain ⟨y, hxy, hy⟩ := h
    have he : x = y := haecceity_injective x y hxy
    rw [he] at hy ⊢
    exact hy
  · exact False.elim (h ⟨x, rfl⟩)

/-- A genuine closed H equivalence, safe for Logical Equivalence. -/
theorem decode_haecceity_prop (p : Prop) :
    (∃ q : Prop, q = p ∧ q) = p :=
  propext ⟨fun h => h.elim fun q hq => hq.1 ▸ hq.2,
    fun hp => ⟨p, rfl, hp⟩⟩

/-- The same retraction at predicate types, the shape of every tower stage. -/
theorem decode_haecceity_predicate {σ : Type} [Ty σ] (f : σ → Prop) :
    (fun x => ∃ g : σ → Prop, g = f ∧ g x) = f :=
  funext fun x => propext
    ⟨fun h => h.elim fun g hg => hg.1 ▸ hg.2,
      fun hx => ⟨f, rfl, hx⟩⟩

theorem selector_down_prop : Selector (Prop → Prop) → Selector Prop :=
  selector_retract (fun p q : Prop => q = p)
    (fun Q => ∃ p : Prop, Q p ∧ p) decode_haecceity_prop

theorem selector_down_predicate {σ : Type} [Ty σ] :
    Selector ((σ → Prop) → Prop) → Selector (σ → Prop) :=
  selector_retract (fun f g : σ → Prop => g = f)
    (fun Q x => ∃ f : σ → Prop, Q f ∧ f x) decode_haecceity_predicate

theorem boxed_selector_down_predicate {σ : Type} [Ty σ] :
    □ (Selector ((σ → Prop) → Prop)) → □ (Selector (σ → Prop)) :=
  fun h => modal_K _ _ (nec% (selector_down_predicate (σ := σ))) h

/-- The use of individual nonemptiness is exposed by this theorem's axiom report. -/
theorem decode_constant_predicate (p : Prop) : (∀ _ : e, p) = p :=
  propext ⟨fun h => e_exists.elim fun x _ => h x, fun hp _ => hp⟩

theorem selector_prop_of_selector_et : Selector (e → Prop) → Selector Prop :=
  selector_retract (fun (p : Prop) (_ : e) => p)
    (fun f => ∀ x : e, f x) decode_constant_predicate

theorem boxed_selector_prop_of_selector_et :
    □ (Selector (e → Prop)) → □ (Selector Prop) :=
  fun h => modal_K _ _ (nec% selector_prop_of_selector_et) h

/-- Diagonal Choice supplies a selector when a haecceity decoder is available.
The decoder law is an explicit hypothesis, not an imported choice principle. -/
theorem diagonal_selector_with_decoder {τ : Type} [Rel τ]
    (r : (τ → Prop) → τ) :
    (∀ y, r (fun z => z = y) = y) →
    P.FunctionalChoice (τ → Prop) (τ → Prop) → Selector τ := by
  intro hr fc
  have hs : P.Serial (fun (Q : τ → Prop) (Z : τ → Prop) =>
      (∃ y, Q y) → ∃ y, Q y ∧ Z = (fun z => z = y)) := by
    intro Q
    exact (em (∃ y, Q y)).elim
      (fun h => h.elim fun y hy => ⟨fun z => z = y, fun _ => ⟨y, hy, rfl⟩⟩)
      (fun h => ⟨fun _ => False, fun hz => False.elim (h hz)⟩)
  obtain ⟨f, hf⟩ := fc _ hs
  refine ⟨fun Q => r (f Q), ?_⟩
  intro Q hQ
  obtain ⟨y, hy, he⟩ := hf Q hQ
  change Q (r (f Q))
  rw [he, hr y]
  exact hy

theorem diagonal_selector_prop :
    P.FunctionalChoice (Prop → Prop) (Prop → Prop) → Selector Prop :=
  diagonal_selector_with_decoder (fun Q => ∃ p : Prop, Q p ∧ p) decode_haecceity_prop

theorem diagonal_selector_predicate {σ : Type} [Ty σ] :
    P.FunctionalChoice ((σ → Prop) → Prop) ((σ → Prop) → Prop) → Selector (σ → Prop) :=
  diagonal_selector_with_decoder (fun Q x => ∃ f : σ → Prop, Q f ∧ f x)
    decode_haecceity_predicate

theorem boxed_diagonal_selector_predicate {σ : Type} [Ty σ] :
    P.NecFunctionalChoice ((σ → Prop) → Prop) ((σ → Prop) → Prop) →
      □ (Selector (σ → Prop)) :=
  fun h => modal_K _ _ (nec% (diagonal_selector_predicate (σ := σ))) h

end Classicism.ChoiceHierarchy

#classicism_check
  Classicism.ChoiceHierarchy.selector_of_functionalChoice
  Classicism.ChoiceHierarchy.functionalChoice_of_selector
  Classicism.ChoiceHierarchy.selector_iff_functionalChoice
  Classicism.ChoiceHierarchy.boxed_selector_of_boxed_functionalChoice
  Classicism.ChoiceHierarchy.boxed_functionalChoice_of_boxed_selector
  Classicism.ChoiceHierarchy.haecceity_injective
  Classicism.ChoiceHierarchy.selector_retract
  Classicism.ChoiceHierarchy.functionalChoice_output_retract
  Classicism.ChoiceHierarchy.functionalChoice_input_haecceity
  Classicism.ChoiceHierarchy.decode_haecceity_prop
  Classicism.ChoiceHierarchy.decode_haecceity_predicate
  Classicism.ChoiceHierarchy.selector_down_prop
  Classicism.ChoiceHierarchy.selector_down_predicate
  Classicism.ChoiceHierarchy.boxed_selector_down_predicate
  Classicism.ChoiceHierarchy.decode_constant_predicate
  Classicism.ChoiceHierarchy.selector_prop_of_selector_et
  Classicism.ChoiceHierarchy.boxed_selector_prop_of_selector_et
  Classicism.ChoiceHierarchy.diagonal_selector_with_decoder
  Classicism.ChoiceHierarchy.diagonal_selector_prop
  Classicism.ChoiceHierarchy.diagonal_selector_predicate
  Classicism.ChoiceHierarchy.boxed_diagonal_selector_predicate

#classicism_types Classicism.ChoiceHierarchy.selector_of_functionalChoice
  Classicism.ChoiceHierarchy.functionalChoice_of_selector
  Classicism.ChoiceHierarchy.selector_iff_functionalChoice
  Classicism.ChoiceHierarchy.boxed_selector_of_boxed_functionalChoice
  Classicism.ChoiceHierarchy.boxed_functionalChoice_of_boxed_selector
  Classicism.ChoiceHierarchy.haecceity_injective
  Classicism.ChoiceHierarchy.selector_retract
  Classicism.ChoiceHierarchy.functionalChoice_output_retract
  Classicism.ChoiceHierarchy.functionalChoice_input_haecceity
  Classicism.ChoiceHierarchy.decode_haecceity_prop
  Classicism.ChoiceHierarchy.decode_haecceity_predicate
  Classicism.ChoiceHierarchy.selector_down_prop
  Classicism.ChoiceHierarchy.selector_down_predicate
  Classicism.ChoiceHierarchy.boxed_selector_down_predicate
  Classicism.ChoiceHierarchy.decode_constant_predicate
  Classicism.ChoiceHierarchy.selector_prop_of_selector_et
  Classicism.ChoiceHierarchy.boxed_selector_prop_of_selector_et
  Classicism.ChoiceHierarchy.diagonal_selector_with_decoder
  Classicism.ChoiceHierarchy.diagonal_selector_prop
  Classicism.ChoiceHierarchy.diagonal_selector_predicate
  Classicism.ChoiceHierarchy.boxed_diagonal_selector_predicate
#classicism_derive Classicism.ChoiceHierarchy.selector_of_functionalChoice
  Classicism.ChoiceHierarchy.functionalChoice_of_selector
  Classicism.ChoiceHierarchy.selector_iff_functionalChoice
  Classicism.ChoiceHierarchy.boxed_selector_of_boxed_functionalChoice
  Classicism.ChoiceHierarchy.boxed_functionalChoice_of_boxed_selector
  Classicism.ChoiceHierarchy.haecceity_injective
  Classicism.ChoiceHierarchy.selector_retract
  Classicism.ChoiceHierarchy.functionalChoice_output_retract
  Classicism.ChoiceHierarchy.functionalChoice_input_haecceity
  Classicism.ChoiceHierarchy.decode_haecceity_prop
  Classicism.ChoiceHierarchy.decode_haecceity_predicate
  Classicism.ChoiceHierarchy.selector_down_prop
  Classicism.ChoiceHierarchy.selector_down_predicate
  Classicism.ChoiceHierarchy.boxed_selector_down_predicate
  Classicism.ChoiceHierarchy.decode_constant_predicate
  Classicism.ChoiceHierarchy.selector_prop_of_selector_et
  Classicism.ChoiceHierarchy.boxed_selector_prop_of_selector_et
  Classicism.ChoiceHierarchy.diagonal_selector_with_decoder
  Classicism.ChoiceHierarchy.diagonal_selector_prop
  Classicism.ChoiceHierarchy.diagonal_selector_predicate
  Classicism.ChoiceHierarchy.boxed_diagonal_selector_predicate

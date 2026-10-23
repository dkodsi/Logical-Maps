import Classicism.ChoiceHierarchy
import Classicism.Principles.Extensionality

/-!
# Coding and inverse-operation steps for the selector hierarchy

Fixed-type C reductions from `finite-functional-choice.md` §5. Kuratowski
codes are terms of the original relational language, not Lean product types.
The graph step explicitly requires the one Functionality instance it uses.
Turning an injection into a retraction explicitly requires Plenitude.
These lemmas do not assert the recursive all-type embedding theorem or any
separation model. Gate, type and object-language derivation audits are requested
at the end; compilation is owned by the integration task.
-/

namespace Classicism.ChoiceHierarchyEncoding

def singleton {α : Type} [Ty α] (a : α) : α → Prop := fun x => x = a

def doubleton {α : Type} [Ty α] (a b : α) : α → Prop :=
  fun x => x = a ∨ x = b

/-- `{{a},{a,b}}`, without a product or set type in the object language. -/
def pairCode {α : Type} [Ty α] (a b : α) : (α → Prop) → Prop :=
  fun X => X = singleton a ∨ X = doubleton a b

theorem singleton_doubleton {α : Type} [Ty α] (a c d : α) :
    singleton a = doubleton c d → a = c ∧ a = d := by
  intro h
  have hc : c = a := Eq.mpr (congrFun h c) (Or.inl rfl)
  have hd : d = a := Eq.mpr (congrFun h d) (Or.inr rfl)
  exact ⟨hc.symm, hd.symm⟩

theorem doubleton_cancel {α : Type} [Ty α] (a b d : α) :
    doubleton a b = doubleton a d → b = d := by
  intro h
  have hb : b = a ∨ b = d := Eq.mp (congrFun h b) (Or.inr rfl)
  exact hb.elim
    (fun hba =>
      have hd : d = a ∨ d = b := Eq.mpr (congrFun h d) (Or.inr rfl)
      hd.elim (fun hda => hba.trans hda.symm) (fun hdb => hdb.symm))
    (fun hbd => hbd)

/-- Equality of intensional codes implies component identities; no appeal to
coextension-to-identity, and no Functionality assumption. -/
theorem pairCode_same_head {α : Type} [Ty α] (a b d : α)
    (h : pairCode a b = pairCode a d) : b = d := by
  apply doubleton_cancel a b d
  have hab : doubleton a b = singleton a ∨ doubleton a b = doubleton a d :=
    Eq.mp (congrFun h (doubleton a b)) (Or.inr rfl)
  apply hab.elim
  · intro habs
    have had : doubleton a d = singleton a ∨ doubleton a d = doubleton a b :=
      Eq.mpr (congrFun h (doubleton a d)) (Or.inr rfl)
    exact had.elim (fun hads => habs.trans hads.symm) (fun hadb => hadb.symm)
  · intro habd
    exact habd

theorem pairCode_injective {α : Type} [Ty α] (a b c d : α) :
    pairCode a b = pairCode c d → a = c ∧ b = d := by
  intro h
  have hhead : singleton a = singleton c ∨ singleton a = doubleton c d :=
    Eq.mp (congrFun h (singleton a)) (Or.inl rfl)
  have hac : a = c := hhead.elim
    (fun hs => ChoiceHierarchy.haecceity_injective a c hs)
    (fun hd => (singleton_doubleton a c d hd).1)
  have hsame : pairCode a b = pairCode a d := by
    rw [← hac] at h
    exact h
  exact ⟨hac, pairCode_same_head a b d hsame⟩

/-- A graph code uses three predicate levels above the common target `α`. -/
def graphCode {σ τ α : Type} [Ty σ] [Rel τ] [Rel α]
    (i : σ → α) (j : τ → α) (f : σ → τ) : ((α → Prop) → Prop) → Prop :=
  fun Z => ∃ x, Z = pairCode (i x) (j (f x))

/-- The precise Functionality dependency in the graph-injection argument. -/
theorem graphCode_injective {σ τ α : Type} [Ty σ] [Rel τ] [Rel α]
    (i : σ → α) (j : τ → α) :
    (∀ x y, i x = i y → x = y) →
    (∀ x y, j x = j y → x = y) →
    P.Functionality σ τ →
    ∀ f g : σ → τ, graphCode i j f = graphCode i j g → f = g := by
  intro hi hj hfun f g hcode
  apply hfun f g
  intro x
  have hmem : ∃ y, pairCode (i x) (j (f x)) = pairCode (i y) (j (g y)) :=
    Eq.mp (congrFun hcode (pairCode (i x) (j (f x)))) ⟨x, rfl⟩
  obtain ⟨y, he⟩ := hmem
  obtain ⟨hinput, houtput⟩ := pairCode_injective (i x) (j (f x)) (i y) (j (g y)) he
  have hxy : x = y := hi x y hinput
  rw [← hxy] at houtput
  exact hj (f x) (g x) houtput

/-- A total, single-valued inverse relation, with a relational default output. -/
theorem inverse_relation_functional {α β : Type} [Rel α] [Rel β] (i : α → β) :
    (∀ x y, i x = i y → x = y) →
    P.Functional (fun z y => i y = z ∨ ((¬ ∃ u, i u = z) ∧ y = Rel.top α)) := by
  intro hi z
  exact (em (∃ u, i u = z)).elim
    (fun h => h.elim fun y hy =>
      ⟨y, Or.inl hy, fun w hw => hw.elim
        (fun hw' => hi y w (hy.trans hw'.symm))
        (fun hw' => False.elim (hw'.1 ⟨y, hy⟩))⟩)
    (fun h =>
      ⟨Rel.top α, Or.inr ⟨h, rfl⟩, fun w hw => hw.elim
        (fun hw' => False.elim (h ⟨w, hw'⟩))
        (fun hw' => hw'.2.symm)⟩)

/-- The inverse operation is an existential witness supplied by Plenitude,
not a claimed pure inverse term and never an individual-valued operation. -/
theorem retraction_of_injection_plenitude {α β : Type} [Rel α] [Rel β]
    (i : α → β) :
    (∀ x y, i x = i y → x = y) → P.Plenitude β α →
    ∃ r : β → α, ∀ x, r (i x) = x := by
  intro hi pl
  obtain ⟨r, hr⟩ := pl _ (inverse_relation_functional i hi)
  refine ⟨r, ?_⟩
  intro x
  exact (hr (i x)).elim
    (fun h => hi (r (i x)) x h)
    (fun h => False.elim (h.1 ⟨x, rfl⟩))

theorem selector_of_injection_plenitude {α β : Type} [Rel α] [Rel β]
    (i : α → β) :
    (∀ x y, i x = i y → x = y) → P.Plenitude β α →
    ChoiceHierarchy.Selector β → ChoiceHierarchy.Selector α := by
  intro hi pl hs
  obtain ⟨r, hr⟩ := retraction_of_injection_plenitude i hi pl
  exact ChoiceHierarchy.selector_retract i r hr hs

end Classicism.ChoiceHierarchyEncoding

#classicism_check
  Classicism.ChoiceHierarchyEncoding.singleton_doubleton
  Classicism.ChoiceHierarchyEncoding.doubleton_cancel
  Classicism.ChoiceHierarchyEncoding.pairCode_injective
  Classicism.ChoiceHierarchyEncoding.graphCode_injective
  Classicism.ChoiceHierarchyEncoding.inverse_relation_functional
  Classicism.ChoiceHierarchyEncoding.retraction_of_injection_plenitude
  Classicism.ChoiceHierarchyEncoding.selector_of_injection_plenitude

#classicism_types
  Classicism.ChoiceHierarchyEncoding.singleton_doubleton
  Classicism.ChoiceHierarchyEncoding.doubleton_cancel
  Classicism.ChoiceHierarchyEncoding.pairCode_injective
  Classicism.ChoiceHierarchyEncoding.graphCode_injective
  Classicism.ChoiceHierarchyEncoding.inverse_relation_functional
  Classicism.ChoiceHierarchyEncoding.retraction_of_injection_plenitude
  Classicism.ChoiceHierarchyEncoding.selector_of_injection_plenitude

#classicism_derive
  Classicism.ChoiceHierarchyEncoding.singleton_doubleton
  Classicism.ChoiceHierarchyEncoding.doubleton_cancel
  Classicism.ChoiceHierarchyEncoding.pairCode_injective
  Classicism.ChoiceHierarchyEncoding.graphCode_injective
  Classicism.ChoiceHierarchyEncoding.inverse_relation_functional
  Classicism.ChoiceHierarchyEncoding.retraction_of_injection_plenitude
  Classicism.ChoiceHierarchyEncoding.selector_of_injection_plenitude

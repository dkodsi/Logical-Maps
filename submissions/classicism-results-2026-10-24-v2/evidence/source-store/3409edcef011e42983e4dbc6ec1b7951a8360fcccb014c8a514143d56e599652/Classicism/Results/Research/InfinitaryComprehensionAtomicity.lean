import Init

/-!
# Infinitary closure, signed truth patterns, and atomicity

Direct source: `research/2026-10-23/infinitary-comprehension/infinitary-comprehension.md`,
sections 2--3 (misc, 23 October 2026, unpaginated).

These are semantic metatheorems in ordinary Lean, not shallow proofs of C.
The input is a faithful family of supports, closed under pointwise complement
and arbitrary intersections of represented elements. Neither atomicity,
singleton supports, nor fullness of the family is an input. The atoms proved
below may contain many points that the represented supports cannot distinguish.

An application to object-language Infinitary Comprehension must separately
construct this interface: prove faithfulness of the support interpretation and
obtain its intersection operation from the relevant infinitary formulas and
Comprehension instances. This module does not assume or assert that bridge.

The proof uses Lean's classical metatheory, including excluded middle. This is
not an invocation of unrestricted classical extensionality or Choice within
the object theory C. The final axiom reports expose the metatheoretic cost.
-/

namespace Classicism.Research.InfinitaryComprehension

universe u v w

/-- A represented family of sets, with no singleton or fullness requirement. -/
structure SupportFamily (Carrier : Type u) (Point : Type v) where
  holds : Carrier → Point → Prop
  ext : ∀ {a b}, (∀ x, holds a x ↔ holds b x) → a = b
  bottom : Carrier
  bottom_spec : ∀ x, ¬ holds bottom x
  neg : Carrier → Carrier
  neg_spec : ∀ a x, holds (neg a) x ↔ ¬ holds a x
  inf : (Carrier → Prop) → Carrier
  inf_spec : ∀ S x, holds (inf S) x ↔ ∀ a, S a → holds a x

namespace SupportFamily

variable {Carrier : Type u} {Point : Type v}
variable (F : SupportFamily Carrier Point)

def Included (a b : Carrier) : Prop := ∀ x, F.holds a x → F.holds b x

def IsAtom (a : Carrier) : Prop :=
  a ≠ F.bottom ∧ ∀ b, F.Included b a → b = F.bottom ∨ b = a

def Atomic : Prop :=
  ∀ a, a ≠ F.bottom → ∃ b, F.IsAtom b ∧ F.Included b a

def ActualityAt (x : Point) : Prop :=
  ∃ a, F.holds a x ∧ ∀ b, F.holds b x → F.Included a b

theorem included_antisymm {a b : Carrier}
    (hab : F.Included a b) (hba : F.Included b a) : a = b :=
  F.ext (fun x => ⟨hab x, hba x⟩)

theorem eq_bottom_iff (a : Carrier) :
    a = F.bottom ↔ ∀ x, ¬ F.holds a x := by
  constructor
  · intro h
    subst a
    exact F.bottom_spec
  · intro h
    exact F.ext (fun x => ⟨fun hx => False.elim (h x hx),
      fun hx => False.elim (F.bottom_spec x hx)⟩)

theorem nonzero_iff (a : Carrier) :
    a ≠ F.bottom ↔ ∃ x, F.holds a x := by
  classical
  constructor
  · intro ha
    by_cases h : ∃ x, F.holds a x
    · exact h
    · exact False.elim (ha ((F.eq_bottom_iff a).2
        (fun x hx => h ⟨x, hx⟩)))
  · rintro ⟨x, hx⟩ h
    exact (F.eq_bottom_iff a).1 h x hx

theorem inf_lower (S : Carrier → Prop) (a : Carrier) (ha : S a) :
    F.Included (F.inf S) a :=
  fun x hx => (F.inf_spec S x).1 hx a ha

theorem le_inf (S : Carrier → Prop) (a : Carrier)
    (ha : ∀ b, S b → F.Included a b) : F.Included a (F.inf S) :=
  fun x hx => (F.inf_spec S x).2 (fun b hb => ha b hb x hx)

/-- Arbitrary unions are derived from intersection and complement. -/
def sup (S : Carrier → Prop) : Carrier :=
  F.neg (F.inf (fun a => ∃ b, S b ∧ a = F.neg b))

theorem sup_spec (S : Carrier → Prop) (x : Point) :
    F.holds (F.sup S) x ↔ ∃ a, S a ∧ F.holds a x := by
  classical
  constructor
  · intro hx
    have hn := (F.neg_spec _ x).1 hx
    by_cases h : ∃ a, S a ∧ F.holds a x
    · exact h
    · apply False.elim
      apply hn
      apply (F.inf_spec _ x).2
      rintro a ⟨b, hb, hab⟩
      subst a
      exact (F.neg_spec b x).2 (fun hbx => h ⟨b, hb, hbx⟩)
  · rintro ⟨a, ha, hax⟩
    apply (F.neg_spec _ x).2
    intro hi
    have hn : F.holds (F.neg a) x :=
      (F.inf_spec _ x).1 hi (F.neg a) ⟨a, ha, rfl⟩
    exact (F.neg_spec a x).1 hn hax

theorem le_sup (S : Carrier → Prop) (a : Carrier) (ha : S a) :
    F.Included a (F.sup S) :=
  fun x hx => (F.sup_spec S x).2 ⟨a, ha, hx⟩

theorem sup_le (S : Carrier → Prop) (a : Carrier)
    (ha : ∀ b, S b → F.Included b a) : F.Included (F.sup S) a := by
  intro x hx
  obtain ⟨b, hb, hbx⟩ := (F.sup_spec S x).1 hx
  exact ha b hb x hbx

theorem arbitrary_join (S : Carrier → Prop) :
    (∀ a, S a → F.Included a (F.sup S)) ∧
      (∀ b, (∀ a, S a → F.Included a b) → F.Included (F.sup S) b) :=
  ⟨fun a ha => F.le_sup S a ha, fun b hb => F.sup_le S b hb⟩

theorem arbitrary_meet (S : Carrier → Prop) :
    (∀ a, S a → F.Included (F.inf S) a) ∧
      (∀ b, (∀ a, S a → F.Included b a) → F.Included b (F.inf S)) :=
  ⟨fun a ha => F.inf_lower S a ha, fun b hb => F.le_inf S b hb⟩

/-- Indexed joins also allow index types in a universe independent of the carrier. -/
def indexedSup {Index : Type w} (a : Index → Carrier) : Carrier :=
  F.sup (fun b => ∃ i, b = a i)

theorem indexedSup_spec {Index : Type w} (a : Index → Carrier) (x : Point) :
    F.holds (F.indexedSup a) x ↔ ∃ i, F.holds (a i) x := by
  constructor
  · intro hx
    obtain ⟨b, ⟨i, hbi⟩, hbx⟩ := (F.sup_spec _ x).1 hx
    exact ⟨i, hbi ▸ hbx⟩
  · rintro ⟨i, hix⟩
    exact (F.sup_spec _ x).2 ⟨a i, ⟨i, rfl⟩, hix⟩

/-- A complete signed conjunction: the sign chooses an entity or its complement. -/
def pattern (sign : Carrier → Prop) : Carrier :=
  F.inf (fun b => ∃ a, (sign a ∧ b = a) ∨ (¬ sign a ∧ b = F.neg a))

theorem pattern_spec (sign : Carrier → Prop) (x : Point) :
    F.holds (F.pattern sign) x ↔
      ∀ a, (sign a → F.holds a x) ∧ (¬ sign a → ¬ F.holds a x) := by
  constructor
  · intro hx a
    constructor
    · intro ha
      exact (F.inf_spec _ x).1 hx a ⟨a, Or.inl ⟨ha, rfl⟩⟩
    · intro ha
      apply (F.neg_spec a x).1
      exact (F.inf_spec _ x).1 hx (F.neg a) ⟨a, Or.inr ⟨ha, rfl⟩⟩
  · intro hx
    apply (F.inf_spec _ x).2
    rintro b ⟨a, ha⟩
    cases ha with
    | inl ha =>
      obtain ⟨hs, hba⟩ := ha
      subst b
      exact (hx a).1 hs
    | inr ha =>
      obtain ⟨hs, hba⟩ := ha
      subst b
      exact (F.neg_spec a x).2 ((hx a).2 hs)

theorem pattern_decides (sign : Carrier → Prop) (a : Carrier) :
    F.Included (F.pattern sign) a ∨ F.Included (F.pattern sign) (F.neg a) := by
  classical
  by_cases ha : sign a
  · exact Or.inl (fun x hx => ((F.pattern_spec sign x).1 hx a).1 ha)
  · exact Or.inr (fun x hx => (F.neg_spec a x).2
      (((F.pattern_spec sign x).1 hx a).2 ha))

theorem atom_of_decides (a : Carrier) (ha : a ≠ F.bottom)
    (decides : ∀ b, F.Included a b ∨ F.Included a (F.neg b)) : F.IsAtom a := by
  classical
  refine ⟨ha, ?_⟩
  intro b hba
  by_cases hb : b = F.bottom
  · exact Or.inl hb
  · apply Or.inr
    cases decides b with
    | inl hab => exact F.included_antisymm hba hab
    | inr hab =>
      obtain ⟨x, hbx⟩ := (F.nonzero_iff b).1 hb
      exact False.elim ((F.neg_spec b x).1 (hab x (hba x hbx)) hbx)

theorem nonzero_pattern_is_atom (sign : Carrier → Prop)
    (ha : F.pattern sign ≠ F.bottom) : F.IsAtom (F.pattern sign) :=
  F.atom_of_decides _ ha (F.pattern_decides sign)

/-- The complete truth pattern at a point, not an assumed represented singleton. -/
def core (x : Point) : Carrier := F.pattern (fun a => F.holds a x)

theorem holds_core (x : Point) : F.holds (F.core x) x :=
  (F.pattern_spec _ x).2 (fun _ => ⟨fun h => h, fun h => h⟩)

theorem core_below (x : Point) (a : Carrier) (ha : F.holds a x) :
    F.Included (F.core x) a :=
  fun y hy => ((F.pattern_spec _ y).1 hy a).1 ha

theorem core_is_atom (x : Point) : F.IsAtom (F.core x) :=
  F.nonzero_pattern_is_atom _ ((F.nonzero_iff _).2 ⟨x, F.holds_core x⟩)

theorem atomicity : F.Atomic := by
  intro a ha
  obtain ⟨x, hx⟩ := (F.nonzero_iff a).1 ha
  exact ⟨F.core x, F.core_is_atom x, F.core_below x a hx⟩

theorem actuality (x : Point) : F.ActualityAt x :=
  ⟨F.core x, F.holds_core x, F.core_below x⟩

def top : Carrier := F.neg F.bottom

theorem holds_top (x : Point) : F.holds F.top x :=
  (F.neg_spec F.bottom x).2 (F.bottom_spec x)

/-- Classical truth-pattern exhaustiveness is a conclusion of the pointwise interface. -/
theorem truth_pattern_exhaustive :
    F.sup (fun a => ∃ sign : Carrier → Prop, a = F.pattern sign) = F.top := by
  apply F.ext
  intro x
  constructor
  · intro _
    exact F.holds_top x
  · intro _
    apply (F.sup_spec _ x).2
    exact ⟨F.core x, ⟨fun a => F.holds a x, rfl⟩, F.holds_core x⟩

end SupportFamily

-- These report ordinary metatheoretic dependencies, not object-C certification.
#print axioms SupportFamily.arbitrary_join
#print axioms SupportFamily.arbitrary_meet
#print axioms SupportFamily.nonzero_pattern_is_atom
#print axioms SupportFamily.atomicity
#print axioms SupportFamily.actuality
#print axioms SupportFamily.truth_pattern_exhaustive

end Classicism.Research.InfinitaryComprehension

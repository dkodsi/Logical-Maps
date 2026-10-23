import Classicism.Results.Research.MaxAtomicitySetFormulaTools
import Classicism.Results.Research.MaxAtomicityRegularCompletion

/-!
# Finite codes for the regular-lower-set completion

Direct source: the regular-lower-set construction proved in
`MaxAtomicityRegularCompletion` (misc, 22 October 2026, unpaginated), and the
finite coding needed by the canonical Jech--Shelah algebra route in the local
Max/Atomicity research. All displayed formulas are actual finite SetFormula
values. Their satisfaction theorems do not assume formula existence or meaning.

The separate representation bridge states its hypotheses: an injective coding
of the underlying preorder, correctness of its order graph, and representation
of every subset when proving the converse regularity assertion. It constructs
the pseudocomplement and proves agreement with Mathlib's Heyting complement.
No coded poset, full subset representation, JSCode, or rigidity is asserted to
exist. The designated serial checker owns compilation and axiom inspection.
-/

namespace Classicism.Meta.Research.MaxAtomicityRegularOpenCode

open MaxAtomicitySetSyntax MaxAtomicitySetSemantics MaxAtomicitySetFormulaTools

def lowerSet {n : Nat} (P O X : Fin n) : SetFormula n :=
  .conj (subset X P)
    (boundedAll X (boundedAll P.succ
      (.imp (graphApp O.succ.succ 0 (0 : Fin (n + 1)).succ)
        (.mem 0 X.succ.succ))))

/-- Y consists exactly of conditions with no strengthening in X. -/
def pseudoComplement {n : Nat} (P O X Y : Fin n) : SetFormula n :=
  .all (.iff (.mem 0 Y.succ)
    (.conj (.mem 0 P.succ)
      (boundedAll P.succ
        (.imp (graphApp O.succ.succ 0 (0 : Fin (n + 1)).succ)
          (.neg (.mem 0 X.succ.succ))))))

/-- The intermediate pseudocomplement is an explicitly quantified set code. -/
def regular {n : Nat} (P O X : Fin n) : SetFormula n :=
  .conj (lowerSet P O X)
    (.ex (.conj
      (pseudoComplement P.succ O.succ X.succ 0)
      (pseudoComplement P.succ O.succ 0 X.succ)))

def algebraCarrier {n : Nat} (P O B : Fin n) : SetFormula n :=
  .all (.iff (.mem 0 B.succ) (regular P.succ O.succ 0))

def intersection {n : Nat} (X Y Z : Fin n) : SetFormula n :=
  .all (.iff (.mem 0 Z.succ) (.conj (.mem 0 X.succ) (.mem 0 Y.succ)))

/-- The complement graph consists exactly of coded pairs (X,Y) in the carrier
whose second component is the pseudocomplement of the first. -/
def complementGraph {n : Nat} (P O B G : Fin n) : SetFormula n :=
  .all (.iff (.mem 0 G.succ)
    (boundedEx B.succ (boundedEx B.succ.succ
      (.conj
        (orderedPair (0 : Fin (n + 2)).succ 0 (0 : Fin (n + 1)).succ.succ)
        (pseudoComplement P.succ.succ.succ O.succ.succ.succ
          (0 : Fin (n + 2)).succ 0)))))

/-- Binary operations are represented by Kuratowski pairs ((X,Y),Z). -/
def meetGraph {n : Nat} (B G : Fin n) : SetFormula n :=
  .all (.iff (.mem 0 G.succ)
    (boundedEx B.succ (boundedEx B.succ.succ (boundedEx B.succ.succ.succ
      (.ex (.conj
        (orderedPair (0 : Fin (n + 2)).succ.succ.succ
          (0 : Fin (n + 3)).succ.succ 0)
        (.conj
          (orderedPair 0 (0 : Fin (n + 4)).succ (0 : Fin (n + 1)).succ.succ.succ.succ)
          (intersection (0 : Fin (n + 2)).succ.succ.succ
            (0 : Fin (n + 3)).succ.succ (0 : Fin (n + 4)).succ))))))))

namespace Ordinary

open MaxAtomicitySetFormulaTools.Ordinary

variable {D : Type*} (R : D → D → Prop)

def Lower (P O X : D) : Prop :=
  Subset R X P ∧ ∀ p, R p X → ∀ q, R q P → GraphApp R O q p → R q X

def PseudoComplement (P O X Y : D) : Prop :=
  ∀ p, R p Y ↔ R p P ∧ ∀ q, R q P → GraphApp R O q p → ¬ R q X

def Regular (P O X : D) : Prop :=
  Lower R P O X ∧ ∃ Y, PseudoComplement R P O X Y ∧ PseudoComplement R P O Y X

def AlgebraCarrier (P O B : D) : Prop := ∀ X, R X B ↔ Regular R P O X

def Intersection (X Y Z : D) : Prop := ∀ p, R p Z ↔ R p X ∧ R p Y

def ComplementGraph (P O B G : D) : Prop :=
  ∀ z, R z G ↔ ∃ X, R X B ∧ ∃ Y, R Y B ∧
    OrderedPair R X Y z ∧ PseudoComplement R P O X Y

def MeetGraph (B G : D) : Prop :=
  ∀ z, R z G ↔ ∃ X, R X B ∧ ∃ Y, R Y B ∧ ∃ Z, R Z B ∧
    ∃ p, OrderedPair R X Y p ∧ OrderedPair R p Z z ∧ Intersection R X Y Z

end Ordinary

theorem satisfies_lowerSet {D : Type} {n : Nat} (P O X : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (lowerSet P O X) R ρ ↔ Ordinary.Lower R (ρ P) (ρ O) (ρ X) := Iff.rfl

theorem satisfies_pseudoComplement {D : Type} {n : Nat} (P O X Y : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (pseudoComplement P O X Y) R ρ ↔
      Ordinary.PseudoComplement R (ρ P) (ρ O) (ρ X) (ρ Y) := Iff.rfl

theorem satisfies_regular {D : Type} {n : Nat} (P O X : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (regular P O X) R ρ ↔ Ordinary.Regular R (ρ P) (ρ O) (ρ X) := Iff.rfl

theorem satisfies_algebraCarrier {D : Type} {n : Nat} (P O B : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (algebraCarrier P O B) R ρ ↔
      Ordinary.AlgebraCarrier R (ρ P) (ρ O) (ρ B) := Iff.rfl

theorem satisfies_intersection {D : Type} {n : Nat} (X Y Z : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (intersection X Y Z) R ρ ↔
      Ordinary.Intersection R (ρ X) (ρ Y) (ρ Z) := Iff.rfl

theorem satisfies_complementGraph {D : Type} {n : Nat} (P O B G : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (complementGraph P O B G) R ρ ↔
      Ordinary.ComplementGraph R (ρ P) (ρ O) (ρ B) (ρ G) := Iff.rfl

theorem satisfies_meetGraph {D : Type} {n : Nat} (B G : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (meetGraph B G) R ρ ↔ Ordinary.MeetGraph R (ρ B) (ρ G) := Iff.rfl

section LowerSets

variable {α : Type*} [Preorder α]

/-- Pseudocomplement as an explicitly constructed lower set. -/
def pseudoLower (S : Set α) : LowerSet α where
  carrier := {p | ∀ q, q ≤ p → q ∉ S}
  lower' := by
    intro a b hab hb q hqa
    exact hb q (hqa.trans hab)

theorem le_pseudoLower_iff_disjoint (T S : LowerSet α) :
    T ≤ pseudoLower (S : Set α) ↔ Disjoint T S := by
  constructor
  · intro h
    apply disjoint_iff_inf_le.mpr
    intro p hp
    exact (h hp.1) p le_rfl hp.2
  · intro h p hp q hqp hq
    have hb : T ⊓ S ≤ ⊥ := disjoint_iff_inf_le.mp h
    exact hb ⟨T.lower hqp hp, hq⟩

/-- The explicit construction is the actual Heyting complement, by its
universal disjointness property. -/
theorem pseudoLower_eq_compl (S : LowerSet α) : pseudoLower (S : Set α) = Sᶜ := by
  apply eq_of_forall_le_iff
  intro T
  rw [le_pseudoLower_iff_disjoint, le_compl_iff_disjoint_right]

theorem mem_compl_iff (S : LowerSet α) (p : α) :
    p ∈ Sᶜ ↔ ∀ q, q ≤ p → q ∉ S := by
  change p ∈ Sᶜ ↔ p ∈ pseudoLower (S : Set α)
  rw [← pseudoLower_eq_compl S]

end LowerSets

/-- An explicitly supplied coding of a preorder inside an ordinary membership
structure. The structure makes no subset-representation assumption. -/
structure PosetCoding (D : Type*) (α : Type*) [Preorder α]
    (R : D → D → Prop) (P O : D) where
  point : α ↪ D
  mem_carrier : ∀ d, R d P ↔ ∃ a, point a = d
  order_iff : ∀ a b,
    MaxAtomicitySetFormulaTools.Ordinary.GraphApp R O (point a) (point b) ↔ a ≤ b

namespace PosetCoding

variable {D α : Type*} [Preorder α] {R : D → D → Prop} {P O : D}
variable (c : PosetCoding D α R P O)

/-- A code represents exactly this subset, with no elements outside P. -/
def Represents (S : Set α) (X : D) : Prop :=
  ∀ d, R d X ↔ ∃ a, c.point a = d ∧ a ∈ S

def Full : Prop := ∀ S : Set α, ∃ X : D, c.Represents S X

theorem rep_point {S : Set α} {X : D} (hX : c.Represents S X) (a : α) :
    R (c.point a) X ↔ a ∈ S := by
  constructor
  · intro h
    obtain ⟨b, hba, hb⟩ := (hX (c.point a)).1 h
    exact c.point.injective hba ▸ hb
  · intro ha
    exact (hX (c.point a)).2 ⟨a, rfl, ha⟩

theorem rep_subset {S : Set α} {X : D} (hX : c.Represents S X) :
    MaxAtomicitySetFormulaTools.Ordinary.Subset R X P := by
  intro d hd
  obtain ⟨a, ha, _⟩ := (hX d).1 hd
  exact (c.mem_carrier d).2 ⟨a, ha⟩

theorem rep_ext {S T : Set α} {X : D}
    (hS : c.Represents S X) (hT : c.Represents T X) : S = T := by
  apply Set.ext
  intro a
  exact (c.rep_point hS a).symm.trans (c.rep_point hT a)

theorem lower_iff {S : Set α} {X : D} (hX : c.Represents S X) :
    Ordinary.Lower R P O X ↔ IsLowerSet S := by
  constructor
  · intro h a b hab hb
    apply (c.rep_point hX b).1
    exact h.2 (c.point a) ((c.rep_point hX a).2 hb) (c.point b)
      ((c.mem_carrier _).2 ⟨b, rfl⟩) ((c.order_iff b a).2 hab)
  · intro h
    refine ⟨c.rep_subset hX, ?_⟩
    intro p hp q hq hqp
    obtain ⟨a, rfl, ha⟩ := (hX p).1 hp
    obtain ⟨b, rfl⟩ := (c.mem_carrier q).1 hq
    exact (c.rep_point hX b).2 (h ((c.order_iff b a).1 hqp) ha)

theorem pseudo_condition_iff {S : Set α} {X : D}
    (hX : c.Represents S X) (d : D) :
    (R d P ∧ ∀ q, R q P →
      MaxAtomicitySetFormulaTools.Ordinary.GraphApp R O q d → ¬ R q X) ↔
      ∃ a, c.point a = d ∧ a ∈ pseudoLower S := by
  constructor
  · rintro ⟨hd, havoid⟩
    obtain ⟨a, rfl⟩ := (c.mem_carrier d).1 hd
    refine ⟨a, rfl, ?_⟩
    intro b hba hb
    exact havoid (c.point b) ((c.mem_carrier _).2 ⟨b, rfl⟩)
      ((c.order_iff b a).2 hba) ((c.rep_point hX b).2 hb)
  · rintro ⟨a, rfl, ha⟩
    refine ⟨(c.mem_carrier _).2 ⟨a, rfl⟩, ?_⟩
    intro q hq hqa hqX
    obtain ⟨b, rfl⟩ := (c.mem_carrier q).1 hq
    exact ha b ((c.order_iff b a).1 hqa) ((c.rep_point hX b).1 hqX)

theorem pseudoComplement_iff_rep {S : Set α} {X Y : D}
    (hX : c.Represents S X) :
    Ordinary.PseudoComplement R P O X Y ↔ c.Represents (pseudoLower S : Set α) Y := by
  constructor
  · intro h d
    exact (h d).trans (c.pseudo_condition_iff hX d)
  · intro h d
    exact (h d).trans (c.pseudo_condition_iff hX d).symm

/-- Full subset representation is used exactly to obtain the code of the
pseudocomplement in the reverse implication. -/
theorem regular_iff (hfull : c.Full) {S : LowerSet α} {X : D}
    (hX : c.Represents (S : Set α) X) :
    Ordinary.Regular R P O X ↔ Heyting.IsRegular S := by
  constructor
  · rintro ⟨_, Y, hXY, hYX⟩
    have hY := (c.pseudoComplement_iff_rep hX).1 hXY
    rw [pseudoLower_eq_compl] at hY
    have hXX := (c.pseudoComplement_iff_rep hY).1 hYX
    rw [pseudoLower_eq_compl] at hXX
    exact LowerSet.ext (c.rep_ext hXX hX)
  · intro hS
    refine ⟨(c.lower_iff hX).2 S.lower, ?_⟩
    -- Take the underlying set of the LowerSet pseudocomplement, not the
    -- ordinary set-theoretic complement of the underlying carrier.
    obtain ⟨Y, hY⟩ := hfull ((Sᶜ : LowerSet α) : Set α)
    refine ⟨Y, ?_, ?_⟩
    · apply (c.pseudoComplement_iff_rep hX).2
      rw [pseudoLower_eq_compl]
      exact hY
    · apply (c.pseudoComplement_iff_rep hY).2
      rw [pseudoLower_eq_compl, hS.eq]
      exact hX

theorem carrier_member_iff (hfull : c.Full) {B X : D}
    (hB : Ordinary.AlgebraCarrier R P O B) {S : LowerSet α}
    (hX : c.Represents (S : Set α) X) :
    R X B ↔ Heyting.IsRegular S :=
  (hB X).trans (c.regular_iff hfull hX)

theorem every_regular_represented (hfull : c.Full)
    (S : Heyting.Regular (LowerSet α)) :
    ∃ X, c.Represents ((S : LowerSet α) : Set α) X ∧ Ordinary.Regular R P O X := by
  obtain ⟨X, hX⟩ := hfull ((S : LowerSet α) : Set α)
  exact ⟨X, hX, (c.regular_iff hfull hX).2 S.prop⟩

theorem intersection_iff_rep {S T : Set α} {X Y Z : D}
    (hX : c.Represents S X) (hY : c.Represents T Y) :
    Ordinary.Intersection R X Y Z ↔ c.Represents (S ∩ T) Z := by
  have hcond (d : D) : (R d X ∧ R d Y) ↔ ∃ a, c.point a = d ∧ a ∈ S ∩ T := by
    constructor
    · rintro ⟨hdX, hdY⟩
      obtain ⟨a, rfl, ha⟩ := (hX d).1 hdX
      exact ⟨a, rfl, ha, (c.rep_point hY a).1 hdY⟩
    · rintro ⟨a, rfl, ha, hb⟩
      exact ⟨(c.rep_point hX a).2 ha, (c.rep_point hY a).2 hb⟩
  constructor
  · intro h d
    exact (h d).trans (hcond d)
  · intro h d
    exact (h d).trans (hcond d).symm

/-- The coded meet is the existing Boolean meet on regular lower sets. -/
theorem regular_meet_iff_rep (S T : Heyting.Regular (LowerSet α)) {X Y Z : D}
    (hX : c.Represents ((S : LowerSet α) : Set α) X)
    (hY : c.Represents ((T : LowerSet α) : Set α) Y) :
    Ordinary.Intersection R X Y Z ↔
      c.Represents (((S ⊓ T : Heyting.Regular (LowerSet α)) : LowerSet α) : Set α) Z :=
  c.intersection_iff_rep hX hY

/-- The coded complement is the existing Boolean complement on regular lower
sets; no separate Boolean operation is postulated. -/
theorem regular_compl_iff_rep (S : Heyting.Regular (LowerSet α)) {X Y : D}
    (hX : c.Represents ((S : LowerSet α) : Set α) X) :
    Ordinary.PseudoComplement R P O X Y ↔
      c.Represents (((Sᶜ : Heyting.Regular (LowerSet α)) : LowerSet α) : Set α) Y := by
  simpa only [pseudoLower_eq_compl, Heyting.Regular.coe_compl] using
    c.pseudoComplement_iff_rep hX

def decoded (X : D) : Set α := {a | R (c.point a) X}

theorem represents_decoded {X : D}
    (hX : MaxAtomicitySetFormulaTools.Ordinary.Subset R X P) :
    c.Represents (c.decoded X) X := by
  intro d
  constructor
  · intro hd
    obtain ⟨a, rfl⟩ := (c.mem_carrier d).1 (hX d hd)
    exact ⟨a, rfl, hd⟩
  · rintro ⟨a, rfl, ha⟩
    exact ha

def decodeLower (X : D) (hX : Ordinary.Lower R P O X) : LowerSet α where
  carrier := c.decoded X
  lower' := (c.lower_iff (c.represents_decoded hX.1)).1 hX

/-- Decode an actual regular-set code into Mathlib's regular lower sets. -/
def decodeRegular (hfull : c.Full) (X : {X : D // Ordinary.Regular R P O X}) :
    Heyting.Regular (LowerSet α) :=
  ⟨c.decodeLower X.val X.property.1,
    (c.regular_iff hfull (S := c.decodeLower X.val X.property.1)
      (c.represents_decoded X.property.1.1)).1 X.property⟩

theorem decodeRegular_surjective (hfull : c.Full) :
    Function.Surjective (c.decodeRegular hfull) := by
  intro S
  obtain ⟨X, hX, hrX⟩ := c.every_regular_represented hfull S
  refine ⟨⟨X, hrX⟩, ?_⟩
  apply Heyting.Regular.coe_injective
  apply LowerSet.ext
  apply Set.ext
  intro a
  change R (c.point a) X ↔ a ∈ (S : LowerSet α)
  exact c.rep_point hX a

/-- Extensionality is explicit: without it two different set codes could have
the same extension, so there would only be a surjective decoding. -/
theorem decodeRegular_injective (hfull : c.Full)
    (hext : ∀ X Y : D, (∀ d, R d X ↔ R d Y) → X = Y) :
    Function.Injective (c.decodeRegular hfull) := by
  intro X Y hXY
  apply Subtype.ext
  apply hext
  intro d
  have hs : c.decoded X.val = c.decoded Y.val :=
    congrArg (fun S : Heyting.Regular (LowerSet α) => ((S : LowerSet α) : Set α)) hXY
  rw [c.represents_decoded X.property.1.1 d,
    c.represents_decoded Y.property.1.1 d, hs]

/-- With full subset representation and extensionality, the coded regular sets
are actually in bijection with the canonical Boolean-completion carrier. -/
noncomputable def regularEquiv (hfull : c.Full)
    (hext : ∀ X Y : D, (∀ d, R d X ↔ R d Y) → X = Y) :
    {X : D // Ordinary.Regular R P O X} ≃ Heyting.Regular (LowerSet α) :=
  Equiv.ofBijective (c.decodeRegular hfull)
    ⟨c.decodeRegular_injective hfull hext, c.decodeRegular_surjective hfull⟩

end PosetCoding

end Classicism.Meta.Research.MaxAtomicityRegularOpenCode

#print axioms Classicism.Meta.Research.MaxAtomicityRegularOpenCode.satisfies_regular
#print axioms Classicism.Meta.Research.MaxAtomicityRegularOpenCode.satisfies_algebraCarrier
#print axioms Classicism.Meta.Research.MaxAtomicityRegularOpenCode.satisfies_complementGraph
#print axioms Classicism.Meta.Research.MaxAtomicityRegularOpenCode.satisfies_meetGraph
#print axioms Classicism.Meta.Research.MaxAtomicityRegularOpenCode.pseudoLower_eq_compl
#print axioms Classicism.Meta.Research.MaxAtomicityRegularOpenCode.PosetCoding.regular_iff
#print axioms Classicism.Meta.Research.MaxAtomicityRegularOpenCode.PosetCoding.regular_meet_iff_rep
#print axioms Classicism.Meta.Research.MaxAtomicityRegularOpenCode.PosetCoding.regular_compl_iff_rep
#print axioms Classicism.Meta.Research.MaxAtomicityRegularOpenCode.PosetCoding.regularEquiv

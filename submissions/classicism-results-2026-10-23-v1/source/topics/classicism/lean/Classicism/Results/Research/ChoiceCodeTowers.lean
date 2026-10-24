import Classicism.Principles.Choice

/-!
# Lossless coextension-class codes and their ambiguity ranges

Direct source: `research/2026-10-23/choice-transversal-coherence/continuation-code-operations.md`,
§§1–2 (`misc`, original research, 23 October 2026; unpaginated).

Only the closed class-code/material-union identity uses Logical Equivalence.
The generic split-code lemmas use ordinary substitution from the supplied
pointwise identities. No identification of actually coextensive entities is
used. Choice outputs have any admitted type, including `e`.

Unary property instances are accompanied by explicit nullary instances. The
certificate module requests tuple rules for the unary split and ambiguity
theorems, so their empty-tuple case also covers `t`. Finite tower composition
is expressed by the generic composition theorem, not by quantifying over
object-language types or introducing an infinite composition.
-/

namespace Classicism.Research.ChoiceCodeTowers
open Classicism.Paper Classicism.P

/-- A specified code/decoder pair splits literally and preserves actual coextension. -/
def CodeSplit {A B : Type} [Rel A] [Rel B] (c : A → B) (d : B → A) : Prop :=
  (∀ a, d (c a) = a) ∧
  (∀ a b, a ≡ b → c a ≡ c b) ∧
  (∀ z w, z ≡ w → d z ≡ d w)

/-- Actual ambiguity over all input codes of the same coextension class. -/
def Ambiguity {A σ : Type} [Rel A] [Ty σ]
    (K : A → σ → Prop) (a : A) (y : σ) : Prop :=
  ∃ b, b ≡ a ∧ K b y

/-- Lift a relational chooser along a specified decoder. -/
def liftChooser {A B σ : Type} [Rel A] [Rel B] [Ty σ]
    (d : B → A) (K : A → σ → Prop) : B → σ → Prop :=
  fun z y => K (d z) y

theorem codeSplit_id {A : Type} [Rel A] :
    CodeSplit (fun a : A => a) (fun a : A => a) :=
  ⟨fun _ => rfl, (fun _ _ h => h), (fun _ _ h => h)⟩

/-- This theorem can be applied repeatedly to every fixed finite code tower. -/
theorem codeSplit_comp {A B D : Type} [Rel A] [Rel B] [Rel D]
    (c : A → B) (d : B → A) (e : B → D) (f : D → B)
    (h₁ : CodeSplit c d) (h₂ : CodeSplit e f) :
    CodeSplit (fun a => e (c a)) (fun z => d (f z)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact (congrArg d (h₂.1 (c a))).trans (h₁.1 a)
  · intro a b hab
    exact h₂.2.1 (c a) (c b) (h₁.2.1 a b hab)
  · intro z w hzw
    exact h₁.2.2 (f z) (f w) (h₂.2.2 z w hzw)

theorem codeSplit_injective {A B : Type} [Rel A] [Rel B]
    (c : A → B) (d : B → A) (h : CodeSplit c d)
    (a b : A) (hab : c a = c b) : a = b :=
  (h.1 a).symm.trans ((congrArg d hab).trans (h.1 b))

theorem codeSplit_reflects_coext {A B : Type} [Rel A] [Rel B]
    (c : A → B) (d : B → A) (h : CodeSplit c d)
    (a b : A) : c a ≡ c b ↔ a ≡ b := by
  constructor
  · intro hab
    have hd := h.2.2 (c a) (c b) hab
    rw [h.1 a, h.1 b] at hd
    exact hd
  · exact h.2.1 a b

theorem liftChooser_serial {A B σ : Type} [Rel A] [Rel B] [Ty σ]
    (d : B → A) (U : A → σ → Prop) (h : Serial U) :
    Serial (liftChooser d U) := fun z => h (d z)

theorem liftChooser_functional {A B σ : Type} [Rel A] [Rel B] [Ty σ]
    (d : B → A) (K : A → σ → Prop) (h : Functional K) :
    Functional (liftChooser d K) := fun z => h (d z)

theorem liftChooser_contained {A B σ : Type} [Rel A] [Rel B] [Ty σ]
    (d : B → A) (K U : A → σ → Prop)
    (h : ∀ a y, K a y → U a y) :
    ∀ z y, liftChooser d K z y → liftChooser d U z y :=
  fun z y => h (d z) y

/-- Pointwise literal recovery; no function extensionality is applied to `h`. -/
theorem codeSplit_pullback {A B σ : Type} [Rel A] [Rel B] [Ty σ]
    (c : A → B) (d : B → A) (h : CodeSplit c d)
    (K : A → σ → Prop) (a : A) (y : σ) :
    liftChooser d K (c a) y = K a y :=
  congrArg (fun b => K b y) (h.1 a)

/-- The entire high-level coextension fibre has exactly the old ambiguity. -/
theorem codeSplit_ambiguity {A B σ : Type} [Rel A] [Rel B] [Ty σ]
    (c : A → B) (d : B → A) (h : CodeSplit c d)
    (K : A → σ → Prop) (a : A) (y : σ) :
    Ambiguity (liftChooser d K) (c a) y ↔ Ambiguity K a y := by
  constructor
  · intro hz
    obtain ⟨z, hzc, hk⟩ := hz
    have hd := h.2.2 z (c a) hzc
    rw [h.1 a] at hd
    exact ⟨d z, hd, hk⟩
  · intro hb
    obtain ⟨b, hba, hk⟩ := hb
    refine ⟨c b, h.2.1 b a hba, ?_⟩
    change K (d (c b)) y
    rw [h.1 b]
    exact hk

/-- A high-level selector also pulls back to a selector at the original type. -/
theorem codeSplit_selector_pullback {A B σ : Type} [Rel A] [Rel B] [Ty σ]
    (c : A → B) (d : B → A) (h : CodeSplit c d)
    (U : A → σ → Prop) (J : B → σ → Prop)
    (hf : Functional J)
    (hu : ∀ z y, J z y → liftChooser d U z y) :
    Functional (fun a y => J (c a) y) ∧
      ∀ a y, J (c a) y → U a y := by
  refine ⟨fun a => hf (c a), ?_⟩
  intro a y hj
  have hU := hu (c a) y hj
  change U (d (c a)) y at hU
  rw [h.1 a] at hU
  exact hU

section unary
variable {ν : Type} [Ty ν]

def classCode (A : ν → Prop) : (ν → Prop) → Prop := fun B => B ≡ A

def materialUnion (Z : (ν → Prop) → Prop) : ν → Prop :=
  fun x => ∃ B, Z B ∧ B x

/-- Closed Logical Equivalence, with `A` an object parameter and no proof premise. -/
theorem materialUnion_classCode (A : ν → Prop) :
    materialUnion (classCode A) = A :=
  funext fun x => propext
    ⟨fun h => h.elim fun B hB => (hB.1 x).1 hB.2,
      fun h => ⟨A, (fun _ => Iff.rfl), h⟩⟩

theorem classCode_preserves_coext (A B : ν → Prop) (h : A ≡ B) :
    classCode A ≡ classCode B := by
  intro D
  exact ⟨fun hd x => (hd x).trans (h x),
    fun hd x => (hd x).trans (h x).symm⟩

theorem materialUnion_preserves_coext (Z W : (ν → Prop) → Prop)
    (h : Z ≡ W) : materialUnion Z ≡ materialUnion W := by
  intro x
  exact ⟨fun hz => hz.elim fun B hB => ⟨B, (h B).1 hB.1, hB.2⟩,
    fun hw => hw.elim fun B hB => ⟨B, (h B).2 hB.1, hB.2⟩⟩

/-- Named type-only proposition for certification and tuple vectorization. -/
def ClassCodeSplit (ν : Type) [Ty ν] : Prop :=
  CodeSplit (@classCode ν _) (@materialUnion ν)

theorem class_code_split : ClassCodeSplit ν :=
  ⟨materialUnion_classCode, classCode_preserves_coext, materialUnion_preserves_coext⟩

theorem classCode_injective (A B : ν → Prop) (h : classCode A = classCode B) : A = B :=
  codeSplit_injective classCode materialUnion class_code_split A B h

theorem classCode_coext_iff (A B : ν → Prop) : classCode A ≡ classCode B ↔ A ≡ B :=
  codeSplit_reflects_coext classCode materialUnion class_code_split A B

theorem classCode_double_split :
    CodeSplit (fun A : ν → Prop => classCode (classCode A))
      (fun Z => materialUnion (materialUnion Z)) :=
  codeSplit_comp classCode materialUnion classCode materialUnion
    class_code_split class_code_split

def ClassCodeAmbiguity (ν σ : Type) [Ty ν] [Ty σ] : Prop :=
  ∀ (K : (ν → Prop) → σ → Prop) A y,
    Ambiguity (liftChooser materialUnion K) (classCode A) y ↔ Ambiguity K A y

theorem class_code_ambiguity {σ : Type} [Ty σ] : ClassCodeAmbiguity ν σ :=
  fun K A y => codeSplit_ambiguity classCode materialUnion class_code_split K A y

/-- For these specified closed terms even the whole pullback graph is identical. -/
theorem classCode_pullback_identity {σ : Type} [Ty σ]
    (K : (ν → Prop) → σ → Prop) :
    (fun A y => liftChooser materialUnion K (classCode A) y) = K :=
  funext fun A => funext fun y =>
    congrArg (fun B => K B y) (materialUnion_classCode A)

end unary

/-! Explicit empty-argument case, also present in the requested tuple certificates. -/
def classCodeT (p : Prop) : Prop → Prop := fun q => q ↔ p

def materialUnionT (Z : Prop → Prop) : Prop := ∃ q, Z q ∧ q

theorem materialUnionT_classCodeT (p : Prop) : materialUnionT (classCodeT p) = p :=
  propext ⟨fun h => h.elim fun q hq => hq.1.1 hq.2,
    fun h => ⟨p, Iff.rfl, h⟩⟩

theorem classCodeT_preserves_coext (p q : Prop) (h : p ≡ q) :
    classCodeT p ≡ classCodeT q :=
  fun r => ⟨fun hr => hr.trans h, fun hr => hr.trans h.symm⟩

theorem materialUnionT_preserves_coext (Z W : Prop → Prop) (h : Z ≡ W) :
    materialUnionT Z ≡ materialUnionT W :=
  ⟨fun hz => hz.elim fun p hp => ⟨p, (h p).1 hp.1, hp.2⟩,
    fun hw => hw.elim fun p hp => ⟨p, (h p).2 hp.1, hp.2⟩⟩

theorem class_code_split_t : CodeSplit classCodeT materialUnionT :=
  ⟨materialUnionT_classCodeT, classCodeT_preserves_coext, materialUnionT_preserves_coext⟩

theorem classCodeT_injective (p q : Prop) (h : classCodeT p = classCodeT q) : p = q :=
  codeSplit_injective classCodeT materialUnionT class_code_split_t p q h

theorem class_code_ambiguity_t {σ : Type} [Ty σ]
    (K : Prop → σ → Prop) (p : Prop) (y : σ) :
    Ambiguity (liftChooser materialUnionT K) (classCodeT p) y ↔ Ambiguity K p y :=
  codeSplit_ambiguity classCodeT materialUnionT class_code_split_t K p y

end Classicism.Research.ChoiceCodeTowers

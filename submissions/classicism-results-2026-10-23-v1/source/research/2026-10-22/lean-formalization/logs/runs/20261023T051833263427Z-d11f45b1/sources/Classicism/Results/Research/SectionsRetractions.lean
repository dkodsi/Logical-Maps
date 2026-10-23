import Classicism.Results.Records.Choice
import Classicism.Principles.Coarse

/-!
# Sections and retractions: exact local and necessary equations

Direct sources: `research/2026-10-22/notes/functional-choice-by-sections.md`,
§§1,4,6; `notes/choice-uniformization.md`, §§6,9,11,19
(`misc`, original research, 22 October 2026; unpaginated).

An inverse operation exists only when its codomain is relational. Ordinary
pointwise inverse equations are kept distinct from necessary inverse equations
and literal composition identities. No bridge between them is assumed.
-/
namespace Classicism.Research.Splitting
open Classicism.Paper Classicism.P

def Injective {A B : Type} [Ty A] [Rel B] (f : A → B) : Prop :=
  ∀ a a', f a = f a' → a = a'
def Surjective {A B : Type} [Ty A] [Rel B] (f : A → B) : Prop :=
  ∀ b, ∃ a, f a = b

def LeftInverse {A B : Type} [Rel A] [Rel B] (f : A → B) (g : B → A) : Prop :=
  ∀ a, g (f a) = a
def RightInverse {A B : Type} [Rel A] [Rel B] (f : A → B) (g : B → A) : Prop :=
  ∀ b, f (g b) = b
def StrongLeftInverse {A B : Type} [Rel A] [Rel B] (f : A → B) (g : B → A) : Prop :=
  □ (LeftInverse f g)
def StrongRightInverse {A B : Type} [Rel A] [Rel B] (f : A → B) (g : B → A) : Prop :=
  □ (RightInverse f g)

def LeftSplitting (A B : Type) [Rel A] [Rel B] : Prop :=
  ∀ f : A → B, Injective f → ∃ g, LeftInverse f g
def RightSplitting (A B : Type) [Rel A] [Rel B] : Prop :=
  ∀ f : A → B, Surjective f → ∃ g, RightInverse f g
def StrongLeftSplitting (A B : Type) [Rel A] [Rel B] : Prop :=
  ∀ f : A → B, Injective f → ∃ g, StrongLeftInverse f g
def StrongRightSplitting (A B : Type) [Rel A] [Rel B] : Prop :=
  ∀ f : A → B, Surjective f → ∃ g, StrongRightInverse f g

def InjectivityPersists (A B : Type) [Ty A] [Rel B] : Prop :=
  ∀ f : A → B, Injective f → □ (Injective f)
def SurjectivityPersists (A B : Type) [Ty A] [Rel B] : Prop :=
  ∀ f : A → B, Surjective f → □ (Surjective f)

def Epi {A B : Type} [Ty A] [Rel B] (f : A → B) : Prop :=
  ∀ g h : B → Prop, (fun a => g (f a)) = (fun a => h (f a)) → g = h

/-- One specified source type, not an object-language quantifier over types. -/
def CancelsFrom (D : Type) [Ty D] {A B : Type} [Rel A] [Rel B] (f : A → B) : Prop :=
  ∀ g h : D → A, (fun d => f (g d)) = (fun d => f (h d)) → g = h

section
variable {A B : Type} [Rel A] [Rel B]

theorem strong_left_iff_composition (f : A → B) (g : B → A) :
    StrongLeftInverse f g ↔ (fun a => g (f a)) = (fun a : A => a) :=
  ⟨modalized_functionality _ _, fun h => modal_K _ _
    (nec% (fun (e : (fun a => g (f a)) = (fun a : A => a)) (a : A) => congrFun e a))
    (necessity_of_identity _ _ h)⟩

theorem strong_right_iff_composition (f : A → B) (g : B → A) :
    StrongRightInverse f g ↔ (fun b => f (g b)) = (fun b : B => b) :=
  ⟨modalized_functionality _ _, fun h => modal_K _ _
    (nec% (fun (e : (fun b => f (g b)) = (fun b : B => b)) (b : B) => congrFun e b))
    (necessity_of_identity _ _ h)⟩

theorem left_inverse_injective (f : A → B) (g : B → A)
    (h : LeftInverse f g) : Injective f := fun a b e =>
  (h a).symm.trans ((congrArg g e).trans (h b))

theorem right_inverse_surjective (f : A → B) (g : B → A)
    (h : RightInverse f g) : Surjective f := fun b => ⟨g b, h b⟩

theorem right_inverse_injective (f : A → B) (g : B → A)
    (h : RightInverse f g) : Injective g := left_inverse_injective g f h

theorem left_inverse_surjective (f : A → B) (g : B → A)
    (h : LeftInverse f g) : Surjective g := right_inverse_surjective g f h

theorem strong_left_necessary_injective (f : A → B) (g : B → A) :
    StrongLeftInverse f g → □ (Injective f) :=
  modal_K _ _ (nec% (left_inverse_injective f g))

theorem strong_right_necessary_surjective (f : A → B) (g : B → A) :
    StrongRightInverse f g → □ (Surjective f) :=
  modal_K _ _ (nec% (right_inverse_surjective f g))

theorem injective_right_is_left (f : A → B) (g : B → A)
    (hi : Injective f) (h : RightInverse f g) : LeftInverse f g :=
  fun a => hi _ _ (h (f a))

theorem surjective_left_is_right (f : A → B) (g : B → A)
    (hs : Surjective f) (h : LeftInverse f g) : RightInverse f g := fun b =>
  (hs b).elim fun a e => e ▸ congrArg f (h a)

theorem left_inverse_strong_of_barcan (bf : Barcan A) (f : A → B) (g : B → A)
    (h : LeftInverse f g) : StrongLeftInverse f g :=
  bf (fun a => g (f a) = a) (fun a => necessity_of_identity _ _ (h a))

theorem right_inverse_strong_of_barcan (bf : Barcan B) (f : A → B) (g : B → A)
    (h : RightInverse f g) : StrongRightInverse f g :=
  bf (fun b => f (g b) = b) (fun b => necessity_of_identity _ _ (h b))

theorem functional_choice_sections : FunctionalChoice B A → RightSplitting A B :=
  fun fc f hs => fc (fun b a => f a = b) hs

theorem plenitude_retractions : Plenitude B A → LeftSplitting A B := by
  intro pl f hi
  let a₀ : A := Rel.top A
  let U : B → A → Prop := fun b a => f a = b ∨ ((¬ ∃ x, f x = b) ∧ a = a₀)
  have hf : Functional U := by
    intro b
    refine (em (∃ x, f x = b)).elim (fun hex => ?_) (fun hn => ?_)
    · obtain ⟨a, ha⟩ := hex
      refine ⟨a, Or.inl ha, fun z hz => ?_⟩
      exact hz.elim (fun hz => hi a z (ha.trans hz.symm))
        (fun hz => (hz.1 ⟨a, ha⟩).elim)
    · refine ⟨a₀, Or.inr ⟨hn, rfl⟩, fun z hz => ?_⟩
      exact hz.elim (fun hz => (hn ⟨z, hz⟩).elim) (fun hz => hz.2.symm)
  obtain ⟨g, hg⟩ := pl U hf
  refine ⟨g, fun a => ?_⟩
  exact (hg (f a)).elim (hi _ a) (fun h => (h.1 ⟨a, rfl⟩).elim)

theorem sections_strong_of_barcan :
    RightSplitting A B → Barcan B → StrongRightSplitting A B := fun sr bf f hs =>
  (sr f hs).elim fun g hg => ⟨g, right_inverse_strong_of_barcan bf f g hg⟩

theorem strong_sections_sections : StrongRightSplitting A B → RightSplitting A B :=
  fun sr f hs => (sr f hs).elim fun g hg => ⟨g, box_elim hg⟩

theorem strong_retractions_retractions : StrongLeftSplitting A B → LeftSplitting A B :=
  fun sl f hi => (sl f hi).elim fun g hg => ⟨g, box_elim hg⟩

theorem strong_sections_surjectivity : StrongRightSplitting A B → SurjectivityPersists A B :=
  fun sr f hs => (sr f hs).elim fun g hg => strong_right_necessary_surjective f g hg

theorem strong_retractions_injectivity : StrongLeftSplitting A B → InjectivityPersists A B :=
  fun sl f hi => (sl f hi).elim fun g hg => strong_left_necessary_injective f g hg

theorem cancelsFrom_t_injective (f : A → B) (h : CancelsFrom Prop f) : Injective f :=
  fun a b e => congrFun (h (fun _ => a) (fun _ => b)
    (congrArg (fun z : B => fun _ : Prop => z) e)) True

theorem cancel_pointwise {D : Type} [Ty D] (f : A → B) (g h : D → A) :
    Injective f → (∀ d, f (g d) = f (h d)) → ∀ d, g d = h d :=
  fun hi he d => hi _ _ (he d)

theorem necessary_injective_cancels {D : Type} [Ty D] (f : A → B)
    (hi : □ (Injective f)) : CancelsFrom D f := by
  intro g h e
  have he : □ (∀ d, f (g d) = f (h d)) := modal_K _ _
    (nec% (fun (e : (fun d => f (g d)) = (fun d => f (h d))) (d : D) => congrFun e d))
    (necessity_of_identity _ _ e)
  exact modalized_functionality g h
    (modal_K _ _ (modal_K _ _ (nec% (cancel_pointwise f g h)) hi) he)

theorem injective_cancels_of_barcan {D : Type} [Ty D] (bf : Barcan D)
    (f : A → B) (hi : Injective f) : CancelsFrom D f :=
  fun g h e => modalized_functionality g h
    (bf (fun d => g d = h d) (fun d =>
      necessity_of_identity _ _ (hi _ _ (congrFun e d))))

end

section
variable {A B : Type} [Ty A] [Rel B]

theorem surjectivity_of_barcan (bf : Barcan B) : SurjectivityPersists A B := by
  intro f hs
  apply bf (fun b => ∃ a, f a = b)
  intro b
  obtain ⟨a, e⟩ := hs b
  exact modal_K _ _
    (nec% (fun (e : f a = b) => (Exists.intro a e : ∃ x, f x = b)))
    (necessity_of_identity _ _ e)

theorem surjective_cancel (f : A → B) (g h : B → Prop) :
    Surjective f → (∀ a, g (f a) = h (f a)) → ∀ b, g b = h b :=
  fun hs he b => (hs b).elim fun a e => e ▸ he a

theorem necessary_surjective_epi (f : A → B) (hs : □ (Surjective f)) : Epi f := by
  intro g h e
  have he : □ (∀ a, g (f a) = h (f a)) := modal_K _ _
    (nec% (fun (e : (fun a => g (f a)) = (fun a => h (f a))) (a : A) => congrFun e a))
    (necessity_of_identity _ _ e)
  exact modalized_functionality g h
    (modal_K _ _ (modal_K _ _ (nec% (surjective_cancel f g h)) hs) he)

theorem epi_necessary_surjective (f : A → B) (hepi : Epi f) : □ (Surjective f) := by
  let I : B → Prop := fun b => ∃ a, f a = b
  have he : (fun a => I (f a)) = (fun _ : A => True) :=
    funext fun a => propext ⟨fun _ => trivial, fun _ => ⟨a, rfl⟩⟩
  have hi : I = (fun _ : B => True) := hepi I (fun _ => True) he
  exact modal_K _ _
    (nec% (fun (e : I = (fun _ : B => True)) (b : B) => Eq.mpr (congrFun e b) trivial))
    (necessity_of_identity _ _ hi)

theorem epi_iff_necessary_surjective (f : A → B) : Epi f ↔ □ (Surjective f) :=
  ⟨epi_necessary_surjective f, necessary_surjective_epi f⟩

end
end Classicism.Research.Splitting

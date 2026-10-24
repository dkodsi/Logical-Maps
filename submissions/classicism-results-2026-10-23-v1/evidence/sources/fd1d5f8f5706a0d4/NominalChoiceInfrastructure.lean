import Classicism.Models.NominalSoundness
import Classicism.Certified.Signatures
import Mathlib.Data.Nat.Find

/-!
# Typed IC graphs, fixed-point obstruction, and individual witnesses

This module proves the individual-witness clause of the nominal classification
for every support ideal used by the construction. It also proves the general
graph construction and the stabilizer obstruction used by the remaining orbit
arguments. It does NOT assume that all serial families have supported selectors.

Source: nominal-choice-classification-20261022.md §§3–5,7, and
support-bounds-world-geometry-20261022.md §§1–4; local research, unpaginated,
misc. Ordinary classical metatheory; uncompiled candidate.
-/

namespace Classicism.Meta.Nominal
noncomputable section
variable {G : Type} [Group G] {A : Action G} {I : SupportIdeal A}

theorem exponential_covariance (X Y : Nom A I) {S : Set A} {f : exponential X Y}
    (hf : Supports A (exponential X Y).obj S f) (g : G) (hg : Fixes A S g) (x : X) :
    f.val (X.obj.act g x) = Y.obj.act g (f.val x) :=
  (function_support_iff X Y S f.val).1
    (fun k hk => congrArg Subtype.val (hf k hk)) g hg x

/-- The external world-to-witness function is only an aid. Its graph has the
original admitted relational type X→t, even when X is the individual domain. -/
def graph (W X : Nom A I) : Hom (exponential W X) (exponential X (propositions W)) :=
  curry (lift (productNom (exponential W X) X) (function W.obj (trivial Prop))
    (fun z w => z.1.val w = z.2) (by
      intro g z
      funext w
      apply propext
      change (X.obj.act g (z.1.val (W.obj.act g⁻¹ w)) = X.obj.act g z.2) ↔
        z.1.val (W.obj.act g⁻¹ w) = z.2
      exact ⟨fun h => act_injective X.obj g h, fun h => congrArg (X.obj.act g) h⟩))

def IC (W X : Nom A I) : Prop :=
  ∀ F : exponential X (propositions W), (∀ w : W, ∃ x : X, (F.val x).val w) →
    ∃ Q : exponential X (propositions W),
      (∀ x w, (Q.val x).val w → (F.val x).val w) ∧
      ∀ w, ∃ x, (Q.val x).val w ∧ ∀ y, (Q.val y).val w → y = x

theorem graph_selects (W X : Nom A I) (F : exponential X (propositions W))
    (h : exponential W X) (hh : ∀ w, (F.val (h.val w)).val w) :
    (∀ x w, (((graph W X).fn h).val x).val w → (F.val x).val w) ∧
      ∀ w, ∃ x, (((graph W X).fn h).val x).val w ∧
        ∀ y, (((graph W X).fn h).val y).val w → y = x := by
  constructor
  · intro x w hx
    change h.val w = x at hx
    have he := congrArg (fun y : X => ((F.val y).val w : Prop)) hx
    exact Eq.mp he (hh w)
  · intro w
    exact ⟨h.val w, rfl, fun _ hy => hy.symm⟩

/-- A uniquely selected witness must be fixed by every symmetry fixing both
the selector support and the evaluation world. The world premise is essential. -/
theorem unique_witness_fixed (W X : Nom A I)
    (Q : exponential X (propositions W)) {S : Set A}
    (hQ : Supports A (exponential X (propositions W)).obj S Q)
    (w : W) (x : X) (hx : (Q.val x).val w)
    (hu : ∀ y, (Q.val y).val w → y = x)
    (g : G) (hg : Fixes A S g) (hw : W.obj.act g w = w) : X.obj.act g x = x := by
  have hi : W.obj.act g⁻¹ w = w := by
    have he := congrArg (W.obj.act g⁻¹) hw
    rw [inv_act] at he
    exact he.symm
  apply hu
  have he := congrArg (fun p : propositions W => p.val w)
    (exponential_covariance X (propositions W) hQ g hg x)
  change (Q.val (X.obj.act g x)).val w = (Q.val x).val (W.obj.act g⁻¹ w) at he
  rw [hi] at he
  exact Eq.mpr he hx

/-- The least witness graph is an admitted operation of the supplied family.
There is no countable union of supports in this construction. -/
def minimalNatural (W : Nom A I) :
    Hom (exponential (trivialNom A I Nat) (propositions W))
      (exponential (trivialNom A I Nat) (propositions W)) :=
  curry (lift
    (productNom (exponential (trivialNom A I Nat) (propositions W)) (trivialNom A I Nat))
    (function W.obj (trivial Prop))
    (fun z w => (z.1.val z.2).val w ∧ ∀ m : Nat, m < (z.2 : Nat) → ¬(z.1.val m).val w)
    (fun _ _ => rfl))

theorem ic_individuals (W : Nom A I) : IC W (trivialNom A I Nat) := by
  classical
  intro F hF
  refine ⟨(minimalNatural W).fn F, ?_, ?_⟩
  · intro n w hn
    exact hn.1
  · intro w
    let R : Nat → Prop := fun n => (F.val n).val w
    have hR : ∃ n : Nat, R n := hF w
    let n : Nat := Nat.find hR
    have hn : (F.val n).val w ∧ ∀ m < n, ¬(F.val m).val w :=
      ⟨Nat.find_spec hR, fun m hm => Nat.find_min hR hm⟩
    refine ⟨n, hn, ?_⟩
    intro m hm
    exact Nat.le_antisymm
      (Nat.le_of_not_gt (fun h => hm.2 n h hn.1))
      (Nat.le_of_not_gt (fun h => hn.2 m h hm.1))

def TrivialAction (X : Nom A I) : Prop := ∀ g : G, ∀ x : X, X.obj.act g x = x

theorem exponential_trivial (X Y : Nom A I) (hX : TrivialAction X) (hY : TrivialAction Y) :
    TrivialAction (exponential X Y) := by
  intro g f
  apply Subtype.ext
  funext x
  change Y.obj.act g (f.val (X.obj.act g⁻¹ x)) = f.val x
  rw [hX, hY]

theorem ic_trivial (W X : Nom A I) (hW : TrivialAction W) (hX : TrivialAction X) : IC W X := by
  classical
  intro F hF
  let h : W → X := fun w => Classical.choose (hF w)
  have hh : Supported A (function W.obj X.obj) I h := by
    refine ⟨∅, I.empty, ?_⟩
    intro g _
    funext w
    change X.obj.act g (h (W.obj.act g⁻¹ w)) = h w
    rw [hW, hX]
  let hs : exponential W X := ⟨h, hh⟩
  exact ⟨(graph W X).fn hs,
    graph_selects W X F hs (fun w => Classical.choose_spec (hF w))⟩

namespace Hierarchy
variable (W : Nom A I)

mutual
  theorem dom_trivial (hW : TrivialAction W) : ∀ σ : Ty, TrivialAction (dom W σ)
    | .e => fun _ _ => rfl
    | .var _ => fun _ _ => rfl
    | .rel ρ => rdom_trivial hW ρ
  theorem rdom_trivial (hW : TrivialAction W) : ∀ ρ : RTy, TrivialAction (rdom W ρ)
    | .t => exponential_trivial W (trivialNom A I Prop) hW (fun _ _ => rfl)
    | .arr σ ρ => exponential_trivial _ _ (dom_trivial hW σ) (rdom_trivial hW ρ)
end

theorem ic_all_types_trivial (hW : TrivialAction W) (σ : Ty) : IC W (dom W σ) :=
  ic_trivial W _ hW (dom_trivial W hW σ)

theorem holds_imp {Sig : Signature} (C : FixedConstants W Sig) {Γ}
    (η : env W Γ) (w : W) (p q : Formula Sig Γ) :
    Holds W C η w (Term.imp p q) ↔ (Holds W C η w p → Holds W C η w q) := by
  classical
  change (¬Holds W C η w p ∨ Holds W C η w q) ↔ _
  constructor
  · intro h hp
    exact h.elim (fun hn => False.elim (hn hp)) id
  · intro h
    by_cases hp : Holds W C η w p
    · exact Or.inr (h hp)
    · exact Or.inl hp

theorem property_le_iff (X : Nom A I) (Q F : exponential X (propositions W)) :
    F = (pointwise₂ (truthBinary W Or)).fn (Q, F) ↔
      ∀ x w, (Q.val x).val w → (F.val x).val w := by
  constructor
  · intro he x w hx
    have hp := congrArg (fun f : exponential X (propositions W) => (f.val x).val w) he
    exact Eq.mpr hp (Or.inl hx)
  · intro h
    apply Subtype.ext
    funext x
    apply Subtype.ext
    funext w
    exact propext ⟨Or.inr, fun hp => hp.elim (h x w) id⟩

/-- Connection to the existing generated pure Intensional Choice instance. -/
theorem intensionalChoice_quoted_iff (σ : Ty) (w : W) :
    Holds W (pureConstants W) (Γ := []) () w (P.IntensionalChoice.quoted σ) ↔ IC W (dom W σ) := by
  classical
  suffices h : ∀ η : env W [],
      Holds W (pureConstants W) (Γ := []) η w
        (P.IntensionalChoice.quoted σ) ↔ IC W (dom W σ) by
    exact h ()
  intro η
  unfold P.IntensionalChoice.quoted
  rw [holds_all W (pureConstants W) (Γ := []) (σ := σ ⇒ RTy.t) η w]
  simp only [holds_all W (pureConstants W),
    holds_imp W (pureConstants W), holds_exists W (pureConstants W),
    holds_and W (pureConstants W), holds_box W (pureConstants W),
    holds_eq W (pureConstants W)]
  change (∀ F : exponential (dom W σ) (propositions W),
    (∀ v, ∃ x, (F.val x).val v) →
    ∃ Q : exponential (dom W σ) (propositions W),
      F = (pointwise₂ (truthBinary W Or)).fn (Q, F) ∧
      ∀ v, ∃ x, (Q.val x).val v ∧ ∀ y, (Q.val y).val v → y = x) ↔ _
  simp only [property_le_iff W]
  rfl

theorem individuals_intensionalChoice_quoted (w : W) :
    Holds W (pureConstants W) (Γ := []) () w (P.IntensionalChoice.quoted .e) :=
  (intensionalChoice_quoted_iff W .e w).2 (ic_individuals W)

theorem individuals_boxed_intensionalChoice_quoted (w : W) :
    Holds W (pureConstants W) (Γ := []) () w (P.NecIntensionalChoice.quoted .e) := by
  change Holds W (pureConstants W) (Γ := []) () w (Term.box (P.IntensionalChoice.quoted .e))
  exact (holds_box W (pureConstants W) (Γ := []) _ () w).2 (individuals_intensionalChoice_quoted W)

theorem trivial_intensionalChoice_quoted (hW : TrivialAction W) (σ : Ty) (w : W) :
    Holds W (pureConstants W) (Γ := []) () w (P.IntensionalChoice.quoted σ) :=
  (intensionalChoice_quoted_iff W σ w).2 (ic_all_types_trivial W hW σ)

end Hierarchy
end
end Classicism.Meta.Nominal

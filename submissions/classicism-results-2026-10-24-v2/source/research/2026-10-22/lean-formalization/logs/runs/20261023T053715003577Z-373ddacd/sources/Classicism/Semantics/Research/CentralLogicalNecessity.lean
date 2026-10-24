import Classicism.Semantics.Research.CentralSupportedProductGluing
import Classicism.Semantics.Research.CentralSyntaxCountable
import Classicism.Semantics.IntensionalTheory
import Classicism.Semantics.IntensionalProperties
import Classicism.Certified.Signatures

/-!
# A concrete finite-signature Logical Necessity countermodel

New research `followup/central-map.md`, §§1–3, specialized to Sigma={c:et}.
The alphabet consists of the countably many pure formulas with one et variable.
One chosen witness for every satisfiable such formula is glued into c.
The statement is the existing `AxiomSet.logicalNecessity`, including its empty
constant tuple and all admitted finitary type instances. Its consequence for
Actuality uses the exact quoted sentence and the existing C soundness theorem.

This is an uncompiled author draft. The arbitrary-signature theorem, Tame
Rigidity, internal Countable BC, and the second symmetric model are separate
remaining obligations. No conclusion below assumes those stronger packages.
-/

namespace Classicism.Meta.Intensional.Central.OneConstant
open CategoryTheory
open Product

abbrev relationType : RTy := .arr .e .t
abbrev constantType : Ty := .rel relationType
def signature : Signature := ⟨Unit, fun _ => constantType⟩

theorem signature_closed : signature.Closed := fun _ => by decide
theorem signature_has_relational_constant :
    ∃ c : signature.Const, ∃ ρ : RTy, signature.typeOf c = .rel ρ := ⟨(), relationType, rfl⟩

abbrev Label := Formula Signature.pure [constantType]
abbrev W := World (Set Nat) Label
abbrev base : W := star (Set Nat) Label
abbrev Ar := Arrow (Set Nat) Label
noncomputable abbrev Carrier := (domain (Set Nat) Label constantType).obj base
noncomputable abbrev B₀ := pureModel (Set Nat) Label

instance : Countable Label := inferInstanceAs (Countable (Term Signature.pure [constantType] Ty.t))

noncomputable def fallback : Carrier :=
  constantProfile (Set Nat) Label relationType base (fun _ => ∅)

def Satisfiable (P : Label) : Prop := ∃ x : Carrier, B₀.Holds (𝟙 base) P (.cons x .nil)

noncomputable def witness (P : Label) : Carrier := by
  classical
  exact if h : Satisfiable P then Classical.choose h else fallback

theorem witness_holds (P : Label) (h : Satisfiable P) :
    B₀.Holds (𝟙 base) P (.cons (witness P) .nil) := by
  simpa only [witness, dif_pos h] using Classical.choose_spec h

noncomputable def glued : Carrier :=
  Classical.choose (simultaneous_predecessor Label relationType witness)

noncomputable def coordinate : Set Nat :=
  Classical.choose (Classical.choose_spec (simultaneous_predecessor Label relationType witness))

theorem glued_map (P : Label) :
    (domain (Set Nat) Label constantType).map (spike (Set Nat) Label coordinate P) glued = witness P :=
  Classical.choose_spec
    (Classical.choose_spec (simultaneous_predecessor Label relationType witness)) P

noncomputable def B : Premodel signature W := model (Set Nat) Label (fun _ => glued)
theorem B_isModel : B.IsModel := model_isModel (Set Nat) Label _
theorem B₀_isModel : B₀.IsModel := model_isModel (Set Nat) Label _

theorem reduct_eq : B.reduct = B₀ := rfl

theorem pure_at {Γ : Ctx} (P : Formula Signature.pure Γ) (h : Ar)
    (g : IEnv (B₀.Dom base) Γ) : B₀.Holds h P g ↔ B₀.Holds (𝟙 base) P g := by
  unfold Premodel.Holds
  rw [B₀.sem_pure P (Term.pure_of_pureSig P) h (𝟙 base)]

theorem holds_ofPure_at {Γ : Ctx} (P : Formula Signature.pure Γ) (h : Ar)
    (g : IEnv (B.Dom base) Γ) : B.Holds h (Term.ofPure P) g ↔ B₀.Holds (𝟙 base) P g := by
  unfold Premodel.Holds
  rw [B.sem_ofPure]
  change B₀.Holds h P g ↔ B₀.Holds (𝟙 base) P g
  exact pure_at P h g

theorem holds_at_constant (P : Label) (h : Ar) :
    B.Holds h (Term.atConsts [()] P) .nil ↔
      B₀.Holds (𝟙 base) P (.cons ((domain (Set Nat) Label constantType).map h glued) .nil) := by
  change B.Holds h ((Term.ofPure P).instantiate (.const ())) .nil ↔ _
  unfold Premodel.Holds
  rw [B.sem_instantiate B_isModel h (Term.ofPure P) (.const ()) .nil rfl,
    B.sem_ofPure]
  change B₀.Holds h P (.cons ((domain (Set Nat) Label constantType).map h glued) .nil) ↔ _
  exact pure_at P h _

theorem holds_box_at_constant (P : Label) :
    B.HoldsSentence (Term.box (Term.atConsts [()] P)) ↔
      ∀ h : Ar, B₀.Holds (𝟙 base) P
        (.cons ((domain (Set Nat) Label constantType).map h glued) .nil) := by
  constructor
  · intro H h
    have hh := (B.holds_box B_isModel _ _ _).1 H (V := base) h
    rw [Category.id_comp, IEnv.nil_eq (B.push h IEnv.nil)] at hh
    exact (holds_at_constant P _).1 hh
  · intro H
    apply (B.holds_box B_isModel _ _ _).2
    intro V h
    have e : V = base := Subsingleton.elim _ _
    subst V
    rw [IEnv.nil_eq (B.push h IEnv.nil)]
    exact (holds_at_constant P _).2 (H _)

theorem holds_unary_LN (P : Label) :
    B.HoldsSentence (Term.iff (Term.box (Term.atConsts [()] P))
      (Term.ofPure (Term.forall' P))) := by
  apply (B.holds_iff B_isModel _ _ _ _).2
  constructor
  · intro H
    apply (B.holdsSentence_ofPure (Term.forall' P)).2
    change B₀.Holds (𝟙 base) (Term.forall' P) .nil
    apply (B₀.holds_forall B₀_isModel _ _ _).2
    intro x
    by_contra hx
    have hs : Satisfiable (Term.neg P) :=
      ⟨x, (B₀.holds_neg B₀_isModel _ _ _).2 hx⟩
    have hw := (B₀.holds_neg B₀_isModel _ _ _).1 (witness_holds (Term.neg P) hs)
    have hp := (holds_box_at_constant P).1 H (spike (Set Nat) Label coordinate (Term.neg P))
    rw [glued_map] at hp
    exact hw hp
  · intro H
    apply (holds_box_at_constant P).2
    have hAll := (B.holdsSentence_ofPure (Term.forall' P)).1 H
    change B₀.Holds (𝟙 base) (Term.forall' P) .nil at hAll
    exact fun h => (B₀.holds_forall B₀_isModel _ _ _).1 hAll _

theorem holds_empty_LN (P : Sentence Signature.pure) :
    B.HoldsSentence (Term.iff (Term.box (Term.atConsts [] P)) (Term.ofPure P)) := by
  rw [Term.atConsts_nil]
  apply (B.holds_iff B_isModel _ _ _ _).2
  constructor
  · exact B.holdsSentence_of_box B_isModel
  · intro H
    have h₀ := (holds_ofPure_at P (𝟙 base) .nil).1 H
    apply (B.holds_box B_isModel _ _ _).2
    intro V h
    have e : V = base := Subsingleton.elim _ _
    subst V
    rw [IEnv.nil_eq (B.push h IEnv.nil)]
    exact (holds_ofPure_at P _ .nil).2 h₀

/-- The existing signature schema in full, not a selected formula fragment. -/
theorem holds_logicalNecessity : B.HoldsAx (AxiomSet.logicalNecessity signature) := by
  rintro a ⟨_, cs, P, hcs, rfl⟩
  cases cs with
  | nil => exact holds_empty_LN P
  | cons c cs =>
    cases c
    cases cs with
    | nil => exact holds_unary_LN P
    | cons d ds =>
      cases d
      exact False.elim ((List.nodup_cons.mp hcs).1 (by simp))

theorem holds_all_boxed_barcan (σ : Ty) : B.HoldsSentence (Term.box (Sentence.bf σ)) :=
  holds_box_bf (Set Nat) Label _ σ

theorem not_holds_actuality : ¬ B.HoldsSentence (Term.ofPure P.Actuality.quoted) := by
  intro H
  have H₀ := (B.holdsSentence_ofPure P.Actuality.quoted).1 H
  rw [reduct_eq] at H₀
  exact Product.not_holds_actuality Label (Term.top : Label) H₀

/-- Actual C nonderivability over this permitted, nonempty finite signature. -/
theorem actuality_not_theorem :
    ¬ Theorem (Meta.C.axioms ∪ AxiomSet.logicalNecessity signature)
      (Term.ofPure P.Actuality.quoted) :=
  B.not_theorem_of_model B_isModel holds_logicalNecessity not_holds_actuality

theorem logicalNecessity_consistent : (AxiomSet.logicalNecessity signature).Consistent :=
  AxiomSet.Consistent.of_model B B_isModel holds_logicalNecessity

end Classicism.Meta.Intensional.Central.OneConstant

import Classicism.Semantics.Research.CentralSupportedProductChoice

/-!
# The exact Vicinity obstruction in the supported product

New research, `followup/central-map.md`, §3. A fresh-coordinate killing arrow
preserves a proposed vicinity p and permanently falsifies another actual
truth q. Thus p cannot entail the possibility of q. This is a separate
extension of the first separator; its status is determined by the checker,
not by this source file's existence.
-/

namespace Classicism.Meta.Intensional.Central.Product
open CategoryTheory

theorem not_holds_vicinity (L : Type) (a : L) :
    ¬ (pureModel (Set Nat) L).HoldsSentence P.Vicinity.quoted := by
  let B := pureModel (Set Nat) L
  have M : B.IsModel := model_isModel (Set Nat) L _
  change ¬ B.Holds (𝟙 B.W₀) P.Vicinity.quoted .nil
  simp only [P.Vicinity.quoted, B.holds_exists M,
    B.holds_conj M, B.holds_forall M, B.holds_imp M, Premodel.holds_var,
    B.holds_eq M, Premodel.sem_var, B.sem_disj M, IEnv.get]
  rintro ⟨p, hp, hleast⟩
  obtain ⟨q, h, hq, hph, hkill⟩ := kill_another_truth L a p hp
  let g : IEnv (B.Dom B.W₀) [Ty.t, Ty.t] := .cons q (.cons p .nil)
  let d : Formula Signature.pure [Ty.t, Ty.t] := Term.dia Term.v0
  have hd : (⟨B.W₀, PUnit.unit, h⟩ : Tuple B.inner .t B.W₀) ∈ B.sem (𝟙 B.W₀) d g := by
    rw [hleast q hq]
    exact Or.inl hph
  have hD := (B.mem_sem_iff (𝟙 B.W₀) g d h).1 hd
  obtain ⟨V, k, hk⟩ := (B.holds_dia M _ Term.v0 _).1 hD
  have e : V = B.W₀ := Subsingleton.elim _ _
  subst V
  have hm := (B.holds_var _ _ Var.zero).1 hk
  let r : Arrow (Set Nat) L := k
  change value (Set Nat) L q (r * h) at hm
  exact hkill r hm

end Classicism.Meta.Intensional.Central.Product

namespace Classicism.Meta.Intensional.Central.OneConstant

theorem not_holds_vicinity : ¬ B.HoldsSentence (Term.ofPure P.Vicinity.quoted) := by
  intro H
  have H₀ := (B.holdsSentence_ofPure P.Vicinity.quoted).1 H
  rw [reduct_eq] at H₀
  exact Product.not_holds_vicinity Label (Term.top : Label) H₀

theorem package_not_entails_vicinity : ¬ (package ⟹ P.Vicinity.schemaIn) :=
  B.not_entails_of_model B_isModel holds_package
    (a := Term.ofPure P.Vicinity.quoted) ⟨P.Vicinity.quoted, rfl, rfl⟩ not_holds_vicinity

end Classicism.Meta.Intensional.Central.OneConstant

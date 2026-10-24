import Classicism.Models.NominalChoiceInfrastructure

/-!
# The exact C and C5 interface of the supported hierarchy

Rigid equality validates the existing generated boxed Necessity of Distinctness
instance at every original type. This does not infer Atomicity or Choice.
Source: nominal-choice-classification-20261022.md §1 (local, unpaginated, misc).
The interpretation and rule-by-rule soundness proofs are in the nominal modules.
Uncompiled ordinary metatheory candidate.
-/

namespace Classicism.Meta.Nominal.Hierarchy
noncomputable section
variable {G : Type} [Group G] {A : Action G} {I : SupportIdeal A}
variable (W : Nom A I)

theorem C_sound {Sig : Signature} (K : FixedConstants W Sig) {p : Sentence Sig}
    (h : Classicism.Meta.C.Theorem p) (w : W) : Holds W K () w p :=
  theorem_at W K h w (logical_valid W K w)

theorem C_consistent {Sig : Signature} (K : FixedConstants W Sig) (w : W) :
    ¬Classicism.Meta.C.Theorem (Term.bot : Sentence Sig) := logical_consistent W K w

theorem C5_quoted (σ : Ty) (w : W) :
    Holds W (pureConstants W) () w (P.NecNecessityOfDistinctness.quoted σ) := by
  classical
  simp only [P.NecNecessityOfDistinctness.quoted, P.NecessityOfDistinctness.quoted,
    holds_box, holds_all, holds_imp, holds_not, holds_eq]
  intro v x y h u
  exact h

end
end Classicism.Meta.Nominal.Hierarchy

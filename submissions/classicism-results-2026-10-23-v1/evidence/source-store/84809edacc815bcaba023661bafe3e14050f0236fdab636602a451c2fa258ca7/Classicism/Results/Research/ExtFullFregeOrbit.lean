import Classicism.Results.Research.ExtFullFregeOrbitBase

/-! Final standard-orbit bridge. Supporting lemmas are compiled separately;
all original public theorem statements and hypotheses are retained. -/

noncomputable section

namespace Classicism.Meta.Research.ExtFullFregeOrbit

open CategoryTheory Intensional ExtFullFregeCounting

#eval (do
  let out ← IO.getStdout
  out.putStrLn "Orbit endpoint: imports complete"
  out.flush : IO Unit)

variable {C : Type} [SmallCategory C] (B : Premodel Signature.pure C)
variable (M : B.IsModel) (hE : B.ExtFull) {W : C} (h : B.W₀ ⟶ W) (σ : Ty)

include hE in
/-- The actual internal number predicate denotes the standard successor orbit
in an extensionally full model. Different numerals may denote one object. -/
theorem quoted_number_iff_numeral (n : B.Dom W (tC σ)) :
    B.Holds h (Term.app (Arith.N.term σ).close (Term.var .zero)) (.cons n .nil) ↔
      ∃ k : Nat, Premodel.numeral M h σ k = n := by
  have hc : B.Holds h (Term.app (Arith.N.term σ).close (Term.var .zero)) (.cons n .nil) ↔
      B.Holds h (numberFormula σ) (.cons n .nil) := by
    unfold Premodel.Holds
    rw [B.sem_conv M (number_conversion σ)]
  refine hc.trans ((number_reflect B M hE h σ n).trans ?_)
  refine ((frame B M hE h σ).isNumber_iff_numeral n).trans ?_
  exact exists_congr (fun k => Iff.of_eq
    (congrArg (fun v : B.Dom W (tC σ) => v = n) (frame_numeral B M hE h σ k)))

end Classicism.Meta.Research.ExtFullFregeOrbit

#print axioms Classicism.Meta.Research.ExtFullFregeOrbit.number_conversion
#print axioms Classicism.Meta.Research.ExtFullFregeOrbit.quoted_number_iff_numeral

#eval (do
  let out ← IO.getStdout
  out.putStrLn "Orbit endpoint: complete"
  out.flush : IO Unit)


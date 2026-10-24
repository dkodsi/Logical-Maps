import Classicism.Results.Research.ExtFullFregeCounting
import Classicism.Semantics.Numerals
import Classicism.Certified.Arithmetic
import Classicism.Syntax.Normalize

/-!
# Standard successor orbit in extensionally full models

Original semantic argument (misc), 23 October 2026, unpaginated. This connects
the abstract counting frame to the actual quoted impredicative number predicate.
Extensionally full tests are essential: no standardness claim is made for an
arbitrary Henkin model. Collapsing successor orbits are allowed.
-/

noncomputable section

namespace Classicism.Meta.Research.ExtFullFregeOrbit

open CategoryTheory Intensional ExtFullFregeCounting

#eval (do
  let out ← IO.getStdout
  out.putStrLn "Orbit base: imports complete"
  out.flush : IO Unit)

variable {C : Type} [SmallCategory C] (B : Premodel Signature.pure C)
variable (M : B.IsModel) (hE : B.ExtFull) {W : C} (h : B.W₀ ⟶ W) (σ : Ty)

def successor (n : B.Dom W (tC σ)) : B.Dom W (tC σ) :=
  Classical.choose (M h (sucT σ) (.cons n .nil))

theorem successor_spec (n : B.Dom W (tC σ)) :
    B.Incl _ W (successor B M h σ n) = B.sem h (sucT σ) (.cons n .nil) :=
  Classical.choose_spec (M h (sucT σ) (.cons n .nil))

include hE in
theorem tests_full : Function.Surjective
    (Premodel.pext (B := B) (W := W) (σ := tC σ)) := by
  intro S
  obtain ⟨Q, hQ⟩ := hE (.arr (tC σ) .t) W {a | a.1 ∈ S}
  refine ⟨Q, ?_⟩
  ext n
  exact Iff.of_eq (congrArg (fun T => (n, PUnit.unit) ∈ T) hQ)

def frame : Frame (B.Dom W σ) (B.Dom W (tC σ))
    (B.Dom W (tP σ)) (B.Dom W (tP (tC σ))) where
  extension := Premodel.pext
  tests := Premodel.pext
  tests_full := tests_full B hE σ
  zero := Premodel.numeral M h σ 0
  successor := successor B M h σ
  realizes := Premodel.holdsOf
  remove := Premodel.minus M h
  remove_extension := Premodel.pext_minus M h
  zero_realizes := Premodel.holdsOf_zero M h _ (Premodel.numeral_zero_spec M h σ)
  successor_realizes := fun n P =>
    Premodel.holdsOf_suc M h n _ (successor_spec B M h σ n) P

/-- Exactly the numberhood clause used inside quantified Infinity. -/
def numberFormula (σ : Ty) : Formula Signature.pure [tC σ] :=
  Term.forall' (σ := tP (tC σ)) (Term.imp
    (Term.conj (Term.app (Term.var .zero) ((zeroT σ).rename Ren.ofEmpty))
      (Term.forall' (σ := tC σ) (Term.imp
        (Term.app (Term.var Var.zero.succ) (Term.var .zero))
        (Term.app (Term.var Var.zero.succ) ((sucT σ).rename (Ren.lift Ren.ofEmpty))))))
    (Term.app (Term.var .zero) (Term.var Var.zero.succ)))

#eval (do
  let out ← IO.getStdout
  out.putStrLn "Orbit base: before number_conversion"
  out.flush : IO Unit)

theorem number_conversion : Conv
    (Term.app (Arith.N.term σ).close (Term.var .zero)) (numberFormula σ) :=
  Conv.of_nf 64 _ _ rfl

#eval (do
  let out ← IO.getStdout
  out.putStrLn "Orbit base: before number_reflect"
  out.flush : IO Unit)

theorem number_reflect (n : B.Dom W (tC σ)) :
    B.Holds h (numberFormula σ) (.cons n .nil) ↔
      (frame B M hE h σ).IsNumber n := by
  rw [numberFormula, B.holds_forall M]
  change (∀ Q, _) ↔ (∀ Q, _)
  apply forall_congr'
  intro Q
  rw [B.holds_imp M, B.holds_conj M, B.holds_forall M]
  have ez : B.Incl _ W (Premodel.numeral M h σ 0) =
      B.sem h ((zeroT σ).rename Ren.ofEmpty) (.cons Q (.cons n .nil)) := by
    rw [B.sem_rename, IEnv.nil_eq (IEnv.ren _ _)]
    exact Premodel.numeral_zero_spec M h σ
  rw [B.holds_app h _ _ _ ez]
  have es (m : B.Dom W (tC σ)) : B.Incl _ W (successor B M h σ m) =
      B.sem h ((sucT σ).rename (Ren.lift Ren.ofEmpty))
        (.cons m (.cons Q (.cons n .nil))) := by
    rw [B.sem_rename]
    exact (successor_spec B M h σ m).trans
      (congrArg _ (IEnv.ext fun _ v => by cases v <;> rfl))
  simp only [B.holds_imp M, Premodel.holds_app_var1]
  have step (m : B.Dom W (tC σ)) := B.holds_app h
    (.cons m (.cons Q (.cons n .nil))) (Term.var Var.zero.succ)
    ((sucT σ).rename (Ren.lift Ren.ofEmpty)) (es m)
  simp only [step]
  change ((Premodel.numeral M h σ 0 ∈ Premodel.pext Q ∧
    (∀ m, m ∈ Premodel.pext Q → successor B M h σ m ∈ Premodel.pext Q)) →
      n ∈ Premodel.pext Q) ↔ _
  exact and_imp

#eval (do
  let out ← IO.getStdout
  out.putStrLn "Orbit base: before frame_numeral"
  out.flush : IO Unit)

theorem frame_numeral (k : Nat) :
    (frame B M hE h σ).numeral k = Premodel.numeral M h σ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change successor B M h σ ((frame B M hE h σ).numeral k) = _
      rw [ih]
      rfl

#eval (do
  let out ← IO.getStdout
  out.putStrLn "Orbit base: complete"
  out.flush : IO Unit)

end Classicism.Meta.Research.ExtFullFregeOrbit

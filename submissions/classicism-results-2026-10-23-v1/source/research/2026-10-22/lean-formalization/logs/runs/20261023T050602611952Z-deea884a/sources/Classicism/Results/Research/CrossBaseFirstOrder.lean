import Classicism.Results.Research.FregeArithmeticVocabulary

/-!
# First-order arithmetic invariance at two original counting bases

Direct source: research/2026-10-22/notes/relational-coding-recursion-20261022.md
§34.2 and §38; original unpaginated research, misc.

This is a METALINGUISTIC structural induction over the existing Meta.ATerm and
Meta.AForm syntax. Nat, Fin and environments below belong to that metatheory;
they are not newly admitted object-language types. The evaluator uses precisely
Arith.N, Arith.Sum, Arith.Prod and numerical guards at universal quantifiers.
The number fields are INTERNAL; no externally standard-numeral hypothesis occurs.

The atomic cases use submitted object-level graph-transfer proofs. The present
module does not by itself construct Derivable C for every syntax code, and does
not claim a full syntax/soundness reflection theorem for AForm.toTerm. Its checks
therefore report the kernel axioms of this metatheorem rather than run the C
relational type audit on the external syntax/environment binders.
-/
namespace Classicism.Research.CrossBaseFirstOrder
open Classicism.Meta (ATerm AForm)
open Classicism.Research.FregeNoncollapse
open Classicism.Research.CrossBaseArithmetic
open Classicism.Research.FregeArithmeticVocabulary

variable {σ ρ : Type} [Ty σ] [Ty ρ]

abbrev Num (σ : Type) := (σ → Prop) → Prop
abbrev NumEnv (σ : Type) (k : Nat) := Fin k → Num σ

def extendEnv {k : Nat} (x : Num σ) (η : NumEnv σ k) : NumEnv σ (k + 1) :=
  Fin.cases x η

def readTerm {k : Nat} : ATerm k → NumEnv σ k → Num σ
  | .var i, η => η i
  | .zero, _ => ZeroCard σ
  | .suc t, η => SucCard (readTerm t η)

def readFormula : {k : Nat} → AForm k → NumEnv σ k → Prop
  | _, .nat t, η => Arith.N σ (readTerm t η)
  | _, .sum t u v, η => Arith.Sum σ (readTerm t η) (readTerm u η) (readTerm v η)
  | _, .prod t u v, η => Arith.Prod σ (readTerm t η) (readTerm u η) (readTerm v η)
  | _, .eq t u, η => readTerm t η = readTerm u η
  | _, .neg φ, η => ¬ readFormula φ η
  | _, .disj φ ψ, η => readFormula φ η ∨ readFormula ψ η
  | _, .conj φ ψ, η => readFormula φ η ∧ readFormula ψ η
  | _, .all φ, η => ∀ x : Num σ, FiniteCardinality x → readFormula φ (extendEnv x η)

def RelatedEnvs {k : Nat} (η : NumEnv σ k) (θ : NumEnv ρ k) : Prop :=
  ∀ i, Synch (η i) (θ i)

theorem related_extend {k : Nat} (η : NumEnv σ k) (θ : NumEnv ρ k)
    (he : RelatedEnvs η θ) (x : Num σ) (y : Num ρ) (hxy : Synch x y) :
    RelatedEnvs (extendEnv x η) (extendEnv y θ) := by
  intro i
  exact Fin.cases hxy (fun j => he j) i

theorem term_synch {k : Nat} (t : ATerm k) (η : NumEnv σ k) (θ : NumEnv ρ k)
    (he : RelatedEnvs η θ) : Synch (readTerm t η) (readTerm t θ) := by
  induction t with
  | var i => exact he i
  | zero => exact synch_zero
  | suc t ih => exact synch_suc _ _ ih

theorem formula_transfer (hσ : Noncollapse σ) (hρ : Noncollapse ρ)
    {k : Nat} (φ : AForm k) :
    ∀ (η : NumEnv σ k) (θ : NumEnv ρ k), RelatedEnvs η θ →
      (readFormula φ η ↔ readFormula φ θ) := by
  induction φ with
  | nat t =>
      intro η θ he
      have hn := synch_numbers _ _ (term_synch t η θ he)
      exact ⟨fun _ => hn.2, fun _ => hn.1⟩
  | sum t u v =>
      intro η θ he
      exact sum_cross_base hσ hρ _ _ _ _ _ _
        (term_synch t η θ he) (term_synch u η θ he) (term_synch v η θ he)
  | prod t u v =>
      intro η θ he
      exact prod_cross_base hσ hρ _ _ _ _ _ _
        (term_synch t η θ he) (term_synch u η θ he) (term_synch v η θ he)
  | eq t u =>
      intro η θ he
      exact equality_cross_base hσ hρ _ _ _ _
        (term_synch t η θ he) (term_synch u η θ he)
  | neg φ ih =>
      intro η θ he
      exact ⟨fun hn hp => hn ((ih η θ he).2 hp),
        fun hn hp => hn ((ih η θ he).1 hp)⟩
  | disj φ ψ ihφ ihψ =>
      intro η θ he
      exact ⟨fun h => h.elim (fun h => Or.inl ((ihφ η θ he).1 h))
          (fun h => Or.inr ((ihψ η θ he).1 h)),
        fun h => h.elim (fun h => Or.inl ((ihφ η θ he).2 h))
          (fun h => Or.inr ((ihψ η θ he).2 h))⟩
  | conj φ ψ ihφ ihψ =>
      intro η θ he
      exact ⟨fun h => ⟨(ihφ η θ he).1 h.1, (ihψ η θ he).1 h.2⟩,
        fun h => ⟨(ihφ η θ he).2 h.1, (ihψ η θ he).2 h.2⟩⟩
  | all φ ih =>
      intro η θ he
      constructor
      · intro h y hy
        obtain ⟨x, hxy⟩ := synch_onto (σ := σ) y hy
        have hx := (synch_numbers x y hxy).1
        exact (ih (extendEnv x η) (extendEnv y θ) (related_extend η θ he x y hxy)).1
          (h x hx)
      · intro h x hx
        obtain ⟨y, hxy⟩ := synch_total (ρ := ρ) x hx
        have hy := (synch_numbers x y hxy).2
        exact (ih (extendEnv x η) (extendEnv y θ) (related_extend η θ he x y hxy)).2
          (h y hy)

def readSentence (σ : Type) [Ty σ] (φ : AForm 0) : Prop :=
  readFormula φ (fun i : Fin 0 => Fin.elim0 i : NumEnv σ 0)

theorem sentence_transfer (hσ : Noncollapse σ) (hρ : Noncollapse ρ)
    (φ : AForm 0) : readSentence σ φ ↔ readSentence ρ φ :=
  formula_transfer hσ hρ φ _ _ (fun i => Fin.elim0 i)

theorem sentence_transfer_of_arithmeticI (hσ : ArithmeticI σ) (hρ : ArithmeticI ρ)
    (φ : AForm 0) : readSentence σ φ ↔ readSentence ρ φ :=
  sentence_transfer (istar_iff_noncollapse.1 (arithmeticI_iff_istar.1 hσ))
    (istar_iff_noncollapse.1 (arithmeticI_iff_istar.1 hρ)) φ

end Classicism.Research.CrossBaseFirstOrder

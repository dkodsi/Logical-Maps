import Classicism.Semantics.IntensionalSoundness
import Classicism.Certified.Arithmetic

/-!
# Arithmetic reflection in arbitrary intensional action models

Original research, 23 October 2026 (misc), unpaginated. The proof is structural
induction over the existing ATerm/AForm grammar. Its five arithmetic symbols
are interpreted by the existing quoted zero, successor, N, Sum and Prod terms.
Boolean operations use truth at the evaluation object; guarded quantifiers
range over its INNER cardinality domain. No fullness, C5, noncollapse, choice
of an arithmetic isomorphism, or external-standardness premise is added.

This is classical semantic metatheory, not a shallow object-C proof. In
particular, it does not yet build a C derivation uniformly from a formula code.
-/

noncomputable section

namespace Classicism.Meta.Research.IntensionalArithmeticReflection

open CategoryTheory Intensional

variable {C : Type} [SmallCategory C]
variable (A : Premodel Signature.pure C) (σ : Ty)
variable {W : C} (h : A.W₀ ⟶ W)

abbrev Num := A.Dom W (Ty.nu σ)
abbrev NumValue := Outer A.inner (Ty.nu σ) W
abbrev NumEnv (k : Nat) := Fin k → Num A σ (W := W)

def extendEnv {k : Nat} (x : Num A σ (W := W))
    (η : NumEnv A σ (W := W) k) : NumEnv A σ (W := W) (k + 1) :=
  Fin.cases x η

def environment {k : Nat} (g : IEnv (A.Dom W) (numCtx σ k)) :
    NumEnv A σ (W := W) k := fun i => g.get (numVar σ i)

theorem environment_cons {k : Nat} (g : IEnv (A.Dom W) (numCtx σ k))
    (x : Num A σ (W := W)) :
    environment A σ (.cons x g) = extendEnv A σ x (environment A σ g) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · cases j
    rfl

def zero : NumValue A σ (W := W) := A.sem h (Arith.zero.term σ) .nil

def successor (x : NumValue A σ (W := W)) : NumValue A σ (W := W) :=
  A.apply (A.sem h (Arith.suc.term σ) .nil) x

def number (x : NumValue A σ (W := W)) : Prop :=
  (A.apply (A.sem h (Arith.N.term σ) .nil) x).True A.inner

def sum (x y z : NumValue A σ (W := W)) : Prop :=
  (A.apply (A.apply (A.apply (A.sem h (Arith.Sum.term σ) .nil) x) y) z).True A.inner

def prod (x y z : NumValue A σ (W := W)) : Prop :=
  (A.apply (A.apply (A.apply (A.sem h (Arith.Prod.term σ) .nil) x) y) z).True A.inner

def readTerm {k : Nat} : ATerm k → NumEnv A σ (W := W) k → NumValue A σ (W := W)
  | .var i, η => A.Incl (Ty.nu σ) W (η i)
  | .zero, _ => zero A σ h
  | .suc t, η => successor A σ h (readTerm t η)

def readFormula : {k : Nat} → AForm k → NumEnv A σ (W := W) k → Prop
  | _, .nat t, η => number A σ h (readTerm A σ h t η)
  | _, .sum t u v, η => sum A σ h (readTerm A σ h t η)
      (readTerm A σ h u η) (readTerm A σ h v η)
  | _, .prod t u v, η => prod A σ h (readTerm A σ h t η)
      (readTerm A σ h u η) (readTerm A σ h v η)
  | _, .eq t u, η => readTerm A σ h t η = readTerm A σ h u η
  | _, .neg φ, η => ¬ readFormula φ η
  | _, .disj φ ψ, η => readFormula φ η ∨ readFormula ψ η
  | _, .conj φ ψ, η => readFormula φ η ∧ readFormula ψ η
  | _, .all φ, η => ∀ x : Num A σ (W := W),
      number A σ h (A.Incl (Ty.nu σ) W x) → readFormula φ (extendEnv A σ x η)

theorem term_reflect {k : Nat} (t : ATerm k)
    (g : IEnv (A.Dom W) (numCtx σ k)) :
    A.sem h (t.toTerm σ) g = readTerm A σ h t (environment A σ g) := by
  induction t with
  | var i => rfl
  | zero => exact A.sem_close h (Arith.zero.term σ) g
  | suc t ih =>
      change A.apply (A.sem h (Arith.suc.term σ).close g)
        (A.sem h (t.toTerm σ) g) = _
      rw [A.sem_close, ih]
      rfl

variable (M : A.IsModel)
include M

/-- Every interpreted arithmetic term is an admitted inner cardinality object. -/
theorem term_admitted {k : Nat} (t : ATerm k)
    (g : IEnv (A.Dom W) (numCtx σ k)) :
    ∃ x : Num A σ (W := W),
      A.Incl (Ty.nu σ) W x = readTerm A σ h t (environment A σ g) := by
  rw [← term_reflect A σ h t g]
  exact M h (t.toTerm σ) g

theorem formula_reflect {k : Nat} (φ : AForm k) :
    ∀ g : IEnv (A.Dom W) (numCtx σ k),
      A.Holds h (φ.toTerm σ) g ↔ readFormula A σ h φ (environment A σ g) := by
  induction φ with
  | nat t =>
      intro g
      change (A.apply (A.sem h (Arith.N.term σ).close g)
        (A.sem h (t.toTerm σ) g)).True A.inner ↔ _
      rw [A.sem_close, term_reflect]
      rfl
  | sum t u v =>
      intro g
      change (A.apply (A.apply (A.apply (A.sem h (Arith.Sum.term σ).close g)
        (A.sem h (t.toTerm σ) g)) (A.sem h (u.toTerm σ) g))
          (A.sem h (v.toTerm σ) g)).True A.inner ↔ _
      rw [A.sem_close, term_reflect, term_reflect, term_reflect]
      rfl
  | prod t u v =>
      intro g
      change (A.apply (A.apply (A.apply (A.sem h (Arith.Prod.term σ).close g)
        (A.sem h (t.toTerm σ) g)) (A.sem h (u.toTerm σ) g))
          (A.sem h (v.toTerm σ) g)).True A.inner ↔ _
      rw [A.sem_close, term_reflect, term_reflect, term_reflect]
      rfl
  | eq t u =>
      intro g
      rw [AForm.toTerm, A.holds_eq M, term_reflect, term_reflect]
      rfl
  | neg φ ih =>
      intro g
      rw [AForm.toTerm, A.holds_neg M, ih]
      rfl
  | disj φ ψ ihφ ihψ =>
      intro g
      rw [AForm.toTerm, A.holds_disj M, ihφ, ihψ]
      rfl
  | conj φ ψ ihφ ihψ =>
      intro g
      rw [AForm.toTerm, A.holds_conj M, ihφ, ihψ]
      rfl
  | all φ ih =>
      intro g
      rw [AForm.toTerm, A.holds_forall M]
      change (∀ x : Num A σ (W := W), _) ↔ _
      apply forall_congr'
      intro x
      rw [A.holds_imp M, ih, environment_cons]
      change ((A.apply (A.sem h (Arith.N.term σ).close (.cons x g))
        (A.Incl (Ty.nu σ) W x)).True A.inner → _) ↔ _
      rw [A.sem_close]
      rfl

def readSentence (φ : AForm 0) : Prop :=
  readFormula A σ h φ (fun i => Fin.elim0 i)

theorem sentence_reflect (φ : AForm 0) :
    A.Holds h (φ.toTerm σ) .nil ↔ readSentence A σ h φ := by
  have he : environment A σ (W := W) (k := 0) .nil =
      (fun i : Fin 0 => Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  rw [formula_reflect A σ h M, he]
  rfl

end Classicism.Meta.Research.IntensionalArithmeticReflection

#print axioms Classicism.Meta.Research.IntensionalArithmeticReflection.term_reflect
#print axioms Classicism.Meta.Research.IntensionalArithmeticReflection.term_admitted
#print axioms Classicism.Meta.Research.IntensionalArithmeticReflection.formula_reflect
#print axioms Classicism.Meta.Research.IntensionalArithmeticReflection.sentence_reflect

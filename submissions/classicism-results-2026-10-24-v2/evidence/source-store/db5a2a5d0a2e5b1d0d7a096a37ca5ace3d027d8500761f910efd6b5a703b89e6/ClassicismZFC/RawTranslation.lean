import ClassicismZFC.SetLaws
import Classicism.Models.CoalescedInternalSyntax
import Mathlib.Data.Fintype.EquivFin

/-!
# The actual finite membership-language translation

Original formalization (misc), 23 October 2026. Raw parameters become free
variables of the source language, and finite-support restriction subsequently
moves exactly the finitely many occurring parameters into bound positions.
Every constructor has a truth lemma. No satisfaction correspondence or
arbitrary external predicate is an input to the construction.
-/

open FirstOrder FirstOrder.Language
open Erdos501.FOL (L Func Rel memM)
open Classicism.Meta (Ty Ctx Var IEnv)
open Classicism.Meta.CoalescedInternalHierarchy
open ClassicismZFC.SetLaws (pairM)

namespace ClassicismZFC.RawTranslation

variable {M : Type} [L.Structure M]

/-- Raw contexts use indices with the newest variable first; Mathlib uses
levels with the newest variable last. -/
def level : ∀ {Γ : Ctx} {σ : Ty}, Var Γ σ → Fin Γ.length
  | _ :: Γ, _, .zero => Fin.last Γ.length
  | _ :: _, _, .succ v => (level v).castSucc

def valuation : {Γ : Ctx} → RawEnv M Γ → Fin Γ.length → M
  | _, .nil => Fin.elim0
  | _, .cons x g => Fin.snoc (valuation g) x

theorem valuation_level : ∀ {Γ σ} (g : RawEnv M Γ) (v : Var Γ σ),
    valuation g (level v) = g.get v
  | _, _, .cons x g, .zero =>
    Fin.snoc_last (α := fun _ => M) (x := x) (p := valuation g)
  | _, _, .cons x g, .succ v => by
    change Fin.snoc (α := fun _ => M) (valuation g) x (level v).castSucc = g.get v
    rw [Fin.snoc_castSucc]
    exact valuation_level g v

def term : {Γ : Ctx} → RawTerm M Γ → L.Term (M ⊕ Fin Γ.length)
  | _, .var v => .var (.inr (level v))
  | _, .param x => .var (.inl x)
  | _, .pair a b => Functions.apply₂ (Func.pair : L.Functions 2) (term a) (term b)

theorem term_correct : ∀ {Γ} (t : RawTerm M Γ) (g : RawEnv M Γ),
    (term t).realize (Sum.elim id (valuation g)) = t.eval pairM g
  | _, .var v, g => by
    simpa only [term, Term.realize, RawTerm.eval, Sum.elim] using valuation_level g v
  | _, .param _, _ => by
    simp only [term, Term.realize, RawTerm.eval, Sum.elim, id_eq]
  | _, .pair a b, g => by
    simp only [term, Term.realize_functions_apply₂, RawTerm.eval]
    change pairM ((term a).realize (Sum.elim id (valuation g)))
      ((term b).realize (Sum.elim id (valuation g))) =
      pairM (a.eval pairM g) (b.eval pairM g)
    rw [term_correct a g, term_correct b g]

def formula : {Γ : Ctx} → RawFormula M Γ → L.BoundedFormula M Γ.length
  | _, .equal a b => (term a).bdEqual (term b)
  | _, .mem a b => Relations.boundedFormula₂ (Rel.mem : L.Relations 2) (term a) (term b)
  | _, .falsum => ⊥
  | _, .neg p => (formula p).not
  | _, .conj p q => formula p ⊓ formula q
  | _, .disj p q => formula p ⊔ formula q
  | _, .all _ p => (formula p).all
  | _, .ex _ p => (formula p).ex

theorem formula_correct : ∀ {Γ} (p : RawFormula M Γ) (g : RawEnv M Γ),
    (formula p).Realize id (valuation g) ↔ p.Realize memM pairM g
  | _, .equal a b, g =>
    Iff.of_eq (congrArg₂ (fun x y => x = y) (term_correct a g) (term_correct b g))
  | _, .mem a b, g => by
    rw [formula, BoundedFormula.realize_rel₂]
    exact Iff.of_eq (congrArg₂ memM (term_correct a g) (term_correct b g))
  | _, .falsum, _ => Iff.rfl
  | _, .neg p, g => by
    rw [formula, BoundedFormula.realize_not]
    exact not_congr (formula_correct p g)
  | _, .conj p q, g => by
    rw [formula, BoundedFormula.realize_inf]
    exact and_congr (formula_correct p g) (formula_correct q g)
  | _, .disj p q, g => by
    rw [formula, BoundedFormula.realize_sup]
    exact or_congr (formula_correct p g) (formula_correct q g)
  | _, .all σ p, g => by
    rw [formula, BoundedFormula.realize_all]
    apply forall_congr'
    intro x
    exact formula_correct p (.cons x g)
  | _, .ex σ p, g => by
    rw [formula, BoundedFormula.realize_ex]
    apply exists_congr
    intro x
    exact formula_correct p (.cons x g)

/-- A formula has only finitely many parameters even when the ambient model
is infinite. Restriction and relabeling produce a literal parameter-free
bounded formula, with those parameters in its first finitely many positions. -/
theorem finitely_parameterized {n : ℕ} (φ : L.BoundedFormula M n) :
    ∃ (k : ℕ) (ψ : L.BoundedFormula Empty (k + n)) (p : Fin k → M),
      ∀ xs : Fin n → M,
        ψ.Realize (fun e => nomatch e) (Fin.append p xs) ↔ φ.Realize id xs := by
  classical
  let k := Fintype.card φ.freeVarFinset
  let e : φ.freeVarFinset ≃ Fin k := Fintype.equivFin _
  let ψ₀ : L.BoundedFormula (Fin k) n := φ.restrictFreeVar e
  let ψ : L.BoundedFormula Empty (k + n) :=
    ψ₀.relabel (fun i => Sum.inr i)
  let p : Fin k → M := fun i => (e.symm i).val
  refine ⟨k, ψ, p, ?_⟩
  intro xs
  change (ψ₀.relabel (fun i => Sum.inr i)).Realize _ (Fin.append p xs) ↔ _
  rw [BoundedFormula.realize_relabel]
  have hp :
      (Sum.elim (fun e : Empty => nomatch e)
        (Fin.append p xs ∘ Fin.castAdd n) ∘ (fun i : Fin k => Sum.inr i)) = p := by
    funext i
    simp only [Function.comp_apply, Sum.elim_inr, Fin.append_left]
  have hx : Fin.append p xs ∘ Fin.natAdd k = xs := by
    funext i
    simp only [Function.comp_apply, Fin.append_right]
  rw [hp, hx]
  exact BoundedFormula.realize_restrictFreeVar (φ := φ) (f := e) (v := p) id
    (fun a => by
      change (e.symm (e a)).val = a.val
      rw [e.symm_apply_apply])

theorem finite_formula {Γ : Ctx} (φ : RawFormula M Γ) :
    ∃ (k : ℕ) (ψ : L.BoundedFormula Empty (k + Γ.length)) (p : Fin k → M),
      ∀ g : RawEnv M Γ,
        ψ.Realize (fun e => nomatch e) (Fin.append p (valuation g)) ↔
          φ.Realize memM pairM g := by
  obtain ⟨k, ψ, p, h⟩ := finitely_parameterized (formula φ)
  exact ⟨k, ψ, p, fun g => (h (valuation g)).trans (formula_correct φ g)⟩

private theorem append_snoc {k n : ℕ} (p : Fin k → M) (q : Fin n → M) (x : M) :
    Fin.snoc (Fin.append p q) x ∘ Fin.cast (Nat.add_assoc k n 1).symm =
      Fin.append p (Fin.snoc q x) := by
  calc
    _ = Fin.append (Fin.append p q) (Fin.cons x Fin.elim0) ∘
        Fin.cast (Nat.add_assoc k n 1).symm := by rw [Fin.snoc_eq_append]
    _ = (Fin.append p (Fin.append q (Fin.cons x Fin.elim0)) ∘
        Fin.cast (Nat.add_assoc k n 1)) ∘ Fin.cast (Nat.add_assoc k n 1).symm :=
      congrArg (fun f => f ∘ Fin.cast (Nat.add_assoc k n 1).symm)
        (Fin.append_assoc p q (Fin.cons x Fin.elim0))
    _ = Fin.append p (Fin.append q (Fin.cons x Fin.elim0)) := by
      funext i
      exact congrArg (Fin.append p (Fin.append q (Fin.cons x Fin.elim0))) (Fin.ext rfl)
    _ = Fin.append p (Fin.snoc q x) :=
      congrArg (Fin.append p) (Fin.snoc_eq_append q x).symm

/-- The exact format needed for the ordinary unary Separation scheme:
finitely many fixed parameters, followed by the single variable being cut out.
All raw parameters and the displayed context are included in that finite tuple. -/
theorem unary_formula {Γ : Ctx} (φ : RawFormula M (.e :: Γ)) (g : RawEnv M Γ) :
    ∃ (n : ℕ) (ψ : L.BoundedFormula Empty (n + 1)) (p : Fin n → M),
      ∀ x : M,
        ψ.Realize (fun e => nomatch e) (Fin.snoc p x) ↔
          φ.Realize memM pairM (.cons x g) := by
  obtain ⟨k, ψ₀, p₀, h⟩ := finite_formula φ
  let n := k + Γ.length
  have he : k + (.e :: Γ).length = n + 1 := (Nat.add_assoc k Γ.length 1).symm
  let ψ : L.BoundedFormula Empty (n + 1) := ψ₀.castLE he.le
  refine ⟨n, ψ, Fin.append p₀ (valuation g), ?_⟩
  intro x
  change (ψ₀.castLE he.le).Realize _ (Fin.snoc (Fin.append p₀ (valuation g)) x) ↔ _
  rw [BoundedFormula.realize_castLE_of_eq he]
  have hv : Fin.snoc (Fin.append p₀ (valuation g)) x ∘ Fin.cast he =
      Fin.append p₀ (valuation (.cons x g)) := append_snoc p₀ (valuation g) x
  rw [hv]
  exact h (.cons x g)

#print axioms term_correct
#print axioms formula_correct
#print axioms unary_formula

end ClassicismZFC.RawTranslation

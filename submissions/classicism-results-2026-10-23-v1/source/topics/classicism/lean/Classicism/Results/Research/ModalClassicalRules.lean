import Classicism.Results.Research.ModalComprehensionClassicalExtension

/-!
# Actual classical rules in the lambda-free base

Original research, misc, 23 October 2026. These are derivations in the
independently defined concrete calculus. Conjunction and disjunction retain
their implication/falsity definitions. Classicality is supplied by the
explicit DNE axiom family; no Lean proposition is used as an object proof.
The helper parameter `ContainsClassical` is just inclusion of that displayed
axiom family, so the rules apply also after conservative definition naming.
-/

namespace Classicism.Research.ModalClassicalRules
open Classicism.Meta
open ModalComprehensionConcreteSyntax

variable {Const : Ty → Type} {Ax : Axioms Const}

def ContainsClassical (Ax : Axioms Const) : Prop :=
  ∀ Γ p, ClassicalAxioms Const Γ p → Ax Γ p

theorem classical_contains : ContainsClassical (ClassicalAxioms Const) :=
  fun _ _ h => h

theorem addHyp {Γ Δ p} (q : Formula Const Γ)
    (h : Derives Const Ax Γ Δ p) : Derives Const Ax Γ (q :: Δ) p :=
  .weaken (fun _ hm => List.mem_cons_of_mem _ hm) h

theorem cutHead {Γ Δ p q}
    (hp : Derives Const Ax Γ Δ p)
    (hq : Derives Const Ax Γ (p :: Δ) q) : Derives Const Ax Γ Δ q :=
  .impE (.impI hq) hp

theorem dne (hc : ContainsClassical Ax) {Γ Δ} (p : Formula Const Γ)
    (h : Derives Const Ax Γ Δ (neg (neg p))) : Derives Const Ax Γ Δ p :=
  .impE (.ax (hc _ _ (.dne p))) h

theorem negI {Γ Δ p q}
    (hq : Derives Const Ax Γ (p :: Δ) q)
    (hnq : Derives Const Ax Γ (p :: Δ) (neg q)) :
    Derives Const Ax Γ Δ (neg p) :=
  .impI (.impE hnq hq)

theorem negE {Γ Δ p} (q : Formula Const Γ)
    (hp : Derives Const Ax Γ Δ p)
    (hnp : Derives Const Ax Γ Δ (neg p)) : Derives Const Ax Γ Δ q :=
  bottom_elimination q (.impE hnp hp)

theorem conjunctionI {Γ Δ p q}
    (hp : Derives Const Ax Γ Δ p) (hq : Derives Const Ax Γ Δ q) :
    Derives Const Ax Γ Δ (conjunction p q) :=
  .impI (.impE (.impE .hyp₀ (addHyp _ hp)) (addHyp _ hq))

theorem conjunctionE₁ (hc : ContainsClassical Ax) {Γ Δ p q}
    (h : Derives Const Ax Γ Δ (conjunction p q)) :
    Derives Const Ax Γ Δ p := by
  apply dne hc p
  apply Derives.impI
  apply Derives.impE (addHyp _ h)
  apply Derives.impI
  apply Derives.impI
  exact Derives.impE (Derives.hyp (by simp [neg])) Derives.hyp₁

theorem conjunctionE₂ (hc : ContainsClassical Ax) {Γ Δ p q}
    (h : Derives Const Ax Γ Δ (conjunction p q)) :
    Derives Const Ax Γ Δ q := by
  apply dne hc q
  apply Derives.impI
  apply Derives.impE (addHyp _ h)
  apply Derives.impI
  exact Derives.hyp₁

theorem disjunctionI₁ {Γ Δ p q}
    (hp : Derives Const Ax Γ Δ p) :
    Derives Const Ax Γ Δ (disjunction p q) :=
  .impI (negE q (addHyp _ hp) .hyp₀)

theorem disjunctionI₂ {Γ Δ p q}
    (hq : Derives Const Ax Γ Δ q) :
    Derives Const Ax Γ Δ (disjunction p q) := .impI (addHyp _ hq)

theorem disjunctionE (hc : ContainsClassical Ax) {Γ Δ p q r}
    (hpq : Derives Const Ax Γ Δ (disjunction p q))
    (hp : Derives Const Ax Γ (p :: Δ) r)
    (hq : Derives Const Ax Γ (q :: Δ) r) :
    Derives Const Ax Γ Δ r := by
  apply dne hc r
  apply Derives.impI
  have hnp : Derives Const Ax Γ (neg r :: Δ) (neg p) := by
    apply Derives.impI
    have hr : Derives Const Ax Γ (p :: neg r :: Δ) r :=
      .impE (addHyp _ (addHyp _ (Derives.impI hp))) .hyp₀
    exact Derives.impE Derives.hyp₁ hr
  have hq' : Derives Const Ax Γ (neg r :: Δ) q :=
    .impE (addHyp _ hpq) hnp
  have hr : Derives Const Ax Γ (neg r :: Δ) r :=
    .impE (addHyp _ (Derives.impI hq)) hq'
  exact Derives.impE Derives.hyp₀ hr

theorem excludedMiddle {Γ Δ} (p : Formula Const Γ) :
    Derives Const Ax Γ Δ (disjunction p (neg p)) :=
  defined_excluded_middle p

/-- The exact theoremhood restriction used by C's contextual Subst rule:
the two directions have only their displayed single hypothesis. -/
theorem equivalence_identity {Γ p q}
    (hpq : Derives Const Ax Γ [p] q)
    (hqp : Derives Const Ax Γ [q] p) :
    Derives Const Ax Γ [] (.eq p q) :=
  .intensionality .t p q (.nec (.iffI (.impI hpq) (.impI hqp)))

theorem theorem_equivalence_identity {Γ p q}
    (h : Derives Const Ax Γ [] (.iff p q)) :
    Derives Const Ax Γ [] (.eq p q) :=
  .intensionality .t p q (.nec h)

/-- Binder congruence is theorem-level and never moves a box through a
quantifier or generalizes a premise containing the eigenvariable. -/
theorem all_identity {Γ σ} {P Q : Formula Const (σ :: Γ)}
    (h : Derives Const Ax (σ :: Γ) [] (.eq P Q)) :
    Derives Const Ax Γ [] (.eq (.all P) (.all Q)) := by
  apply equivalence_identity
  · apply Derives.allI
    have hp : Derives Const Ax (σ :: Γ) [(Term.all P).wk] P := by
      have hu := Derives.allE (.var (.zero : Var (σ :: Γ) σ))
        (Derives.hyp₀ : Derives Const Ax (σ :: Γ) [(Term.all P).wk]
          (Term.all P).wk)
      simpa only [Term.rename, Derives.instantiate_at_fresh] using hu
    exact Derives.eqTruth h.lift hp
  · apply Derives.allI
    have hq : Derives Const Ax (σ :: Γ) [(Term.all Q).wk] Q := by
      have hu := Derives.allE (.var (.zero : Var (σ :: Γ) σ))
        (Derives.hyp₀ : Derives Const Ax (σ :: Γ) [(Term.all Q).wk]
          (Term.all Q).wk)
      simpa only [Term.rename, Derives.instantiate_at_fresh] using hu
    exact Derives.eqTruth (Derives.eqSymm h).lift hq

#print axioms conjunctionI
#print axioms conjunctionE₁
#print axioms conjunctionE₂
#print axioms disjunctionE
#print axioms equivalence_identity
#print axioms all_identity

end Classicism.Research.ModalClassicalRules

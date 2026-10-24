import Classicism.Results.Research.FullTypedLogicalSeparationHBridge

/-!
# The identity observer is fully qualified in H

Original proof, misc, 23 October 2026, unpaginated; ordinary H observer note §1.
Composite Boolean and quantifier identities follow by contextual beta/eta
conversion. The translated equality clauses follow from H reflexivity and
Leibniz's Law. No Classicism, Functionality, object extensionality, or
closedness assumption on the finite type list is used.
-/

namespace Classicism.Meta.Research.FullTypedLogicalSeparation
open Term Classicism.Research.FullTypedLogicalSeparationH

variable {Sig : Signature} {Γ : Ctx}

abbrev identityObserver : Term Sig Γ Observer := .lam v0

/-- Actual object beta conversion, valid at an arbitrary current context. -/
theorem identity_observe (p : Formula Sig Γ) :
    Term.app identityObserver p ≡ p := Conv.beta v0 p

@[simp] theorem identityObserver_rename {Θ : Ctx} (r : Ren Γ Θ) :
    (identityObserver (Sig := Sig) (Γ := Γ)).rename r = identityObserver := rfl

@[simp] theorem identityObserver_weaken (σ : Ty) :
    (identityObserver (Sig := Sig) (Γ := Γ)).weaken (τ := σ) = identityObserver := rfl

/-- Ref plus contextual conversion gives literal equality of convertible terms. -/
theorem identity_conversion_eq {Ax : Axioms Sig} {Ξ : List (Formula Sig Γ)}
    {σ : Ty} {a b : Term Sig Γ σ} (c : a ≡ b) :
    Derives Ax Ξ (eq' a b) :=
  .conv (.refl a) (Conv.app_congr (Conv.refl _) c)

variable {Ax : Axioms Sig} {Ξ : List (Formula Sig Γ)}

theorem identity_boolFull : Derives Ax Ξ (boolFull (identityObserver (Sig := Sig))) := by
  apply Derives.andI
  · exact identity_conversion_eq (identity_observe top)
  apply Derives.andI
  · exact identity_conversion_eq (identity_observe bot)
  apply Derives.andI
  · apply identity_conversion_eq
    exact Conv.trans
      (Conv.lam_congr (identity_observe (neg v0)))
      (Conv.symm (Conv.lam_congr
        (Conv.app_congr (Conv.refl _) (identity_observe v0))))
  apply Derives.andI
  · apply identity_conversion_eq
    exact Conv.trans
      (Conv.lam_congr (Conv.lam_congr (identity_observe (conj v1 v0))))
      (Conv.symm (Conv.lam_congr (Conv.lam_congr
        (Conv.app_congr
          (Conv.app_congr (Conv.refl _) (identity_observe v1))
          (identity_observe v0)))))
  · apply identity_conversion_eq
    exact Conv.trans
      (Conv.lam_congr (Conv.lam_congr (identity_observe (disj v1 v0))))
      (Conv.symm (Conv.lam_congr (Conv.lam_congr
        (Conv.app_congr
          (Conv.app_congr (Conv.refl _) (identity_observe v1))
          (identity_observe v0)))))

theorem identity_quantifierFull (σ : Ty) :
    Derives Ax Ξ (quantifierFull σ (identityObserver (Sig := Sig))) := by
  apply Derives.andI
  · apply identity_conversion_eq
    exact Conv.trans
      (Conv.lam_congr (identity_observe (.app (.all σ) v0)))
      (Conv.symm (Conv.lam_congr
        (Conv.app_congr (Conv.refl _)
          (Conv.trans (Conv.lam_congr (identity_observe (.app v1 v0)))
            (Conv.eta v0)))))
  · apply identity_conversion_eq
    exact Conv.trans
      (Conv.lam_congr (identity_observe (.app (.ex σ) v0)))
      (Conv.symm (Conv.lam_congr
        (Conv.app_congr (Conv.refl _)
          (Conv.trans (Conv.lam_congr (identity_observe (.app v1 v0)))
            (Conv.eta v0)))))

theorem identity_reflexivityClause (σ : Ty) :
    Derives Ax Ξ (reflexivityClause σ (identityObserver (Sig := Sig))) := by
  apply Derives.allI
  exact .conv (.refl v0) (Conv.symm (identity_observe (eq' v0 v0)))

theorem identity_leibnizClause (σ : Ty) :
    Derives Ax Ξ (leibnizClause σ (identityObserver (Sig := Sig))) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  exact .conv
    (.ll v0
      (.conv (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        (identity_observe (eq' v2 v1)))
      (.conv .hyp₀ (identity_observe (.app v0 v2))))
    (Conv.symm (identity_observe (.app v0 v1)))

theorem identity_equalityClauses (σ : Ty) :
    Derives Ax Ξ (equalityClauses σ (identityObserver (Sig := Sig))) :=
  .andI (identity_reflexivityClause σ) (identity_leibnizClause σ)

theorem identity_typeClauses : ∀ S : List Ty,
    Derives Ax Ξ (typeClauses S (identityObserver (Sig := Sig)))
  | [] => .top
  | σ :: S => .andI (identity_quantifierFull σ)
      (.andI (identity_equalityClauses σ) (identity_typeClauses S))

/-- The full composite qualification is an H theorem, uniformly in every
finite raw type list and with any unused proper axioms/local hypotheses. -/
theorem identity_goodFull (S : List Ty) :
    Derives Ax Ξ (goodFull S (identityObserver (Sig := Sig))) :=
  .andI identity_boolFull (identity_typeClauses S)

/-- Explicit base-H specialization used by the C proof transport. -/
theorem identity_goodFull_noAx (S : List Ty) :
    Derives (NoAxioms Sig) [] (goodFull S (identityObserver (Sig := Sig) (Γ := Γ))) :=
  identity_goodFull S

end Classicism.Meta.Research.FullTypedLogicalSeparation

#print axioms Classicism.Meta.Research.FullTypedLogicalSeparation.identity_goodFull_noAx

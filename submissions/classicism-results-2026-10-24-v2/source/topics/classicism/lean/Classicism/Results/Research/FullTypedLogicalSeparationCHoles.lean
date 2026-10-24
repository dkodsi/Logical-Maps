import Classicism.Results.Research.FullTypedLogicalSeparationHConsequences

/-!
# Hole congruence in H plus full typed logical separation

Original proof, misc, 23 October 2026, unpaginated; accompanying ordinary
observer note section 3. This is the contextual identity lemma needed for
the existing Subst presentation of C. All object derivations below belong
to the independent H calculus. No repository C derivation, object-level
funext, or equivalence-to-identity rule is used.

Only abstraction requires a closed-type restriction: it uses the proved
Functionality instance at the abstraction's domain and codomain. The
application branches use ordinary H identity substitution and require
no additional types in the support list.
-/

namespace Classicism.Meta.Research.FullTypedLogicalSeparation
open Term Classicism.Research.FullTypedLogicalSeparationH

variable {Sig : Signature}

/-- The finite types needed to lift an identity through a hole.
Lambda records its domain and relational codomain; applications introduce
no Functionality obligation. Its use below is restricted to formula holes. -/
def holeTypes : ∀ {Γ Γ' : Ctx} {σ τ : Ty}, Hole Sig Γ σ Γ' τ → List Ty
  | _, _, _, _, .hole => []
  | _, _, _, _, .appL C _ => holeTypes C
  | _, _, _, _, .appR _ C => holeTypes C
  | _, _, _, _, .lam (σ := σ) (ρ := ρ) C => σ :: Ty.rel ρ :: holeTypes C

@[simp] theorem holeTypes_hole {Γ : Ctx} :
    holeTypes (Sig := Sig) (Hole.hole (Γ := Γ) (τ := Ty.t)) = [] := rfl

@[simp] theorem holeTypes_appL {Γ Γ' : Ctx} {σ : Ty} {ρ : RTy}
    (C : Hole Sig Γ (σ ⇒ ρ) Γ' Ty.t) (a : Term Sig Γ σ) :
    holeTypes (.appL C a) = holeTypes C := rfl

@[simp] theorem holeTypes_appR {Γ Γ' : Ctx} {σ : Ty} {ρ : RTy}
    (f : Term Sig Γ (σ ⇒ ρ)) (C : Hole Sig Γ σ Γ' Ty.t) :
    holeTypes (.appR f C) = holeTypes C := rfl

@[simp] theorem holeTypes_lam {Γ Γ' : Ctx} {σ : Ty} {ρ : RTy}
    (C : Hole Sig (σ :: Γ) ρ Γ' Ty.t) :
    holeTypes (.lam C) = σ :: Ty.rel ρ :: holeTypes C := rfl

/-- Variable renaming changes no type collected from the binder spine. -/
theorem holeTypes_rename : ∀ {Γ Θ Γ' : Ctx} {σ : Ty}
    (r : Ren Γ Θ) (C : Hole Sig Γ σ Γ' Ty.t),
    holeTypes (C.rename r).hole = holeTypes C
  | _, _, _, _, _, .hole => rfl
  | _, _, _, _, r, .appL C _ => holeTypes_rename r C
  | _, _, _, _, r, .appR _ C => holeTypes_rename r C
  | _, _, _, _, r, .lam C => by
      simp only [Hole.rename, holeTypes, holeTypes_rename (Ren.lift r) C]

/-- Generic form: the supplied assumption consists of actual H derivations
of Functionality at closed types. It is not a hole-congruence assumption.
The input identity is unconditional in its hole context. -/
theorem hole_congruence {Ax : Axioms Sig}
    (hFun : ∀ {Γ : Ctx} {σ : Ty} {ρ : RTy}, σ.Closed → ρ.Closed →
      (F G : Term Sig Γ (σ ⇒ ρ)) →
      Derives Ax [] (imp (pointwiseIdentity F G) (eq' F G))) :
    ∀ {Γ Γ' : Ctx} {σ : Ty} (C : Hole Sig Γ σ Γ' Ty.t)
      (hClosed : Ty.AllClosed (holeTypes C)) {P Q : Formula Sig Γ'},
      Derives Ax [] (eq' P Q) →
      Derives Ax [] (eq' (C.plug P) (C.plug Q))
  | _, _, _, .hole, _, _, _, h => h
  | _, _, _, .appL C a, hClosed, _, _, h =>
      .eqCongrFun (hole_congruence hFun C hClosed h) a
  | _, _, _, .appR f C, hClosed, _, _, h =>
      .eqCongr f (hole_congruence hFun C hClosed h)
  | Γ, _, _, .lam (σ := σ) (ρ := ρ) C, hClosed, P, Q, h => by
      have hσ : σ.Closed := hClosed σ (List.mem_cons_self ..)
      have hρ : ρ.Closed := hClosed (Ty.rel ρ)
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hC : Ty.AllClosed (holeTypes C) := fun τ hτ =>
        hClosed τ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hτ))
      have hBody : Derives Ax [] (eq' (C.plug P) (C.plug Q)) :=
        hole_congruence hFun C hC h
      have hPoint : Derives Ax []
          (pointwiseIdentity (.lam (C.plug P)) (.lam (C.plug Q))) := by
        apply Derives.allI
        exact .conv hBody
          (Conv.app_congr
            (Conv.app_congr (Conv.refl _) (Conv.symm (app_lam_fresh (C.plug P))))
            (Conv.symm (app_lam_fresh (C.plug Q))))
      exact .impE (hFun hσ hρ (.lam (C.plug P)) (.lam (C.plug Q))) hPoint

/-- H plus the actual full typed OS axiom schema proves the required hole
identity. Functionality is supplied by its already-derived OS theorem. -/
theorem hole_congruence_os {Γ Γ' : Ctx} {σ : Ty}
    (C : Hole Sig Γ σ Γ' Ty.t) (hClosed : Ty.AllClosed (holeTypes C))
    {P Q : Formula Sig Γ'} (h : Derives OSAx [] (eq' P Q)) :
    Derives OSAx [] (eq' (C.plug P) (C.plug Q)) :=
  hole_congruence (fun hσ hρ F G => functionality_os_instance hσ hρ F G) C hClosed h

end Classicism.Meta.Research.FullTypedLogicalSeparation

#print axioms Classicism.Meta.Research.FullTypedLogicalSeparation.hole_congruence_os

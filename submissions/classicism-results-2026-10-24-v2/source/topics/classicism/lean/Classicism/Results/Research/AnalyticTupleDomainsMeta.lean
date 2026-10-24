import Classicism.Results.Research.AnalyticTupleDomainCertificates
import Classicism.Results.Research.AnalyticVocabulary
import Classicism.Syntax.Blocks

/-!
# Arbitrary finite curried tuple domains

`k` is a natural-number index in the metatheory, never an object-language
quantifier. `domain σ k X` is an admitted term of the actual curried k-ary
relational type. The proof of persistence is an induction assembling existing
C-minus derivations, with explicit beta/delta conversions at the interfaces.
-/

namespace Classicism.Meta.Analytic

open Classicism.Research.Analytic

def relArity (σ : Ty) : Nat → RTy
  | 0 => .t
  | k + 1 => σ ⇒ relArity σ k

theorem relArity_closed (σ : Ty) (hσ : σ.Closed) : ∀ k, (relArity σ k).Closed
  | 0 => trivial
  | k + 1 => ⟨hσ, relArity_closed σ hσ k⟩

/-- The term for `λx, D ∧ const(X x)`; there is no tuple object. -/
def appendCoordinate (σ : Ty) (ρ : RTy) {Γ : Ctx}
    (X : Term Signature.pure Γ (σ ⇒ RTy.t)) (D : Term Signature.pure Γ ρ) :
    Term Signature.pure Γ (σ ⇒ ρ) :=
  .lam (.app (.app (.andR ρ) D.weaken)
    (.app (.constR ρ) (.app X.weaken Term.v0)))

def domain (σ : Ty) : (k : Nat) → {Γ : Ctx} →
    Term Signature.pure Γ (σ ⇒ RTy.t) → Term Signature.pure Γ (relArity σ k)
  | 0, _, _ => Term.top
  | k + 1, _, X => appendCoordinate σ (relArity σ k) X (domain σ k X)

@[simp] theorem domain_zero (σ : Ty) {Γ : Ctx} (X : Term Signature.pure Γ (σ ⇒ RTy.t)) :
    domain σ 0 X = Term.top := rfl

@[simp] theorem domain_succ (σ : Ty) (k : Nat) {Γ : Ctx}
    (X : Term Signature.pure Γ (σ ⇒ RTy.t)) :
    domain σ (k + 1) X = appendCoordinate σ (relArity σ k) X (domain σ k X) := rfl

theorem appendCoordinate_rename (σ : Ty) (ρ : RTy) {Γ Δ : Ctx} (r : Ren Γ Δ)
    (X : Term Signature.pure Γ (σ ⇒ RTy.t)) (D : Term Signature.pure Γ ρ) :
    (appendCoordinate σ ρ X D).rename r =
      appendCoordinate σ ρ (X.rename r) (D.rename r) := by
  simp only [appendCoordinate, Term.rename_lam, Term.rename_app,
    Term.rename_andR, Term.rename_constR, Term.rename_var, Term.weaken_rename] <;> rfl

theorem domain_rename (σ : Ty) (k : Nat) {Γ Δ : Ctx} (r : Ren Γ Δ)
    (X : Term Signature.pure Γ (σ ⇒ RTy.t)) :
    (domain σ k X).rename r = domain σ k (X.rename r) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (appendCoordinate σ (relArity σ k) X (domain σ k X)).rename r =
      appendCoordinate σ (relArity σ k) (X.rename r) (domain σ k (X.rename r))
    exact (appendCoordinate_rename σ (relArity σ k) r X (domain σ k X)).trans
      (congrArg (fun D => appendCoordinate σ (relArity σ k) (X.rename r) D) ih)

theorem tuple_weaken_subst {Γ Δ : Ctx} {τ υ : Ty}
    (s : Sub Signature.pure Γ Δ) (a : Term Signature.pure Γ τ) :
    (a.weaken (τ := υ)).subst (Sub.lift s) = (a.subst s).weaken := by
  simp only [Term.weaken, Term.subst_rename, Term.rename_subst] <;> rfl

theorem appendCoordinate_subst (σ : Ty) (ρ : RTy) {Γ Δ : Ctx}
    (s : Sub Signature.pure Γ Δ)
    (X : Term Signature.pure Γ (σ ⇒ RTy.t)) (D : Term Signature.pure Γ ρ) :
    (appendCoordinate σ ρ X D).subst s =
      appendCoordinate σ ρ (X.subst s) (D.subst s) := by
  simp only [appendCoordinate, Term.subst_lam, Term.subst_app,
    Term.subst_andR, Term.subst_constR, Term.subst_var, tuple_weaken_subst] <;> rfl

theorem domain_subst (σ : Ty) (k : Nat) {Γ Δ : Ctx}
    (s : Sub Signature.pure Γ Δ) (X : Term Signature.pure Γ (σ ⇒ RTy.t)) :
    (domain σ k X).subst s = domain σ k (X.subst s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (appendCoordinate σ (relArity σ k) X (domain σ k X)).subst s =
      appendCoordinate σ (relArity σ k) (X.subst s) (domain σ k (X.subst s))
    exact (appendCoordinate_subst σ (relArity σ k) s X (domain σ k X)).trans
      (congrArg (fun D => appendCoordinate σ (relArity σ k) (X.subst s) D) ih)

theorem tuple_box_congr {Γ : Ctx} {p q : Formula Signature.pure Γ} (h : Conv p q) :
    Conv (Term.box p) (Term.box q) :=
  Conv.app_congr (Conv.app_congr (Conv.refl _) h) (Conv.refl _)

theorem tuple_forall_congr {Γ : Ctx} {σ : Ty}
    {p q : Formula Signature.pure (σ :: Γ)} (h : Conv p q) :
    Conv (Term.forall' p) (Term.forall' q) :=
  Conv.app_congr (Conv.refl _) (Conv.lam_congr h)

theorem tuple_lift_instantiate {Γ : Ctx} {σ : Ty} {ρ : RTy}
    (b : Term Signature.pure (σ :: Γ) ρ) :
    (b.rename (Ren.lift Ren.shift)).instantiate (.var .zero) = b := by
  show (b.rename (Ren.lift Ren.shift)).subst (Sub.cons (.var .zero) Sub.id) = b
  rw [Term.subst_rename]
  refine (congrArg (fun s : Sub Signature.pure (σ :: Γ) (σ :: Γ) => b.subst s)
    ?_).trans (Term.subst_id b)
  funext υ v
  cases v <;> rfl

theorem tuple_lam_weaken_apply {Γ : Ctx} {σ : Ty} {ρ : RTy}
    (b : Term Signature.pure (σ :: Γ) ρ) :
    Conv (Term.app (Term.lam b).weaken (.var .zero)) b := by
  have h := Conv.beta (b.rename (Ren.lift Ren.shift)) (.var .zero)
  rwa [tuple_lift_instantiate] at h

theorem tuple_box_arrow {Γ : Ctx} (σ : Ty) (ρ : RTy)
    (D : Term Signature.pure Γ (σ ⇒ ρ)) :
    Conv (Term.app (.boxR (σ ⇒ ρ)) D)
      (Term.lam (Term.app (.boxR ρ) (Term.app D.weaken Term.v0))) :=
  Conv.trans (Conv.app_congr (Conv.delta rfl) (Conv.refl D)) (Conv.beta _ D)

theorem tuple_incl_arrow {Γ : Ctx} (σ : Ty) (ρ : RTy)
    (D E : Term Signature.pure Γ (σ ⇒ ρ)) :
    Conv (Term.app (Term.app (.inclR (σ ⇒ ρ)) D) E)
      (Term.forall' (Term.app (Term.app (.inclR ρ) (Term.app D.weaken Term.v0))
        (Term.app E.weaken Term.v0))) := by
  refine Conv.trans
    (Conv.app_congr (Conv.app_congr (Conv.delta rfl) (Conv.refl D)) (Conv.refl E)) ?_
  refine Conv.trans (Conv.app_congr (Conv.beta _ D) (Conv.refl E)) ?_
  refine Conv.trans (Conv.beta _ E) (Conv.of_eq ?_)
  change Term.forall' (Term.app
      (Term.app (.inclR ρ) (Term.app
        (D.weaken.weaken.subst (Sub.lift (Sub.cons E Sub.id))) Term.v0))
      (Term.app E.weaken Term.v0)) =
    Term.forall' (Term.app (Term.app (.inclR ρ) (Term.app D.weaken Term.v0))
      (Term.app E.weaken Term.v0))
  rw [Term.weaken_weaken_subst_lift]

def persistArrow (σ : Ty) (ρ : RTy) {Γ : Ctx}
    (D : Term Signature.pure Γ (σ ⇒ ρ)) : Formula Signature.pure Γ :=
  Term.box (Term.forall' (Term.app
    (Term.app (.inclR ρ) (Term.app D.weaken Term.v0))
    (Term.app (.boxR ρ) (Term.app D.weaken Term.v0))))

theorem persist_arrow_conversion {Γ : Ctx} (σ : Ty) (ρ : RTy)
    (D : Term Signature.pure Γ (σ ⇒ ρ)) :
    Conv (persist (σ ⇒ ρ) D) (persistArrow σ ρ D) := by
  apply tuple_box_congr
  refine Conv.trans
    (Conv.app_congr (Conv.refl _) (tuple_box_arrow σ ρ D)) ?_
  refine Conv.trans (tuple_incl_arrow σ ρ D _) ?_
  apply tuple_forall_congr
  exact Conv.app_congr (Conv.refl _)
    (tuple_lam_weaken_apply (Term.app (.boxR ρ) (Term.app D.weaken Term.v0)))

theorem tuple_box_t {Γ : Ctx} (p : Formula Signature.pure Γ) :
    Conv (Term.app (.boxR .t) p) (Term.box p) :=
  Conv.trans (Conv.app_congr (Conv.delta rfl) (Conv.refl p)) (Conv.beta _ p)

theorem tuple_incl_t {Γ : Ctx} (p q : Formula Signature.pure Γ) :
    Conv (Term.app (Term.app (.inclR .t) p) q) (Term.imp p q) := by
  refine Conv.trans
    (Conv.app_congr (Conv.app_congr (Conv.delta rfl) (Conv.refl p)) (Conv.refl q)) ?_
  refine Conv.trans (Conv.app_congr (Conv.beta _ p) (Conv.refl q)) ?_
  refine Conv.trans (Conv.beta _ q) (Conv.of_eq ?_)
  change Term.imp (p.weaken.instantiate q) q = Term.imp p q
  rw [Term.instantiate_weaken]

theorem tuple_persistence_body_t {Γ : Ctx} (p : Formula Signature.pure Γ) :
    Conv (Term.app (Term.app (.inclR .t) p) (Term.app (.boxR .t) p))
      (Term.imp p (Term.box p)) :=
  Conv.trans (Conv.app_congr (Conv.refl _) (tuple_box_t p)) (tuple_incl_t p (Term.box p))

theorem persist_t_conversion {Γ : Ctx} (p : Formula Signature.pure Γ) :
    Conv (persist .t p) (Term.box (Term.imp p (Term.box p))) :=
  tuple_box_congr (tuple_persistence_body_t p)

def persistUnary (σ : Ty) {Γ : Ctx}
    (X : Term Signature.pure Γ (σ ⇒ RTy.t)) : Formula Signature.pure Γ :=
  Term.box (Term.forall' (Term.imp (Term.app X.weaken Term.v0)
    (Term.box (Term.app X.weaken Term.v0))))

theorem persist_unary_conversion {Γ : Ctx} (σ : Ty)
    (X : Term Signature.pure Γ (σ ⇒ RTy.t)) :
    Conv (persist (σ ⇒ RTy.t) X) (persistUnary σ X) :=
  Conv.trans (persist_arrow_conversion σ .t X)
    (tuple_box_congr (tuple_forall_congr
      (tuple_persistence_body_t (Term.app X.weaken Term.v0))))

def appendPersistExpanded (σ : Ty) (ρ : RTy) {Γ : Ctx}
    (X : Term Signature.pure Γ (σ ⇒ RTy.t)) (D : Term Signature.pure Γ ρ) :
    Formula Signature.pure Γ :=
  Term.box (Term.forall' (Term.app
    (Term.app (.inclR ρ) (Term.app (Term.app (.andR ρ) D.weaken)
      (Term.app (.constR ρ) (Term.app X.weaken Term.v0))))
    (Term.app (.boxR ρ) (Term.app (Term.app (.andR ρ) D.weaken)
      (Term.app (.constR ρ) (Term.app X.weaken Term.v0))))))

theorem append_persist_conversion {Γ : Ctx} (σ : Ty) (ρ : RTy)
    (X : Term Signature.pure Γ (σ ⇒ RTy.t)) (D : Term Signature.pure Γ ρ) :
    Conv (persist (σ ⇒ ρ) (appendCoordinate σ ρ X D)) (appendPersistExpanded σ ρ X D) := by
  refine Conv.trans (persist_arrow_conversion σ ρ (appendCoordinate σ ρ X D)) ?_
  apply tuple_box_congr
  apply tuple_forall_congr
  have hb := tuple_lam_weaken_apply
    (Term.app (Term.app (.andR ρ) D.weaken)
      (Term.app (.constR ρ) (Term.app X.weaken Term.v0)))
  exact Conv.app_congr (Conv.app_congr (Conv.refl _) hb) (Conv.app_congr (Conv.refl _) hb)

set_option maxHeartbeats 600000 in
theorem append_coordinate_rule (σ : Ty) (ρ : RTy) {Γ : Ctx}
    {Δ : List (Formula Signature.pure Γ)}
    (X : Term Signature.pure Γ (σ ⇒ RTy.t)) (D : Term Signature.pure Γ ρ)
    (hX : Derivable C.axiomsMinus Δ (persist (σ ⇒ RTy.t) X))
    (hD : Derivable C.axiomsMinus Δ (persist ρ D)) :
    Derivable C.axiomsMinus Δ (persist (σ ⇒ ρ) (appendCoordinate σ ρ X D)) := by
  have rule : Theorem C.axiomsMinus
      (Term.forall' (σ := σ ⇒ RTy.t) (Term.forall' (σ := ρ)
        (Term.imp (persistUnary σ Term.v1)
          (Term.imp (persist ρ Term.v0) (appendPersistExpanded σ ρ Term.v1 Term.v0))))) :=
    Derivable.conv (append_coordinate_persistent.derivable σ ρ)
      (Conv.of_nf_left 3 _ _ rfl)
  have h : Derivable C.axiomsMinus Δ (appendPersistExpanded σ ρ X D) :=
    Derivable.impE (Derivable.impE
      (Derivable.allE₂β (Derivable.ofTheorem rule) X D)
      (Derivable.conv hX (persist_unary_conversion σ X))) hD
  exact Derivable.conv h (append_persist_conversion σ ρ X D).symm

/-- Every finite curried tuple-domain is persistent when `X` is. -/
theorem domain_persistent (σ : Ty) (k : Nat) {Γ : Ctx}
    {Δ : List (Formula Signature.pure Γ)}
    (X : Term Signature.pure Γ (σ ⇒ RTy.t))
    (hX : Derivable C.axiomsMinus Δ (persist (σ ⇒ RTy.t) X)) :
    Derivable C.axiomsMinus Δ (persist (relArity σ k) (domain σ k X)) := by
  induction k with
  | zero =>
    have base : Theorem C.axiomsMinus
        (Term.box (Term.imp Term.top (Term.box Term.top))) :=
      Derivable.conv empty_domain_persistent.derivable (Conv.of_nf 4 _ _ rfl)
    exact Derivable.conv (Derivable.ofTheorem base)
      (persist_t_conversion Term.top).symm
  | succ k ih => exact append_coordinate_rule σ (relArity σ k) X (domain σ k X) hX ih

/-- The implication certificate, with the premise explicit in the object language. -/
theorem domain_persistence_imp (σ : Ty) (k : Nat) {Γ : Ctx}
    (X : Term Signature.pure Γ (σ ⇒ RTy.t)) :
    Derivable C.axiomsMinus [] (Term.imp (persist (σ ⇒ RTy.t) X)
      (persist (relArity σ k) (domain σ k X))) :=
  Derivable.impI (domain_persistent σ k X Derivable.hyp₀)

end Classicism.Meta.Analytic

#print axioms Classicism.Meta.Analytic.domain_persistent

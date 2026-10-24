import Classicism.Results.Research.FullTypedLogicalSeparationHClosure

/-!
# Barcan and Functionality from full typed observer separation over H

Original proof, misc, 23 October 2026, unpaginated; ordinary observer note §3.
The proofs below use the independent H calculus. Their separation premise is
an explicit formula of the object language, not an assumed metatheoretic rule.
-/
namespace Classicism.Meta.Research.FullTypedLogicalSeparation
open Term Classicism.Research.FullTypedLogicalSeparationH

variable {Sig : Signature} {Ax : Axioms Sig} {Γ : Ctx}

/-- The right side of the exact typed separation instance. -/
def observerCondition (ρ : RTy) (S : List Ty)
    (X Y : Term Sig Γ ρ) : Formula Sig Γ :=
  forall' (σ := Observer) (imp (goodFull S v0) (agree ρ v0 X.weaken Y.weaken))

def pointwiseTop {σ : Ty} (F : Term Sig Γ (σ ⇒ RTy.t)) : Formula Sig Γ :=
  forall' (σ := σ) (eq' (.app F.weaken v0) top)

def pointwiseIdentity {σ : Ty} {ρ : RTy}
    (F G : Term Sig Γ (σ ⇒ ρ)) : Formula Sig Γ :=
  forall' (σ := σ) (eq' (.app F.weaken v0) (.app G.weaken v0))

theorem pointwiseTop_rename {Θ : Ctx} {σ : Ty} (r : Ren Γ Θ)
    (F : Term Sig Γ (σ ⇒ RTy.t)) :
    (pointwiseTop F).rename r = pointwiseTop (F.rename r) := by
  simp [pointwiseTop, forall', eq', top, ← Term.weaken_rename, Ren.lift]

theorem pointwiseIdentity_rename {Θ : Ctx} {σ : Ty} {ρ : RTy} (r : Ren Γ Θ)
    (F G : Term Sig Γ (σ ⇒ ρ)) :
    (pointwiseIdentity F G).rename r = pointwiseIdentity (F.rename r) (G.rename r) := by
  simp [pointwiseIdentity, forall', eq', ← Term.weaken_rename, Ren.lift]

theorem pointwiseTop_at {Ξ : List (Formula Sig Γ)} {σ : Ty}
    {F : Term Sig Γ (σ ⇒ RTy.t)} (h : Derives Ax Ξ (pointwiseTop F))
    (a : Term Sig Γ σ) : Derives Ax Ξ (eq' (.app F a) top) := by
  have hh := Derives.allEβ h a
  simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using hh

theorem pointwiseIdentity_at {Ξ : List (Formula Sig Γ)} {σ : Ty} {ρ : RTy}
    {F G : Term Sig Γ (σ ⇒ ρ)} (h : Derives Ax Ξ (pointwiseIdentity F G))
    (a : Term Sig Γ σ) : Derives Ax Ξ (eq' (.app F a) (.app G a)) := by
  have hh := Derives.allEβ h a
  simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using hh

theorem goodFull_observes_top {Ξ : List (Formula Sig Γ)} {S : List Ty}
    {E : Term Sig Γ Observer} (h : Derives Ax Ξ (goodFull S E)) :
    Derives Ax Ξ (.app E top) :=
  .eqMpr (boolFull_top_eq (goodFull_bool h)) .top

/-- Each qualified observer accepts a universal whose instances are literally top. -/
theorem observes_forall_of_pointwiseTop
    (hAx : ∀ {Γ Θ : Ctx} (r : Ren Γ Θ) {a : Formula Sig Γ}, Ax a → Ax (a.rename r))
    {Ξ : List (Formula Sig Γ)} {σ : Ty} {S : List Ty} (hσ : σ ∈ S)
    {E : Term Sig Γ Observer} {F : Term Sig Γ (σ ⇒ RTy.t)}
    (hGood : Derives Ax Ξ (goodFull S E))
    (hF : Derives Ax Ξ (pointwiseTop F)) :
    Derives Ax Ξ (.app E (.app (.all σ) F)) := by
  apply Derives.eqMpr (quantifierFull_all_eq (goodFull_quantifier hσ hGood) F)
  apply Derives.allI
  have hGood' : Derives Ax (Hyps.weaken (σ := σ) Ξ) (goodFull S (E.weaken (τ := σ))) := by
    have hh := Derives.rename hAx (Ren.shift (σ := σ)) hGood
    simpa only [goodFull_rename] using hh
  have hF' : Derives Ax (Hyps.weaken (σ := σ) Ξ) (pointwiseTop F.weaken) := by
    have hh := Derives.rename hAx (Ren.shift (σ := σ)) hF
    simpa only [pointwiseTop_rename] using hh
  exact .eqMpr (.eqCongr E.weaken (pointwiseTop_at hF' v0))
    (goodFull_observes_top hGood')

/-- Exact H consequence of the propositional instance of the full typed schema.
No optional premise is necessitated. -/
theorem barcan_of_separation_instance
    (hAx : ∀ {Γ Θ : Ctx} (r : Ren Γ Θ) {a : Formula Sig Γ}, Ax a → Ax (a.rename r))
    {Ξ : List (Formula Sig Γ)} {σ : Ty} (F : Term Sig Γ (σ ⇒ RTy.t))
    (hSep : Derives Ax Ξ (iff (eq' (.app (.all σ) F) top)
      (observerCondition .t [σ] (.app (.all σ) F) top)))
    (hF : Derives Ax Ξ (pointwiseTop F)) :
    Derives Ax Ξ (eq' (.app (.all σ) F) top) := by
  apply Derives.iffE₂ hSep
  apply Derives.allI
  apply Derives.impI
  let E : Term Sig (Observer :: Γ) Observer := v0
  have hGood : Derives Ax (goodFull [σ] E :: Hyps.weaken Ξ) (goodFull [σ] E) := .hyp₀
  have hF' : Derives Ax (goodFull [σ] E :: Hyps.weaken Ξ) (pointwiseTop F.weaken) := by
    have hh := Derives.rename hAx (Ren.shift (σ := Observer)) hF
    exact Derives.weaken₁ (by simpa only [pointwiseTop_rename] using hh)
  have hall := observes_forall_of_pointwiseTop hAx (List.mem_cons_self ..) hGood hF'
  have htop := goodFull_observes_top hGood
  exact .iffI (Derives.weaken₁ htop) (Derives.weaken₁ hall)

/-- Literal identity implies observed truth agreement at every arity, already in H.
This is identity substitution, not a rule identifying coextensive functions. -/
theorem agreement_of_identity
    (hAx : ∀ {Γ Θ : Ctx} (r : Ren Γ Θ) {a : Formula Sig Γ}, Ax a → Ax (a.rename r)) :
    ∀ (ρ : RTy) {Γ : Ctx} {Ξ : List (Formula Sig Γ)}
      (E : Term Sig Γ Observer) (X Y : Term Sig Γ ρ),
      Derives Ax Ξ (eq' X Y) → Derives Ax Ξ (agree ρ E X Y)
  | .t, _, _, E, _, _, h => equality_iff (.eqCongr E h)
  | .arr σ ρ, _, Ξ, E, X, Y, h => by
      apply Derives.allI
      have hh : Derives Ax (Hyps.weaken (σ := σ) Ξ) (eq' X.weaken Y.weaken) :=
        Derives.rename hAx Ren.shift h
      exact agreement_of_identity hAx ρ E.weaken (.app X.weaken v0) (.app Y.weaken v0)
        (.eqCongrFun hh v0)

/-- Pointwise literal identities supply the agreement demanded by separation,
regardless of the observer qualification. -/
theorem functionality_of_separation_instance
    (hAx : ∀ {Γ Θ : Ctx} (r : Ren Γ Θ) {a : Formula Sig Γ}, Ax a → Ax (a.rename r))
    {Ξ : List (Formula Sig Γ)} {σ : Ty} {ρ : RTy}
    (F G : Term Sig Γ (σ ⇒ ρ))
    (hSep : Derives Ax Ξ (iff (eq' F G) (observerCondition (σ ⇒ ρ) [] F G)))
    (hFG : Derives Ax Ξ (pointwiseIdentity F G)) :
    Derives Ax Ξ (eq' F G) := by
  apply Derives.iffE₂ hSep
  apply Derives.allI
  apply Derives.impI
  apply Derives.allI
  let Ξ := goodFull [] (v0 : Term Sig (Observer :: Γ) Observer) :: Hyps.weaken Ξ
  have hFG' : Derives Ax Ξ (pointwiseIdentity F.weaken G.weaken) := by
    have hh := Derives.rename hAx (Ren.shift (σ := Observer)) hFG
    exact Derives.weaken₁ (by simpa only [pointwiseIdentity_rename] using hh)
  have hFG'' : Derives Ax (Hyps.weaken (σ := σ) Ξ)
      (pointwiseIdentity F.weaken.weaken G.weaken.weaken) := by
    have hh := Derives.rename hAx (Ren.shift (σ := σ)) hFG'
    simpa only [pointwiseIdentity_rename] using hh
  exact agreement_of_identity hAx ρ (v1 : Term Sig (σ :: Observer :: Γ) Observer)
    (.app F.weaken.weaken v0) (.app G.weaken.weaken v0) (pointwiseIdentity_at hFG'' v0)


theorem barcan_of_full_separation
    (hAx : ∀ {Γ Θ : Ctx} (r : Ren Γ Θ) {a : Formula Sig Γ}, Ax a → Ax (a.rename r))
    {Ξ : List (Formula Sig Γ)} {σ : Ty} (F : Term Sig Γ (σ ⇒ RTy.t))
    (hSep : Derives Ax Ξ (separation .t [σ]).close)
    (hF : Derives Ax Ξ (pointwiseTop F)) :
    Derives Ax Ξ (eq' (.app (.all σ) F) top) :=
  barcan_of_separation_instance hAx F
    (separation_instance .t [σ] (.app (.all σ) F) top hSep) hF

theorem functionality_of_full_separation
    (hAx : ∀ {Γ Θ : Ctx} (r : Ren Γ Θ) {a : Formula Sig Γ}, Ax a → Ax (a.rename r))
    {Ξ : List (Formula Sig Γ)} {σ : Ty} {ρ : RTy} (F G : Term Sig Γ (σ ⇒ ρ))
    (hSep : Derives Ax Ξ (separation (σ ⇒ ρ) []).close)
    (hFG : Derives Ax Ξ (pointwiseIdentity F G)) :
    Derives Ax Ξ (eq' F G) :=
  functionality_of_separation_instance hAx F G
    (separation_instance (σ ⇒ ρ) [] F G hSep) hFG

/-- BF at an admitted type, with every premise and quantifier explicit. -/
theorem barcan_os_instance {σ : Ty} (hσ : σ.Closed)
    (F : Term Sig Γ (σ ⇒ RTy.t)) :
    Derives OSAx [] (imp (pointwiseTop F) (eq' (.app (.all σ) F) top)) := by
  apply Derives.impI
  apply barcan_of_full_separation OSAx_rename F
    (separation_axiom .t [σ] trivial ?_) Derives.hyp₀
  intro τ hτ
  have he : τ = σ := List.mem_singleton.1 hτ
  subst τ
  exact hσ

/-- Current Functionality at every admitted arrow into a relational type. -/
theorem functionality_os_instance {σ : Ty} {ρ : RTy}
    (hσ : σ.Closed) (hρ : ρ.Closed) (F G : Term Sig Γ (σ ⇒ ρ)) :
    Derives OSAx [] (imp (pointwiseIdentity F G) (eq' F G)) := by
  apply Derives.impI
  exact functionality_of_full_separation OSAx_rename F G
    (separation_axiom (σ ⇒ ρ) [] ⟨hσ, hρ⟩ (by intro τ hτ; exact False.elim (List.not_mem_nil hτ)))
    Derives.hyp₀

def barcanSentence (σ : Ty) : Sentence Sig :=
  forall' (σ := σ ⇒ RTy.t)
    (imp (pointwiseTop v0) (eq' (.app (.all σ) v0) top))

def functionalitySentence (σ : Ty) (ρ : RTy) : Sentence Sig :=
  forall' (σ := σ ⇒ ρ) (forall' (σ := σ ⇒ ρ)
    (imp (pointwiseIdentity v1 v0) (eq' v1 v0)))

theorem barcan_os (σ : Ty) (hσ : σ.Closed) :
    Derives OSAx [] (barcanSentence (Sig := Sig) σ) :=
  .allI (barcan_os_instance hσ v0)

theorem functionality_os (σ : Ty) (ρ : RTy) (hσ : σ.Closed) (hρ : ρ.Closed) :
    Derives OSAx [] (functionalitySentence (Sig := Sig) σ ρ) :=
  .allI (.allI (functionality_os_instance hσ hρ v1 v0))

/-- The exact combined H result: C as the H-closure of H Logical Equivalence,
Barcan at every admitted type, and Functionality at every admitted arrow.
The full composite B/Q identities and translated R/L remain in OSAx. -/
theorem h_full_logical_separation :
    (∀ {Γ : Ctx} {Ξ : List (Formula Sig Γ)} {p : Formula Sig Γ},
      CFromH Ξ p → Derives OSAx Ξ p) ∧
    (∀ σ : Ty, σ.Closed → Derives OSAx [] (barcanSentence (Sig := Sig) σ)) ∧
    (∀ (σ : Ty) (ρ : RTy), σ.Closed → ρ.Closed →
      Derives OSAx [] (functionalitySentence (Sig := Sig) σ ρ)) :=
  ⟨fun h => classicism_from_full_separation h, barcan_os, functionality_os⟩

end Classicism.Meta.Research.FullTypedLogicalSeparation

#print axioms Classicism.Meta.Research.FullTypedLogicalSeparation.barcan_os
#print axioms Classicism.Meta.Research.FullTypedLogicalSeparation.functionality_os
#print axioms Classicism.Meta.Research.FullTypedLogicalSeparation.h_full_logical_separation

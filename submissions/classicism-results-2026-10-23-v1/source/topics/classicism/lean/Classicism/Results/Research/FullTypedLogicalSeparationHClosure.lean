import Classicism.Results.Research.FullTypedLogicalSeparationHBridge

/-!
# Full typed logical separation closes H under Logical Equivalence

Direct source: `research/2026-10-23/operator-characterizations/h-logical-observer-strengthening.txt`,
sections 2--3 (misc, original proof, 23 October 2026, unpaginated).

This file uses the independent H calculus throughout. Its CFromH presentation
adds the identities licensed by ClosedH proofs of coextension. No identification
with the existing `Meta.C.Derivable` (which has recursive Subst) is asserted.
ClosedH records finite closed rule support. The forgetful map to unrestricted
H is proved; no general bridge from a fixed-language H proof to ClosedH is
claimed here. The larger type list needed by separation also contains the
argument types of the relation being identified.
-/

namespace Classicism.Meta.Research.FullTypedLogicalSeparation
open Term
open Classicism.Research.FullTypedLogicalSeparationH

variable {Sig : Signature} {Γ : Ctx}

/-- Explicit coextension, with a material biconditional at the final type t. -/
def coext₀ : (ρ : RTy) → {Γ : Ctx} →
    Term Sig Γ ρ → Term Sig Γ ρ → Formula Sig Γ
  | .t, _, X, Y => iff X Y
  | .arr σ ρ, _, X, Y => forall' (σ := σ)
      (coext₀ ρ (.app X.weaken v0) (.app Y.weaken v0))

theorem coext₀_rename (ρ : RTy) {Θ : Ctx} (r : Ren Γ Θ)
    (X Y : Term Sig Γ ρ) :
    (coext₀ ρ X Y).rename r = coext₀ ρ (X.rename r) (Y.rename r) := by
  induction ρ using RTy.induction generalizing Γ Θ with
  | t => simp [coext₀, iff, imp, conj, disj, neg]
  | arr σ ρ ih =>
      simp [coext₀, forall', ih, ← Term.weaken_rename, Ren.lift]

/-- The context-indexed instances of the closed separation sentences. -/
def OSAx : Axioms Sig := fun {Γ} p =>
  ∃ ρ : RTy, ∃ S : List Ty,
    ρ.Closed ∧ Ty.AllClosed S ∧ p = (separation (Sig := Sig) ρ S).close

theorem close_rename {Θ : Ctx} (r : Ren Γ Θ) (a : Sentence Sig) :
    (a.close : Formula Sig Γ).rename r = a.close := by
  simp only [Term.close, Term.rename_rename]
  congr 1
  funext σ v
  exact nomatch v

theorem OSAx_rename {Θ : Ctx} (r : Ren Γ Θ) {a : Formula Sig Γ}
    (ha : OSAx a) : OSAx (a.rename r) := by
  obtain ⟨ρ, S, hρ, hS, rfl⟩ := ha
  exact ⟨ρ, S, hρ, hS, close_rename r _⟩

theorem separation_axiom (ρ : RTy) (S : List Ty) (hρ : ρ.Closed)
    (hS : Ty.AllClosed S) {Ξ : List (Formula Sig Γ)} :
    Derives OSAx Ξ (separation (Sig := Sig) ρ S).close :=
  .ax ⟨ρ, S, hρ, hS, rfl⟩

/-- Applying the two relation quantifiers of an exact separation sentence. -/
theorem separation_instance {Ax : Axioms Sig} {Ξ : List (Formula Sig Γ)}
    (ρ : RTy) (S : List Ty) (X Y : Term Sig Γ ρ)
    (hSep : Derives Ax Ξ (separation (Sig := Sig) ρ S).close) :
    Derives Ax Ξ (iff (eq' X Y)
      (forall' (σ := Observer)
        (imp (goodFull S v0) (agree ρ v0 X.weaken Y.weaken)))) := by
  have h₀ : Derives Ax Ξ (forall' (σ := ρ) (forall' (σ := ρ)
      (iff (eq' v1 v0) (forall' (σ := Observer)
        (imp (goodFull S v0) (agree ρ v0 v2 v1)))))) := by
    simpa only [Term.close, separation, forall', iff, imp, conj, disj, neg, eq',
      Term.rename_lam, Term.rename_app, Term.rename_and, Term.rename_or,
      Term.rename_not, Term.rename_eq, Term.rename_all, goodFull_rename,
      agree_rename, Term.rename_var, v0, v1, v2, Ren.lift] using hSep
  have h₁ : Derives Ax Ξ (forall' (σ := ρ)
      (iff (eq' X.weaken v0) (forall' (σ := Observer)
        (imp (goodFull S v0) (agree ρ v0 X.weaken.weaken v1))))) := by
    simpa [Term.instantiate, forall', iff, imp, conj, disj, neg, eq',
      goodFull_subst, agree_subst, subst_weaken_lift, Sub.lift,
      Ren.shift, v0, v1, v2]
      using Derives.allEβ h₀ X
  have h₂ := Derives.allEβ h₁ Y
  simp only [Term.instantiate, forall', iff, imp, conj, disj, neg, eq',
    Term.subst_lam, Term.subst_app, goodFull_subst, agree_subst,
    subst_weaken_lift] at h₂
  simpa [Term.instantiate, Term.subst_rename, Term.subst_id, forall',
    iff, imp, conj, disj, neg, eq', goodFull_subst, agree_subst,
    Sub.lift] using h₂

/-- The generic separation elimination API keeps its exact sentence premise. -/
theorem separate {Ax : Axioms Sig} {Ξ : List (Formula Sig Γ)}
    (ρ : RTy) (S : List Ty) (X Y : Term Sig Γ ρ)
    (hSep : Derives Ax Ξ (separation (Sig := Sig) ρ S).close)
    (hAgree : Derives Ax Ξ (forall' (σ := Observer)
      (imp (goodFull S v0) (agree ρ v0 X.weaken Y.weaken)))) :
    Derives Ax Ξ (eq' X Y) :=
  .iffE₂ (separation_instance ρ S X Y hSep) hAgree

theorem separate_os {Ξ : List (Formula Sig Γ)}
    (ρ : RTy) (S : List Ty) (hρ : ρ.Closed) (hS : Ty.AllClosed S)
    (X Y : Term Sig Γ ρ)
    (hAgree : Derives OSAx Ξ (forall' (σ := Observer)
      (imp (goodFull S v0) (agree ρ v0 X.weaken Y.weaken)))) :
    Derives OSAx Ξ (eq' X Y) :=
  separate ρ S X Y (separation_axiom ρ S hρ hS) hAgree

theorem boolFull_imp_eq {Ax : Axioms Sig} {Ξ : List (Formula Sig Γ)}
    {E : Term Sig Γ Observer} (hb : Derives Ax Ξ (boolFull E))
    (p q : Formula Sig Γ) :
    Derives Ax Ξ (eq' (.app E (imp p q)) (imp (.app E p) (.app E q))) := by
  have hn := Derives.eqCongrβ (disj v0 (Term.app E q).weaken) (boolFull_neg_eq hb p)
  have hn' : Derives Ax Ξ (eq'
      (disj (.app E (neg p)) (.app E q))
      (disj (neg (.app E p)) (.app E q))) := by
    simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using hn
  exact .eqTrans (boolFull_disj_eq hb (neg p) q) hn'

theorem boolFull_iff_eq {Ax : Axioms Sig} {Ξ : List (Formula Sig Γ)}
    {E : Term Sig Γ Observer} (hb : Derives Ax Ξ (boolFull E))
    (p q : Formula Sig Γ) :
    Derives Ax Ξ (eq' (.app E (iff p q)) (iff (.app E p) (.app E q))) := by
  have h₁ := Derives.eqCongrβ
    (conj v0 (Term.app E (imp q p)).weaken) (boolFull_imp_eq hb p q)
  have h₁' : Derives Ax Ξ (eq'
      (conj (.app E (imp p q)) (.app E (imp q p)))
      (conj (imp (.app E p) (.app E q)) (.app E (imp q p)))) := by
    simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using h₁
  have h₂ := Derives.eqCongrβ
    (conj (imp (.app E p) (.app E q)).weaken v0) (boolFull_imp_eq hb q p)
  have h₂' : Derives Ax Ξ (eq'
      (conj (imp (.app E p) (.app E q)) (.app E (imp q p)))
      (iff (.app E p) (.app E q))) := by
    simpa [Term.instantiate, Term.subst_rename, Term.subst_id, iff] using h₂
  exact .eqTrans (boolFull_conj_eq hb (imp p q) (imp q p)) (.eqTrans h₁' h₂')

/-- Removing a fresh universal binder after weakening a derived universal. -/
theorem all_body_noAx {σ : Ty} {Ξ : List (Formula Sig Γ)}
    {b : Formula Sig (σ :: Γ)}
    (h : Derives (NoAxioms Sig) Ξ (forall' b)) :
    Derives (NoAxioms Sig) (Hyps.weaken Ξ) b := by
  have hr : Derives (NoAxioms Sig) (Hyps.weaken Ξ)
      (forall' (b.rename (Ren.lift (Ren.shift (σ := σ))))) := by
    simpa only [Hyps.rename, Hyps.weaken, forall', Term.rename_app,
      Term.rename_all, Term.rename_lam] using
      Derives.rename_noAx (Ren.shift (σ := σ)) h
  have hi := Derives.allEβ hr (v0 (σ := σ))
  simpa only [instantiate_fresh] using hi

/-- Full quantifier identities peel each argument binder; full Boolean identities
handle the final biconditional. Every step is a derivation in unextended H. -/
theorem agree_of_observed (ρ : RTy) (S : List Ty)
    (hargs : ρ.args ⊆ S) {Ξ : List (Formula Sig Γ)}
    (E : Term Sig Γ Observer) (X Y : Term Sig Γ ρ)
    (hg : Derives (NoAxioms Sig) Ξ (goodFull S E))
    (hc : Derives (NoAxioms Sig) Ξ (.app E (coext₀ ρ X Y))) :
    Derives (NoAxioms Sig) Ξ (agree ρ E X Y) := by
  induction ρ using RTy.induction generalizing Γ with
  | t => exact .eqMp (boolFull_iff_eq (goodFull_bool hg) X Y) hc
  | arr σ ρ ih =>
      let b : Formula Sig (σ :: Γ) :=
        coext₀ ρ (.app X.weaken v0) (.app Y.weaken v0)
      have hσ : σ ∈ S := hargs (List.mem_cons_self ..)
      have hq : Derives (NoAxioms Sig) Ξ
          (forall' (.app E.weaken b)) :=
        .conv (.eqMp (quantifierFull_all_eq (goodFull_quantifier hσ hg) (.lam b)) hc)
          (Conv.app_congr (Conv.refl _) (observedPredicate_lam E b))
      have hg' : Derives (NoAxioms Sig) (Hyps.weaken (σ := σ) Ξ)
          (goodFull S E.weaken) := by
        simpa [Hyps.rename, Hyps.weaken, goodFull_rename] using
          Derives.rename_noAx (Ren.shift (σ := σ)) hg
      exact .allI (ih (fun υ hυ => hargs (List.mem_cons_of_mem _ hυ))
        E.weaken (.app X.weaken v0) (.app Y.weaken v0) hg' (all_body_noAx hq))

/-- Transport is instantiated with the actual qualification laws proved in HBridge.
The witness observer is a new variable; its scope is discharged by allI. -/
theorem supported_agreement (ρ : RTy) (S : List Ty)
    (hargs : ρ.args ⊆ S) (X Y : Term Sig Γ ρ)
    (h : Supported S [] (coext₀ ρ X Y)) :
    Derives (NoAxioms Sig) [] (forall' (σ := Observer)
      (imp (goodFull S v0) (agree ρ v0 X.weaken Y.weaken))) := by
  apply Derives.allI
  apply Derives.impI
  have hs := Supported.rename (Ren.shift (σ := Observer)) h
  have hs' : Supported S (Γ := Ty.rel Observer :: Γ) []
      (coext₀ ρ X.weaken Y.weaken) := by
    simpa [Hyps.rename, coext₀_rename] using hs
  have ht := (fullTransportLaws (NoAxioms Sig) S).transport hs' (v0 (σ := Observer))
  have ht' : Derives (NoAxioms Sig) [goodFull S v0]
      (.app v0 (coext₀ ρ X.weaken Y.weaken)) := by
    simpa [TransportLaws.context, observedHyps, fullTransportLaws] using ht
  exact agree_of_observed ρ S hargs v0 X.weaken Y.weaken .hyp₀ ht'

/-- H derivations with finite closed rule support. Only the forgetful direction
to unrestricted H is established here; a general fixed-language H-to-ClosedH
bridge is not part of this file. -/
def ClosedH (p : Formula Sig Γ) : Prop :=
  ∃ S : List Ty, Ty.AllClosed S ∧ Supported S [] p

theorem ClosedH.forget {p : Formula Sig Γ} (h : ClosedH p) :
    Derives (NoAxioms Sig) [] p :=
  h.elim (fun _ hs => hs.2.forget)

/-- Each coextension theorem supplied with finite closed rule support produces
literal relation identity from OS, at every relational arity including zero. -/
theorem logical_equivalence (ρ : RTy) (hρ : ρ.Closed)
    (X Y : Term Sig Γ ρ) (h : ClosedH (coext₀ ρ X Y)) :
    Derives OSAx [] (eq' X Y) := by
  obtain ⟨S, hS, hs⟩ := h
  have hc : Ty.AllClosed (S ++ ρ.args) := by
    intro σ hσ
    exact (List.mem_append.1 hσ).elim (hS σ) (RTy.closed_args hρ σ)
  apply separate_os ρ (S ++ ρ.args) hρ hc X Y
  exact Derives.monoAx (fun {_} {_} hf => False.elim hf)
    (supported_agreement ρ (S ++ ρ.args)
      (fun _ hσ => List.mem_append_right _ hσ) X Y
      (hs.mono (fun _ hσ => List.mem_append_left _ hσ)))

/-- The Logical-Equivalence identities licensed by ClosedH, as contextual axioms. -/
def HLogicalEquivalence : Axioms Sig := fun {Γ} p =>
  ∃ ρ : RTy, ∃ X Y : Term Sig Γ ρ,
    ρ.Closed ∧ ClosedH (coext₀ ρ X Y) ∧ p = eq' X Y

/-- The independent presentation H plus ClosedH-licensed Logical Equivalence. -/
abbrev CFromH {Γ : Ctx} (Ξ : List (Formula Sig Γ)) (p : Formula Sig Γ) : Prop :=
  Derives HLogicalEquivalence Ξ p

private theorem replace_axioms {A B : Axioms Sig}
    (hAB : ∀ {Γ : Ctx} {p : Formula Sig Γ}, A p → Derives B [] p) :
    ∀ {Γ : Ctx} {Ξ : List (Formula Sig Γ)} {p : Formula Sig Γ},
      Derives A Ξ p → Derives B Ξ p
  | _, _, _, .hyp h => .hyp h
  | _, _, _, .ax h => (hAB h).weaken (fun _ hf => nomatch hf)
  | _, _, _, .existence => .existence
  | _, _, _, .andI h k => .andI (replace_axioms hAB h) (replace_axioms hAB k)
  | _, _, _, .andE₁ h => .andE₁ (replace_axioms hAB h)
  | _, _, _, .andE₂ h => .andE₂ (replace_axioms hAB h)
  | _, _, _, .orI₁ h => .orI₁ (replace_axioms hAB h)
  | _, _, _, .orI₂ h => .orI₂ (replace_axioms hAB h)
  | _, _, _, .orE h k l =>
      .orE (replace_axioms hAB h) (replace_axioms hAB k) (replace_axioms hAB l)
  | _, _, _, .notI h k => .notI (replace_axioms hAB h) (replace_axioms hAB k)
  | _, _, _, .notE h k => .notE (replace_axioms hAB h) (replace_axioms hAB k)
  | _, _, _, .em p => .em p
  | _, _, _, .allE h a => .allE (replace_axioms hAB h) a
  | _, _, _, .allI h => .allI (replace_axioms hAB h)
  | _, _, _, .exI a h => .exI a (replace_axioms hAB h)
  | _, _, _, .exE h k => .exE (replace_axioms hAB h) (replace_axioms hAB k)
  | _, _, _, .refl a => .refl a
  | _, _, _, .ll F h k => .ll F (replace_axioms hAB h) (replace_axioms hAB k)
  | _, _, _, .conv h c => .conv (replace_axioms hAB h) c

/-- Every theorem of this H-plus-ClosedH-Equivalence presentation follows from
H plus full typed logical separation. No pre-existing C proof is assumed. -/
theorem classicism_from_full_separation {Ξ : List (Formula Sig Γ)} {p : Formula Sig Γ}
    (h : CFromH Ξ p) : Derives OSAx Ξ p := by
  apply replace_axioms (B := OSAx) (hAB := ?_) h
  intro Θ q hq
  obtain ⟨ρ, X, Y, hρ, hh, rfl⟩ := hq
  exact logical_equivalence ρ hρ X Y hh

end Classicism.Meta.Research.FullTypedLogicalSeparation

#print axioms Classicism.Meta.Research.FullTypedLogicalSeparation.supported_agreement
#print axioms Classicism.Meta.Research.FullTypedLogicalSeparation.logical_equivalence
#print axioms Classicism.Meta.Research.FullTypedLogicalSeparation.classicism_from_full_separation

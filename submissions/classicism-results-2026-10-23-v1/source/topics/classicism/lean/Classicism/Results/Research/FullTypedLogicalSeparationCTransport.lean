import Classicism.Results.Research.FullTypedLogicalSeparationCSupport
import Classicism.Results.Research.FullTypedLogicalSeparationIdentity

/-!
# Observer transport through the actual recursive C rules

Original proof, misc, 23 October 2026, unpaginated; extension of the ordinary
observer proof in h-logical-observer-strengthening.txt, sections 2--3.

The target is the independent H calculus with the actual full typed OS
sentences. The source includes recursive Subst. The induction is uniform
in renaming, so its logical-premise instances can use a fresh observer.
Those instances yield an unconditional identity by separation. Derived
Functionality lifts it through the hole, including binders, and H identity
substitution transfers the observed main premise. No local premise or OS
axiom is necessitated or assumed preserved by an observer.
-/

namespace Classicism.Meta.Research.FullTypedLogicalSeparation
open Term Classicism.Research.FullTypedLogicalSeparationH

variable {Sig : Signature}

/-- Uniformity under variable renaming is part of the induction invariant,
not a call of the induction hypothesis on a newly constructed proof. -/
def UniformObserverTransport (S : List Ty) {Γ : Ctx}
    (Δ : List (Formula Sig Γ)) (p : Formula Sig Γ) : Prop :=
  ∀ {Θ : Ctx} (r : Ren Γ Θ) (E : Term Sig Θ Observer),
    Derives OSAx ((fullTransportLaws OSAx S).context E (Hyps.rename r Δ))
      (observe E (p.rename r))

/-- Two transported logical implications identify their endpoints. The
qualification is discharged before this identity is used elsewhere. -/
theorem identity_of_uniform_transport {S : List Ty} (hS : Ty.AllClosed S)
    {Γ Θ : Ctx} {P Q : Formula Sig Γ}
    (hPQ : UniformObserverTransport S [P] Q)
    (hQP : UniformObserverTransport S [Q] P) (r : Ren Γ Θ) :
    Derives OSAx [] (eq' (P.rename r) (Q.rename r)) := by
  apply separate_os .t S trivial hS (P.rename r) (Q.rename r)
  apply Derives.allI
  apply Derives.impI
  have h₁ := Derives.swap (hPQ (Ren.comp (Ren.shift (σ := Observer)) r) v0)
  have h₂ := Derives.swap (hQP (Ren.comp (Ren.shift (σ := Observer)) r) v0)
  apply Derives.iffI
  · simpa only [TransportLaws.context, observedHyps, Hyps.rename, List.map_cons,
      List.map_nil, fullTransportLaws, observe, Term.weaken, Term.rename_rename]
      using h₁
  · simpa only [TransportLaws.context, observedHyps, Hyps.rename, List.map_cons,
      List.map_nil, fullTransportLaws, observe, Term.weaken, Term.rename_rename]
      using h₂

/-- Every supported C derivation is transported, including all recursive
premises of Subst. Closedness is used only for actual OS instances and the
Functionality instances in its hole-congruence step. -/
theorem c_transport {S : List Ty} (hS : Ty.AllClosed S) :
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ},
      CSupported S Δ p → UniformObserverTransport S Δ p
  | _, _, _, .hyp h, _, r, E =>
      .hyp (List.mem_cons_of_mem _
        (List.mem_map.2 ⟨_, List.mem_map.2 ⟨_, h, rfl⟩, rfl⟩))
  | _, Δ, _, .existence hσ, _, r, E => by
      exact (fullTransportLaws OSAx S).transport
        (Supported.existence (Δ := Hyps.rename r Δ) hσ) E
  | _, Δ, _, .andI (p := p) (q := q) h k, _, r, E =>
      .iffE₂ ((fullTransportLaws OSAx S).liftLaw
        ((fullTransportLaws OSAx S).andLaw E (p.rename r) (q.rename r)) (Hyps.rename r Δ))
        (.andI (c_transport hS h r E) (c_transport hS k r E))
  | _, Δ, _, .andE₁ (p := p) (q := q) h, _, r, E =>
      .andE₁ (.iffE₁ ((fullTransportLaws OSAx S).liftLaw
        ((fullTransportLaws OSAx S).andLaw E (p.rename r) (q.rename r)) (Hyps.rename r Δ))
        (c_transport hS h r E))
  | _, Δ, _, .andE₂ (p := p) (q := q) h, _, r, E =>
      .andE₂ (.iffE₁ ((fullTransportLaws OSAx S).liftLaw
        ((fullTransportLaws OSAx S).andLaw E (p.rename r) (q.rename r)) (Hyps.rename r Δ))
        (c_transport hS h r E))
  | _, Δ, _, .orI₁ (p := p) (q := q) h, _, r, E =>
      .iffE₂ ((fullTransportLaws OSAx S).liftLaw
        ((fullTransportLaws OSAx S).orLaw E (p.rename r) (q.rename r)) (Hyps.rename r Δ))
        (.orI₁ (c_transport hS h r E))
  | _, Δ, _, .orI₂ (p := p) (q := q) h, _, r, E =>
      .iffE₂ ((fullTransportLaws OSAx S).liftLaw
        ((fullTransportLaws OSAx S).orLaw E (p.rename r) (q.rename r)) (Hyps.rename r Δ))
        (.orI₂ (c_transport hS h r E))
  | _, Δ, _, .orE (p := p) (q := q) h k l, _, r, E =>
      .orE (.iffE₁ ((fullTransportLaws OSAx S).liftLaw
        ((fullTransportLaws OSAx S).orLaw E (p.rename r) (q.rename r)) (Hyps.rename r Δ))
        (c_transport hS h r E))
        (Derives.swap (c_transport hS k r E)) (Derives.swap (c_transport hS l r E))
  | _, Δ, _, .notI (p := p) (q := q) h k, _, r, E => by
      let K := fullTransportLaws (Sig := Sig) OSAx S
      apply Derives.iffE₂ (K.liftLaw (K.notLaw E (p.rename r)) (Hyps.rename r Δ))
      exact .notI (Derives.swap (c_transport hS h r E))
        (.iffE₁ (Derives.weaken₁ (K.liftLaw (K.notLaw E (q.rename r)) (Hyps.rename r Δ)))
          (Derives.swap (c_transport hS k r E)))
  | _, Δ, _, .notE (p := p) h k, _, r, E =>
      .notE (c_transport hS h r E)
        (.iffE₁ ((fullTransportLaws OSAx S).liftLaw
          ((fullTransportLaws OSAx S).notLaw E (p.rename r)) (Hyps.rename r Δ))
          (c_transport hS k r E))
  | _, Δ, _, .em p, _, r, E => by
      let K := fullTransportLaws (Sig := Sig) OSAx S
      apply Derives.iffE₂
        (K.liftLaw (K.orLaw E (p.rename r) (Term.neg (p.rename r))) (Hyps.rename r Δ))
      exact .orE (.em (observe E (p.rename r))) (.orI₁ .hyp₀)
        (.orI₂ (.iffE₂ (Derives.weaken₁
          (K.liftLaw (K.notLaw E (p.rename r)) (Hyps.rename r Δ))) .hyp₀))
  | _, Δ, _, .allE (F := F) hσ h a, _, r, E =>
      .conv (.allE (.iffE₁ ((fullTransportLaws OSAx S).liftLaw
        ((fullTransportLaws OSAx S).allLaw hσ E (F.rename r)) (Hyps.rename r Δ))
        (c_transport hS h r E)) (a.rename r))
        (observedPredicate_beta E (F.rename r) (a.rename r))
  | _, Δ, _, .allI (b := b) hσ h, _, r, E => by
      let K := fullTransportLaws (Sig := Sig) OSAx S
      have hb : Derives OSAx (Hyps.weaken (K.context E (Hyps.rename r Δ)))
          (observe E.weaken (b.rename (Ren.lift r))) := by
        simpa only [← Hyps.weaken_rename, TransportLaws.context_weaken] using
          c_transport hS h (Ren.lift r) E.weaken
      apply Derives.iffE₂
        (K.liftLaw (K.allLaw hσ E (.lam (b.rename (Ren.lift r)))) (Hyps.rename r Δ))
      exact .conv (.allI hb) (Conv.app_congr (Conv.refl _)
        (Conv.symm (observedPredicate_lam E (b.rename (Ren.lift r)))))
  | _, Δ, _, .exI (F := F) hσ a h, _, r, E =>
      .iffE₂ ((fullTransportLaws OSAx S).liftLaw
        ((fullTransportLaws OSAx S).exLaw hσ E (F.rename r)) (Hyps.rename r Δ))
        (.exI (a.rename r) (.conv (c_transport hS h r E)
          (Conv.symm (observedPredicate_beta E (F.rename r) (a.rename r)))))
  | _, Δ, _, .exE (σ := σ) (F := F) (r := q) hσ h k, _, r, E => by
      let K := fullTransportLaws (Sig := Sig) OSAx S
      apply Derives.exE (.iffE₁
        (K.liftLaw (K.exLaw hσ E (F.rename r)) (Hyps.rename r Δ)) (c_transport hS h r E))
      have hk := Derives.swap (c_transport hS k (Ren.lift r) E.weaken)
      have hk' : Derives OSAx
          (observe E.weaken (.app (F.rename r).weaken Term.v0) ::
            Hyps.weaken (K.context E (Hyps.rename r Δ)))
          (observe E (q.rename r)).weaken := by
        simpa only [K, Hyps.rename, List.map_cons, Term.rename_app, ← Term.weaken_rename,
          Term.rename_var, Ren.lift, TransportLaws.context, observedHyps,
          (fullTransportLaws OSAx S).qualification_weaken,
          Hyps.weaken, List.map_map, Function.comp_def, observe_weaken] using hk
      apply hk'.convertHyps
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · refine ⟨Term.app (observedPredicate E (F.rename r)).weaken Term.v0,
          List.mem_cons_self .., ?_⟩
        have hn : (observedPredicate E (F.rename r)).weaken (τ := σ) =
            observedPredicate (E.weaken (τ := σ)) ((F.rename r).weaken (τ := σ)) := by
          change (observedPredicate E (F.rename r)).rename Ren.shift = _
          simp only [observedPredicate, Term.rename_lam, Term.rename_app,
            ← Term.weaken_rename]
          rfl
        rw [hn]
        exact observedPredicate_beta E.weaken (F.rename r).weaken Term.v0
      · exact ⟨p, List.mem_cons_of_mem _ hp, Conv.refl _⟩
  | _, Δ, _, .refl hσ a, _, r, E =>
      (fullTransportLaws OSAx S).liftLaw
        ((fullTransportLaws OSAx S).refLaw hσ E (a.rename r)) (Hyps.rename r Δ)
  | _, Δ, _, .ll (a := a) (b := b) hσ F h k, _, r, E =>
      .impE (.impE ((fullTransportLaws OSAx S).liftLaw
        ((fullTransportLaws OSAx S).leibnizLaw hσ E (a.rename r) (b.rename r) (F.rename r))
        (Hyps.rename r Δ)) (c_transport hS h r E)) (c_transport hS k r E)
  | _, _, _, .conv h c, _, r, E =>
      .conv (c_transport hS h r E) (Conv.app_congr (Conv.refl _) (Conv.rename r c))
  | _, Δ, _, .subst (P := P) (Q := Q) C _ht hC h₁ h₂ h₃, _, r, E => by
      have hid := identity_of_uniform_transport hS
        (c_transport hS h₁) (c_transport hS h₂) (C.rename r).ren
      have hc : Ty.AllClosed (holeTypes (C.rename r).hole) := by
        rw [holeTypes_rename]
        exact fun σ hσ => hS σ (hC hσ)
      have hhole := hole_congruence_os (C.rename r).hole hc hid
      have hhole' : Derives OSAx []
          (eq' ((C.plug P).rename r) ((C.plug Q).rename r)) := by
        simpa only [Hole.plug_rename] using hhole
      exact .eqMp
        (.eqCongr E (hhole'.weaken (by intro p hp; exact nomatch hp)))
        (c_transport hS h₃ r E)

/-- Eliminating the observed qualification at the identity observer recovers
the original local hypotheses as well as the original conclusion. -/
theorem supported_c_sequent {S : List Ty} (hS : Ty.AllClosed S)
    {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ}
    (h : CSupported S Δ p) : Derives OSAx Δ p := by
  have ht := c_transport hS h Ren.id (identityObserver (Sig := Sig) (Γ := Γ))
  have hΔ : ∀ Δ' : List (Formula Sig Γ), Hyps.rename Ren.id Δ' = Δ' := by
    intro Δ'
    induction Δ' with
    | nil => rfl
    | cons q Δ ih =>
        change q.rename Ren.id :: Hyps.rename Ren.id Δ = q :: Δ
        rw [Term.rename_id, ih]
  have ht' : Derives OSAx (goodFull S identityObserver :: observedHyps identityObserver Δ)
      (observe identityObserver p) := by
    simpa only [TransportLaws.context, fullTransportLaws, hΔ, Term.rename_id] using ht
  have ht'' : Derives OSAx (goodFull S identityObserver :: Δ)
      (observe identityObserver p) := by
    apply ht'.convertHyps
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact ⟨_, List.mem_cons_self .., Conv.refl _⟩
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hq
      exact ⟨a, List.mem_cons_of_mem _ ha, Conv.symm (identity_observe a)⟩
  exact .conv (.impE (.impI ht'') (identity_goodFull S)) (identity_observe p)

/-- The empty-local-hypothesis specialization. -/
theorem supported_c_theorem {S : List Ty} (hS : Ty.AllClosed S)
    {Γ : Ctx} {p : Formula Sig Γ} (h : CSupported S [] p) :
    Derives OSAx [] p := supported_c_sequent hS h

end Classicism.Meta.Research.FullTypedLogicalSeparation

#print axioms Classicism.Meta.Research.FullTypedLogicalSeparation.c_transport
#print axioms Classicism.Meta.Research.FullTypedLogicalSeparation.supported_c_sequent
#print axioms Classicism.Meta.Research.FullTypedLogicalSeparation.supported_c_theorem

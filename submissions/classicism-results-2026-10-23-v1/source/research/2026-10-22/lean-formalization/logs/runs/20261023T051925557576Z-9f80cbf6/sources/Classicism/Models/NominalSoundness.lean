import Classicism.Models.NominalConversion

/-!
# Soundness of C in the supported-world hierarchy

Proper axioms are required only at the selected world. The logical-only side
derivations in Subst are evaluated at EVERY world, using the logical Existence
axiom there; this proves equality of their complete supported propositions.
That equality can then be transported through the actual typed hole.

No IC, FC, RC, Atomicity, C5, regular cardinal bound, or orbit assumption is
used. Source: nominal-choice-classification-20261022.md §2, original local
research, unpaginated, misc. New proof candidate, not compiler-verified.
-/

namespace Classicism.Meta.Nominal.Hierarchy
noncomputable section
variable {G : Type} [Group G] {A : Action G} {I : SupportIdeal A}
variable (W : Nom A I) {Sig : Signature} (C : FixedConstants W Sig)

def HypsAt {Γ} (η : env W Γ) (w : W) (Δ : List (Formula Sig Γ)) : Prop :=
  ∀ p ∈ Δ, Holds W C η w p

def AxiomsAt (w : W) (Ax : AxiomSet Sig) : Prop :=
  ∀ a, Ax a → Holds W C () w a

theorem logical_valid (w : W) : AxiomsAt W C w Logical := by
  intro a ha
  subst a
  exact ⟨0, rfl⟩

theorem hyps_weaken {Γ σ} (η : env W Γ) (w : W) (x : dom W σ)
    {Δ : List (Formula Sig Γ)} (h : HypsAt W C η w Δ) :
    HypsAt W C (x, η) w (Hyps.weaken Δ) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  change ((denote W C q.weaken).fn (x, η)).val w
  rw [denote_weaken]
  exact h q hq

/-- Local-world soundness, with globally logical Subst side premises. -/
theorem sound : ∀ {Ax : AxiomSet Sig} {Γ} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ},
    Derivable Ax Δ p → ∀ (η : env W Γ) (w : W),
      AxiomsAt W C w Ax → HypsAt W C η w Δ → Holds W C η w p
  | _, _, _, _, .hyp h, _, _, _, hΔ => hΔ _ h
  | _, _, _, _, .ax h, η, w, hAx, _ => by
    change ((denote W C _).fn η).val w
    rw [denote_close]
    exact hAx _ h
  | _, _, _, _, .andI h₁ h₂, η, w, hAx, hΔ =>
    ⟨sound h₁ η w hAx hΔ, sound h₂ η w hAx hΔ⟩
  | _, _, _, _, .andE₁ h, η, w, hAx, hΔ => (sound h η w hAx hΔ).1
  | _, _, _, _, .andE₂ h, η, w, hAx, hΔ => (sound h η w hAx hΔ).2
  | _, _, _, _, .orI₁ h, η, w, hAx, hΔ => Or.inl (sound h η w hAx hΔ)
  | _, _, _, _, .orI₂ h, η, w, hAx, hΔ => Or.inr (sound h η w hAx hΔ)
  | _, _, _, _, .orE h h₁ h₂, η, w, hAx, hΔ =>
    (sound h η w hAx hΔ).elim
      (fun hp => sound h₁ η w hAx (fun q hq => by
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hp
        · exact hΔ q hq))
      (fun hp => sound h₂ η w hAx (fun q hq => by
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hp
        · exact hΔ q hq))
  | _, _, _, _, .notI h₁ h₂, η, w, hAx, hΔ => fun hp =>
    have hΔ' : HypsAt W C η w (_ :: _) := fun q hq => by
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hp
      · exact hΔ q hq
    sound h₂ η w hAx hΔ' (sound h₁ η w hAx hΔ')
  | _, _, _, _, .notE h₁ h₂, η, w, hAx, hΔ =>
    False.elim (sound h₂ η w hAx hΔ (sound h₁ η w hAx hΔ))
  | _, _, _, _, .em p, η, w, _, _ => Classical.em (Holds W C η w p)
  | _, _, _, _, .allE h a, η, w, hAx, hΔ => sound h η w hAx hΔ ((denote W C a).fn η)
  | _, _, _, _, .allI h, η, w, hAx, hΔ =>
    fun x => sound h (x, η) w hAx (hyps_weaken W C η w x hΔ)
  | _, _, _, _, .exI a h, η, w, hAx, hΔ => ⟨(denote W C a).fn η, sound h η w hAx hΔ⟩
  | _, _, _, _, .exE (F := F) (r := r) h h', η, w, hAx, hΔ => by
    obtain ⟨x, hx⟩ := sound h η w hAx hΔ
    have hr := sound h' (x, η) w hAx (fun q hq => by
      rcases List.mem_cons.1 hq with rfl | hq
      · change (((denote W C F.weaken).fn (x, η)).val x).val w
        rw [denote_weaken]
        exact hx
      · exact hyps_weaken W C η w x hΔ q hq)
    change ((denote W C r.weaken).fn (x, η)).val w at hr
    rw [denote_weaken] at hr
    exact hr
  | _, _, _, _, .refl _, _, _, _, _ => rfl
  | _, _, _, _, .ll (a := a) (b := b) F h₁ h₂, η, w, hAx, hΔ => by
    have e : (denote W C a).fn η = (denote W C b).fn η := sound h₁ η w hAx hΔ
    have h := sound h₂ η w hAx hΔ
    change (((denote W C F).fn η).val ((denote W C b).fn η)).val w
    rw [← e]
    exact h
  | _, _, _, _, .conv h c, η, w, hAx, hΔ => by
    change ((denote W C _).fn η).val w
    rw [← conv_denote W C c η]
    exact sound h η w hAx hΔ
  | Ax, _, _, _, .subst (P := P) (Q := Q) K h₁ h₂ h₃, η, w, hAx, hΔ => by
    have hL : ∀ v : W, AxiomsAt W C v Ax.logical :=
      fun v a ha => logical_valid W C v a ha.2
    have e : ∀ θ, (denote W C P).fn θ = (denote W C Q).fn θ := by
      intro θ
      apply Subtype.ext
      funext v
      apply propext
      exact ⟨fun hp => sound h₁ θ v (hL v) (fun q hq => by
          rw [List.mem_singleton.1 hq]; exact hp),
        fun hq => sound h₂ θ v (hL v) (fun p hp => by
          rw [List.mem_singleton.1 hp]; exact hq)⟩
    change ((denote W C (K.plug Q)).fn η).val w
    rw [← hole_denote W C K e η]
    exact sound h₃ η w hAx hΔ

theorem theorem_at {Ax : AxiomSet Sig} {p : Sentence Sig} (h : Theorem Ax p)
    (w : W) (hAx : AxiomsAt W C w Ax) : Holds W C () w p :=
  sound W C h () w hAx (fun _ h => nomatch h)

/-- A nonempty world domain gives a consistency witness for the logical calculus. -/
theorem logical_consistent (w : W) : ¬Theorem (Logical : AxiomSet Sig) Term.bot := by
  intro h
  have hb := theorem_at W C h w (logical_valid W C w)
  change ((denote W C Term.bot).fn ()).val w at hb
  rw [denote_bot] at hb
  exact hb

end
end Classicism.Meta.Nominal.Hierarchy

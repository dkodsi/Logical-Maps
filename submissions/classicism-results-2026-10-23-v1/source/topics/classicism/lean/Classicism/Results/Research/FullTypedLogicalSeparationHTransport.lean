import Classicism.Results.Research.FullTypedLogicalSeparationHSupport

/-!
# H observer transport, with the qualification kept local

Original proof, misc, 23 October 2026, unpaginated; ordinary observer note §2.
The target relation is the independent Subst-free H calculus. The source
proof has a finite support S. No C derivation or equivalence-to-identity rule
is used. An observer may be any term in the current context; under an
object binder it is weakened, so no eigenvariable can enter it by capture.
-/
namespace Classicism.Research.FullTypedLogicalSeparationH
open Classicism.Meta
variable {Sig : Signature}

abbrev observe {Γ : Ctx} (E : Term Sig Γ (Ty.t ⇒ RTy.t))
    (p : Formula Sig Γ) : Formula Sig Γ := .app E p

@[simp] theorem observe_weaken {Γ : Ctx} {σ : Ty}
    (E : Term Sig Γ (Ty.t ⇒ RTy.t)) (p : Formula Sig Γ) :
    (observe E p).weaken (τ := σ) = observe E.weaken p.weaken := by
  simp only [observe, Term.weaken, Term.rename_app]

def observedHyps {Γ : Ctx} (E : Term Sig Γ (Ty.t ⇒ RTy.t))
    (Δ : List (Formula Sig Γ)) := Δ.map (observe E)

/-- The observed predicate, with its quantified variable fresh for E. -/
abbrev observedPredicate {Γ : Ctx} {σ : Ty} (E : Term Sig Γ (Ty.t ⇒ RTy.t))
    (F : Term Sig Γ (σ ⇒ RTy.t)) : Term Sig Γ (σ ⇒ RTy.t) :=
  .lam (observe E.weaken (.app F.weaken Term.v0))

/-- Elementary qualification consequences, each proved from the LOCAL
qualification hypothesis in H. This is an interface to the full composite
syntax, not an assumption of the transport theorem or of Classicism. -/
structure TransportLaws (Ax : Axioms Sig) (S : List Ty) where
  qualification : ∀ {Γ : Ctx}, Term Sig Γ (Ty.t ⇒ RTy.t) → Formula Sig Γ
  qualification_weaken : ∀ {Γ : Ctx} {σ : Ty} (E : Term Sig Γ (Ty.t ⇒ RTy.t)),
    qualification (E.weaken (τ := σ)) = (qualification E).weaken
  andLaw : ∀ {Γ : Ctx} (E : Term Sig Γ (Ty.t ⇒ RTy.t)) (p q : Formula Sig Γ),
    Derives Ax [qualification E]
      (Term.iff (observe E (Term.conj p q)) (Term.conj (observe E p) (observe E q)))
  orLaw : ∀ {Γ : Ctx} (E : Term Sig Γ (Ty.t ⇒ RTy.t)) (p q : Formula Sig Γ),
    Derives Ax [qualification E]
      (Term.iff (observe E (Term.disj p q)) (Term.disj (observe E p) (observe E q)))
  notLaw : ∀ {Γ : Ctx} (E : Term Sig Γ (Ty.t ⇒ RTy.t)) (p : Formula Sig Γ),
    Derives Ax [qualification E]
      (Term.iff (observe E (Term.neg p)) (Term.neg (observe E p)))
  allLaw : ∀ {Γ : Ctx} {σ : Ty}, σ ∈ S →
    (E : Term Sig Γ (Ty.t ⇒ RTy.t)) → (F : Term Sig Γ (σ ⇒ RTy.t)) →
    Derives Ax [qualification E]
      (Term.iff (observe E (.app (.all σ) F)) (.app (.all σ) (observedPredicate E F)))
  exLaw : ∀ {Γ : Ctx} {σ : Ty}, σ ∈ S →
    (E : Term Sig Γ (Ty.t ⇒ RTy.t)) → (F : Term Sig Γ (σ ⇒ RTy.t)) →
    Derives Ax [qualification E]
      (Term.iff (observe E (.app (.ex σ) F)) (.app (.ex σ) (observedPredicate E F)))
  refLaw : ∀ {Γ : Ctx} {σ : Ty}, σ ∈ S →
    (E : Term Sig Γ (Ty.t ⇒ RTy.t)) → (a : Term Sig Γ σ) →
    Derives Ax [qualification E] (observe E (Term.eq' a a))
  leibnizLaw : ∀ {Γ : Ctx} {σ : Ty}, σ ∈ S →
    (E : Term Sig Γ (Ty.t ⇒ RTy.t)) → (a b : Term Sig Γ σ) →
    (F : Term Sig Γ (σ ⇒ RTy.t)) →
    Derives Ax [qualification E]
      (Term.imp (observe E (Term.eq' a b))
        (Term.imp (observe E (.app F a)) (observe E (.app F b))))


/-- Pointwise conversion of hypotheses; unlike a cut rule this needs no
stability condition on the context-indexed proper axioms. -/
def ConvertsHyps {Γ : Ctx} (Δ Δ' : List (Formula Sig Γ)) : Prop :=
  ∀ p, p ∈ Δ → ∃ q, q ∈ Δ' ∧ q ≡ p

namespace ConvertsHyps

theorem cons {Γ : Ctx} {Δ Δ' : List (Formula Sig Γ)}
    (h : ConvertsHyps Δ Δ') (p : Formula Sig Γ) : ConvertsHyps (p :: Δ) (p :: Δ') := by
  intro q hq
  rcases List.mem_cons.1 hq with rfl | hq
  · exact ⟨q, List.mem_cons_self .., Conv.refl _⟩
  · obtain ⟨r, hr, c⟩ := h q hq
    exact ⟨r, List.mem_cons_of_mem _ hr, c⟩

theorem weaken {Γ : Ctx} {σ : Ty} {Δ Δ' : List (Formula Sig Γ)}
    (h : ConvertsHyps Δ Δ') :
    ConvertsHyps (Hyps.weaken (σ := σ) Δ) (Hyps.weaken Δ') := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  obtain ⟨r, hr, c⟩ := h q hq
  exact ⟨r.weaken, List.mem_map.2 ⟨r, hr, rfl⟩, Conv.rename Ren.shift c⟩

end ConvertsHyps

namespace Derives
variable {Ax : Axioms Sig}

theorem convertHyps : ∀ {Γ : Ctx} {Δ Δ' : List (Formula Sig Γ)} {p : Formula Sig Γ},
    Derives Ax Δ p → ConvertsHyps Δ Δ' → Derives Ax Δ' p
  | _, _, _, _, .hyp h, hc => by
      obtain ⟨q, hq, c⟩ := hc _ h
      exact .conv (.hyp hq) c
  | _, _, _, _, .ax h, _ => .ax h
  | _, _, _, _, .existence, _ => .existence
  | _, _, _, _, .andI h k, hc => .andI (convertHyps h hc) (convertHyps k hc)
  | _, _, _, _, .andE₁ h, hc => .andE₁ (convertHyps h hc)
  | _, _, _, _, .andE₂ h, hc => .andE₂ (convertHyps h hc)
  | _, _, _, _, .orI₁ h, hc => .orI₁ (convertHyps h hc)
  | _, _, _, _, .orI₂ h, hc => .orI₂ (convertHyps h hc)
  | _, _, _, _, .orE h k l, hc =>
      .orE (convertHyps h hc) (convertHyps k (hc.cons _)) (convertHyps l (hc.cons _))
  | _, _, _, _, .notI h k, hc => .notI (convertHyps h (hc.cons _)) (convertHyps k (hc.cons _))
  | _, _, _, _, .notE h k, hc => .notE (convertHyps h hc) (convertHyps k hc)
  | _, _, _, _, .em p, _ => .em p
  | _, _, _, _, .allE h a, hc => .allE (convertHyps h hc) a
  | _, _, _, _, .allI h, hc => .allI (convertHyps h hc.weaken)
  | _, _, _, _, .exI a h, hc => .exI a (convertHyps h hc)
  | _, _, _, _, .exE h k, hc =>
      .exE (convertHyps h hc) (convertHyps k (hc.weaken.cons _))
  | _, _, _, _, .refl a, _ => .refl a
  | _, _, _, _, .ll F h k, hc => .ll F (convertHyps h hc) (convertHyps k hc)
  | _, _, _, _, .conv h c, hc => .conv (convertHyps h hc) c

theorem swap {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q r : Formula Sig Γ}
    (h : Derives Ax (p :: q :: Δ) r) : Derives Ax (q :: p :: Δ) r :=
  h.weaken (by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha))

end Derives

@[simp] theorem observedHyps_weaken {Γ : Ctx} {σ : Ty}
    (E : Term Sig Γ (Ty.t ⇒ RTy.t)) (Δ : List (Formula Sig Γ)) :
    observedHyps (E.weaken (τ := σ)) (Hyps.weaken Δ) =
      Hyps.weaken (observedHyps E Δ) := by
  simp only [observedHyps, Hyps.weaken, List.map_map]
  rfl

theorem observedPredicate_beta {Γ : Ctx} {σ : Ty}
    (E : Term Sig Γ (Ty.t ⇒ RTy.t)) (F : Term Sig Γ (σ ⇒ RTy.t))
    (a : Term Sig Γ σ) :
    Term.app (observedPredicate E F) a ≡ observe E (.app F a) := by
  have h := Conv.beta (observe E.weaken (.app F.weaken Term.v0)) a
  simpa [observe, Term.instantiate, Term.subst_rename, Term.subst_id] using h

/-- This equation is an equation of syntax/substitutions, not Functionality. -/
theorem instantiate_fresh {Γ : Ctx} {σ : Ty} {τ : Ty}
    (b : Term Sig (σ :: Γ) τ) :
    (b.rename (Ren.lift (Ren.shift (σ := σ)))).instantiate Term.v0 = b := by
  simp only [Term.instantiate, Term.subst_rename]
  have hs : Sub.compRen (Sub.cons (Term.v0 : Term Sig (σ :: Γ) σ) Sub.id)
      (Ren.lift (Ren.shift (σ := σ))) = Sub.id := by
    funext υ v
    cases v <;> rfl
  rw [hs, Term.subst_id]

theorem app_lam_fresh {Γ : Ctx} {σ : Ty} {ρ : RTy}
    (b : Term Sig (σ :: Γ) ρ) :
    Term.app (Term.lam b).weaken Term.v0 ≡ b := by
  have h := Conv.beta (b.rename (Ren.lift (Ren.shift (σ := σ)))) Term.v0
  simpa only [Term.weaken, Term.rename_lam, instantiate_fresh] using h

theorem observedPredicate_lam {Γ : Ctx} {σ : Ty}
    (E : Term Sig Γ (Ty.t ⇒ RTy.t)) (b : Formula Sig (σ :: Γ)) :
    observedPredicate E (.lam b) ≡ .lam (observe E.weaken b) :=
  Conv.lam_congr (Conv.app_congr (Conv.refl _) (app_lam_fresh b))

namespace TransportLaws
variable {Ax : Axioms Sig} {S : List Ty}

def context (K : TransportLaws Ax S) {Γ : Ctx}
    (E : Term Sig Γ (Ty.t ⇒ RTy.t)) (Δ : List (Formula Sig Γ)) :=
  K.qualification E :: observedHyps E Δ

@[simp] theorem context_weaken (K : TransportLaws Ax S) {Γ : Ctx} {σ : Ty}
    (E : Term Sig Γ (Ty.t ⇒ RTy.t)) (Δ : List (Formula Sig Γ)) :
    K.context (E.weaken (τ := σ)) (Hyps.weaken Δ) = Hyps.weaken (K.context E Δ) := by
  simp only [context, K.qualification_weaken, observedHyps_weaken, Hyps.weaken, List.map_cons]

theorem liftLaw (K : TransportLaws Ax S) {Γ : Ctx}
    {E : Term Sig Γ (Ty.t ⇒ RTy.t)} {p : Formula Sig Γ}
    (h : Derives Ax [K.qualification E] p) (Δ : List (Formula Sig Γ)) :
    Derives Ax (K.context E Δ) p :=
  h.weaken (by intro q hq; rw [List.mem_singleton.1 hq]; exact List.mem_cons_self ..)

/-- A genuine induction through every H rule. The qualification stays among
local hypotheses throughout, including generalization and existential elimination. -/
theorem transport (K : TransportLaws Ax S) :
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ},
    Supported S Δ p → (E : Term Sig Γ (Ty.t ⇒ RTy.t)) →
    Derives Ax (K.context E Δ) (observe E p)
  | _, _, _, .hyp h, E => .hyp (List.mem_cons_of_mem _ (List.mem_map.2 ⟨_, h, rfl⟩))
  | Γ, Δ, _, .existence hσ, E => by
      have hr : Derives Ax (Hyps.weaken (K.context E Δ))
          (observe E.weaken (Term.eq' (Term.v0 (σ := Ty.e)) Term.v0)) := by
        have h := K.liftLaw (K.refLaw hσ E.weaken (Term.v0 (σ := Ty.e))) (Hyps.weaken Δ)
        simpa only [context_weaken] using h
      have he : Derives Ax (K.context E Δ)
          (Term.exists' (observe E.weaken (Term.eq' (Term.v0 (σ := Ty.e)) Term.v0))) := by
        apply Derives.exE Derives.existence
        apply Derives.exI Term.v0
        exact .conv (Derives.weaken₁ hr) (Conv.symm
          (app_lam_fresh (observe E.weaken (Term.eq' (Term.v0 (σ := Ty.e)) Term.v0))))
      apply Derives.iffE₂ (K.liftLaw (K.exLaw hσ E (.lam (Term.eq' Term.v0 Term.v0))) Δ)
      exact .conv he (Conv.app_congr (Conv.refl _) (Conv.symm
        (observedPredicate_lam E (Term.eq' Term.v0 Term.v0))))
  | _, Δ, _, .andI (p := p) (q := q) h k, E =>
      .iffE₂ (K.liftLaw (K.andLaw E p q) Δ) (.andI (transport K h E) (transport K k E))
  | _, Δ, _, .andE₁ (p := p) (q := q) h, E =>
      .andE₁ (.iffE₁ (K.liftLaw (K.andLaw E p q) Δ) (transport K h E))
  | _, Δ, _, .andE₂ (p := p) (q := q) h, E =>
      .andE₂ (.iffE₁ (K.liftLaw (K.andLaw E p q) Δ) (transport K h E))
  | _, Δ, _, .orI₁ (p := p) (q := q) h, E =>
      .iffE₂ (K.liftLaw (K.orLaw E p q) Δ) (.orI₁ (transport K h E))
  | _, Δ, _, .orI₂ (p := p) (q := q) h, E =>
      .iffE₂ (K.liftLaw (K.orLaw E p q) Δ) (.orI₂ (transport K h E))
  | _, Δ, _, .orE (p := p) (q := q) h k l, E =>
      .orE (.iffE₁ (K.liftLaw (K.orLaw E p q) Δ) (transport K h E))
        (Derives.swap (transport K k E)) (Derives.swap (transport K l E))
  | _, Δ, _, .notI (p := p) (q := q) h k, E => by
      apply Derives.iffE₂ (K.liftLaw (K.notLaw E p) Δ)
      exact .notI (Derives.swap (transport K h E))
        (.iffE₁ (Derives.weaken₁ (K.liftLaw (K.notLaw E q) Δ))
          (Derives.swap (transport K k E)))
  | _, Δ, _, .notE (p := p) h k, E =>
      .notE (transport K h E) (.iffE₁ (K.liftLaw (K.notLaw E p) Δ) (transport K k E))
  | _, Δ, _, .em p, E => by
      apply Derives.iffE₂ (K.liftLaw (K.orLaw E p (Term.neg p)) Δ)
      exact .orE (.em (observe E p)) (.orI₁ .hyp₀)
        (.orI₂ (.iffE₂ (Derives.weaken₁ (K.liftLaw (K.notLaw E p) Δ)) .hyp₀))
  | _, Δ, _, .allE (F := F) hσ h a, E =>
      .conv (.allE (.iffE₁ (K.liftLaw (K.allLaw hσ E F) Δ) (transport K h E)) a)
        (observedPredicate_beta E F a)
  | _, Δ, _, .allI (b := b) hσ h, E => by
      have hb : Derives Ax (Hyps.weaken (K.context E Δ)) (observe E.weaken b) := by
        simpa only [context_weaken] using transport K h E.weaken
      apply Derives.iffE₂ (K.liftLaw (K.allLaw hσ E (.lam b)) Δ)
      exact .conv (.allI hb)
        (Conv.app_congr (Conv.refl _) (Conv.symm (observedPredicate_lam E b)))
  | _, Δ, _, .exI (F := F) hσ a h, E =>
      .iffE₂ (K.liftLaw (K.exLaw hσ E F) Δ)
        (.exI a (.conv (transport K h E) (Conv.symm (observedPredicate_beta E F a))))
  | Γ, Δ, _, .exE (σ := σ) (F := F) (r := r) hσ h k, E => by
      apply Derives.exE (.iffE₁ (K.liftLaw (K.exLaw hσ E F) Δ) (transport K h E))
      have hk := Derives.swap (transport K k E.weaken)
      have hk' : Derives Ax
          (observe E.weaken (.app F.weaken Term.v0) :: Hyps.weaken (K.context E Δ))
          (observe E r).weaken := by
        simpa only [context, observedHyps, List.map_cons, K.qualification_weaken,
          Hyps.weaken, List.map_map, Function.comp_def, observe_weaken] using hk
      apply hk'.convertHyps
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · refine ⟨Term.app (observedPredicate E F).weaken Term.v0, List.mem_cons_self .., ?_⟩
        have hn : (observedPredicate E F).weaken (τ := σ) =
            observedPredicate (E.weaken (τ := σ)) (F.weaken (τ := σ)) := by
          change (observedPredicate E F).rename Ren.shift = _
          simp only [observedPredicate, Term.rename_lam, Term.rename_app,
            ← Term.weaken_rename]
          rfl
        rw [hn]
        exact observedPredicate_beta E.weaken F.weaken Term.v0
      · exact ⟨p, List.mem_cons_of_mem _ hp, Conv.refl _⟩
  | _, Δ, _, .refl hσ a, E => K.liftLaw (K.refLaw hσ E a) Δ
  | _, Δ, _, .ll (a := a) (b := b) hσ F h k, E =>
      .impE (.impE (K.liftLaw (K.leibnizLaw hσ E a b F) Δ) (transport K h E))
        (transport K k E)
  | _, _, _, .conv h c, E =>
      .conv (transport K h E) (Conv.app_congr (Conv.refl _) c)

end TransportLaws

end Classicism.Research.FullTypedLogicalSeparationH

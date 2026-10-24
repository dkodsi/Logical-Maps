import Classicism.Results.Research.FullTypedLogicalSeparationCHoles

/-!
# Finite type support for the actual C derivation relation

Direct source: `research/2026-10-23/operator-characterizations/h-logical-observer-strengthening.txt`,
sections 2--3 (misc, original research, 23 October 2026, unpaginated).

`CSupported` follows `Meta.Derivable` including all three recursive premises of
Subst. It permits only the logical existence axiom. Ordinary quantifier and
equality rules record their types; Subst also records t and the domain/codomain
types needed to pass identities through every abstraction enclosing its hole.
The support list is raw syntax. Closing its type parameters is a separate step.
-/
namespace Classicism.Research.FullTypedLogicalSeparationH
open Classicism.Meta
open Classicism.Meta.Research.FullTypedLogicalSeparation (holeTypes holeTypes_rename)
variable {Sig : Signature}

inductive CSupported (S : List Ty) : ∀ {Γ : Ctx}, List (Formula Sig Γ) → Formula Sig Γ → Prop
  /-- A hypothesis. -/
  | hyp {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ} :
      p ∈ Δ → CSupported S Δ p
  /-- H's sole non-rule logical axiom: existence at e. -/
  | existence {Γ : Ctx} {Δ : List (Formula Sig Γ)} :
      Ty.e ∈ S → CSupported S Δ (Term.exists' (σ := Ty.e) (Term.eq' Term.v0 Term.v0))
  /-- `∧`-introduction. -/
  | andI {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      CSupported S Δ p → CSupported S Δ q → CSupported S Δ (Term.conj p q)
  /-- `∧`-elimination, left. -/
  | andE₁ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      CSupported S Δ (Term.conj p q) → CSupported S Δ p
  /-- `∧`-elimination, right. -/
  | andE₂ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      CSupported S Δ (Term.conj p q) → CSupported S Δ q
  /-- `∨`-introduction, left. -/
  | orI₁ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      CSupported S Δ p → CSupported S Δ (Term.disj p q)
  /-- `∨`-introduction, right. -/
  | orI₂ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      CSupported S Δ q → CSupported S Δ (Term.disj p q)
  /-- `∨`-elimination: by cases. -/
  | orE {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q r : Formula Sig Γ} :
      CSupported S Δ (Term.disj p q) → CSupported S (p :: Δ) r → CSupported S (q :: Δ) r →
      CSupported S Δ r
  /-- `¬`-introduction: what yields a contradiction is false. -/
  | notI {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      CSupported S (p :: Δ) q → CSupported S (p :: Δ) (Term.neg q) → CSupported S Δ (Term.neg p)
  /-- `¬`-elimination: from a contradiction, anything. -/
  | notE {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      CSupported S Δ p → CSupported S Δ (Term.neg p) → CSupported S Δ q
  /-- Excluded middle, which makes the propositional fragment classical. -/
  | em {Γ : Ctx} {Δ : List (Formula Sig Γ)} (p : Formula Sig Γ) :
      CSupported S Δ (Term.disj p (Term.neg p))
  /-- `UI`: `∀σ F → F A`, for any predicate term `F`. -/
  | allE {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {F : Term Sig Γ (σ ⇒ RTy.t)} :
      σ ∈ S → CSupported S Δ (.app (.all σ) F) → (a : Term Sig Γ σ) → CSupported S Δ (.app F a)
  /-- `Gen`: from `b`, derived with a fresh variable and hypotheses not mentioning it,
  `∀v. b`. -/
  | allI {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {b : Formula Sig (σ :: Γ)} :
      σ ∈ S → CSupported S (Hyps.weaken Δ) b → CSupported S Δ (Term.forall' b)
  /-- `EG`: `F A → ∃σ F`. -/
  | exI {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {F : Term Sig Γ (σ ⇒ RTy.t)}
      (hs : σ ∈ S) (a : Term Sig Γ σ) : CSupported S Δ (.app F a) → CSupported S Δ (.app (.ex σ) F)
  /-- `Inst`: from `∃σ F`, and `r` derived from `F v` for a fresh `v`, `r`. -/
  | exE {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {F : Term Sig Γ (σ ⇒ RTy.t)}
      {r : Formula Sig Γ} :
      σ ∈ S → CSupported S Δ (.app (.ex σ) F) →
      CSupported S (Term.app F.weaken (.var .zero) :: Hyps.weaken Δ) r.weaken →
      CSupported S Δ r
  /-- `Ref`: `A = A`. -/
  | refl {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} (hs : σ ∈ S) (a : Term Sig Γ σ) :
      CSupported S Δ (Term.eq' a a)
  /-- `LL`: from `A = B` and `F A`, `F B`. -/
  | ll {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {a b : Term Sig Γ σ}
      (hs : σ ∈ S) (F : Term Sig Γ (σ ⇒ RTy.t)) :
      CSupported S Δ (Term.eq' a b) → CSupported S Δ (.app F a) → CSupported S Δ (.app F b)
  /-- `β`, `η` and `δ`: derivability transfers along conversion. -/
  | conv {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      CSupported S Δ p → p ≡ q → CSupported S Δ q
  /-- The actual C rule: both equivalence premises and the main premise recurse.
  The t entry supports separation of P and Q; the hole entries support the
  Functionality instances at its enclosing abstractions. -/
  | subst {Γ Γ' : Ctx} {Δ : List (Formula Sig Γ)} {P Q : Formula Sig Γ'}
      (C : Hole Sig Γ Ty.t Γ' Ty.t) (ht : Ty.t ∈ S) (hC : holeTypes C ⊆ S) :
      CSupported S [P] Q → CSupported S [Q] P →
      CSupported S Δ (C.plug P) → CSupported S Δ (C.plug Q)

namespace CSupported

theorem rename {S : List Ty} : ∀ {Γ Δ : Ctx} (r : Ren Γ Δ) {Δ' : List (Formula Sig Γ)}
    {p : Formula Sig Γ}, CSupported S Δ' p → CSupported S (Hyps.rename r Δ') (p.rename r)
  | _, _, r, _, _, hyp h => hyp (List.mem_map.2 ⟨_, h, rfl⟩)
  | _, _, _, _, _, existence hσ => existence hσ
  | _, _, r, _, _, andI h₁ h₂ => andI (rename r h₁) (rename r h₂)
  | _, _, r, _, _, andE₁ h => andE₁ (rename r h)
  | _, _, r, _, _, andE₂ h => andE₂ (rename r h)
  | _, _, r, _, _, orI₁ h => orI₁ (rename r h)
  | _, _, r, _, _, orI₂ h => orI₂ (rename r h)
  | _, _, r, _, _, orE h h₁ h₂ => orE (rename r h) (rename r h₁) (rename r h₂)
  | _, _, r, _, _, notI h₁ h₂ => notI (rename r h₁) (rename r h₂)
  | _, _, r, _, _, notE h₁ h₂ => notE (rename r h₁) (rename r h₂)
  | _, _, r, _, _, em p => em _
  | _, _, r, _, _, allE hσ h a => allE hσ (rename r h) (a.rename r)
  | _, _, r, _, _, allI hσ h => by
    have := rename (Ren.lift r) h
    rw [← Hyps.weaken_rename] at this
    exact allI hσ this
  | _, _, r, _, _, exI hσ a h => exI hσ (a.rename r) (rename r h)
  | _, _, r, Δ', _, exE (σ := σ) (F := F) (r := q) hσ h h' => by
    have this := rename (Ren.lift r) h'
    have e₁ : Hyps.rename (Ren.lift r) (Term.app F.weaken (.var .zero) :: Hyps.weaken Δ')
        = Term.app (F.rename r).weaken (.var .zero) :: Hyps.weaken (Hyps.rename r Δ') := by
      simp only [Hyps.rename, List.map_cons, Hyps.weaken_rename, Term.weaken_rename]
      rfl
    have e₂ : q.weaken.rename (Ren.lift r) = (q.rename r).weaken (τ := σ) :=
      (Term.weaken_rename (τ := σ) r q).symm
    rw [e₁, e₂] at this
    exact exE hσ (rename r h) this
  | _, _, r, _, _, refl hσ a => refl hσ _
  | _, _, r, _, _, ll hσ F h₁ h₂ => ll hσ (F.rename r) (rename r h₁) (rename r h₂)
  | _, _, r, _, _, conv h c => conv (rename r h) (Conv.rename r c)
  | _, _, r, _, _, subst C ht hC h₁ h₂ h₃ => by
      have h₁' := rename (C.rename r).ren h₁
      have h₂' := rename (C.rename r).ren h₂
      have h₃' := rename r h₃
      have hC' : holeTypes (C.rename r).hole ⊆ S := by
        simpa only [holeTypes_rename] using hC
      rw [Hole.plug_rename] at h₃' ⊢
      exact subst (C.rename r).hole ht hC' h₁' h₂' h₃'



/-- Enlarging the finite qualification type list never loses a proof. -/
theorem mono {S T : List Ty} (hs : S ⊆ T) :
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ},
    CSupported S Δ p → CSupported T Δ p
  | _, _, _, .hyp h => .hyp h
  | _, _, _, .existence h => .existence (hs h)
  | _, _, _, .andI h k => .andI (mono hs h) (mono hs k)
  | _, _, _, .andE₁ h => .andE₁ (mono hs h)
  | _, _, _, .andE₂ h => .andE₂ (mono hs h)
  | _, _, _, .orI₁ h => .orI₁ (mono hs h)
  | _, _, _, .orI₂ h => .orI₂ (mono hs h)
  | _, _, _, .orE h k l => .orE (mono hs h) (mono hs k) (mono hs l)
  | _, _, _, .notI h k => .notI (mono hs h) (mono hs k)
  | _, _, _, .notE h k => .notE (mono hs h) (mono hs k)
  | _, _, _, .em p => .em p
  | _, _, _, .allE hσ h a => .allE (hs hσ) (mono hs h) a
  | _, _, _, .allI hσ h => .allI (hs hσ) (mono hs h)
  | _, _, _, .exI hσ a h => .exI (hs hσ) a (mono hs h)
  | _, _, _, .exE hσ h k => .exE (hs hσ) (mono hs h) (mono hs k)
  | _, _, _, .refl hσ a => .refl (hs hσ) a
  | _, _, _, .ll hσ F h k => .ll (hs hσ) F (mono hs h) (mono hs k)
  | _, _, _, .conv h c => .conv (mono hs h) c
  | _, _, _, .subst C ht hC h k l =>
      .subst C (hs ht) (fun _ hσ => hs (hC hσ))
        (mono hs h) (mono hs k) (mono hs l)

/-- Forgetting support gives a derivation in the actual unextended C relation. -/
theorem forget {S : List Ty} :
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ},
    CSupported S Δ p → Derivable Logical Δ p
  | _, _, _, .hyp h => .hyp h
  | _, _, _, .existence _ => .ax (a := existence_e) rfl
  | _, _, _, .andI h k => .andI (forget h) (forget k)
  | _, _, _, .andE₁ h => .andE₁ (forget h)
  | _, _, _, .andE₂ h => .andE₂ (forget h)
  | _, _, _, .orI₁ h => .orI₁ (forget h)
  | _, _, _, .orI₂ h => .orI₂ (forget h)
  | _, _, _, .orE h k l => .orE (forget h) (forget k) (forget l)
  | _, _, _, .notI h k => .notI (forget h) (forget k)
  | _, _, _, .notE h k => .notE (forget h) (forget k)
  | _, _, _, .em p => .em p
  | _, _, _, .allE _ h a => .allE (forget h) a
  | _, _, _, .allI _ h => .allI (forget h)
  | _, _, _, .exI _ a h => .exI a (forget h)
  | _, _, _, .exE _ h k => .exE (forget h) (forget k)
  | _, _, _, .refl _ a => .refl a
  | _, _, _, .ll _ F h k => .ll F (forget h) (forget k)
  | _, _, _, .conv h c => .conv (forget h) c
  | _, _, _, .subst C _ _ h k l =>
      .subst C
        (Derivable.mono (Ax := Logical) (Ax' := Logical.logical)
          (fun _ ha => ⟨ha, ha⟩) (forget h))
        (Derivable.mono (Ax := Logical) (Ax' := Logical.logical)
          (fun _ ha => ⟨ha, ha⟩) (forget k))
        (forget l)

end CSupported

/-- Every actual C derivation with logical axioms only has finite type support.
The axiom-set parameter remains indexed through the induction, so both logical
premises of each Subst occurrence are recursively inspected, even when nested. -/
theorem c_finite_support :
    ∀ {Ax : AxiomSet Sig}, (∀ a, Ax a → Logical a) →
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ},
    Derivable Ax Δ p → ∃ S : List Ty, CSupported S Δ p
  | _, hA, _, _, _, .hyp h => ⟨[], .hyp h⟩
  | _, hA, _, _, _, .ax (a := a) h => by
      have ha : a = existence_e := hA a h
      subst a
      exact ⟨[Ty.e], .existence (List.mem_cons_self ..)⟩
  | _, hA, _, _, _, .andI h k => by
      obtain ⟨S, hS⟩ := c_finite_support hA h
      obtain ⟨T, hT⟩ := c_finite_support hA k
      exact ⟨S ++ T, .andI
        (hS.mono (fun _ h => List.mem_append_left _ h))
        (hT.mono (fun _ h => List.mem_append_right _ h))⟩
  | _, hA, _, _, _, .andE₁ h => by
      obtain ⟨S, hS⟩ := c_finite_support hA h
      exact ⟨S, .andE₁ hS⟩
  | _, hA, _, _, _, .andE₂ h => by
      obtain ⟨S, hS⟩ := c_finite_support hA h
      exact ⟨S, .andE₂ hS⟩
  | _, hA, _, _, _, .orI₁ h => by
      obtain ⟨S, hS⟩ := c_finite_support hA h
      exact ⟨S, .orI₁ hS⟩
  | _, hA, _, _, _, .orI₂ h => by
      obtain ⟨S, hS⟩ := c_finite_support hA h
      exact ⟨S, .orI₂ hS⟩
  | _, hA, _, _, _, .orE h k l => by
      obtain ⟨S, hS⟩ := c_finite_support hA h
      obtain ⟨T, hT⟩ := c_finite_support hA k
      obtain ⟨U, hU⟩ := c_finite_support hA l
      refine ⟨(S ++ T) ++ U, .orE (hS.mono ?_) (hT.mono ?_) (hU.mono ?_)⟩
      · intro σ hσ; exact List.mem_append_left _ (List.mem_append_left _ hσ)
      · intro σ hσ; exact List.mem_append_left _ (List.mem_append_right _ hσ)
      · intro σ hσ; exact List.mem_append_right _ hσ
  | _, hA, _, _, _, .notI h k => by
      obtain ⟨S, hS⟩ := c_finite_support hA h
      obtain ⟨T, hT⟩ := c_finite_support hA k
      exact ⟨S ++ T, .notI
        (hS.mono (fun _ h => List.mem_append_left _ h))
        (hT.mono (fun _ h => List.mem_append_right _ h))⟩
  | _, hA, _, _, _, .notE h k => by
      obtain ⟨S, hS⟩ := c_finite_support hA h
      obtain ⟨T, hT⟩ := c_finite_support hA k
      exact ⟨S ++ T, .notE
        (hS.mono (fun _ h => List.mem_append_left _ h))
        (hT.mono (fun _ h => List.mem_append_right _ h))⟩
  | _, hA, _, _, _, .em p => ⟨[], .em p⟩
  | _, hA, _, _, _, .allE (σ := σ) h a => by
      obtain ⟨S, hS⟩ := c_finite_support hA h
      exact ⟨σ :: S, .allE (List.mem_cons_self ..)
        (hS.mono (List.subset_cons_self ..)) a⟩
  | _, hA, _, _, _, .allI (σ := σ) h => by
      obtain ⟨S, hS⟩ := c_finite_support hA h
      exact ⟨σ :: S, .allI (List.mem_cons_self ..)
        (hS.mono (List.subset_cons_self ..))⟩
  | _, hA, _, _, _, .exI (σ := σ) a h => by
      obtain ⟨S, hS⟩ := c_finite_support hA h
      exact ⟨σ :: S, .exI (List.mem_cons_self ..) a
        (hS.mono (List.subset_cons_self ..))⟩
  | _, hA, _, _, _, .exE (σ := σ) h k => by
      obtain ⟨S, hS⟩ := c_finite_support hA h
      obtain ⟨T, hT⟩ := c_finite_support hA k
      refine ⟨σ :: (S ++ T), .exE (List.mem_cons_self ..)
        (hS.mono ?_) (hT.mono ?_)⟩
      · intro υ hυ; exact List.mem_cons_of_mem _ (List.mem_append_left _ hυ)
      · intro υ hυ; exact List.mem_cons_of_mem _ (List.mem_append_right _ hυ)
  | _, hA, _, _, _, .refl (σ := σ) a => ⟨[σ], .refl (List.mem_cons_self ..) a⟩
  | _, hA, _, _, _, .ll (σ := σ) F h k => by
      obtain ⟨S, hS⟩ := c_finite_support hA h
      obtain ⟨T, hT⟩ := c_finite_support hA k
      refine ⟨σ :: (S ++ T), .ll (List.mem_cons_self ..) F
        (hS.mono ?_) (hT.mono ?_)⟩
      · intro υ hυ; exact List.mem_cons_of_mem _ (List.mem_append_left _ hυ)
      · intro υ hυ; exact List.mem_cons_of_mem _ (List.mem_append_right _ hυ)
  | _, hA, _, _, _, .conv h c => by
      obtain ⟨S, hS⟩ := c_finite_support hA h
      exact ⟨S, .conv hS c⟩
  | Ax, hA, _, _, _, .subst C h k l => by
      obtain ⟨S, hS⟩ := c_finite_support (Ax := Ax.logical) (fun _ ha => ha.2) h
      obtain ⟨T, hT⟩ := c_finite_support (Ax := Ax.logical) (fun _ ha => ha.2) k
      obtain ⟨U, hU⟩ := c_finite_support hA l
      refine ⟨Ty.t :: (holeTypes C ++ ((S ++ T) ++ U)),
        .subst C (List.mem_cons_self ..) ?_
          (hS.mono ?_) (hT.mono ?_) (hU.mono ?_)⟩
      · intro σ hσ
        exact List.mem_cons_of_mem _ (List.mem_append_left _ hσ)
      · intro σ hσ
        exact List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_append_left _ (List.mem_append_left _ hσ)))
      · intro σ hσ
        exact List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_append_left _ (List.mem_append_right _ hσ)))
      · intro σ hσ
        exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _ hσ))

#print axioms CSupported.forget
#print axioms CSupported.rename
#print axioms c_finite_support

end Classicism.Research.FullTypedLogicalSeparationH

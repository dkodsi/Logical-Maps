import Classicism.Results.Research.FullTypedLogicalSeparationHCalculus

/-!
# Finite type support for H derivations

Original proof, misc, 23 October 2026, unpaginated; H observer note section 2.
`Supported S` records exactly the types at which a derivation uses a quantifier
or identity rule. Every unrestricted H proof admits such a finite list.
-/
namespace Classicism.Research.FullTypedLogicalSeparationH
open Classicism.Meta
variable {Sig : Signature}

inductive Supported (S : List Ty) : ∀ {Γ : Ctx}, List (Formula Sig Γ) → Formula Sig Γ → Prop
  /-- A hypothesis. -/
  | hyp {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ} :
      p ∈ Δ → Supported S Δ p
  /-- H's sole non-rule logical axiom: existence at e. -/
  | existence {Γ : Ctx} {Δ : List (Formula Sig Γ)} :
      Ty.e ∈ S → Supported S Δ (Term.exists' (σ := Ty.e) (Term.eq' Term.v0 Term.v0))
  /-- `∧`-introduction. -/
  | andI {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Supported S Δ p → Supported S Δ q → Supported S Δ (Term.conj p q)
  /-- `∧`-elimination, left. -/
  | andE₁ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Supported S Δ (Term.conj p q) → Supported S Δ p
  /-- `∧`-elimination, right. -/
  | andE₂ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Supported S Δ (Term.conj p q) → Supported S Δ q
  /-- `∨`-introduction, left. -/
  | orI₁ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Supported S Δ p → Supported S Δ (Term.disj p q)
  /-- `∨`-introduction, right. -/
  | orI₂ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Supported S Δ q → Supported S Δ (Term.disj p q)
  /-- `∨`-elimination: by cases. -/
  | orE {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q r : Formula Sig Γ} :
      Supported S Δ (Term.disj p q) → Supported S (p :: Δ) r → Supported S (q :: Δ) r →
      Supported S Δ r
  /-- `¬`-introduction: what yields a contradiction is false. -/
  | notI {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Supported S (p :: Δ) q → Supported S (p :: Δ) (Term.neg q) → Supported S Δ (Term.neg p)
  /-- `¬`-elimination: from a contradiction, anything. -/
  | notE {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Supported S Δ p → Supported S Δ (Term.neg p) → Supported S Δ q
  /-- Excluded middle, which makes the propositional fragment classical. -/
  | em {Γ : Ctx} {Δ : List (Formula Sig Γ)} (p : Formula Sig Γ) :
      Supported S Δ (Term.disj p (Term.neg p))
  /-- `UI`: `∀σ F → F A`, for any predicate term `F`. -/
  | allE {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {F : Term Sig Γ (σ ⇒ RTy.t)} :
      σ ∈ S → Supported S Δ (.app (.all σ) F) → (a : Term Sig Γ σ) → Supported S Δ (.app F a)
  /-- `Gen`: from `b`, derived with a fresh variable and hypotheses not mentioning it,
  `∀v. b`. -/
  | allI {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {b : Formula Sig (σ :: Γ)} :
      σ ∈ S → Supported S (Hyps.weaken Δ) b → Supported S Δ (Term.forall' b)
  /-- `EG`: `F A → ∃σ F`. -/
  | exI {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {F : Term Sig Γ (σ ⇒ RTy.t)}
      (hs : σ ∈ S) (a : Term Sig Γ σ) : Supported S Δ (.app F a) → Supported S Δ (.app (.ex σ) F)
  /-- `Inst`: from `∃σ F`, and `r` derived from `F v` for a fresh `v`, `r`. -/
  | exE {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {F : Term Sig Γ (σ ⇒ RTy.t)}
      {r : Formula Sig Γ} :
      σ ∈ S → Supported S Δ (.app (.ex σ) F) →
      Supported S (Term.app F.weaken (.var .zero) :: Hyps.weaken Δ) r.weaken →
      Supported S Δ r
  /-- `Ref`: `A = A`. -/
  | refl {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} (hs : σ ∈ S) (a : Term Sig Γ σ) :
      Supported S Δ (Term.eq' a a)
  /-- `LL`: from `A = B` and `F A`, `F B`. -/
  | ll {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {a b : Term Sig Γ σ}
      (hs : σ ∈ S) (F : Term Sig Γ (σ ⇒ RTy.t)) :
      Supported S Δ (Term.eq' a b) → Supported S Δ (.app F a) → Supported S Δ (.app F b)
  /-- `β`, `η` and `δ`: derivability transfers along conversion. -/
  | conv {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Supported S Δ p → p ≡ q → Supported S Δ q


namespace Supported

theorem rename {S : List Ty} : ∀ {Γ Δ : Ctx} (r : Ren Γ Δ) {Δ' : List (Formula Sig Γ)}
    {p : Formula Sig Γ}, Supported S Δ' p → Supported S (Hyps.rename r Δ') (p.rename r)
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



/-- Enlarging the finite qualification type list never loses a proof. -/
theorem mono {S T : List Ty} (hs : S ⊆ T) :
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ},
    Supported S Δ p → Supported T Δ p
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

/-- Forgetting support gives a derivation in unextended H. -/
theorem forget {S : List Ty} :
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ},
    Supported S Δ p → Derives (NoAxioms Sig) Δ p
  | _, _, _, .hyp h => .hyp h
  | _, _, _, .existence _ => .existence
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

end Supported

/-- Every H derivation uses only finitely many quantifier/equality types.
This is a statement about proof trees, not an infinitary object axiom. -/
theorem finite_support :
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ},
    Derives (NoAxioms Sig) Δ p → ∃ S : List Ty, Supported S Δ p
  | _, _, _, .hyp h => ⟨[], .hyp h⟩
  | _, _, _, .ax h => False.elim h
  | _, _, _, .existence => ⟨[Ty.e], .existence (List.mem_cons_self ..)⟩
  | _, _, _, .andI h k => by
      obtain ⟨S, hS⟩ := finite_support h
      obtain ⟨T, hT⟩ := finite_support k
      exact ⟨S ++ T, .andI
        (hS.mono (fun _ h => List.mem_append_left _ h))
        (hT.mono (fun _ h => List.mem_append_right _ h))⟩
  | _, _, _, .andE₁ h => by
      obtain ⟨S, hS⟩ := finite_support h
      exact ⟨S, .andE₁ hS⟩
  | _, _, _, .andE₂ h => by
      obtain ⟨S, hS⟩ := finite_support h
      exact ⟨S, .andE₂ hS⟩
  | _, _, _, .orI₁ h => by
      obtain ⟨S, hS⟩ := finite_support h
      exact ⟨S, .orI₁ hS⟩
  | _, _, _, .orI₂ h => by
      obtain ⟨S, hS⟩ := finite_support h
      exact ⟨S, .orI₂ hS⟩
  | _, _, _, .orE h k l => by
      obtain ⟨S, hS⟩ := finite_support h
      obtain ⟨T, hT⟩ := finite_support k
      obtain ⟨U, hU⟩ := finite_support l
      refine ⟨(S ++ T) ++ U, .orE (hS.mono ?_) (hT.mono ?_) (hU.mono ?_)⟩
      · intro σ hσ; exact List.mem_append_left _ (List.mem_append_left _ hσ)
      · intro σ hσ; exact List.mem_append_left _ (List.mem_append_right _ hσ)
      · intro σ hσ; exact List.mem_append_right _ hσ
  | _, _, _, .notI h k => by
      obtain ⟨S, hS⟩ := finite_support h
      obtain ⟨T, hT⟩ := finite_support k
      exact ⟨S ++ T, .notI
        (hS.mono (fun _ h => List.mem_append_left _ h))
        (hT.mono (fun _ h => List.mem_append_right _ h))⟩
  | _, _, _, .notE h k => by
      obtain ⟨S, hS⟩ := finite_support h
      obtain ⟨T, hT⟩ := finite_support k
      exact ⟨S ++ T, .notE
        (hS.mono (fun _ h => List.mem_append_left _ h))
        (hT.mono (fun _ h => List.mem_append_right _ h))⟩
  | _, _, _, .em p => ⟨[], .em p⟩
  | _, _, _, .allE (σ := σ) h a => by
      obtain ⟨S, hS⟩ := finite_support h
      exact ⟨σ :: S, .allE (List.mem_cons_self ..)
        (hS.mono (List.subset_cons_self ..)) a⟩
  | _, _, _, .allI (σ := σ) h => by
      obtain ⟨S, hS⟩ := finite_support h
      exact ⟨σ :: S, .allI (List.mem_cons_self ..)
        (hS.mono (List.subset_cons_self ..))⟩
  | _, _, _, .exI (σ := σ) a h => by
      obtain ⟨S, hS⟩ := finite_support h
      exact ⟨σ :: S, .exI (List.mem_cons_self ..) a
        (hS.mono (List.subset_cons_self ..))⟩
  | _, _, _, .exE (σ := σ) h k => by
      obtain ⟨S, hS⟩ := finite_support h
      obtain ⟨T, hT⟩ := finite_support k
      refine ⟨σ :: (S ++ T), .exE (List.mem_cons_self ..)
        (hS.mono ?_) (hT.mono ?_)⟩
      · intro υ hυ; exact List.mem_cons_of_mem _ (List.mem_append_left _ hυ)
      · intro υ hυ; exact List.mem_cons_of_mem _ (List.mem_append_right _ hυ)
  | _, _, _, .refl (σ := σ) a => ⟨[σ], .refl (List.mem_cons_self ..) a⟩
  | _, _, _, .ll (σ := σ) F h k => by
      obtain ⟨S, hS⟩ := finite_support h
      obtain ⟨T, hT⟩ := finite_support k
      refine ⟨σ :: (S ++ T), .ll (List.mem_cons_self ..) F
        (hS.mono ?_) (hT.mono ?_)⟩
      · intro υ hυ; exact List.mem_cons_of_mem _ (List.mem_append_left _ hυ)
      · intro υ hυ; exact List.mem_cons_of_mem _ (List.mem_append_right _ hυ)
  | _, _, _, .conv h c => by
      obtain ⟨S, hS⟩ := finite_support h
      exact ⟨S, .conv hS c⟩

end Classicism.Research.FullTypedLogicalSeparationH

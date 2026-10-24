import Classicism.Results.Research.FullTypedLogicalSeparationCSupport
import Classicism.Syntax.VectorizeDerivable
import Classicism.Syntax.ClosedTypes

/-!
# Closed rule support for the repository C derivation relation

Direct source: `research/2026-10-23/operator-characterizations/h-logical-observer-strengthening.txt`,
sections 2--3 (misc, original research, 23 October 2026, unpaginated).

Every metalanguage type variable is instantiated by the singleton [e]. The
induction below refines the repository's vectorization proof: it retains finite
closed rule support, and recursively translates all three premises of Subst.
The final fixed-sentence lemma recovers a sentence already in the paper's
language. No premise identifying arbitrary C proofs with the auxiliary H
calculus is used.
-/
namespace Classicism.Research.FullTypedLogicalSeparationH
open Classicism.Meta
open Classicism.Meta.Research.FullTypedLogicalSeparation (holeTypes)
variable {Sig : Signature}

/-- A single ordinary individual type replaces each metalanguage type variable. -/
def erase : Assign := fun _ => [Ty.e]

mutual
  /-- Erasure always sends a type to a singleton closed type. -/
  theorem erase_singleton : ∀ σ : Ty, ∃ τ : Ty, σ.vec erase = [τ] ∧ τ.Closed
    | .e => ⟨.e, rfl, trivial⟩
    | .var _ => ⟨.e, rfl, trivial⟩
    | .rel ρ => ⟨.rel (ρ.vec erase), rfl, erase_rel_closed ρ⟩

  theorem erase_rel_closed : ∀ ρ : RTy, (ρ.vec erase).Closed
    | .t => trivial
    | .arr σ ρ => by
        obtain ⟨τ, hτ, hcτ⟩ := erase_singleton σ
        change (σ.vec erase ⇒* ρ.vec erase).Closed
        rw [hτ]
        exact And.intro hcτ (erase_rel_closed ρ)
end

private theorem closed_nil : Ty.AllClosed [] := by
  intro σ hσ
  cases hσ

private theorem closed_append {S T : List Ty} (hS : Ty.AllClosed S)
    (hT : Ty.AllClosed T) : Ty.AllClosed (S ++ T) := by
  intro σ hσ
  exact (List.mem_append.1 hσ).elim (hS σ) (hT σ)

private theorem closed_cons {S : List Ty} {σ : Ty} (hσ : σ.Closed)
    (hS : Ty.AllClosed S) : Ty.AllClosed (σ :: S) := by
  intro τ hτ
  rcases List.mem_cons.1 hτ with rfl | hτ
  · exact hσ
  · exact hS τ hτ

/-- An actual C proof with some finite list of closed rule types. -/
abbrev ClosedCSupported {Γ : Ctx} (Δ : List (Formula Sig Γ)) (p : Formula Sig Γ) : Prop :=
  ∃ S : List Ty, Ty.AllClosed S ∧ CSupported S Δ p

namespace ClosedCSupported
variable {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q r : Formula Sig Γ}

theorem hyp (h : p ∈ Δ) : ClosedCSupported Δ p := ⟨[], closed_nil, .hyp h⟩
theorem existence : ClosedCSupported Δ (existence_e.close (Γ := Γ)) :=
  ⟨[Ty.e], Ty.allClosed_singleton trivial, .existence (List.mem_cons_self ..)⟩
theorem andI (h : ClosedCSupported Δ p) (k : ClosedCSupported Δ q) :
    ClosedCSupported Δ (Term.conj p q) := by
  obtain ⟨S, hS, h⟩ := h
  obtain ⟨T, hT, k⟩ := k
  exact ⟨S ++ T, closed_append hS hT,
    .andI (h.mono (fun _ h => List.mem_append_left _ h))
      (k.mono (fun _ h => List.mem_append_right _ h))⟩
theorem andE₁ (h : ClosedCSupported Δ (Term.conj p q)) : ClosedCSupported Δ p := by
  obtain ⟨S, hS, h⟩ := h; exact ⟨S, hS, .andE₁ h⟩
theorem andE₂ (h : ClosedCSupported Δ (Term.conj p q)) : ClosedCSupported Δ q := by
  obtain ⟨S, hS, h⟩ := h; exact ⟨S, hS, .andE₂ h⟩
theorem orI₁ (h : ClosedCSupported Δ p) : ClosedCSupported Δ (Term.disj p q) := by
  obtain ⟨S, hS, h⟩ := h; exact ⟨S, hS, .orI₁ h⟩
theorem orI₂ (h : ClosedCSupported Δ q) : ClosedCSupported Δ (Term.disj p q) := by
  obtain ⟨S, hS, h⟩ := h; exact ⟨S, hS, .orI₂ h⟩
theorem orE (h : ClosedCSupported Δ (Term.disj p q))
    (k : ClosedCSupported (p :: Δ) r) (l : ClosedCSupported (q :: Δ) r) :
    ClosedCSupported Δ r := by
  obtain ⟨S, hS, h⟩ := h
  obtain ⟨T, hT, k⟩ := k
  obtain ⟨U, hU, l⟩ := l
  refine ⟨(S ++ T) ++ U, closed_append (closed_append hS hT) hU,
    .orE (h.mono ?_) (k.mono ?_) (l.mono ?_)⟩
  · intro σ hσ; exact List.mem_append_left _ (List.mem_append_left _ hσ)
  · intro σ hσ; exact List.mem_append_left _ (List.mem_append_right _ hσ)
  · intro σ hσ; exact List.mem_append_right _ hσ
theorem notI (h : ClosedCSupported (p :: Δ) q)
    (k : ClosedCSupported (p :: Δ) (Term.neg q)) : ClosedCSupported Δ (Term.neg p) := by
  obtain ⟨S, hS, h⟩ := h
  obtain ⟨T, hT, k⟩ := k
  exact ⟨S ++ T, closed_append hS hT,
    .notI (h.mono (fun _ h => List.mem_append_left _ h))
      (k.mono (fun _ h => List.mem_append_right _ h))⟩
theorem notE (h : ClosedCSupported Δ p) (k : ClosedCSupported Δ (Term.neg p)) :
    ClosedCSupported Δ q := by
  obtain ⟨S, hS, h⟩ := h
  obtain ⟨T, hT, k⟩ := k
  exact ⟨S ++ T, closed_append hS hT,
    .notE (h.mono (fun _ h => List.mem_append_left _ h))
      (k.mono (fun _ h => List.mem_append_right _ h))⟩
theorem em (p : Formula Sig Γ) : ClosedCSupported Δ (Term.disj p (Term.neg p)) :=
  ⟨[], closed_nil, .em p⟩
theorem conv (h : ClosedCSupported Δ p) (c : p ≡ q) : ClosedCSupported Δ q := by
  obtain ⟨S, hS, h⟩ := h; exact ⟨S, hS, .conv h c⟩

/- Singleton block rules avoid any dependent casts in the derivation induction. -/
theorem allEC (σs : List Ty) (hs : ∃ σ, σs = [σ] ∧ σ.Closed)
    {F : Term Sig Γ (σs ⇒* .t)}
    (h : ClosedCSupported Δ (.app (Term.allC σs) F)) (as : Terms Sig Γ σs) :
    ClosedCSupported Δ (Term.appBlock F as) := by
  obtain ⟨σ, rfl, hσ⟩ := hs
  obtain ⟨S, hS, h⟩ := h
  exact ⟨σ :: S, closed_cons hσ hS,
    .allE (List.mem_cons_self ..) (h.mono (List.subset_cons_self ..)) as.head1⟩

theorem allIC (σs : List Ty) (hs : ∃ σ, σs = [σ] ∧ σ.Closed)
    {p : Formula Sig (Ctx.block σs Γ)}
    (h : ClosedCSupported (Hyps.wkBlock σs Δ) p) :
    ClosedCSupported Δ (.app (Term.allC σs) (Term.lamBlock σs p)) := by
  obtain ⟨σ, rfl, hσ⟩ := hs
  obtain ⟨S, hS, h⟩ := h
  exact ⟨σ :: S, closed_cons hσ hS,
    .allI (List.mem_cons_self ..) (h.mono (List.subset_cons_self ..))⟩

theorem exIC (σs : List Ty) (hs : ∃ σ, σs = [σ] ∧ σ.Closed)
    {F : Term Sig Γ (σs ⇒* .t)} (as : Terms Sig Γ σs)
    (h : ClosedCSupported Δ (Term.appBlock F as)) :
    ClosedCSupported Δ (.app (Term.exC σs) F) := by
  obtain ⟨σ, rfl, hσ⟩ := hs
  obtain ⟨S, hS, h⟩ := h
  exact ⟨σ :: S, closed_cons hσ hS,
    .exI (List.mem_cons_self ..) as.head1 (h.mono (List.subset_cons_self ..))⟩

theorem exEC (σs : List Ty) (hs : ∃ σ, σs = [σ] ∧ σ.Closed)
    {F : Term Sig Γ (σs ⇒* .t)} (h : ClosedCSupported Δ (.app (Term.exC σs) F))
    (k : ClosedCSupported
      (Term.appBlock (F.rename (Ren.wkBlock σs)) (Terms.vars σs Γ) :: Hyps.wkBlock σs Δ)
      (r.rename (Ren.wkBlock σs))) : ClosedCSupported Δ r := by
  obtain ⟨σ, rfl, hσ⟩ := hs
  obtain ⟨S, hS, h⟩ := h
  obtain ⟨T, hT, k⟩ := k
  refine ⟨σ :: (S ++ T), closed_cons hσ (closed_append hS hT),
    .exE (List.mem_cons_self ..) (h.mono ?_) (k.mono ?_)⟩
  · intro τ hτ; exact List.mem_cons_of_mem _ (List.mem_append_left _ hτ)
  · intro τ hτ; exact List.mem_cons_of_mem _ (List.mem_append_right _ hτ)

theorem reflC (σs : List Ty) (hs : ∃ σ, σs = [σ] ∧ σ.Closed)
    (as : Terms Sig Γ σs) :
    ClosedCSupported Δ (Term.appBlock (Term.appBlock (Term.eqC σs) as) as) := by
  obtain ⟨σ, rfl, hσ⟩ := hs
  exact ⟨[σ], Ty.allClosed_singleton hσ, .refl (List.mem_cons_self ..) as.head1⟩

theorem llC (σs : List Ty) (hs : ∃ σ, σs = [σ] ∧ σ.Closed)
    (F : Term Sig Γ (σs ⇒* .t)) {as bs : Terms Sig Γ σs}
    (h : ClosedCSupported Δ (Term.appBlock (Term.appBlock (Term.eqC σs) as) bs))
    (k : ClosedCSupported Δ (Term.appBlock F as)) : ClosedCSupported Δ (Term.appBlock F bs) := by
  obtain ⟨σ, rfl, hσ⟩ := hs
  obtain ⟨S, hS, h⟩ := h
  obtain ⟨T, hT, k⟩ := k
  refine ⟨σ :: (S ++ T), closed_cons hσ (closed_append hS hT),
    .ll (List.mem_cons_self ..) F (h.mono ?_) (k.mono ?_)⟩
  · intro τ hτ; exact List.mem_cons_of_mem _ (List.mem_append_left _ hτ)
  · intro τ hτ; exact List.mem_cons_of_mem _ (List.mem_append_right _ hτ)

theorem subst {Γ' : Ctx} {P Q : Formula Sig Γ'} (C : Hole Sig Γ Ty.t Γ' Ty.t)
    (hc : Ty.AllClosed (holeTypes C)) (h : ClosedCSupported [P] Q)
    (k : ClosedCSupported [Q] P) (l : ClosedCSupported Δ (C.plug P)) :
    ClosedCSupported Δ (C.plug Q) := by
  obtain ⟨S, hS, h⟩ := h
  obtain ⟨T, hT, k⟩ := k
  obtain ⟨U, hU, l⟩ := l
  refine ⟨Ty.t :: (holeTypes C ++ ((S ++ T) ++ U)),
    closed_cons trivial (closed_append hc (closed_append (closed_append hS hT) hU)),
    .subst C (List.mem_cons_self ..) ?_ (h.mono ?_) (k.mono ?_) (l.mono ?_)⟩
  · intro σ hσ; exact List.mem_cons_of_mem _ (List.mem_append_left _ hσ)
  · intro σ hσ
    exact List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_append_left _ (List.mem_append_left _ hσ)))
  · intro σ hσ
    exact List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_append_left _ (List.mem_append_right _ hσ)))
  · intro σ hσ
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _ hσ))
end ClosedCSupported

private theorem holeTypes_appLBlock {Γ Γ' : Ctx} {σs : List Ty} {ρ : RTy}
    (C : Hole Sig Γ (σs ⇒* ρ) Γ' Ty.t) (as : Terms Sig Γ σs) :
    holeTypes (Hole.appLBlock C as) = holeTypes C := by
  induction σs generalizing Γ ρ with
  | nil => rfl
  | cons σ σs ih => exact ih (C := .appL C as.head) (as := as.tail)

private theorem holeTypes_singleton_lamBlock {Γ Γ' : Ctx} {σs : List Ty} {ρ : RTy}
    (hs : ∃ σ, σs = [σ] ∧ σ.Closed) (hρ : ρ.Closed)
    (C : Hole Sig (Ctx.block σs Γ) ρ Γ' Ty.t) (hC : Ty.AllClosed (holeTypes C)) :
    Ty.AllClosed (holeTypes (Hole.lamBlock σs C)) := by
  obtain ⟨σ, rfl, hσ⟩ := hs
  exact closed_cons hσ (closed_cons hρ hC)

/-- Every abstraction needed by the erased hole has closed domain and codomain. -/
theorem erased_holeTypes_closed (hc : Sig.VecFixed erase) :
    ∀ {Γ Γ' : Ctx} {ρ : RTy} (C : Hole Sig Γ ρ Γ' Ty.t),
      Ty.AllClosed (holeTypes (C.vec erase hc))
  | _, _, _, .hole => by
      rw [Hole.vec]
      exact closed_nil
  | _, _, _, .appL C a => by
      simpa only [Hole.vec, holeTypes_appLBlock] using erased_holeTypes_closed hc C
  | _, _, _, .appR (σ := .rel _) f C => by
      rw [Hole.vec]
      exact erased_holeTypes_closed hc C
  | _, _, _, .appR (σ := .e) _ C => nomatch C
  | _, _, _, .appR (σ := .var _) _ C => nomatch C
  | _, _, _, .lam (σ := σ) (ρ := ρ) C => by
      rw [Hole.vec]
      exact holeTypes_singleton_lamBlock (erase_singleton σ) (erase_rel_closed ρ)
        (C.vec erase hc) (erased_holeTypes_closed hc C)

/-- The full derivation induction, including the recursive logical side proofs
of every Subst occurrence. Its conclusion carries closed support, not merely a
second bare repository derivation. -/
theorem c_closed_support (hSig : ∀ c, (Sig.typeOf c).Closed) :
    ∀ {Ax : AxiomSet Sig}, (∀ a, Ax a → Logical a) →
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ},
      Derivable Ax Δ p →
      ClosedCSupported
        (Hyps.vecG erase (Signature.VecFixed.of_closed hSig erase) Δ)
        (p.vecG1 erase (Signature.VecFixed.of_closed hSig erase))
  | _, _, _, _, _, .hyp h => ClosedCSupported.hyp (List.mem_map_of_mem h)
  | _, hA, _, _, _, .ax (a := a) h => by
      have ha : a = existence_e := hA a h
      subst a
      exact ClosedCSupported.existence
  | _, hA, _, _, _, .andI h k => ClosedCSupported.andI (c_closed_support hSig hA h) (c_closed_support hSig hA k)
  | _, hA, _, _, _, .andE₁ h => ClosedCSupported.andE₁ (c_closed_support hSig hA h)
  | _, hA, _, _, _, .andE₂ h => ClosedCSupported.andE₂ (c_closed_support hSig hA h)
  | _, hA, _, _, _, .orI₁ h => ClosedCSupported.orI₁ (c_closed_support hSig hA h)
  | _, hA, _, _, _, .orI₂ h => ClosedCSupported.orI₂ (c_closed_support hSig hA h)
  | _, hA, _, _, _, .orE h k l =>
      ClosedCSupported.orE (c_closed_support hSig hA h) (c_closed_support hSig hA k) (c_closed_support hSig hA l)
  | _, hA, _, _, _, .notI h k => ClosedCSupported.notI (c_closed_support hSig hA h) (c_closed_support hSig hA k)
  | _, hA, _, _, _, .notE h k => ClosedCSupported.notE (c_closed_support hSig hA h) (c_closed_support hSig hA k)
  | _, _, _, _, _, .em p => ClosedCSupported.em _
  | _, hA, _, _, _, .allE (σ := σ) h a =>
      ClosedCSupported.allEC (σ.vec erase) (erase_singleton σ) (c_closed_support hSig hA h) (a.vecG erase _)
  | _, hA, _, _, _, .allI (σ := σ) h => by
      have h' := c_closed_support hSig hA h
      rw [Hyps.vecG_weaken] at h'
      exact ClosedCSupported.allIC (σ.vec erase) (erase_singleton σ) h'
  | _, hA, _, _, _, .exI (σ := σ) a h =>
      ClosedCSupported.exIC (σ.vec erase) (erase_singleton σ) (a.vecG erase _) (c_closed_support hSig hA h)
  | _, hA, Γ, Δ, _, .exE (σ := σ) (F := F) (r := r) h k => by
      let hc := Signature.VecFixed.of_closed hSig erase
      have k' := c_closed_support hSig hA k
      have e₁ : (Term.app F.weaken (.var .zero) : Formula Sig (σ :: Γ)).vecG1 erase hc
          = Term.appBlock ((F.vecG1 erase hc).rename (Ren.wkBlock (σ.vec erase)))
              (Terms.vars (σ.vec erase) _) := by
        show Term.appBlock ((F.weaken (τ := σ)).vecG1 erase hc) _ = _
        rw [Term.vecG1_weaken]; rfl
      have e₂ : Hyps.vecG erase hc (Term.app F.weaken (.var .zero) :: Hyps.weaken (σ := σ) Δ)
          = Term.appBlock ((F.vecG1 erase hc).rename (Ren.wkBlock (σ.vec erase)))
              (Terms.vars (σ.vec erase) _) :: Hyps.wkBlock (σ.vec erase) (Hyps.vecG erase hc Δ) := by
        show Term.vecG1 erase hc (Term.app F.weaken (.var .zero) : Formula Sig (σ :: Γ)) ::
          Hyps.vecG erase hc (Hyps.weaken (σ := σ) Δ) = _
        rw [e₁, Hyps.vecG_weaken]
      rw [e₂, Term.vecG1_weaken] at k'
      exact ClosedCSupported.exEC (σ.vec erase) (erase_singleton σ) (c_closed_support hSig hA h) k'
  | _, _, _, _, _, .refl (σ := σ) a =>
      ClosedCSupported.reflC (σ.vec erase) (erase_singleton σ) (a.vecG erase _)
  | _, hA, _, _, _, .ll (σ := σ) F h k =>
      ClosedCSupported.llC (σ.vec erase) (erase_singleton σ) (F.vecG1 erase _)
        (c_closed_support hSig hA h) (c_closed_support hSig hA k)
  | _, hA, _, _, _, .conv h c =>
      ClosedCSupported.conv (c_closed_support hSig hA h) (Term.vecG_conv erase _ c).head1
  | Ax, hA, _, _, _, .subst C h k l => by
      let hc := Signature.VecFixed.of_closed hSig erase
      have h' := c_closed_support hSig (Ax := Ax.logical) (fun _ ha => ha.2) h
      have k' := c_closed_support hSig (Ax := Ax.logical) (fun _ ha => ha.2) k
      have l' := c_closed_support hSig hA l
      rw [Hole.vecG1_plug] at l' ⊢
      exact ClosedCSupported.subst (C.vec erase hc) (erased_holeTypes_closed hc C) h' k' l'

/-! ## Recovery of the original closed language

The heterogeneous equalities in this section concern Lean's indexed syntax,
not object-language identity or logical equivalence. The constructor lemmas
eliminate only metalinguistic context/type equalities. In particular, there is
no object-level extensionality principle in the fixed-sentence argument.
-/

theorem ctx_vec_closed (θ : Assign) : ∀ {Γ : Ctx}, Ty.AllClosed Γ → Ctx.vec θ Γ = Γ
  | [], _ => rfl
  | σ :: Γ, hΓ => by
      rw [Ctx.vec_cons, Ty.vec_closed θ hΓ.head, ctx_vec_closed θ hΓ.tail]

private theorem vars_single_heq {Γ Γ' : Ctx} {σs : List Ty} {σ : Ty}
    (hΓ : Γ = Γ') (hs : σs = [σ]) :
    HEq (Terms.vars (Sig := Sig) σs Γ)
      (Terms.single (Sig := Sig) (.var (.zero : Var (σ :: Γ') σ))) := by
  cases hΓ
  cases hs
  rfl

private theorem rename_single_succ_heq {Γ Γ' : Ctx} {σs τs : List Ty} {σ τ : Ty}
    (hΓ : Γ = Γ') (hσ : σs = [σ]) (hτ : τs = [τ])
    (as : Terms Sig Γ σs) (v : Var Γ' σ)
    (h : HEq as (Terms.single (Sig := Sig) (Term.var v))) :
    HEq (as.rename (Ren.wkBlock τs)) (Terms.single (Sig := Sig) (Term.var (.succ (τ := τ) v))) := by
  cases hΓ
  cases hσ
  cases hτ
  cases (eq_of_heq h)
  rfl

private theorem var_type_mem : ∀ {Γ : Ctx} {σ : Ty}, Var Γ σ → σ ∈ Γ
  | _, _, .zero => List.mem_cons_self ..
  | _, _, .succ v => List.mem_cons_of_mem _ (var_type_mem v)

private theorem var_vec_closed_heq (θ : Assign) :
    ∀ {Γ : Ctx} {σ : Ty} (v : Var Γ σ), Ty.AllClosed Γ →
      HEq (Var.vec (Sig := Sig) θ v) (Terms.single (Sig := Sig) (Term.var v))
  | _ :: _, _, .zero, hΓ =>
      vars_single_heq (ctx_vec_closed θ hΓ.tail) (Ty.vec_closed θ hΓ.head)
  | τ :: Γ, σ, .succ v, hΓ => by
      rw [Var.vec_succ]
      have hσ : σ.Closed := hΓ.tail σ (var_type_mem v)
      exact rename_single_succ_heq (ctx_vec_closed θ hΓ.tail)
        (Ty.vec_closed θ hσ) (Ty.vec_closed θ hΓ.head) (Var.vec θ v) v
        (var_vec_closed_heq θ v hΓ.tail)

private theorem const_vec_heq {Γ Γ' : Ctx} {σs : List Ty} (hΓ : Γ = Γ')
    (c : Sig.Const) (hs : [Sig.typeOf c] = σs) :
    HEq (Terms.cast hs (Terms.single (Term.const (Γ := Γ) c)))
      (Terms.single (Term.const (Γ := Γ') c)) := by
  cases hΓ
  cases hs
  rfl

private theorem single_param_heq {I : Type} (T : I → Ty)
    (mk : ∀ Γ : Ctx, (i : I) → Term Sig Γ (T i))
    {Γ Γ' : Ctx} {i j : I} (hΓ : Γ = Γ') (hi : i = j) :
    HEq (Terms.single (mk Γ i)) (Terms.single (mk Γ' j)) := by
  cases hΓ
  cases hi
  rfl

private theorem appBlock_single_heq {Γ Γ' : Ctx} {σs : List Ty} {σ : Ty} {ρ ρ' : RTy}
    (hΓ : Γ = Γ') (hs : σs = [σ]) (hρ : ρ = ρ')
    (fs : Terms Sig Γ [Ty.rel (σs ⇒* ρ)]) (as : Terms Sig Γ σs)
    (f : Term Sig Γ' (σ ⇒ ρ')) (a : Term Sig Γ' σ)
    (hf : HEq fs (Terms.single f)) (ha : HEq as (Terms.single a)) :
    HEq (Terms.single (Term.appBlock fs.head1 as)) (Terms.single (Term.app f a)) := by
  cases hΓ
  cases hs
  cases hρ
  cases (eq_of_heq hf)
  cases (eq_of_heq ha)
  rfl

private theorem lamBlock_single_heq {Γ Γ' : Ctx} {σs : List Ty} {σ : Ty} {ρ ρ' : RTy}
    (hΓ : Γ = Γ') (hs : σs = [σ]) (hρ : ρ = ρ')
    (bs : Terms Sig (Ctx.block σs Γ) [Ty.rel ρ]) (b : Term Sig (σ :: Γ') ρ')
    (hb : HEq bs (Terms.single b)) :
    HEq (Terms.single (Term.lamBlock σs bs.head1)) (Terms.single (Term.lam b)) := by
  cases hΓ
  cases hs
  cases hρ
  cases (eq_of_heq hb)
  rfl

/-- Generic vectorization fixes every closed-types term in a closed context.
HEq permits the context and result-type indices to be shown fixed separately. -/
theorem vecG_closed_heq (θ : Assign) (hc : Sig.VecFixed θ) :
    ∀ {Γ : Ctx} {σ : Ty} (a : Term Sig Γ σ), Ty.AllClosed Γ → a.closedTypes = true →
      HEq (a.vecG θ hc) (Terms.single a)
  | _, _, .var v, hΓ, _ => var_vec_closed_heq θ v hΓ
  | _, _, .const c, hΓ, _ => const_vec_heq (ctx_vec_closed θ hΓ) c (hc c).symm
  | _, _, .app (σ := σ) (ρ := ρ) f a, hΓ, ha => by
      have hfa : f.closedTypes = true ∧ a.closedTypes = true := by
        simpa only [Term.closedTypes, Bool.and_eq_true] using ha
      exact appBlock_single_heq (ctx_vec_closed θ hΓ)
        (Ty.vec_closed θ (Term.closed_of_closedTypes hfa.2))
        (RTy.vec_closed θ (Term.closed_of_closedTypes hfa.1).2)
        (f.vecG θ hc) (a.vecG θ hc) f a
        (vecG_closed_heq θ hc f hΓ hfa.1) (vecG_closed_heq θ hc a hΓ hfa.2)
  | _, _, .lam (σ := σ) b, hΓ, hb => by
      have hb' : σ.Closed ∧ b.closedTypes = true := by
        simpa only [Term.closedTypes, Bool.and_eq_true, decide_eq_true_eq] using hb
      exact lamBlock_single_heq (ctx_vec_closed θ hΓ) (Ty.vec_closed θ hb'.1)
        (RTy.vec_closed θ (Term.closed_of_closedTypes hb'.2))
        (b.vecG θ hc) b (vecG_closed_heq θ hc b (closed_cons hb'.1 hΓ) hb'.2)
  | _, _, .and, hΓ, _ =>
      single_param_heq (Sig := Sig) (fun _ : Unit => Ty.rel (RTy.t ⇒ RTy.t ⇒ RTy.t))
        (fun _ _ => .and) (ctx_vec_closed θ hΓ) (rfl : () = ())
  | _, _, .or, hΓ, _ =>
      single_param_heq (Sig := Sig) (fun _ : Unit => Ty.rel (RTy.t ⇒ RTy.t ⇒ RTy.t))
        (fun _ _ => .or) (ctx_vec_closed θ hΓ) (rfl : () = ())
  | _, _, .not, hΓ, _ =>
      single_param_heq (Sig := Sig) (fun _ : Unit => Ty.rel (RTy.t ⇒ RTy.t))
        (fun _ _ => .not) (ctx_vec_closed θ hΓ) (rfl : () = ())
  | _, _, .all σ, hΓ, hσ => by
      have hσ' : σ.Closed := by simpa only [Term.closedTypes, decide_eq_true_eq] using hσ
      exact single_param_heq (fun σs => Ty.rel ((σs ⇒* .t) ⇒ .t))
        (fun _ σs => Term.allC σs) (ctx_vec_closed θ hΓ) (Ty.vec_closed θ hσ')
  | _, _, .ex σ, hΓ, hσ => by
      have hσ' : σ.Closed := by simpa only [Term.closedTypes, decide_eq_true_eq] using hσ
      exact single_param_heq (fun σs => Ty.rel ((σs ⇒* .t) ⇒ .t))
        (fun _ σs => Term.exC σs) (ctx_vec_closed θ hΓ) (Ty.vec_closed θ hσ')
  | _, _, .eq σ, hΓ, hσ => by
      have hσ' : σ.Closed := by simpa only [Term.closedTypes, decide_eq_true_eq] using hσ
      exact single_param_heq (fun σs => Ty.rel (σs ⇒* (σs ⇒* .t)))
        (fun _ σs => Term.eqC σs) (ctx_vec_closed θ hΓ) (Ty.vec_closed θ hσ')
  | _, _, .constR ρ, hΓ, hρ => by
      have hρ' : ρ.Closed := by simpa only [Term.closedTypes, decide_eq_true_eq] using hρ
      exact single_param_heq (fun ρ : RTy => Ty.rel (RTy.t ⇒ ρ)) (fun _ ρ => .constR ρ)
        (ctx_vec_closed θ hΓ) (RTy.vec_closed θ hρ')
  | _, _, .negR ρ, hΓ, hρ => by
      have hρ' : ρ.Closed := by simpa only [Term.closedTypes, decide_eq_true_eq] using hρ
      exact single_param_heq (fun ρ : RTy => Ty.rel (ρ ⇒ ρ)) (fun _ ρ => .negR ρ)
        (ctx_vec_closed θ hΓ) (RTy.vec_closed θ hρ')
  | _, _, .andR ρ, hΓ, hρ => by
      have hρ' : ρ.Closed := by simpa only [Term.closedTypes, decide_eq_true_eq] using hρ
      exact single_param_heq (fun ρ : RTy => Ty.rel (ρ ⇒ ρ ⇒ ρ)) (fun _ ρ => .andR ρ)
        (ctx_vec_closed θ hΓ) (RTy.vec_closed θ hρ')
  | _, _, .orR ρ, hΓ, hρ => by
      have hρ' : ρ.Closed := by simpa only [Term.closedTypes, decide_eq_true_eq] using hρ
      exact single_param_heq (fun ρ : RTy => Ty.rel (ρ ⇒ ρ ⇒ ρ)) (fun _ ρ => .orR ρ)
        (ctx_vec_closed θ hΓ) (RTy.vec_closed θ hρ')
  | _, _, .coextR ρ, hΓ, hρ => by
      have hρ' : ρ.Closed := by simpa only [Term.closedTypes, decide_eq_true_eq] using hρ
      exact single_param_heq (fun ρ : RTy => Ty.rel (ρ ⇒ ρ ⇒ RTy.t)) (fun _ ρ => .coextR ρ)
        (ctx_vec_closed θ hΓ) (RTy.vec_closed θ hρ')
  | _, _, .boxR ρ, hΓ, hρ => by
      have hρ' : ρ.Closed := by simpa only [Term.closedTypes, decide_eq_true_eq] using hρ
      exact single_param_heq (fun ρ : RTy => Ty.rel (ρ ⇒ ρ)) (fun _ ρ => .boxR ρ)
        (ctx_vec_closed θ hΓ) (RTy.vec_closed θ hρ')
  | _, _, .inclR ρ, hΓ, hρ => by
      have hρ' : ρ.Closed := by simpa only [Term.closedTypes, decide_eq_true_eq] using hρ
      exact single_param_heq (fun ρ : RTy => Ty.rel (ρ ⇒ ρ ⇒ RTy.t)) (fun _ ρ => .inclR ρ)
        (ctx_vec_closed θ hΓ) (RTy.vec_closed θ hρ')

private theorem formula_head_heq {Γ Γ' : Ctx} (hΓ : Γ = Γ')
    (as : Terms Sig Γ [Ty.t]) (p : Formula Sig Γ')
    (h : HEq as (Terms.single p)) : HEq as.head1 p := by
  cases hΓ
  cases (eq_of_heq h)
  rfl

theorem vecG1_closed_heq (θ : Assign) (hc : Sig.VecFixed θ)
    {Γ : Ctx} (hΓ : Ty.AllClosed Γ) (p : Formula Sig Γ) (hp : p.closedTypes = true) :
    HEq (p.vecG1 θ hc) p :=
  formula_head_heq (ctx_vec_closed θ hΓ) (p.vecG θ hc) p (vecG_closed_heq θ hc p hΓ hp)

/-- Singleton erasure recovers a closed-types sentence as the same term. -/
theorem erase_sentence_fixed (hSig : ∀ c, (Sig.typeOf c).Closed)
    (p : Sentence Sig) (hp : p.closedTypes = true) :
    p.vecG1 erase (Signature.VecFixed.of_closed hSig erase) = p :=
  eq_of_heq (vecG1_closed_heq erase _ closed_nil p hp)

private theorem list_cons_heq {A B : Type} (hAB : A = B) {a : A} {b : B}
    {as : List A} {bs : List B} (hab : HEq a b) (hs : HEq as bs) :
    HEq (a :: as) (b :: bs) := by
  cases hAB
  cases (eq_of_heq hab)
  cases (eq_of_heq hs)
  rfl

private theorem list_nil_heq {A B : Type} (hAB : A = B) :
    HEq ([] : List A) ([] : List B) := by
  cases hAB
  rfl

theorem hyps_vecG_closed_heq (θ : Assign) (hc : Sig.VecFixed θ)
    {Γ : Ctx} (hΓ : Ty.AllClosed Γ) :
    ∀ Δ : List (Formula Sig Γ), (∀ p ∈ Δ, p.closedTypes = true) →
      HEq (Hyps.vecG θ hc Δ) Δ
  | [], _ => list_nil_heq (congrArg (fun Γ => Formula Sig Γ) (ctx_vec_closed θ hΓ))
  | p :: Δ, hΔ =>
      list_cons_heq (congrArg (fun Γ => Formula Sig Γ) (ctx_vec_closed θ hΓ))
        (vecG1_closed_heq θ hc hΓ p (hΔ p (List.mem_cons_self ..)))
        (hyps_vecG_closed_heq θ hc hΓ Δ (fun q hq => hΔ q (List.mem_cons_of_mem _ hq)))

private theorem closedCSupported_heq {Γ Γ' : Ctx}
    {Δ : List (Formula Sig Γ)} {Δ' : List (Formula Sig Γ')}
    {p : Formula Sig Γ} {p' : Formula Sig Γ'} (hΓ : Γ = Γ')
    (hΔ : HEq Δ Δ') (hp : HEq p p') (h : ClosedCSupported Δ p) :
    ClosedCSupported Δ' p' := by
  cases hΓ
  cases (eq_of_heq hΔ)
  cases (eq_of_heq hp)
  exact h

/-- Every actual C proof of a sentence in the fixed closed language has finite
closed rule support, including all recursively nested Subst side derivations. -/
theorem c_closed_theorem (hSig : ∀ c, (Sig.typeOf c).Closed)
    {p : Sentence Sig} (hp : p.closedTypes = true) (h : C.Theorem p) :
    ClosedCSupported [] p := by
  have h' := c_closed_support hSig (fun _ ha => ha) h
  rw [erase_sentence_fixed hSig p hp] at h'
  exact h'

/-- The same recovery for arbitrary finite closed contexts and closed-types
hypotheses. The result is the original sequent, not a translated substitute. -/
theorem c_closed_sequent (hSig : ∀ c, (Sig.typeOf c).Closed)
    {Γ : Ctx} (hΓ : Ty.AllClosed Γ) {Δ : List (Formula Sig Γ)}
    (hΔ : ∀ p ∈ Δ, p.closedTypes = true) {p : Formula Sig Γ}
    (hp : p.closedTypes = true) (h : Derivable C.axioms Δ p) :
    ClosedCSupported Δ p :=
  closedCSupported_heq (ctx_vec_closed erase hΓ)
    (hyps_vecG_closed_heq erase _ hΓ Δ hΔ) (vecG1_closed_heq erase _ hΓ p hp)
    (c_closed_support hSig (fun _ ha => ha) h)

end Classicism.Research.FullTypedLogicalSeparationH

#print axioms Classicism.Research.FullTypedLogicalSeparationH.c_closed_theorem
#print axioms Classicism.Research.FullTypedLogicalSeparationH.c_closed_sequent

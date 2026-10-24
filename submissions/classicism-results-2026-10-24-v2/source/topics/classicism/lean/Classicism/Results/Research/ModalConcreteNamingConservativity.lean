import Classicism.Results.Research.ModalConcreteProofTransport

/-!
# Conservative closed naming in the concrete comprehension calculus

The guard is first eliminated in the same signature, where it is a closed
formula. Its lift to an eigenvariable context is exactly its weakening.
The subsequent, already proved concrete syntax/proof translation replaces
the distinguished constant by a fresh parameter. Existential elimination
then recovers the old-signature conclusion. Optional old premises remain
local throughout; only global stability proofs are necessitated.

The theorem has genuine object-proof inputs for stability and existence.
It does not assume conservativity, arbitrary-proof preservation or choice.
-/

namespace Classicism.Research.ModalFreshConstantSyntax
open Classicism.Meta
open Classicism.Research.ModalComprehensionConcreteSyntax
open Classicism.Research.ModalComprehensionRepresentation (diagram)

variable {C : Ty → Type}

def emptyRen (Γ : Ctx) : Ren [] Γ := fun v => nomatch v

def closedAt (g : Term C [] Ty.t) (Γ : Ctx) : Term C Γ Ty.t :=
  g.rename (emptyRen Γ)

theorem closedAt_wk (g : Term C [] Ty.t) (Γ : Ctx) (σ : Ty) :
    (closedAt g Γ).wk (σ := σ) = closedAt g (σ :: Γ) := by
  have h : @Eq (Ren [] (σ :: Γ))
      (Ren.comp (Ren.shift (σ := σ)) (emptyRen Γ)) (emptyRen (σ :: Γ)) := by
    funext τ v
    exact nomatch v
  simp only [closedAt, Term.wk, Term.rename_comp, h]

theorem closedAt_nil (g : Term C [] Ty.t) : closedAt g [] = g := by
  have h : @Eq (Ren [] []) (emptyRen []) Ren.id := by
    funext τ v
    exact nomatch v
  rw [closedAt, h, Term.rename_id]

theorem translate_as_rename {Γ Θ σ} (r : Ren Γ Θ) (t : Term C Γ σ) :
    translate (fun c => Term.const c) (fun v => Term.var (r v)) t = t.rename r := by
  have hl {Γ Θ υ} (r : Ren Γ Θ) :
      @Eq (Sub C (υ :: Γ) (υ :: Θ))
        (Sub.lift (fun {τ} (v : Var Γ τ) => Term.var (Const := C) (r v)))
        (fun {τ} (v : Var (υ :: Γ) τ) => Term.var (Ren.lift r v)) := by
    funext τ v
    cases v <;> rfl
  induction t generalizing Θ <;>
    simp_all only [translate, Term.rename, hl, Term.wk]

theorem base_derives_rename {Γ Δ p}
    (proof : Derives C (noAdditionalAxioms C) Γ Δ p)
    {Θ} (r : Ren Γ Θ) :
    Derives C (noAdditionalAxioms C) Θ
      (Δ.map (fun p => p.rename r)) (p.rename r) := by
  have hf : (translate (fun c => Term.const c) (fun v => Term.var (r v)) :
      Term C Γ Ty.t → Term C Θ Ty.t) = (fun q => q.rename r) := by
    funext q
    exact translate_as_rename r q
  have h := base_derives_translate proof (fun c => .const c) (fun v => .var (r v))
  rw [hf] at h
  exact h

/-- The single new closed global axiom, read in any variable context. -/
def DefinitionAx (g : Term C [] Ty.t) : Axioms C :=
  fun Γ p => p = closedAt g Γ

private theorem swap_front {Γ Δ p q r}
    (h : Derives C (noAdditionalAxioms C) Γ (p :: q :: Δ) r) :
    Derives C (noAdditionalAxioms C) Γ (q :: p :: Δ) r := by
  apply Derives.weaken ?_ h
  intro a ha
  rcases List.mem_cons.mp ha with h | h
  · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl h))
  · rcases List.mem_cons.mp h with h | h
    · exact List.mem_cons.mpr (Or.inl h)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

/-- The guarded induction for the actual concrete proof system. -/
theorem concrete_guarded {g : Term C [] Ty.t}
    (stable : Derives C (noAdditionalAxioms C) [] [] (.imp g g.box))
    {Γ Δ p} (proof : Derives C (DefinitionAx g) Γ Δ p) :
    Derives C (noAdditionalAxioms C) Γ (closedAt g Γ :: Δ) p := by
  have stability (Γ : Ctx) : Derives C (noAdditionalAxioms C) Γ []
      (.imp (closedAt g Γ) (closedAt g Γ).box) := by
    simpa only [closedAt, Term.rename, Term.box, List.map_nil] using
      base_derives_rename stable (emptyRen Γ)
  induction proof with
  | hyp h => exact .hyp (List.mem_cons_of_mem _ h)
  | ax h =>
      change _ = closedAt g _ at h
      cases h
      exact .hyp₀
  | weaken h _ ih =>
      apply Derives.weaken ?_ ih
      intro a ha
      rcases List.mem_cons.mp ha with ha | ha
      · exact List.mem_cons.mpr (Or.inl ha)
      · exact List.mem_cons_of_mem _ (h a ha)
  | impI _ ih => exact .impI (swap_front ih)
  | impE _ _ ihp ihq => exact .impE ihp ihq
  | iffI _ _ ihp ihq => exact .iffI ihp ihq
  | iffE₁ _ _ ihp ihq => exact .iffE₁ ihp ihq
  | iffE₂ _ _ ihp ihq => exact .iffE₂ ihp ihq
  | topI => exact .topI
  | eqRefl a => exact .eqRefl a
  | eqSymm _ ih => exact .eqSymm ih
  | eqTrans _ _ ihp ihq => exact .eqTrans ihp ihq
  | eqApp _ _ ihp ihq => exact .eqApp ihp ihq
  | eqRight a _ ih => exact .eqRight a ih
  | eqTruth _ _ ihp ihq => exact .eqTruth ihp ihq
  | eqSubst P a b _ _ ihEq ihP => exact .eqSubst P a b ihEq ihP
  | allI _ ih =>
      apply Derives.allI
      simpa only [List.map_cons, closedAt_wk] using ih
  | allE a _ ih => exact .allE a ih
  | exI a _ ih => exact .exI a ih
  | exE _ _ ihEx ihQ =>
      apply Derives.exE ihEx
      simpa only [List.map_cons, closedAt_wk] using swap_front ihQ
  | nec _ ih =>
      have guarded := Derives.impI ih
      have necessary := Derives.nec guarded
      exact .K necessary.lift (.impE (stability _).lift .hyp₀)
  | K _ _ ihp ihq => exact .K ihp ihq
  | intensionality ρ a b _ ih => exact .intensionality ρ a b ih
  | comprehension A => exact .comprehension A

/-- Add the new constant to the signature without changing an old term. -/
def embedOld {κ Γ σ} : Term C Γ σ → Term (FreshConst C κ) Γ σ
  | .var v => .var v
  | .const c => .const (.old c)
  | .app f a => .app (embedOld f) (embedOld a)
  | .top => .top
  | .imp p q => .imp (embedOld p) (embedOld q)
  | .iff p q => .iff (embedOld p) (embedOld q)
  | .eq a b => .eq (embedOld a) (embedOld b)
  | .boxOp => .boxOp
  | .all p => .all (embedOld p)
  | .ex p => .ex (embedOld p)

theorem translate_embedOld {D : Ty → Type} {κ Γ Θ σ}
    (cs : ConstImage (FreshConst C κ) D Θ) (vs : Sub D Γ Θ) (t : Term C Γ σ) :
    translate cs vs (embedOld t) = translate (fun c => cs (.old c)) vs t := by
  induction t generalizing Θ <;> simp_all only [embedOld, translate]

theorem replaceFresh_embedOld {κ Γ σ} (t : Term C Γ σ) :
    replaceFresh (embedOld (κ := κ) t) = t.wk := by
  unfold replaceFresh
  rw [translate_embedOld]
  exact translate_as_rename Ren.shift t

theorem replaceFresh_imp {κ Γ} (p q : Term (FreshConst C κ) Γ Ty.t) :
    replaceFresh (.imp p q) = .imp (replaceFresh p) (replaceFresh q) := rfl

theorem replaceFresh_box {κ Γ} (p : Term (FreshConst C κ) Γ Ty.t) :
    replaceFresh p.box = (replaceFresh p).box := rfl

/-- Naming the bound argument of an old matrix and subsequently replacing
that name by the fresh parameter recovers the original matrix exactly. -/
theorem replaceFresh_inst_embedOld {κ Γ σ} (P : Term C (κ :: Γ) σ) :
    replaceFresh ((embedOld P).inst (.const .fresh)) = P := by
  unfold replaceFresh
  rw [translate_inst, translate_embedOld]
  have hv :
      @Eq (Sub C (κ :: Γ) (κ :: κ :: Γ))
        (Sub.lift (fun {τ} (v : Var Γ τ) => Term.var (Const := C) (Var.succ v)))
        (fun {τ} (v : Var (κ :: Γ) τ) =>
          Term.var (Ren.lift (Ren.shift (σ := κ)) v)) := by
    funext τ v
    cases v <;> rfl
  change (translate (fun c => Term.const c)
    (Sub.lift (fun v => Term.var (Var.succ v))) P).inst (.var .zero) = P
  rw [hv, translate_as_rename]
  exact Derives.instantiate_at_fresh P

/-- Removing the global definition yields a local guarded consequence in
the original signature, with the new parameter as an eigenvariable. -/
theorem concrete_named_guarded {κ} (g : Term (FreshConst C κ) [] Ty.t)
    (stable : Derives (FreshConst C κ) (noAdditionalAxioms (FreshConst C κ))
      [] [] (.imp g g.box))
    {Δ : List (Term C [] Ty.t)} {A : Term C [] Ty.t}
    (proof : Derives (FreshConst C κ) (DefinitionAx g) []
      (Δ.map embedOld) (embedOld A)) :
    Derives C (noAdditionalAxioms C) [κ] (Δ.map (fun p => p.wk))
      (.imp (replaceFresh g) A.wk) := by
  have guarded := Derives.impI (concrete_guarded stable proof)
  have transformed := base_derives_replaceFresh guarded
  simpa only [closedAt_nil, replaceFresh_imp, List.map_map, Function.comp_def,
    replaceFresh_embedOld] using transformed

/-- Generalization is legitimate over the fresh parameter, with every old
optional premise weakened into its eigenvariable context. -/
theorem concrete_named_universal {κ} (g : Term (FreshConst C κ) [] Ty.t)
    (stable : Derives (FreshConst C κ) (noAdditionalAxioms (FreshConst C κ))
      [] [] (.imp g g.box))
    {Δ : List (Term C [] Ty.t)} {A : Term C [] Ty.t}
    (proof : Derives (FreshConst C κ) (DefinitionAx g) []
      (Δ.map embedOld) (embedOld A)) :
    Derives C (noAdditionalAxioms C) [] Δ
      (.all (.imp (replaceFresh g) A.wk)) :=
  .allI (concrete_named_guarded g stable proof)

/-- Concrete closed-name conservativity. The existential premise is an
actual base derivation, normally supplied by strong comprehension after
identifying its code with the replacement of g. Neither optional premises
nor the defining axiom are necessitated in the base derivation. -/
theorem concrete_named_consequence_conservative {κ}
    (g : Term (FreshConst C κ) [] Ty.t)
    (stable : Derives (FreshConst C κ) (noAdditionalAxioms (FreshConst C κ))
      [] [] (.imp g g.box))
    (existence : Derives C (noAdditionalAxioms C) [] []
      (.ex (replaceFresh g)))
    {Δ : List (Term C [] Ty.t)} {A : Term C [] Ty.t}
    (proof : Derives (FreshConst C κ) (DefinitionAx g) []
      (Δ.map embedOld) (embedOld A)) :
    Derives C (noAdditionalAxioms C) [] Δ A := by
  have guarded := concrete_named_guarded g stable proof
  apply Derives.exE existence.lift
  have hg : Derives C (noAdditionalAxioms C) [κ]
      (replaceFresh g :: Δ.map (fun p => p.wk))
      (.imp (replaceFresh g) A.wk) :=
    .weaken (fun _ h => List.mem_cons_of_mem _ h) guarded
  exact .impE hg .hyp₀

/-- The closed defining axiom for the new representative constant. Every
parameter of the intended template has already been captured in A. -/
def representationDefinition {ρ : RTy} (A : Body C [] ρ) :
    Term (FreshConst C ρ) [] Ty.t :=
  Term.box ((embedOld (diagram (A.rename Ren.shift) (.var .zero))).inst (.const .fresh))

/-- Strong comprehension discharges both inputs of concrete closed naming:
the definition is boxed, hence persistent by the derived modal-four theorem;
after fresh replacement its existential closure is the actual SC instance.
Only a derivation in the named extension remains as input. -/
theorem representation_name_conservative {ρ : RTy} (A : Body C [] ρ)
    {Δ : List (Term C [] Ty.t)} {P : Term C [] Ty.t}
    (proof : Derives (FreshConst C ρ) (DefinitionAx (representationDefinition A)) []
      (Δ.map embedOld) (embedOld P)) :
    Derives C (noAdditionalAxioms C) [] Δ P := by
  apply concrete_named_consequence_conservative (representationDefinition A) ?_ ?_ proof
  · exact (calculus (FreshConst C ρ) (noAdditionalAxioms (FreshConst C ρ))).modal_four
      ((embedOld (diagram (A.rename Ren.shift) (.var .zero))).inst (.const .fresh))
  · rw [representationDefinition, replaceFresh_box]
    have he := replaceFresh_inst_embedOld
      (diagram (A.rename Ren.shift) (.var .zero) : Term C [ρ] Ty.t)
    exact he.symm ▸ (Derives.comprehension A :
      Derives C (noAdditionalAxioms C) [] [] (.ex (Body.code A)))

#print axioms concrete_guarded
#print axioms concrete_named_guarded
#print axioms concrete_named_universal
#print axioms concrete_named_consequence_conservative
#print axioms representation_name_conservative

end Classicism.Research.ModalFreshConstantSyntax

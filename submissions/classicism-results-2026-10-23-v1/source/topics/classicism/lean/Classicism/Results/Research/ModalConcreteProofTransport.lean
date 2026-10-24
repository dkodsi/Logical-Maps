import Classicism.Results.Research.ModalFreshConstantSyntax
import Classicism.Results.Research.ModalComprehensionConcreteCalculus

/-!
# Proof transport under concrete constant interpretation

The source and target are the explicit lambda-free derivation calculi.
Constants are mapped to admitted target terms; variables are substituted,
with both maps lifted beneath binders. Body-code transport and preservation
of every fixed derivation constructor, including SC, I, UI and theorem-only
Nec, are proved. Additional global axioms require an axiom-instance map;
the unextended base has no such extra obligation. Local premises are mapped
as a list and are never promoted to global axioms.

This is proof transport, not yet the final conservative-name elimination
theorem for this concrete calculus or its equivalence with the full C syntax.
-/

namespace Classicism.Research.ModalFreshConstantSyntax
open Classicism.Meta
open Classicism.Research.ModalComprehensionConcreteSyntax
open Classicism.Research.ModalComprehensionRepresentation (diagram)

variable {C D : Ty → Type}

theorem translate_inst {Γ Θ σ τ} (cs : ConstImage C D Θ)
    (vs : Sub D Γ Θ) (P : Term C (σ :: Γ) τ) (a : Term C Γ σ) :
    translate cs vs (P.inst a) =
      (translate (fun c => (cs c).wk) (Sub.lift vs) P).inst (translate cs vs a) := by
  simp only [Term.inst, translate_subst, subst_translate]
  have hc :
      @Eq (ConstImage C D Θ)
        (fun {υ} (c : C υ) => ((cs c).wk (σ := σ)).subst
          (Sub.cons (translate cs vs a) Sub.id)) cs := by
    funext υ c
    exact Term.inst_wk (cs c) (translate cs vs a)
  rw [hc]
  have hv :
      @Eq (Sub D (σ :: Γ) Θ)
        (fun {υ} (v : Var (σ :: Γ) υ) => translate cs vs (Sub.cons a Sub.id v))
        (fun {υ} (v : Var (σ :: Γ) υ) => (Sub.lift vs v).subst
          (Sub.cons (translate cs vs a) Sub.id)) := by
    funext υ v
    cases v with
    | zero => rfl
    | succ v => exact (Term.inst_wk (vs v) (translate cs vs a)).symm
  rw [hv]

def translateBody {Γ Δ} {ρ : RTy} (cs : ConstImage C D Δ) (vs : Sub D Γ Δ) :
    Body C Γ ρ → Body D Δ ρ
  | .atom p => .atom (translate cs vs p)
  | .bind A => .bind (translateBody (fun c => (cs c).wk) (Sub.lift vs) A)

theorem rename_translateBody {Γ Δ Θ} {ρ : RTy} (cs : ConstImage C D Δ)
    (vs : Sub D Γ Δ) (r : Ren Δ Θ) (A : Body C Γ ρ) :
    (translateBody cs vs A).rename r =
      translateBody (fun c => (cs c).rename r) (fun v => (vs v).rename r) A := by
  have hl {Γ Δ Θ υ} (s : Sub D Γ Δ) (r : Ren Δ Θ) :
      @Eq (Sub D (υ :: Γ) (υ :: Θ))
        (fun {τ} (v : Var (υ :: Γ) τ) => (Sub.lift s v).rename (Ren.lift r))
        (Sub.lift (fun v => (s v).rename r)) := by
    funext τ v
    cases v with
    | zero => rfl
    | succ v => exact Term.rename_wk r (s v)
  have hc {Δ Θ υ} (cs : ConstImage C D Δ) (r : Ren Δ Θ) :
      @Eq (ConstImage C D (υ :: Θ))
        (fun {τ} (c : C τ) => ((cs c).wk (σ := υ)).rename (Ren.lift r))
        (fun c => ((cs c).rename r).wk) := by
    funext τ c
    exact Term.rename_wk r (cs c)
  induction A generalizing Δ Θ with
  | atom p =>
      exact congrArg (ModalComprehensionRepresentation.AdmittedBody.atom
        (L := language D)) (rename_translate cs vs r p)
  | bind A ih =>
      change ModalComprehensionRepresentation.AdmittedBody.bind
          (Body.rename (Ren.lift r)
            (translateBody (fun c => (cs c).wk) (Sub.lift vs) A)) =
        ModalComprehensionRepresentation.AdmittedBody.bind
          (translateBody (fun c => ((cs c).rename r).wk)
            (Sub.lift (fun v => (vs v).rename r)) A)
      rw [ih, hl, hc]

theorem translateBody_rename {Γ Δ Θ} {ρ : RTy} (cs : ConstImage C D Θ)
    (vs : Sub D Δ Θ) (r : Ren Γ Δ) (A : Body C Γ ρ) :
    translateBody cs vs (A.rename r) = translateBody cs (fun v => vs (r v)) A := by
  have hl {Γ Δ Θ υ} (vs : Sub D Δ Θ) (r : Ren Γ Δ) :
      @Eq (Sub D (υ :: Γ) (υ :: Θ))
        (fun {τ} (v : Var (υ :: Γ) τ) => Sub.lift vs (Ren.lift r v))
        (Sub.lift (fun v => vs (r v))) := by
    funext τ v
    cases v <;> rfl
  induction A generalizing Δ Θ with
  | atom p =>
      exact congrArg (ModalComprehensionRepresentation.AdmittedBody.atom
        (L := language D)) (translate_rename cs vs r p)
  | bind A ih =>
      change ModalComprehensionRepresentation.AdmittedBody.bind
          (translateBody (fun c => (cs c).wk) (Sub.lift vs)
            (Body.rename (Ren.lift r) A)) =
        ModalComprehensionRepresentation.AdmittedBody.bind
          (translateBody (fun c => (cs c).wk) (Sub.lift (fun v => vs (r v))) A)
      rw [ih, hl]

theorem translateBody_wk {Γ Δ σ} {ρ : RTy} (cs : ConstImage C D Δ)
    (vs : Sub D Γ Δ) (A : Body C Γ ρ) :
    translateBody (fun c => (cs c).wk) (Sub.lift vs)
      (A.rename (Ren.shift (σ := σ))) =
      (translateBody cs vs A).rename Ren.shift := by
  simp only [translateBody_rename, rename_translateBody, Term.wk]
  rfl

theorem translate_diagram {Γ Δ} {ρ : RTy} (cs : ConstImage C D Δ)
    (vs : Sub D Γ Δ) (A : Body C Γ ρ) (H : Term C Γ ρ) :
    translate cs vs (diagram A H) =
      diagram (translateBody cs vs A) (translate cs vs H) := by
  induction A generalizing Δ with
  | atom p => rfl
  | bind A ih =>
      change Term.all (translate (fun c => (cs c).wk) (Sub.lift vs)
        (diagram A (Term.app H.wk (Term.var .zero)))) =
        Term.all (diagram (translateBody (fun c => (cs c).wk) (Sub.lift vs) A)
          (Term.app (translate cs vs H).wk (Term.var .zero)))
      apply congrArg Term.all
      rw [ih]
      simp only [translate, translate_wk, Sub.lift]
      rfl

/-- The exact SC matrix, including its new representative binder, survives
constant interpretation. Hence SC transport uses an actual target instance. -/
theorem translate_body_code {Γ Δ} {ρ : RTy} (cs : ConstImage C D Δ)
    (vs : Sub D Γ Δ) (A : Body C Γ ρ) :
    translate (fun c => (cs c).wk) (Sub.lift vs) (Body.code A) =
      Body.code (translateBody cs vs A) := by
  simp only [Body.code, Term.box, translate, translate_diagram, translateBody_wk, Sub.lift]

/-- Every fixed inference rule is transported by induction. Only additional
global axiom instances need a supplied map. `Ax` and `Ay` are syntactic
axiom sets; the input does not assume preservation of arbitrary proofs. -/
theorem derives_translate {Ax : Axioms C} {Ay : Axioms D}
    (axiomMap : ∀ {Γ Θ} (cs : ConstImage C D Θ) (vs : Sub D Γ Θ)
      {p : Term C Γ Ty.t}, Ax Γ p → Derives D Ay Θ [] (translate cs vs p))
    {Γ Δ p} (proof : Derives C Ax Γ Δ p) :
    ∀ {Θ} (cs : ConstImage C D Θ) (vs : Sub D Γ Θ),
      Derives D Ay Θ (Δ.map (translate cs vs)) (translate cs vs p) := by
  induction proof with
  | hyp h =>
      intro Θ cs vs
      exact .hyp (List.mem_map_of_mem h)
  | ax h =>
      intro Θ cs vs
      exact (axiomMap cs vs h).lift
  | weaken h _ ih =>
      intro Θ cs vs
      apply Derives.weaken ?_ (ih cs vs)
      intro q hq
      rcases List.mem_map.mp hq with ⟨r, hr, rfl⟩
      exact List.mem_map_of_mem (h r hr)
  | impI _ ih => intro Θ cs vs; exact .impI (ih cs vs)
  | impE _ _ ihp ihq => intro Θ cs vs; exact .impE (ihp cs vs) (ihq cs vs)
  | iffI _ _ ihp ihq => intro Θ cs vs; exact .iffI (ihp cs vs) (ihq cs vs)
  | iffE₁ _ _ ihp ihq => intro Θ cs vs; exact .iffE₁ (ihp cs vs) (ihq cs vs)
  | iffE₂ _ _ ihp ihq => intro Θ cs vs; exact .iffE₂ (ihp cs vs) (ihq cs vs)
  | topI => intro Θ cs vs; exact .topI
  | eqRefl a => intro Θ cs vs; exact .eqRefl (translate cs vs a)
  | eqSymm _ ih => intro Θ cs vs; exact .eqSymm (ih cs vs)
  | eqTrans _ _ ihp ihq => intro Θ cs vs; exact .eqTrans (ihp cs vs) (ihq cs vs)
  | eqApp _ _ ihp ihq => intro Θ cs vs; exact .eqApp (ihp cs vs) (ihq cs vs)
  | eqRight a _ ih => intro Θ cs vs; exact .eqRight (translate cs vs a) (ih cs vs)
  | eqTruth _ _ ihp ihq => intro Θ cs vs; exact .eqTruth (ihp cs vs) (ihq cs vs)
  | eqSubst P a b _ _ ihEq ihP =>
      intro Θ cs vs
      have ihA := ihP cs vs
      rw [translate_inst] at ihA ⊢
      exact .eqSubst (translate (fun c => (cs c).wk) (Sub.lift vs) P)
        (translate cs vs a) (translate cs vs b) (ihEq cs vs) ihA
  | allI _ ih =>
      intro Θ cs vs
      apply Derives.allI
      simpa only [List.map_map, Function.comp_def, translate_wk] using
        ih (fun c => (cs c).wk) (Sub.lift vs)
  | allE a _ ih =>
      intro Θ cs vs
      rw [translate_inst]
      exact .allE (translate cs vs a) (ih cs vs)
  | exI a _ ih =>
      intro Θ cs vs
      apply Derives.exI (translate cs vs a)
      simpa only [translate_inst] using ih cs vs
  | exE _ _ ihEx ihQ =>
      intro Θ cs vs
      apply Derives.exE (ihEx cs vs)
      simpa only [List.map_cons, List.map_map, Function.comp_def, translate_wk] using
        ihQ (fun c => (cs c).wk) (Sub.lift vs)
  | nec _ ih => intro Θ cs vs; exact .nec (ih cs vs)
  | K _ _ ihp ihq => intro Θ cs vs; exact .K (ihp cs vs) (ihq cs vs)
  | intensionality ρ a b _ ih =>
      intro Θ cs vs
      apply Derives.intensionality ρ (translate cs vs a) (translate cs vs b)
      simpa only [Term.box, translate, translate_coext] using ih cs vs
  | comprehension A =>
      intro Θ cs vs
      change Derives D Ay Θ _ (.ex
        (translate (fun c => (cs c).wk) (Sub.lift vs) (Body.code A)))
      rw [translate_body_code]
      exact .comprehension (translateBody cs vs A)

/-- For the stipulated unextended calculus, no axiom-map premise remains. -/
theorem base_derives_translate {Γ Δ p}
    (proof : Derives C (noAdditionalAxioms C) Γ Δ p)
    {Θ} (cs : ConstImage C D Θ) (vs : Sub D Γ Θ) :
    Derives D (noAdditionalAxioms D) Θ (Δ.map (translate cs vs)) (translate cs vs p) :=
  derives_translate (by
    intro Γ Θ cs vs p h
    exact False.elim h) proof cs vs

/-- A concrete base proof remains a proof when the distinguished typed
constant is replaced by the newly inserted parameter; local premises are
translated and stay local. -/
theorem base_derives_replaceFresh {Γ κ Δ p}
    (proof : Derives (FreshConst C κ) (noAdditionalAxioms (FreshConst C κ)) Γ Δ p) :
    Derives C (noAdditionalAxioms C) (κ :: Γ)
      (Δ.map replaceFresh) (replaceFresh p) :=
  base_derives_translate proof (constantImage (.var .zero))
    (fun v => .var (.succ v))

#print axioms translate_body_code
#print axioms derives_translate
#print axioms base_derives_translate
#print axioms base_derives_replaceFresh

end Classicism.Research.ModalFreshConstantSyntax

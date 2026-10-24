import Classicism.Results.Research.ModalConcreteNamingConservativity

/-!
# Finite dependent conservative definitions

Original research, misc, 23 October 2026. Earlier definitions are retained
as CLOSED GLOBAL axioms, eligible for necessitation. A later template may
mention all earlier names. Its new name is eliminated relative to that old
theory, fixing every old constant. A finite tower is then erased from its
last definition backwards. Optional assumptions remain local.

The transport lemma below is an induction on actual concrete derivations.
Its admissibility conditions concern constant maps and individual axiom
instances, never preservation of arbitrary proofs. The final tower theorem
has no transport, stability, existence, choice, or conservativity premise.
This concerns the stipulated concrete positive K/Nec/I/SC calculus; a
translation from full C syntax is a separate obligation.
-/

namespace Classicism.Research.ModalFreshConstantSyntax
open Classicism.Meta
open Classicism.Research.ModalComprehensionConcreteSyntax
open Classicism.Research.ModalComprehensionRepresentation (diagram)

variable {C D : Ty → Type}

/-- A restricted constant interpretation, closed under passage below a
binder. This is proved directly, rather than asking an old theory to be
invariant under arbitrary reinterpretation of its constants. -/
theorem derives_translate_admissible {Ax : Axioms C} {Ay : Axioms D}
    (Allowed : ∀ {Θ}, ConstImage C D Θ → Prop)
    (liftAllowed : ∀ {Θ σ} (cs : ConstImage C D Θ), Allowed cs →
      Allowed (fun c => (cs c).wk (σ := σ)))
    (axiomMap : ∀ {Γ Θ} (cs : ConstImage C D Θ) (vs : Sub D Γ Θ)
      {p : Term C Γ Ty.t}, Allowed cs → Ax Γ p →
        Derives D Ay Θ [] (translate cs vs p))
    {Γ Δ p} (proof : Derives C Ax Γ Δ p) :
    ∀ {Θ} (cs : ConstImage C D Θ) (vs : Sub D Γ Θ), Allowed cs →
      Derives D Ay Θ (Δ.map (translate cs vs)) (translate cs vs p) := by
  induction proof with
  | hyp h => intro Θ cs vs hc; exact .hyp (List.mem_map_of_mem h)
  | ax h => intro Θ cs vs hc; exact (axiomMap cs vs hc h).lift
  | weaken h _ ih =>
      intro Θ cs vs hc
      apply Derives.weaken ?_ (ih cs vs hc)
      intro q hq
      rcases List.mem_map.mp hq with ⟨r, hr, rfl⟩
      exact List.mem_map_of_mem (h r hr)
  | impI _ ih => intro Θ cs vs hc; exact .impI (ih cs vs hc)
  | impE _ _ ihp ihq => intro Θ cs vs hc; exact .impE (ihp cs vs hc) (ihq cs vs hc)
  | iffI _ _ ihp ihq => intro Θ cs vs hc; exact .iffI (ihp cs vs hc) (ihq cs vs hc)
  | iffE₁ _ _ ihp ihq => intro Θ cs vs hc; exact .iffE₁ (ihp cs vs hc) (ihq cs vs hc)
  | iffE₂ _ _ ihp ihq => intro Θ cs vs hc; exact .iffE₂ (ihp cs vs hc) (ihq cs vs hc)
  | topI => intro Θ cs vs hc; exact .topI
  | eqRefl a => intro Θ cs vs hc; exact .eqRefl (translate cs vs a)
  | eqSymm _ ih => intro Θ cs vs hc; exact .eqSymm (ih cs vs hc)
  | eqTrans _ _ ihp ihq => intro Θ cs vs hc; exact .eqTrans (ihp cs vs hc) (ihq cs vs hc)
  | eqApp _ _ ihp ihq => intro Θ cs vs hc; exact .eqApp (ihp cs vs hc) (ihq cs vs hc)
  | eqRight a _ ih => intro Θ cs vs hc; exact .eqRight (translate cs vs a) (ih cs vs hc)
  | eqTruth _ _ ihp ihq => intro Θ cs vs hc; exact .eqTruth (ihp cs vs hc) (ihq cs vs hc)
  | eqSubst P a b _ _ ihEq ihP =>
      intro Θ cs vs hc
      have ihA := ihP cs vs hc
      rw [translate_inst] at ihA ⊢
      exact .eqSubst (translate (fun c => (cs c).wk) (Sub.lift vs) P)
        (translate cs vs a) (translate cs vs b) (ihEq cs vs hc) ihA
  | allI _ ih =>
      intro Θ cs vs hc
      apply Derives.allI
      simpa only [List.map_map, Function.comp_def, translate_wk] using
        ih (fun c => (cs c).wk) (Sub.lift vs) (liftAllowed cs hc)
  | allE a _ ih =>
      intro Θ cs vs hc
      rw [translate_inst]
      exact .allE (translate cs vs a) (ih cs vs hc)
  | exI a _ ih =>
      intro Θ cs vs hc
      apply Derives.exI (translate cs vs a)
      simpa only [translate_inst] using ih cs vs hc
  | exE _ _ ihEx ihQ =>
      intro Θ cs vs hc
      apply Derives.exE (ihEx cs vs hc)
      simpa only [List.map_cons, List.map_map, Function.comp_def, translate_wk] using
        ihQ (fun c => (cs c).wk) (Sub.lift vs) (liftAllowed cs hc)
  | nec _ ih => intro Θ cs vs hc; exact .nec (ih cs vs hc)
  | K _ _ ihp ihq => intro Θ cs vs hc; exact .K (ihp cs vs hc) (ihq cs vs hc)
  | intensionality ρ a b _ ih =>
      intro Θ cs vs hc
      apply Derives.intensionality ρ (translate cs vs a) (translate cs vs b)
      simpa only [Term.box, translate, translate_coext] using ih cs vs hc
  | comprehension A =>
      intro Θ cs vs hc
      change Derives D Ay Θ _ (.ex
        (translate (fun c => (cs c).wk) (Sub.lift vs) (Body.code A)))
      rw [translate_body_code]
      exact .comprehension (translateBody cs vs A)

abbrev ClosedTheory (C : Ty → Type) := Term C [] Ty.t → Prop

/-- Closed global axioms are usable at every variable context. -/
def theoryAx (T : ClosedTheory C) : Axioms C :=
  fun Γ p => ∃ q, T q ∧ p = closedAt q Γ

def liftTheory {κ} (T : ClosedTheory C) : ClosedTheory (FreshConst C κ) :=
  fun p => ∃ q, T q ∧ p = embedOld q

def addDefinition (T : ClosedTheory C) (g : Term C [] Ty.t) : ClosedTheory C :=
  fun p => T p ∨ p = g

def OldConstantsFixed {κ Θ} (cs : ConstImage (FreshConst C κ) C Θ) : Prop :=
  ∀ {σ} (c : C σ), cs (.old c) = .const c

theorem oldConstantsFixed_wk {κ Θ σ}
    (cs : ConstImage (FreshConst C κ) C Θ) (hc : OldConstantsFixed cs) :
    OldConstantsFixed (fun c => (cs c).wk (σ := σ)) := by
  intro τ c
  exact congrArg (fun p : Term C Θ τ => p.wk (σ := σ)) (hc c)

/-- Old closed axiom instances are preserved by every fresh-name
interpretation that fixes old constants, including under eigenvariables. -/
theorem translate_old_closed {κ Γ Θ}
    (cs : ConstImage (FreshConst C κ) C Θ) (vs : Sub C Γ Θ)
    (hc : OldConstantsFixed cs) (q : Term C [] Ty.t) :
    translate cs vs (closedAt (embedOld q) Γ) = closedAt q Θ := by
  rw [closedAt, translate_rename, translate_embedOld]
  have hcs : @Eq (ConstImage C C Θ)
      (fun {σ} (c : C σ) => cs (.old c))
      (fun {σ} (c : C σ) => Term.const (Γ := Θ) c) := by
    funext σ c
    exact hc c
  rw [hcs]
  have hvs : @Eq (Sub C [] Θ)
      (fun {σ} (v : Var [] σ) => vs (emptyRen Γ v))
      (fun {σ} (v : Var [] σ) => Term.var (Const := C) (emptyRen Θ v)) := by
    funext σ v
    exact nomatch v
  rw [hvs, translate_as_rename]
  rfl

theorem theory_derives_replaceFresh {κ} (T : ClosedTheory C)
    {Γ Δ p} (proof : Derives (FreshConst C κ) (theoryAx (liftTheory T)) Γ Δ p) :
    Derives C (theoryAx T) (κ :: Γ) (Δ.map replaceFresh) (replaceFresh p) := by
  have axiomMap : ∀ {Γ Θ} (cs : ConstImage (FreshConst C κ) C Θ)
      (vs : Sub C Γ Θ) {p : Term (FreshConst C κ) Γ Ty.t},
      OldConstantsFixed cs → theoryAx (liftTheory T) Γ p →
        Derives C (theoryAx T) Θ [] (translate cs vs p) := by
    intro Γ Θ cs vs p hc hp
    rcases hp with ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    rw [translate_old_closed cs vs hc]
    exact .ax ⟨r, hr, rfl⟩
  exact derives_translate_admissible OldConstantsFixed oldConstantsFixed_wk axiomMap proof
    (constantImage (.var .zero)) (fun v => .var (.succ v)) (by intro σ c; rfl)

private theorem theory_swap_front {T : ClosedTheory C} {Γ Δ p q r}
    (h : Derives C (theoryAx T) Γ (p :: q :: Δ) r) :
    Derives C (theoryAx T) Γ (q :: p :: Δ) r := by
  apply Derives.weaken ?_ h
  intro a ha
  rcases List.mem_cons.mp ha with h | h
  · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl h))
  · rcases List.mem_cons.mp h with h | h
    · exact List.mem_cons.mpr (Or.inl h)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

/-- Guard elimination relative to an OLD global theory. In the Nec case,
the guard is discharged before necessitation; old globals are retained. -/
theorem concrete_guarded_over (T : ClosedTheory C) (g : Term C [] Ty.t)
    (stable : ∀ Γ, Derives C (theoryAx T) Γ []
      (.imp (closedAt g Γ) (closedAt g Γ).box))
    {Γ Δ p} (proof : Derives C (theoryAx (addDefinition T g)) Γ Δ p) :
    Derives C (theoryAx T) Γ (closedAt g Γ :: Δ) p := by
  induction proof with
  | hyp h => exact .hyp (List.mem_cons_of_mem _ h)
  | ax h =>
      rcases h with ⟨q, hq, rfl⟩
      rcases hq with hq | rfl
      · exact .ax ⟨q, hq, rfl⟩
      · exact .hyp₀
  | weaken h _ ih =>
      apply Derives.weaken ?_ ih
      intro a ha
      rcases List.mem_cons.mp ha with ha | ha
      · exact List.mem_cons.mpr (Or.inl ha)
      · exact List.mem_cons_of_mem _ (h a ha)
  | impI _ ih => exact .impI (theory_swap_front ih)
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
      simpa only [List.map_cons, closedAt_wk] using theory_swap_front ihQ
  | nec _ ih =>
      have necessary := Derives.nec (Derives.impI ih)
      exact .K necessary.lift (.impE (stable _).lift .hyp₀)
  | K _ _ ihp ihq => exact .K ihp ihq
  | intensionality ρ a b _ ih => exact .intensionality ρ a b ih
  | comprehension A => exact .comprehension A

/-- One representative may be named conservatively over ANY old closed
global theory. Its finite body may use constants defined at earlier stages. -/
theorem representation_name_conservative_over (T : ClosedTheory C) {ρ : RTy}
    (A : Body C [] ρ) {Δ : List (Term C [] Ty.t)} {P : Term C [] Ty.t}
    (proof : Derives (FreshConst C ρ)
      (theoryAx (addDefinition (liftTheory T) (representationDefinition A))) []
      (Δ.map embedOld) (embedOld P)) :
    Derives C (theoryAx T) [] Δ P := by
  have stable (Γ : Ctx) : Derives (FreshConst C ρ) (theoryAx (liftTheory T)) Γ []
      (.imp (closedAt (representationDefinition A) Γ)
        (closedAt (representationDefinition A) Γ).box) := by
    let d : Term (FreshConst C ρ) [] Ty.t :=
      (embedOld (diagram (A.rename Ren.shift) (.var .zero))).inst (.const .fresh)
    change Derives (FreshConst C ρ) (theoryAx (liftTheory T)) Γ []
      (.imp (closedAt d Γ).box (closedAt d Γ).box.box)
    exact (calculus (FreshConst C ρ) (theoryAx (liftTheory T))).modal_four (closedAt d Γ)
  have guarded := Derives.impI
    (concrete_guarded_over (liftTheory T) (representationDefinition A) stable proof)
  have translated := theory_derives_replaceFresh T guarded
  have hrep : replaceFresh (representationDefinition A) = Body.code A := by
    rw [representationDefinition, replaceFresh_box]
    exact congrArg Term.box (replaceFresh_inst_embedOld
      (diagram (A.rename Ren.shift) (.var .zero) : Term C [ρ] Ty.t))
  have hg : Derives C (theoryAx T) [ρ] (Δ.map (fun p => p.wk))
      (.imp (Body.code A) P.wk) := by
    simpa only [closedAt_nil, replaceFresh_imp, List.map_map, Function.comp_def,
      replaceFresh_embedOld, hrep] using translated
  apply Derives.exE (Derives.comprehension (Ax := theoryAx T) A)
  exact .impE (.weaken (fun _ h => List.mem_cons_of_mem _ h) hg) .hyp₀

/-- A finite DEPENDENT sequence. Each new body is in the preceding
signature, so it may mention earlier representatives. -/
inductive DefinitionTower (C : Ty → Type) (T : ClosedTheory C) :
    (D : Ty → Type) → ClosedTheory D → Type 1
  | nil : DefinitionTower C T C T
  | snoc {D U} {ρ : RTy} (previous : DefinitionTower C T D U) (A : Body D [] ρ) :
      DefinitionTower C T (FreshConst D ρ)
        (addDefinition (liftTheory U) (representationDefinition A))

namespace DefinitionTower

def embed {T : ClosedTheory C} {D U} (tower : DefinitionTower C T D U)
    {Γ σ} (p : Term C Γ σ) : Term D Γ σ :=
  match tower with
  | .nil => p
  | .snoc previous _ => embedOld (previous.embed p)

/-- Last-to-first erasure. This theorem does not assume the steps
conservative: each step invokes the derived one-name theorem above. -/
theorem conservative {T : ClosedTheory C} {D U} (tower : DefinitionTower C T D U)
    {Δ : List (Term C [] Ty.t)} {P : Term C [] Ty.t} :
    Derives D (theoryAx U) [] (Δ.map tower.embed) (tower.embed P) →
      Derives C (theoryAx T) [] Δ P := by
  induction tower with
  | nil =>
      intro proof
      change Derives C (theoryAx T) [] (Δ.map id) P at proof
      simpa only [List.map_id] using proof
  | snoc previous A ih =>
      intro proof
      apply ih
      apply representation_name_conservative_over _ A
      simpa only [embed, List.map_map, Function.comp_def] using proof

end DefinitionTower

/-- The empty original theory has exactly the intended unextended
conservativity conclusion. No extra axiom-map input remains. -/
theorem finite_representation_names_conservative {D U}
    (tower : DefinitionTower C (fun _ => False) D U)
    {Δ : List (Term C [] Ty.t)} {P : Term C [] Ty.t}
    (proof : Derives D (theoryAx U) [] (Δ.map tower.embed) (tower.embed P)) :
    Derives C (noAdditionalAxioms C) [] Δ P := by
  have old := tower.conservative proof
  have mapped := derives_translate
    (Ay := noAdditionalAxioms C)
    (by
      intro Γ Θ cs vs p h
      rcases h with ⟨_, hf, _⟩
      exact False.elim hf) old
    (fun c => Term.const c) (fun v => Term.var (Ren.id v))
  have hid : (translate (fun c => Term.const c) (fun v => Term.var (Ren.id v)) :
      Term C [] Ty.t → Term C [] Ty.t) = id := by
    funext q
    exact (translate_as_rename Ren.id q).trans (Term.rename_id q)
  rw [hid, List.map_id] at mapped
  exact mapped

#print axioms derives_translate_admissible
#print axioms theory_derives_replaceFresh
#print axioms representation_name_conservative_over
#print axioms DefinitionTower.conservative
#print axioms finite_representation_names_conservative

end Classicism.Research.ModalFreshConstantSyntax

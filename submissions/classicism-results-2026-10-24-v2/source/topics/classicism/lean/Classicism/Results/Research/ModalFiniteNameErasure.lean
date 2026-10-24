import Classicism.Results.Research.ModalIndependentNamedAxioms
import Classicism.Results.Research.ModalConstantMapDerivation

/-!
# Erasing an arbitrary available family of independent representative names

Original research, misc, 23 October 2026. Finite proof support is obtained by
actual derivation induction in ModalFiniteDerivationSupport. The finite list
is now realized by an ACTUAL DefinitionTower; each listed name is mapped to
one of its fresh constants. Unlisted names are not assigned a term. The
initial signature can be infinite and need not contain a closed e-term.

The conclusion concerns old-language open local sequents in the stipulated
classical lambda-free calculus. It does not assert whole-C proof transport.
-/

namespace Classicism.Research.ModalFiniteNameSupport
open Classicism.Meta
open Classicism.Research.ModalComprehensionConcreteSyntax
open Classicism.Research.ModalFreshConstantSyntax
open Classicism.Research.ModalComprehensionRepresentation (diagram UniformRepresents)

variable {C D E : Ty → Type} {Names : RTy → Type}

def towerMap {T : ClosedTheory C} {D U} (tower : DefinitionTower C T D U) : ConstMap C D :=
  match tower with
  | .nil => fun c => c
  | .snoc previous _ => fun c => .old (towerMap previous c)

theorem mapTerm_freshOld {κ Γ σ} (p : Term C Γ σ) :
    mapTerm (FreshConst.old (κ := κ)) p = embedOld p := by
  induction p <;> simp_all only [mapTerm, embedOld]

theorem towerMap_embed {T : ClosedTheory C} {D U}
    (tower : DefinitionTower C T D U) {Γ σ} (p : Term C Γ σ) :
    mapTerm (towerMap tower) p = tower.embed p := by
  induction tower with
  | nil => exact mapTerm_id p
  | snoc previous A ih =>
      change mapTerm (fun c => FreshConst.old (towerMap previous c)) p =
        embedOld (previous.embed p)
      rw [← mapTerm_comp (towerMap previous) FreshConst.old p, mapTerm_freshOld, ih]

theorem tower_member {T : ClosedTheory C} {D U}
    (tower : DefinitionTower C T D U) {p : Formula C []} (hp : T p) :
    U (mapTerm (towerMap tower) p) := by
  rw [towerMap_embed]
  induction tower with
  | nil => exact hp
  | snoc previous A ih => exact Or.inl ⟨previous.embed p, ih, rfl⟩

/-- The closed representation equation in a specified target signature. -/
def repAt (f : ConstMap C D) {ρ : RTy} (A : Body C [] ρ) (c : D ρ) :
    Formula D [] := Term.box (diagram (mapBody f A) (.const c))

theorem map_repAt (f : ConstMap C D) (g : ConstMap D E)
    {ρ : RTy} (A : Body C [] ρ) (c : D ρ) :
    mapTerm g (repAt f A c) = repAt (fun d => g (f d)) A (g c) := by
  change Term.box (mapTerm g (diagram (mapBody f A) (.const c))) = _
  rw [mapTerm_diagram, mapBody_comp]
  rfl

/-- The representation equation used by the tower is exactly the defining
formula used by our named-axiom family, not merely a material equivalent. -/
theorem representationDefinition_eq {ρ : RTy} (A : Body C [] ρ) :
    representationDefinition A = repAt FreshConst.old A FreshConst.fresh := by
  calc
    representationDefinition A = (embedOld (Body.code A)).inst (.const .fresh) := rfl
    _ = (mapTerm FreshConst.old (Body.code A)).inst (.const .fresh) := by
      rw [mapTerm_freshOld]
    _ = (Body.code (mapBody FreshConst.old A)).inst (.const .fresh) := by
      rw [mapTerm_body_code]
    _ = repAt FreshConst.old A FreshConst.fresh :=
      Body.code_inst (mapBody FreshConst.old A) (.const .fresh)

/-- Construct the finite tower, without restricting the old signature.
Repeated labels are harmless; membership selects an available copy. -/
theorem finite_names_tower (body : Definitions C Names) (S : List (Label Names)) :
    ∃ (D : Ty → Type) (U : ClosedTheory D)
      (tower : DefinitionTower C (ClosedClassicalTheory C) D U),
      ∀ l : Label Names, l ∈ S → ∃ c : D l.1,
        U (repAt (towerMap tower) (body l.2) c) := by
  induction S with
  | nil =>
      refine ⟨C, ClosedClassicalTheory C, .nil, ?_⟩
      intro l hl
      exact False.elim (List.not_mem_nil hl)
  | cons head S ih =>
      rcases ih with ⟨D, U, previous, hp⟩
      let A : Body D [] head.1 := mapBody (towerMap previous) (body head.2)
      refine ⟨FreshConst D head.1,
        addDefinition (liftTheory U) (representationDefinition A),
        DefinitionTower.snoc previous A, ?_⟩
      intro l hl
      rcases List.mem_cons.mp hl with he | ht
      · subst l
        refine ⟨.fresh, Or.inr ?_⟩
        change repAt (fun c => FreshConst.old (towerMap previous c)) (body head.2)
          FreshConst.fresh = representationDefinition A
        calc
          _ = repAt FreshConst.old A FreshConst.fresh := by
            simp only [repAt, A, mapBody_comp]
          _ = representationDefinition A := (representationDefinition_eq A).symm
      · rcases hp l ht with ⟨c, hc⟩
        refine ⟨.old c, Or.inl ⟨repAt (towerMap previous) (body l.2) c, hc, ?_⟩⟩
        rw [← mapTerm_freshOld, map_repAt]
        rfl

/-- The tower contains the two closed classical axioms, so every open
classical instance is an actual target derivation by UI. -/
theorem tower_classical_axiom {D U}
    (tower : DefinitionTower C (ClosedClassicalTheory C) D U)
    {Γ p} (h : ClassicalAxioms D Γ p) : Derives D (theoryAx U) Γ [] p := by
  cases h with
  | dne p =>
      have hm : U (closedDNE D) := by
        simpa only [closedDNE, neg, bottom, mapTerm] using
          tower_member tower (ClosedClassicalTheory.dne (C := C))
      have hu : Derives D (theoryAx U) Γ [] (closedAt (closedDNE D) Γ) :=
        .ax ⟨closedDNE D, hm, rfl⟩
      rw [closedDNE_at] at hu
      exact .allE p hu
  | exists_e =>
      have hm : U (closedExistenceE D) := by
        simpa only [closedExistenceE, mapTerm] using
          tower_member tower (ClosedClassicalTheory.existence_e (C := C))
      have hu : Derives D (theoryAx U) Γ [] (closedAt (closedExistenceE D) Γ) :=
        .ax ⟨closedExistenceE D, hm, rfl⟩
      exact hu

/-- Interpret only the finitely scoped names in their constructed tower. -/
noncomputable def scopedTowerMap (S : List (Label Names))
    {D U} (tower : DefinitionTower C (ClosedClassicalTheory C) D U)
    (body : Definitions C Names)
    (hn : ∀ l : Label Names, l ∈ S → ∃ c : D l.1,
      U (repAt (towerMap tower) (body l.2) c)) :
    ConstMap (ScopedConst C Names S) D
  | _, .old c => towerMap tower c
  | _, .name n => Classical.choose (hn ⟨_, n.val⟩ n.property)

theorem scopedTower_definition (S : List (Label Names))
    {D U} (tower : DefinitionTower C (ClosedClassicalTheory C) D U)
    (body : Definitions C Names)
    (hn : ∀ l : Label Names, l ∈ S → ∃ c : D l.1,
      U (repAt (towerMap tower) (body l.2) c))
    {ρ : RTy} (n : ScopedNames Names S ρ) :
    U (mapTerm (scopedTowerMap S tower body hn)
      (nameDefinition (scopedDefinitions body S) n)) := by
  have hm := Classical.choose_spec (hn ⟨ρ, n.val⟩ n.property)
  change U (Term.box (mapTerm (scopedTowerMap S tower body hn)
    (diagram (mapBody NamedConst.old (body n.val)) (.const (.name n)))))
  rw [mapTerm_diagram, mapBody_comp]
  exact hm

/-- All axioms in the restricted proof are supplied by explicit tower
members or genuine classical derivations; arbitrary proofs are not assumed
preserved. -/
theorem scopedTower_axiom (S : List (Label Names))
    {D U} (tower : DefinitionTower C (ClosedClassicalTheory C) D U)
    (body : Definitions C Names)
    (hn : ∀ l : Label Names, l ∈ S → ∃ c : D l.1,
      U (repAt (towerMap tower) (body l.2) c))
    {Γ p} (h : NamedAxioms (scopedDefinitions body S) Γ p) :
    Derives D (theoryAx U) Γ [] (mapTerm (scopedTowerMap S tower body hn) p) := by
  cases h with
  | classical hc => exact tower_classical_axiom tower (classical_map _ hc)
  | definition n =>
      rw [mapTerm_closedAt]
      exact .ax ⟨_, scopedTower_definition S tower body hn n, rfl⟩

/-- An arbitrarily large available family of independent closed SC names
is conservative for EVERY old-language open local sequent. The proof first
restricts its actual finite syntax, constructs a finite tower, transports
that restricted proof by rule induction and erases the tower. -/
theorem independent_names_conservative (body : Definitions C Names)
    {Γ} {Δ : List (Formula C Γ)} {p : Formula C Γ}
    (proof : Derives (NamedConst C Names) (NamedAxioms body) Γ
      (Δ.map (mapTerm NamedConst.old)) (mapTerm NamedConst.old p)) :
    Derives C (ClassicalAxioms C) Γ Δ p := by
  classical
  rcases named_finite_old_support body proof with ⟨S, restricted⟩
  rcases finite_names_tower body S with ⟨D, U, tower, hn⟩
  have mapped := derives_map (scopedTowerMap S tower body hn)
    (fun _ _ h => scopedTower_axiom S tower body hn h) restricted
  have hterm {σ} (a : Term C Γ σ) :
      mapTerm (scopedTowerMap S tower body hn) (mapTerm NamedConst.old a) =
        tower.embed a := by
    rw [mapTerm_comp]
    exact towerMap_embed tower a
  have hlist : (Δ.map (mapTerm NamedConst.old)).map
      (mapTerm (scopedTowerMap S tower body hn)) = Δ.map tower.embed := by
    simp only [List.map_map, Function.comp_def, hterm]
  rw [hlist, hterm] at mapped
  exact finite_classical_representation_names_conservative_open tower mapped

#print axioms finite_names_tower
#print axioms scopedTower_axiom
#print axioms independent_names_conservative

end Classicism.Research.ModalFiniteNameSupport

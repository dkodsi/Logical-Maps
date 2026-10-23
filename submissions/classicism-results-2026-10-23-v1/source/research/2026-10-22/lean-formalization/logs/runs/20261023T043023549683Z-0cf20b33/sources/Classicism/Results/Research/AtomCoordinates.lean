import Classicism.Results.Records.Lattice
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

/-!
# Relational atom coordinates: the unary core

Direct source: `research/2026-10-22/proof-refinements/atom-normal-form.md`, §§1–4.
These statements concern `σ → t`. A tuple/vectorized certificate is a separate
obligation: this module does not infer polyadic BF from several unboxed unary
instances. Projection, pinning and collision require bare C; BF and ND appear only
where explicitly stated. No unrestricted Choice or Functionality is used.
-/

namespace Classicism.Research.AtomCoordinates
open Classicism.P Classicism.Paper Classicism.Proofs

variable {σ : Type} [Ty σ]

def Projection (X : σ → Prop) : Prop := ∃ x, X x
def Pin (w : Prop) (a : σ) : σ → Prop := λ x ↦ w ∧ x = a

/-- Projection cancels pinning without any optional premise. -/
theorem projection_pin (w : Prop) (a : σ) : Projection (Pin w a) = w :=
  propext ⟨fun h => h.elim fun _ hx => hx.1, fun hw => ⟨a, hw, rfl⟩⟩

theorem projection_bot : Projection (Rel.bot (σ → Prop)) = False :=
  propext ⟨fun h => h.elim fun _ hx => hx, fun hf => hf.elim⟩

theorem pin_false (a : σ) : Pin False a = Rel.bot (σ → Prop) :=
  funext fun _ => propext ⟨fun h => h.1, fun hf => hf.elim⟩

theorem pin_value (w : Prop) (a : σ) : Pin w a a = w := and_rfl_eq w a

/-- A pin is zero exactly when its scalar is zero. -/
theorem pin_eq_bot_iff (w : Prop) (a : σ) :
    Pin w a = Rel.bot (σ → Prop) ↔ w = False :=
  ⟨fun h => (projection_pin w a).symm.trans
      ((congrArg Projection h).trans projection_bot),
    fun h => h ▸ pin_false a⟩

/-- Projection is monotone. -/
theorem projection_mono (X Y : σ → Prop) (h : X ≤ Y) : Projection X ≤ Projection Y :=
  (le_iff_prop _ _).2 (modal_K _ _
    (nec% (fun (hxy : ∀ x, X x → Y x) (hx : Projection X) =>
      hx.elim fun x hxx => (show Projection Y from ⟨x, hxy x hxx⟩)))
    ((le_iff X Y).1 h))

/-- Projection is left adjoint to the constant-property operation. -/
theorem projection_le_const (X : σ → Prop) (q : Prop)
    (h : X ≤ (λ _ : σ ↦ q)) : Projection X ≤ q :=
  (le_iff_prop _ _).2 (modal_K _ _
    (nec% (fun (hxq : ∀ x, X x → q) (hx : Projection X) =>
      hx.elim fun x hxx => hxq x hxx))
    ((le_iff _ _).1 h))

/-- The converse half of the same adjunction. -/
theorem le_const_of_projection (X : σ → Prop) (q : Prop)
    (h : Projection X ≤ q) : X ≤ (λ _ : σ ↦ q) :=
  (le_iff _ _).2 (modal_K _ _
    (nec% (fun (hxq : Projection X → q) (x : σ) (hx : X x) => hxq ⟨x, hx⟩))
    ((le_iff_prop _ _).1 h))

theorem projection_adjunction (X : σ → Prop) (q : Prop) :
    Projection X ≤ q ↔ X ≤ (λ _ : σ ↦ q) :=
  ⟨le_const_of_projection X q, projection_le_const X q⟩

/-- Projection detects exactly the zero relation, without BF. -/
theorem projection_eq_false_iff (X : σ → Prop) :
    Projection X = False ↔ X = Rel.bot (σ → Prop) :=
  ⟨fun h => intensionality X _ (modal_K _ _ (nec% (coext_bot_of_not_exists X))
      ((box_not_eq (Projection X)).mpr h)),
    fun h => (congrArg Projection h).trans projection_bot⟩

/-- An atom at the property type cannot be bottom. -/
theorem atom_ne_bot (X : σ → Prop) (hX : Atom X) : X ≠ Rel.bot (σ → Prop) :=
  fun e => not_le_neg_of_atom hX (by rw [e]; exact bot_le_arrow _)

/-- Bare C: existential projection sends a relational atom to a proposition atom. -/
theorem projection_atom (X : σ → Prop) (hX : Atom X) : Atom (Projection X) :=
  atom_of_decides _ ⟨dia_exists_of_ne_bot X (atom_ne_bot X hX), fun q =>
    (atom_decides_arrow X (λ _ : σ ↦ q) hX).elim
      (fun h => Or.inl (projection_le_const X q h))
      (fun h => Or.inr (projection_le_const X (¬ q) h))⟩

/-- Bare C: any world atom pinned to a current argument is a relational atom. -/
theorem pin_atom (w : Prop) (a : σ) (hw : Atom w) : Atom (Pin w a) :=
  atom_of_decides_arrow _
    (fun e => not_le_neg_of_atom hw (le_neg_of_eq_false w ((pin_eq_bot_iff w a).1 e)))
    (pin_decides w a fun q => atom_le_or_le_neg w q hw)

/-- An atom is equal to any nonzero element below it. -/
theorem atom_eq_of_nonzero_below (X Y : σ → Prop) (hX : Atom X)
    (hne : Y ≠ Rel.bot (σ → Prop)) (hle : Y ≤ X) : Y = X :=
  (em (Y = X)).elim (fun h => h)
    (fun h => (hne (eq_bot_of_le_neg_arrow Y ((hX Y).1 ⟨hle, h⟩))).elim)

/-- A nonzero current value already supplies coordinates, without BF. -/
theorem recover_coordinates (X : σ → Prop) (a : σ) (hX : Atom X)
    (ha : X a ≠ False) : X = Pin (Projection X) a := by
  have he : Pin (X a) a = X := atom_eq_of_nonzero_below X (Pin (X a) a) hX
    (fun h => ha ((pin_eq_bot_iff (X a) a).1 h))
    (pin_le_of_le (X a) a X (le_refl_prop (X a)))
  have hs : Projection X = X a := (congrArg Projection he).symm.trans (projection_pin (X a) a)
  exact he.symm.trans (congrArg (λ p : Prop ↦ Pin p a) hs.symm)

/-- Exact current-witness criterion, for an already given relational atom. -/
theorem coordinates_iff_current_value (X : σ → Prop) (hX : Atom X) :
    (∃ w : Prop, ∃ a : σ, Atom w ∧ X = Pin w a) ↔ ∃ a : σ, X a ≠ False :=
  ⟨fun h => h.elim fun w hw => hw.elim fun a ha =>
      ⟨a, fun hz => not_le_neg_of_atom ha.1 (le_neg_of_eq_false w
        ((pin_value w a).symm.trans ((congrFun ha.2 a).symm.trans hz)))⟩,
    fun h => h.elim fun a ha =>
      ⟨Projection X, a, projection_atom X hX, recover_coordinates X a hX ha⟩⟩

/-- Only the dual BF instance for this one atom is needed to recover its coordinates. -/
theorem coordinates_of_local_bf (X : σ → Prop) (hX : Atom X)
    (bfX : ◇ (Projection X) → ∃ a : σ, ◇ (X a)) :
    ∃ a : σ, X = Pin (Projection X) a :=
  (bfX (dia_exists_of_ne_bot X (atom_ne_bot X hX))).elim fun a ha =>
    ⟨a, recover_coordinates X a hX ha⟩

/-- Full unary BF supplies the local instance above. -/
theorem coordinates_of_bf (bf : Barcan σ) (X : σ → Prop) (hX : Atom X) :
    ∃ a : σ, X = Pin (Projection X) a :=
  coordinates_of_local_bf X hX (exists_dia_of_dia_exists bf X)

/-- Exact collision law. This strengthens the atom-only formulation: neither
scalar needs to be an atom for this equivalence. -/
theorem pin_collision (w v : Prop) (a b : σ) :
    Pin w a = Pin v b ↔ w = v ∧ w ≤ (a = b) := by
  constructor
  · intro h
    have hwv : w = v := (projection_pin w a).symm.trans
      ((congrArg Projection h).trans (projection_pin v b))
    have he : w = (v ∧ a = b) := (pin_value w a).symm.trans (congrFun h a)
    exact ⟨hwv, he ▸ and_le_right_prop v (a = b)⟩
  · intro h
    have heq : Pin w a = Pin w b :=
      intensionality _ _ (modal_K _ _
        (nec% (fun (hab : w → a = b) (x : σ) =>
          (show (w ∧ x = a) ↔ (w ∧ x = b) from
            ⟨fun hx => ⟨hx.1, hx.2.trans (hab hx.1)⟩,
             fun hx => ⟨hx.1, hx.2.trans (hab hx.1).symm⟩⟩)))
        ((le_iff_prop _ _).1 h.2))
    exact heq.trans (congrArg (λ p : Prop ↦ Pin p b) h.1)

/-- Under local ND, nonzero scalars have unique coordinates; atomhood is unnecessary. -/
theorem pin_injective_of_nd (nd : NecessityOfDistinctness σ)
    (w v : Prop) (a b : σ) (hw : w ≠ False) (h : Pin w a = Pin v b) :
    w = v ∧ a = b :=
  have hc := (pin_collision w v a b).1 h
  ⟨hc.1, eq_of_dia_eq nd a b (dia_mono _ _ ((le_iff_prop _ _).1 hc.2) hw)⟩

/-- With Atomicity at `t`, injectivity just for atom pins conversely implies ND. -/
theorem nd_of_atomic_pin_injective (at_ : AtomicityT)
    (hi : ∀ (w : Prop) (a b : σ), Atom w → Pin w a = Pin w b → a = b) :
    NecessityOfDistinctness σ :=
  NecessityOfDistinctness.of_dual fun a b hd =>
    (at_ (a = b)).elim
      (fun h => (hd (eq_false_of_le_neg _ h)).elim)
      (fun h => h.elim fun w hw => hi w a b hw.1 ((pin_collision w w a b).2 ⟨rfl, hw.2⟩))

/-- Atomicity at the property type implies propositional Atomicity if a current
argument is supplied. The parameter makes the nonemptiness requirement explicit. -/
theorem atomicity_projection (a : σ) (at_ : Atomicity (σ → Prop)) : AtomicityT := fun p =>
  (at_ (Pin p a)).elim
    (fun h => Or.inl (le_neg_of_eq_false p ((pin_eq_bot_iff p a).1
      (eq_bot_of_le_neg_arrow _ h))))
    (fun h => h.elim fun X hX =>
      Or.inr ⟨Projection X, projection_atom X hX.1,
        (projection_pin p a) ▸ projection_mono X (Pin p a) hX.2⟩)

/-- Under this unary BF instance, Atomicity transfers in both directions. -/
theorem atomicity_iff_of_bf (a : σ) (bf : Barcan σ) :
    Atomicity (σ → Prop) ↔ AtomicityT :=
  ⟨atomicity_projection a,
    fun at_ => atomicity_t_and_bf_imply_atomicity at_ bf⟩

/-! These closed schema wrappers let the standard pipeline attempt the finite-tuple
forms. Only an actually produced `.listRule` certifies that vectorization. -/

def ProjectionAtomLaw (σ : Type) [Ty σ] : Prop :=
  ∀ X : σ → Prop, Atom X → Atom (Projection X)

def PinAtomLaw (σ : Type) [Ty σ] : Prop :=
  ∀ (w : Prop) (a : σ), Atom w → Atom (Pin w a)

def PinCollisionLaw (σ : Type) [Ty σ] : Prop :=
  ∀ (w v : Prop) (a b : σ), Pin w a = Pin v b ↔ w = v ∧ w ≤ (a = b)

theorem projection_atom_law : ProjectionAtomLaw σ := projection_atom
theorem pin_atom_law : PinAtomLaw σ := pin_atom
theorem pin_collision_law : PinCollisionLaw σ := pin_collision

end Classicism.Research.AtomCoordinates

#classicism_check Classicism.Research.AtomCoordinates.projection_pin
  Classicism.Research.AtomCoordinates.projection_bot
  Classicism.Research.AtomCoordinates.pin_false
  Classicism.Research.AtomCoordinates.pin_value
  Classicism.Research.AtomCoordinates.pin_eq_bot_iff
  Classicism.Research.AtomCoordinates.projection_mono
  Classicism.Research.AtomCoordinates.projection_le_const
  Classicism.Research.AtomCoordinates.le_const_of_projection
  Classicism.Research.AtomCoordinates.projection_adjunction
  Classicism.Research.AtomCoordinates.projection_eq_false_iff
  Classicism.Research.AtomCoordinates.atom_ne_bot
  Classicism.Research.AtomCoordinates.projection_atom
  Classicism.Research.AtomCoordinates.pin_atom
  Classicism.Research.AtomCoordinates.atom_eq_of_nonzero_below
  Classicism.Research.AtomCoordinates.recover_coordinates
  Classicism.Research.AtomCoordinates.coordinates_iff_current_value
  Classicism.Research.AtomCoordinates.coordinates_of_local_bf
  Classicism.Research.AtomCoordinates.coordinates_of_bf
  Classicism.Research.AtomCoordinates.pin_collision
  Classicism.Research.AtomCoordinates.pin_injective_of_nd
  Classicism.Research.AtomCoordinates.nd_of_atomic_pin_injective
  Classicism.Research.AtomCoordinates.atomicity_projection
  Classicism.Research.AtomCoordinates.atomicity_iff_of_bf
  Classicism.Research.AtomCoordinates.projection_atom_law
  Classicism.Research.AtomCoordinates.pin_atom_law
  Classicism.Research.AtomCoordinates.pin_collision_law
#classicism_types Classicism.Research.AtomCoordinates.projection_pin
  Classicism.Research.AtomCoordinates.projection_bot
  Classicism.Research.AtomCoordinates.pin_false
  Classicism.Research.AtomCoordinates.pin_value
  Classicism.Research.AtomCoordinates.pin_eq_bot_iff
  Classicism.Research.AtomCoordinates.projection_mono
  Classicism.Research.AtomCoordinates.projection_le_const
  Classicism.Research.AtomCoordinates.le_const_of_projection
  Classicism.Research.AtomCoordinates.projection_adjunction
  Classicism.Research.AtomCoordinates.projection_eq_false_iff
  Classicism.Research.AtomCoordinates.atom_ne_bot
  Classicism.Research.AtomCoordinates.projection_atom
  Classicism.Research.AtomCoordinates.pin_atom
  Classicism.Research.AtomCoordinates.atom_eq_of_nonzero_below
  Classicism.Research.AtomCoordinates.recover_coordinates
  Classicism.Research.AtomCoordinates.coordinates_iff_current_value
  Classicism.Research.AtomCoordinates.coordinates_of_local_bf
  Classicism.Research.AtomCoordinates.coordinates_of_bf
  Classicism.Research.AtomCoordinates.pin_collision
  Classicism.Research.AtomCoordinates.pin_injective_of_nd
  Classicism.Research.AtomCoordinates.nd_of_atomic_pin_injective
  Classicism.Research.AtomCoordinates.atomicity_projection
  Classicism.Research.AtomCoordinates.atomicity_iff_of_bf
  Classicism.Research.AtomCoordinates.projection_atom_law
  Classicism.Research.AtomCoordinates.pin_atom_law
  Classicism.Research.AtomCoordinates.pin_collision_law
#classicism_derive Classicism.Research.AtomCoordinates.projection_atom
  Classicism.Research.AtomCoordinates.projection_adjunction
  Classicism.Research.AtomCoordinates.projection_eq_false_iff
  Classicism.Research.AtomCoordinates.pin_atom
  Classicism.Research.AtomCoordinates.recover_coordinates
  Classicism.Research.AtomCoordinates.coordinates_iff_current_value
  Classicism.Research.AtomCoordinates.coordinates_of_local_bf
  Classicism.Research.AtomCoordinates.coordinates_of_bf
  Classicism.Research.AtomCoordinates.pin_collision
  Classicism.Research.AtomCoordinates.pin_injective_of_nd
  Classicism.Research.AtomCoordinates.nd_of_atomic_pin_injective
  Classicism.Research.AtomCoordinates.atomicity_projection
  Classicism.Research.AtomCoordinates.atomicity_iff_of_bf

#classicism_schema Classicism.Research.AtomCoordinates.ProjectionAtomLaw
  Classicism.Research.AtomCoordinates.PinAtomLaw
  Classicism.Research.AtomCoordinates.PinCollisionLaw

#classicism_certify Classicism.Research.AtomCoordinates.projection_atom_law
  Classicism.Research.AtomCoordinates.pin_atom_law
  Classicism.Research.AtomCoordinates.pin_collision_law

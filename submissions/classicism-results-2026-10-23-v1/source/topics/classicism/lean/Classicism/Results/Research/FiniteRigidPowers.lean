import Classicism.Results.Research.FregeFiniteSets
import Classicism.Results.Research.ModalRigidityDescent
import Classicism.Results.Research.RigidityClosureResearchNullary

/-!
# Finite rigid powers and finite binary argument codes

Direct sources: research/2026-10-22/notes/relational-coding-recursion-20261022.md,
§27.1–§27.4; frege-infinity-20261022-1726.md §25.1 (unpaginated, misc).
The proofs use actual Frege finiteness and whole-tuple haecceities. Partial
application of a rigid binary relation is NOT assumed rigid in bare C.
These are concrete unary/binary induction steps, not the full type recursion.
-/
namespace Classicism.Research.FiniteRigidPowers
open Classicism.Paper
open Classicism.Research.FregeFiniteSets
open Classicism.Research.ModalRigidityDescent

variable {σ τ : Type} [Ty σ] [Ty τ]

def RigidPowerField (A : σ → Prop) (X : σ → Prop) : Prop :=
  Rigid X ∧ ∀ x, X x → A x

theorem finite_rigid_power (A : σ → Prop) (hA : Finite A) :
    Finite (RigidPowerField A) := by
  apply finite_separated_family A (RigidPowerField A) (fun x X => X x) hA
  intro X Y hx hy he
  apply Proofs.eq_of_weaklyRigid_coext (weaklyRigid_of_rigid hx.1)
    (weaklyRigid_of_rigid hy.1)
  intro x
  exact ⟨fun h => (he x (hx.2 x h)).1 h,
    fun h => (he x (hy.2 x h)).2 h⟩

theorem finite_base_of_finite_rigid_power (A : σ → Prop)
    (hA : Finite (RigidPowerField A)) : Finite A := by
  apply finite_injection_domain A (RigidPowerField A)
    (fun a X => X = (fun x => x = a)) hA
  · intro a ha
    exact ⟨(fun x => x = a), ⟨singleton_rigid a,
      fun x hx => hx.symm ▸ ha⟩, rfl⟩
  · intro a b X _ _ ha hb
    have he := congrFun (ha.symm.trans hb) a
    exact Eq.mp he rfl

theorem finite_rigid_power_iff (A : σ → Prop) :
    Finite (RigidPowerField A) ↔ Finite A :=
  ⟨finite_base_of_finite_rigid_power A, finite_rigid_power A⟩

def PairCode (a : σ) (b : τ) : σ → τ → Prop := fun x y => x = a ∧ y = b

theorem pairCode_injective (a c : σ) (b d : τ)
    (he : PairCode a b = PairCode c d) : a = c ∧ b = d :=
  Eq.mp (congrFun (congrFun he a) b) ⟨rfl, rfl⟩

theorem pairCode_weaklyRigid (a : σ) (b : τ) : WeaklyRigid (PairCode a b) := by
  constructor
  · intro x y h
    exact modal_K _ _ (modal_K _ _
      (nec% (fun (hx : x = a) (hy : y = b) => And.intro hx hy))
      (necessity_of_identity x a h.1)) (necessity_of_identity y b h.2)
  · intro Z hz
    exact modal_K _ _ (nec% (fun (hab : Z a b) (x : σ) (y : τ)
      (hxy : x = a ∧ y = b) => hxy.1.symm ▸ hxy.2.symm ▸ hab))
      (hz a b ⟨rfl, rfl⟩)

theorem pairCode_rigid (a : σ) (b : τ) : Rigid (PairCode a b) :=
  (rigid_iff_box_weaklyRigid _).2 (nec% (pairCode_weaklyRigid a b))

def PairCodes (A : σ → Prop) (B : τ → Prop) (c : σ → τ → Prop) : Prop :=
  ∃ x, A x ∧ ∃ y, B y ∧ c = PairCode x y

theorem finite_pairCodes (A : σ → Prop) (B : τ → Prop)
    (hA : Finite A) (hB : Finite B) : Finite (PairCodes A B) := by
  apply finite_fibre_union A (fun x c => ∃ y, B y ∧ c = PairCode x y) hA
  intro x _
  exact finite_functional_image B (fun y c => c = PairCode x y) hB
    (fun y _ c d hc hd => hc.trans hd.symm)

def PairRead (c R : σ → τ → Prop) : Prop :=
  ∃ x y, c = PairCode x y ∧ R x y

theorem pairRead_value (a : σ) (b : τ) (R : σ → τ → Prop) :
    PairRead (PairCode a b) R ↔ R a b := by
  constructor
  · intro h
    obtain ⟨x, y, hxy, hr⟩ := h
    have he := pairCode_injective a x b y hxy
    exact he.1.symm ▸ he.2.symm ▸ hr
  · intro h
    exact ⟨a, b, rfl, h⟩

def BinaryRigidField (A : σ → Prop) (B : τ → Prop) (R : σ → τ → Prop) : Prop :=
  Rigid R ∧ ∀ x y, R x y → A x ∧ B y

theorem finite_binary_rigid_field (A : σ → Prop) (B : τ → Prop)
    (hA : Finite A) (hB : Finite B) : Finite (BinaryRigidField A B) := by
  apply finite_separated_family (PairCodes A B) (BinaryRigidField A B) PairRead
    (finite_pairCodes A B hA hB)
  intro R S hr hs he
  apply Proofs.eq_of_weaklyRigid_coext (weaklyRigid_of_rigid hr.1)
    (weaklyRigid_of_rigid hs.1)
  intro x y
  constructor
  · intro h
    have hx := hr.2 x y h
    exact (pairRead_value x y S).1
      ((he (PairCode x y) ⟨x, hx.1, y, hx.2, rfl⟩).1 ⟨x, y, rfl, h⟩)
  · intro h
    have hx := hs.2 x y h
    exact (pairRead_value x y R).1
      ((he (PairCode x y) ⟨x, hx.1, y, hx.2, rfl⟩).2 ⟨x, y, rfl, h⟩)

theorem finite_left_of_binary_rigid_field (A : σ → Prop) (B : τ → Prop)
    (b : τ) (hb : B b) (hf : Finite (BinaryRigidField A B)) : Finite A := by
  apply finite_injection_domain A (BinaryRigidField A B)
    (fun x R => R = PairCode x b) hf
  · intro x hx
    exact ⟨PairCode x b, ⟨pairCode_rigid x b,
      fun u v h => ⟨h.1.symm ▸ hx, h.2.symm ▸ hb⟩⟩, rfl⟩
  · intro x z R _ _ hx hz
    exact (pairCode_injective x z b b (hx.symm.trans hz)).1

theorem finite_right_of_binary_rigid_field (A : σ → Prop) (B : τ → Prop)
    (a : σ) (ha : A a) (hf : Finite (BinaryRigidField A B)) : Finite B := by
  apply finite_injection_domain B (BinaryRigidField A B)
    (fun y R => R = PairCode a y) hf
  · intro y hy
    exact ⟨PairCode a y, ⟨pairCode_rigid a y,
      fun u v h => ⟨h.1.symm ▸ ha, h.2.symm ▸ hy⟩⟩, rfl⟩
  · intro y z R _ _ hy hz
    exact (pairCode_injective a a y z (hy.symm.trans hz)).2

theorem finite_binary_rigid_field_iff (A : σ → Prop) (B : τ → Prop)
    (a : σ) (ha : A a) (b : τ) (hb : B b) :
    Finite (BinaryRigidField A B) ↔ Finite A ∧ Finite B :=
  ⟨fun hf => ⟨finite_left_of_binary_rigid_field A B b hb hf,
    finite_right_of_binary_rigid_field A B a ha hf⟩,
   fun hf => finite_binary_rigid_field A B hf.1 hf.2⟩

theorem finite_rigid_propositions : Finite (fun p : Prop => Rigid p) :=
  finite_coext _ _ (finite_union _ _ (finite_singleton True) (finite_singleton False))
    (fun p => (Classicism.Research.RigidityClosure.rigid_prop_iff p).symm)

theorem finite_double_rigid_power (A : σ → Prop) :
    Finite (RigidPowerField (RigidPowerField A)) ↔ Finite A :=
  (finite_rigid_power_iff (RigidPowerField A)).trans (finite_rigid_power_iff A)

end Classicism.Research.FiniteRigidPowers

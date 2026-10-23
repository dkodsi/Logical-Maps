import Classicism.Results.Research.FiniteRigidPowers

/-!
# Vectorizable finite rigid-power and separating-family laws

Direct source: research/2026-10-22/notes/relational-coding-recursion-20261022.md
§27.1–§27.3, unpaginated original research, misc. The companion driver requires
actual listRule declarations, so a unary derivation alone is not called an
all-arity certificate. Vectorized finite cardinalities count argument tuples by
n-ary predicates; they do not create forbidden tuple objects or e-valued maps.
The separate recursive hereditary-domain interpretation is not supplied here.
-/
namespace Classicism.Research.FiniteTupleLaws
open Classicism.Research.FregeFiniteSets
open Classicism.Research.FiniteRigidPowers

def FiniteRigidPowerLaw (σ : Type) [Ty σ] : Prop :=
  ∀ A : σ → Prop, Finite (RigidPowerField A) ↔ Finite A

theorem finite_rigid_power_law {σ : Type} [Ty σ] : FiniteRigidPowerLaw σ :=
  finite_rigid_power_iff

def FiniteSeparationLaw (σ τ : Type) [Ty σ] [Ty τ] : Prop :=
  ∀ (A : σ → Prop) (H : τ → Prop) (E : σ → τ → Prop), Finite A →
    (∀ u v, H u → H v → (∀ x, A x → (E x u ↔ E x v)) → u = v) → Finite H

theorem finite_separation_law {σ τ : Type} [Ty σ] [Ty τ] : FiniteSeparationLaw σ τ :=
  finite_separated_family

end Classicism.Research.FiniteTupleLaws

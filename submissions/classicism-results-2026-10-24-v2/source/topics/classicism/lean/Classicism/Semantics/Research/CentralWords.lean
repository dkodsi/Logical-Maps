import Mathlib.Algebra.Group.Basic
import Mathlib.Data.List.Basic

/-!
# Finite words for the central product construction

The free monoid needed in `followup/central-map.md`, §§1–3, implemented
directly as finite lists. This local supporting construction avoids a new
shared-library dependency; it does not change the mathematical model.
-/

namespace Classicism.Meta.Intensional.Central

structure Word (L : Type) where
  toList : List L

namespace Word
variable {L : Type}

@[ext] theorem ext {u v : Word L} (h : u.toList = v.toList) : u = v := by
  cases u
  cases v
  cases h
  rfl

instance : Monoid (Word L) where
  one := ⟨[]⟩
  mul u v := ⟨u.toList ++ v.toList⟩
  one_mul u := by apply ext; exact List.nil_append _
  mul_one u := by apply ext; exact List.append_nil _
  mul_assoc u v w := by apply ext; exact List.append_assoc _ _ _

def of (a : L) : Word L := ⟨[a]⟩
def length (u : Word L) : Nat := u.toList.length

@[simp] theorem toList_one : (1 : Word L).toList = [] := rfl
@[simp] theorem toList_mul (u v : Word L) : (u * v).toList = u.toList ++ v.toList := rfl
@[simp] theorem toList_of (a : L) : (of a).toList = [a] := rfl
@[simp] theorem length_one : length (1 : Word L) = 0 := rfl
@[simp] theorem length_of (a : L) : length (of a) = 1 := rfl
@[simp] theorem length_mul (u v : Word L) : length (u * v) = length u + length v :=
  List.length_append

theorem mul_right_cancel {u v w : Word L} (h : u * w = v * w) : u = v := by
  apply ext
  exact List.append_cancel_right (congrArg toList h)

end Word
end Classicism.Meta.Intensional.Central

import Classicism.Models.ChoiceFirstOrderSmall

/-!
# The admitted-domain semantic matrix of the quoted real predicate

This is the interpretation of the clauses of
`Classicism.Research.Analytic.Real` in a one-world typed structure. Every
second-order quantifier below ranges over an admitted relation object of S,
never over arbitrary external predicates. The separate quotation theorem
connects this explicit matrix to the actual object-language term; these
definitions alone assert no truth correspondence or real-field existence.
-/

open Classicism.Meta

namespace ClassicismZFC.TypedReal

abbrev unaryTy : RTy := .arr .e .t
abbrev binaryTy : RTy := .arr .e (.arr .e .t)
abbrev ternaryTy : RTy := .arr .e (.arr .e (.arr .e .t))

variable (S : ChoiceFirstOrder.Structure)

abbrev Base := S.D .e
abbrev Unary := S.D (.rel unaryTy)
abbrev Binary := S.D (.rel binaryTy)
abbrev Ternary := S.D (.rel ternaryTy)

def un (F : Unary S) (x : Base S) : Prop := S.rel unaryTy F (x, PUnit.unit)
def bin (F : Binary S) (x y : Base S) : Prop := S.rel binaryTy F (x, y, PUnit.unit)
def tri (F : Ternary S) (x y z : Base S) : Prop :=
  S.rel ternaryTy F (x, y, z, PUnit.unit)

def UpperBound (X : Unary S) (le : Binary S) (F : Unary S) (b : Base S) : Prop :=
  un S X b ∧ ∀ x, un S F x → bin S le x b

def LeastUpperBound (X : Unary S) (le : Binary S) (F : Unary S) (s : Base S) : Prop :=
  UpperBound S X le F s ∧ ∀ b, UpperBound S X le F b → bin S le s b

def CompleteClause (X : Unary S) (le : Binary S) (F : Unary S) : Prop :=
  ((∀ x, un S F x → un S X x) ∧ (∃ x, un S F x) ∧
    (∃ b, UpperBound S X le F b)) → ∃ s, LeastUpperBound S X le F s

def CompleteNonempty (X : Unary S) (le : Binary S) : Prop :=
  ∀ F : Unary S, CompleteClause S X le F

def Inductive (X : Unary S) (add : Ternary S) (zero one : Base S) (F : Unary S) : Prop :=
  (∀ x, un S F x → un S X x) ∧ un S F zero ∧
    ∀ x y, un S F x → tri S add x one y → un S F y

def LeastClause (X : Unary S) (add : Ternary S) (zero one : Base S)
    (N F : Unary S) : Prop :=
  Inductive S X add zero one F → ∀ x, un S N x → un S F x

def LeastInductive (X : Unary S) (add : Ternary S) (zero one : Base S)
    (N : Unary S) : Prop :=
  Inductive S X add zero one N ∧ ∀ F : Unary S, LeastClause S X add zero one N F

def BinaryOperation (X : Unary S) (op : Ternary S) : Prop :=
  (∀ x y z, tri S op x y z → un S X x ∧ un S X y ∧ un S X z) ∧
  (∀ x y, un S X x → un S X y → ∃ z, tri S op x y z) ∧
  (∀ x y z w, tri S op x y z → tri S op x y w → z = w)

def LinearOrder (X : Unary S) (le : Binary S) : Prop :=
  (∀ x y, bin S le x y → un S X x ∧ un S X y) ∧
  (∀ x, un S X x → bin S le x x) ∧
  (∀ x y, bin S le x y → bin S le y x → x = y) ∧
  (∀ x y z, bin S le x y → bin S le y z → bin S le x z) ∧
  (∀ x y, un S X x → un S X y → bin S le x y ∨ bin S le y x)

def AdditiveLaws (X : Unary S) (add : Ternary S) (zero : Base S) : Prop :=
  (∀ x, un S X x → tri S add x zero x) ∧
  (∀ x y z, tri S add x y z → tri S add y x z) ∧
  (∀ a b c u v w, tri S add a b u → tri S add u c v →
    tri S add b c w → tri S add a w v) ∧
  (∀ x, un S X x → ∃ y, tri S add x y zero)

def MultiplicativeLaws (X : Unary S) (mul : Ternary S) (zero one : Base S) : Prop :=
  (∀ x, un S X x → tri S mul x one x) ∧
  (∀ x y z, tri S mul x y z → tri S mul y x z) ∧
  (∀ a b c u v w, tri S mul a b u → tri S mul u c v →
    tri S mul b c w → tri S mul a w v) ∧
  (∀ x, un S X x → x ≠ zero → ∃ y, tri S mul x y one)

def Distributive (add mul : Ternary S) : Prop :=
  ∀ a b c s t u v, tri S add b c s → tri S mul a s t →
    tri S mul a b u → tri S mul a c v → tri S add u v t

def OrderCompatible (X : Unary S) (le : Binary S) (add mul : Ternary S)
    (zero : Base S) : Prop :=
  (∀ a b c u v, bin S le a b → un S X c →
    tri S add a c u → tri S add b c v → bin S le u v) ∧
  (∀ a b c, bin S le zero a → bin S le zero b →
    tri S mul a b c → bin S le zero c)

def OrderedField (X : Unary S) (le : Binary S) (add mul : Ternary S)
    (zero one : Base S) : Prop :=
  un S X zero ∧ un S X one ∧ zero ≠ one ∧
  LinearOrder S X le ∧ BinaryOperation S X add ∧ BinaryOperation S X mul ∧
  AdditiveLaws S X add zero ∧ MultiplicativeLaws S X mul zero one ∧
  Distributive S add mul ∧ OrderCompatible S X le add mul zero

def IsReal (X : Unary S) (le : Binary S) (add mul : Ternary S)
    (zero one : Base S) (N : Unary S) : Prop :=
  OrderedField S X le add mul zero one ∧ CompleteNonempty S X le ∧
    LeastInductive S X add zero one N

end ClassicismZFC.TypedReal

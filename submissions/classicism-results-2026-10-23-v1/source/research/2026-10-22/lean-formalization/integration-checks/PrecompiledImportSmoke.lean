import Mathlib.Order.CompleteBooleanAlgebra
import Aesop.Script.Util
import ImportGraph.Lean.Environment

/-! Regression for the pinned library's IR signature companions in the
shared runner's import overlay. This is infrastructure evidence only. -/

example : True := by trivial

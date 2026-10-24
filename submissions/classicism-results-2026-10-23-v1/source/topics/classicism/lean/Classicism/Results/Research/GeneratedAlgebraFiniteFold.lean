import Classicism.Results.Research.GeneratedAlgebraFiniteFactored

/-! Generic induction elimination isolates the remaining forward-proof step.
Direct source: research/2026-10-22/notes/c5-generated-algebra-transfer-20261022.md,
sections 1-7, unpaginated original research (misc). No new premise is added.
The accepted original and constructor proofs remain in their own modules. -/

namespace Classicism.Research.GeneratedAlgebraFiniteFold
open Classicism.Paper
open Classicism.Research.GeneratedAlgebraFinite
open Classicism.Research.GeneratedAlgebraFiniteFactored

variable {μ0 ν0 : Type} [Rel μ0] [Rel ν0]
variable {μ1 ν1 : Type} [Rel μ1] [Rel ν1]
variable {μ2 ν2 : Type} [Rel μ2] [Rel ν2]

theorem source_fold0
    (f0 : μ0)
    (f1 : μ1)
    (f2 : μ0 → μ1)
    (f3 : μ0 → μ1 → μ2)
    (f4 : μ2 → μ1 → μ0 → μ0)
    (f5 : μ2 → μ2 → μ1)
    (x : μ0)
    (hx : (G0 (μ0 := μ0) (μ1 := μ1) (μ2 := μ2) f0 f1 f2 f3 f4 f5 x))
    (V0 : μ0 → Prop)
    (V1 : μ1 → Prop)
    (V2 : μ2 → Prop)
    : ((V0 f0)) → ((V1 f1)) → (∀ (x0 : μ0), (V0 x0) → (V1 (f2 x0))) → (∀ (x0 : μ0) (x1 : μ1), (V0 x0) → (V1 x1) → (V2 (f3 x0 x1))) → (∀ (x0 : μ2) (x1 : μ1) (x2 : μ0), (V2 x0) → (V1 x1) → (V0 x2) → (V0 (f4 x0 x1 x2))) → (∀ (x0 : μ2) (x1 : μ2), (V2 x0) → (V2 x1) → (V1 (f5 x0 x1))) → (V0 x) := (hx V0 V1 V2)

theorem source_fold1
    (f0 : μ0)
    (f1 : μ1)
    (f2 : μ0 → μ1)
    (f3 : μ0 → μ1 → μ2)
    (f4 : μ2 → μ1 → μ0 → μ0)
    (f5 : μ2 → μ2 → μ1)
    (x : μ1)
    (hx : (G1 (μ0 := μ0) (μ1 := μ1) (μ2 := μ2) f0 f1 f2 f3 f4 f5 x))
    (V0 : μ0 → Prop)
    (V1 : μ1 → Prop)
    (V2 : μ2 → Prop)
    : ((V0 f0)) → ((V1 f1)) → (∀ (x0 : μ0), (V0 x0) → (V1 (f2 x0))) → (∀ (x0 : μ0) (x1 : μ1), (V0 x0) → (V1 x1) → (V2 (f3 x0 x1))) → (∀ (x0 : μ2) (x1 : μ1) (x2 : μ0), (V2 x0) → (V1 x1) → (V0 x2) → (V0 (f4 x0 x1 x2))) → (∀ (x0 : μ2) (x1 : μ2), (V2 x0) → (V2 x1) → (V1 (f5 x0 x1))) → (V1 x) := (hx V0 V1 V2)

theorem source_fold2
    (f0 : μ0)
    (f1 : μ1)
    (f2 : μ0 → μ1)
    (f3 : μ0 → μ1 → μ2)
    (f4 : μ2 → μ1 → μ0 → μ0)
    (f5 : μ2 → μ2 → μ1)
    (x : μ2)
    (hx : (G2 (μ0 := μ0) (μ1 := μ1) (μ2 := μ2) f0 f1 f2 f3 f4 f5 x))
    (V0 : μ0 → Prop)
    (V1 : μ1 → Prop)
    (V2 : μ2 → Prop)
    : ((V0 f0)) → ((V1 f1)) → (∀ (x0 : μ0), (V0 x0) → (V1 (f2 x0))) → (∀ (x0 : μ0) (x1 : μ1), (V0 x0) → (V1 x1) → (V2 (f3 x0 x1))) → (∀ (x0 : μ2) (x1 : μ1) (x2 : μ0), (V2 x0) → (V1 x1) → (V0 x2) → (V0 (f4 x0 x1 x2))) → (∀ (x0 : μ2) (x1 : μ2), (V2 x0) → (V2 x1) → (V1 (f5 x0 x1))) → (V2 x) := (hx V0 V1 V2)

theorem forward0
    (f0 : μ0)
    (f1 : μ1)
    (f2 : μ0 → μ1)
    (f3 : μ0 → μ1 → μ2)
    (f4 : μ2 → μ1 → μ0 → μ0)
    (f5 : μ2 → μ2 → μ1)
    (H0 : ν0 → Prop)
    (H1 : ν1 → Prop)
    (H2 : ν2 → Prop)
    (g0 : ν0)
    (g1 : ν1)
    (g2 : ν0 → ν1)
    (g3 : ν0 → ν1 → ν2)
    (g4 : ν2 → ν1 → ν0 → ν0)
    (g5 : ν2 → ν2 → ν1)
    (q0 : μ0 → ν0)
    (q1 : μ1 → ν1)
    (q2 : μ2 → ν2)
    (hc0 : (H0 g0))
    (hc1 : (H1 g1))
    (hc2 : ∀ (y0 : ν0), (H0 y0) → (H1 (g2 y0)))
    (hc3 : ∀ (y0 : ν0) (y1 : ν1), (H0 y0) → (H1 y1) → (H2 (g3 y0 y1)))
    (hc4 : ∀ (y0 : ν2) (y1 : ν1) (y2 : ν0), (H2 y0) → (H1 y1) → (H0 y2) → (H0 (g4 y0 y1 y2)))
    (hc5 : ∀ (y0 : ν2) (y1 : ν2), (H2 y0) → (H2 y1) → (H1 (g5 y0 y1)))
    (hq0 : (q0 f0) = g0)
    (hq1 : (q1 f1) = g1)
    (hq2 : ∀ (x0 : μ0), (H0 (q0 x0)) → (q1 (f2 x0)) = (g2 (q0 x0)))
    (hq3 : ∀ (x0 : μ0) (x1 : μ1), (H0 (q0 x0)) → (H1 (q1 x1)) → (q2 (f3 x0 x1)) = (g3 (q0 x0) (q1 x1)))
    (hq4 : ∀ (x0 : μ2) (x1 : μ1) (x2 : μ0), (H2 (q2 x0)) → (H1 (q1 x1)) → (H0 (q0 x2)) → (q0 (f4 x0 x1 x2)) = (g4 (q2 x0) (q1 x1) (q0 x2)))
    (hq5 : ∀ (x0 : μ2) (x1 : μ2), (H2 (q2 x0)) → (H2 (q2 x1)) → (q1 (f5 x0 x1)) = (g5 (q2 x0) (q2 x1)))
    (x : μ0)
    (hx : (G0 (μ0 := μ0) (μ1 := μ1) (μ2 := μ2) f0 f1 f2 f3 f4 f5 x))
    : (K0 (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) H0 H1 H2 g0 g1 g2 g3 g4 g5 (q0 x)) := by
  apply (source_fold0 (μ0 := μ0) (μ1 := μ1) (μ2 := μ2) f0 f1 f2 f3 f4 f5 x hx (fun z : μ0 => (K0 (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) H0 H1 H2 g0 g1 g2 g3 g4 g5 (q0 z))) (fun z : μ1 => (K1 (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) H0 H1 H2 g0 g1 g2 g3 g4 g5 (q1 z))) (fun z : μ2 => (K2 (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) H0 H1 H2 g0 g1 g2 g3 g4 g5 (q2 z))))
  · exact (pullback_op0 (μ0 := μ0) (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) f0 H0 H1 H2 g0 g1 g2 g3 g4 g5 q0 hc0 hq0)
  · exact (pullback_op1 (μ1 := μ1) (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) f1 H0 H1 H2 g0 g1 g2 g3 g4 g5 q1 hc1 hq1)
  · intro x0 h0
    exact (pullback_op2 (μ0 := μ0) (μ1 := μ1) (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) f2 H0 H1 H2 g0 g1 g2 g3 g4 g5 q0 q1 hc2 hq2 x0 h0)
  · intro x0 x1 h0 h1
    exact (pullback_op3 (μ0 := μ0) (μ1 := μ1) (μ2 := μ2) (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) f3 H0 H1 H2 g0 g1 g2 g3 g4 g5 q0 q1 q2 hc3 hq3 x0 x1 h0 h1)
  · intro x0 x1 x2 h0 h1 h2
    exact (pullback_op4 (μ0 := μ0) (μ1 := μ1) (μ2 := μ2) (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) f4 H0 H1 H2 g0 g1 g2 g3 g4 g5 q0 q1 q2 hc4 hq4 x0 x1 x2 h0 h1 h2)
  · intro x0 x1 h0 h1
    exact (pullback_op5 (μ1 := μ1) (μ2 := μ2) (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) f5 H0 H1 H2 g0 g1 g2 g3 g4 g5 q1 q2 hc5 hq5 x0 x1 h0 h1)

theorem forward1
    (f0 : μ0)
    (f1 : μ1)
    (f2 : μ0 → μ1)
    (f3 : μ0 → μ1 → μ2)
    (f4 : μ2 → μ1 → μ0 → μ0)
    (f5 : μ2 → μ2 → μ1)
    (H0 : ν0 → Prop)
    (H1 : ν1 → Prop)
    (H2 : ν2 → Prop)
    (g0 : ν0)
    (g1 : ν1)
    (g2 : ν0 → ν1)
    (g3 : ν0 → ν1 → ν2)
    (g4 : ν2 → ν1 → ν0 → ν0)
    (g5 : ν2 → ν2 → ν1)
    (q0 : μ0 → ν0)
    (q1 : μ1 → ν1)
    (q2 : μ2 → ν2)
    (hc0 : (H0 g0))
    (hc1 : (H1 g1))
    (hc2 : ∀ (y0 : ν0), (H0 y0) → (H1 (g2 y0)))
    (hc3 : ∀ (y0 : ν0) (y1 : ν1), (H0 y0) → (H1 y1) → (H2 (g3 y0 y1)))
    (hc4 : ∀ (y0 : ν2) (y1 : ν1) (y2 : ν0), (H2 y0) → (H1 y1) → (H0 y2) → (H0 (g4 y0 y1 y2)))
    (hc5 : ∀ (y0 : ν2) (y1 : ν2), (H2 y0) → (H2 y1) → (H1 (g5 y0 y1)))
    (hq0 : (q0 f0) = g0)
    (hq1 : (q1 f1) = g1)
    (hq2 : ∀ (x0 : μ0), (H0 (q0 x0)) → (q1 (f2 x0)) = (g2 (q0 x0)))
    (hq3 : ∀ (x0 : μ0) (x1 : μ1), (H0 (q0 x0)) → (H1 (q1 x1)) → (q2 (f3 x0 x1)) = (g3 (q0 x0) (q1 x1)))
    (hq4 : ∀ (x0 : μ2) (x1 : μ1) (x2 : μ0), (H2 (q2 x0)) → (H1 (q1 x1)) → (H0 (q0 x2)) → (q0 (f4 x0 x1 x2)) = (g4 (q2 x0) (q1 x1) (q0 x2)))
    (hq5 : ∀ (x0 : μ2) (x1 : μ2), (H2 (q2 x0)) → (H2 (q2 x1)) → (q1 (f5 x0 x1)) = (g5 (q2 x0) (q2 x1)))
    (x : μ1)
    (hx : (G1 (μ0 := μ0) (μ1 := μ1) (μ2 := μ2) f0 f1 f2 f3 f4 f5 x))
    : (K1 (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) H0 H1 H2 g0 g1 g2 g3 g4 g5 (q1 x)) := by
  apply (source_fold1 (μ0 := μ0) (μ1 := μ1) (μ2 := μ2) f0 f1 f2 f3 f4 f5 x hx (fun z : μ0 => (K0 (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) H0 H1 H2 g0 g1 g2 g3 g4 g5 (q0 z))) (fun z : μ1 => (K1 (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) H0 H1 H2 g0 g1 g2 g3 g4 g5 (q1 z))) (fun z : μ2 => (K2 (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) H0 H1 H2 g0 g1 g2 g3 g4 g5 (q2 z))))
  · exact (pullback_op0 (μ0 := μ0) (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) f0 H0 H1 H2 g0 g1 g2 g3 g4 g5 q0 hc0 hq0)
  · exact (pullback_op1 (μ1 := μ1) (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) f1 H0 H1 H2 g0 g1 g2 g3 g4 g5 q1 hc1 hq1)
  · intro x0 h0
    exact (pullback_op2 (μ0 := μ0) (μ1 := μ1) (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) f2 H0 H1 H2 g0 g1 g2 g3 g4 g5 q0 q1 hc2 hq2 x0 h0)
  · intro x0 x1 h0 h1
    exact (pullback_op3 (μ0 := μ0) (μ1 := μ1) (μ2 := μ2) (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) f3 H0 H1 H2 g0 g1 g2 g3 g4 g5 q0 q1 q2 hc3 hq3 x0 x1 h0 h1)
  · intro x0 x1 x2 h0 h1 h2
    exact (pullback_op4 (μ0 := μ0) (μ1 := μ1) (μ2 := μ2) (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) f4 H0 H1 H2 g0 g1 g2 g3 g4 g5 q0 q1 q2 hc4 hq4 x0 x1 x2 h0 h1 h2)
  · intro x0 x1 h0 h1
    exact (pullback_op5 (μ1 := μ1) (μ2 := μ2) (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) f5 H0 H1 H2 g0 g1 g2 g3 g4 g5 q1 q2 hc5 hq5 x0 x1 h0 h1)

theorem forward2
    (f0 : μ0)
    (f1 : μ1)
    (f2 : μ0 → μ1)
    (f3 : μ0 → μ1 → μ2)
    (f4 : μ2 → μ1 → μ0 → μ0)
    (f5 : μ2 → μ2 → μ1)
    (H0 : ν0 → Prop)
    (H1 : ν1 → Prop)
    (H2 : ν2 → Prop)
    (g0 : ν0)
    (g1 : ν1)
    (g2 : ν0 → ν1)
    (g3 : ν0 → ν1 → ν2)
    (g4 : ν2 → ν1 → ν0 → ν0)
    (g5 : ν2 → ν2 → ν1)
    (q0 : μ0 → ν0)
    (q1 : μ1 → ν1)
    (q2 : μ2 → ν2)
    (hc0 : (H0 g0))
    (hc1 : (H1 g1))
    (hc2 : ∀ (y0 : ν0), (H0 y0) → (H1 (g2 y0)))
    (hc3 : ∀ (y0 : ν0) (y1 : ν1), (H0 y0) → (H1 y1) → (H2 (g3 y0 y1)))
    (hc4 : ∀ (y0 : ν2) (y1 : ν1) (y2 : ν0), (H2 y0) → (H1 y1) → (H0 y2) → (H0 (g4 y0 y1 y2)))
    (hc5 : ∀ (y0 : ν2) (y1 : ν2), (H2 y0) → (H2 y1) → (H1 (g5 y0 y1)))
    (hq0 : (q0 f0) = g0)
    (hq1 : (q1 f1) = g1)
    (hq2 : ∀ (x0 : μ0), (H0 (q0 x0)) → (q1 (f2 x0)) = (g2 (q0 x0)))
    (hq3 : ∀ (x0 : μ0) (x1 : μ1), (H0 (q0 x0)) → (H1 (q1 x1)) → (q2 (f3 x0 x1)) = (g3 (q0 x0) (q1 x1)))
    (hq4 : ∀ (x0 : μ2) (x1 : μ1) (x2 : μ0), (H2 (q2 x0)) → (H1 (q1 x1)) → (H0 (q0 x2)) → (q0 (f4 x0 x1 x2)) = (g4 (q2 x0) (q1 x1) (q0 x2)))
    (hq5 : ∀ (x0 : μ2) (x1 : μ2), (H2 (q2 x0)) → (H2 (q2 x1)) → (q1 (f5 x0 x1)) = (g5 (q2 x0) (q2 x1)))
    (x : μ2)
    (hx : (G2 (μ0 := μ0) (μ1 := μ1) (μ2 := μ2) f0 f1 f2 f3 f4 f5 x))
    : (K2 (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) H0 H1 H2 g0 g1 g2 g3 g4 g5 (q2 x)) := by
  apply (source_fold2 (μ0 := μ0) (μ1 := μ1) (μ2 := μ2) f0 f1 f2 f3 f4 f5 x hx (fun z : μ0 => (K0 (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) H0 H1 H2 g0 g1 g2 g3 g4 g5 (q0 z))) (fun z : μ1 => (K1 (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) H0 H1 H2 g0 g1 g2 g3 g4 g5 (q1 z))) (fun z : μ2 => (K2 (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) H0 H1 H2 g0 g1 g2 g3 g4 g5 (q2 z))))
  · exact (pullback_op0 (μ0 := μ0) (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) f0 H0 H1 H2 g0 g1 g2 g3 g4 g5 q0 hc0 hq0)
  · exact (pullback_op1 (μ1 := μ1) (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) f1 H0 H1 H2 g0 g1 g2 g3 g4 g5 q1 hc1 hq1)
  · intro x0 h0
    exact (pullback_op2 (μ0 := μ0) (μ1 := μ1) (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) f2 H0 H1 H2 g0 g1 g2 g3 g4 g5 q0 q1 hc2 hq2 x0 h0)
  · intro x0 x1 h0 h1
    exact (pullback_op3 (μ0 := μ0) (μ1 := μ1) (μ2 := μ2) (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) f3 H0 H1 H2 g0 g1 g2 g3 g4 g5 q0 q1 q2 hc3 hq3 x0 x1 h0 h1)
  · intro x0 x1 x2 h0 h1 h2
    exact (pullback_op4 (μ0 := μ0) (μ1 := μ1) (μ2 := μ2) (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) f4 H0 H1 H2 g0 g1 g2 g3 g4 g5 q0 q1 q2 hc4 hq4 x0 x1 x2 h0 h1 h2)
  · intro x0 x1 h0 h1
    exact (pullback_op5 (μ1 := μ1) (μ2 := μ2) (ν0 := ν0) (ν1 := ν1) (ν2 := ν2) f5 H0 H1 H2 g0 g1 g2 g3 g4 g5 q1 q2 hc5 hq5 x0 x1 h0 h1)

end Classicism.Research.GeneratedAlgebraFiniteFold

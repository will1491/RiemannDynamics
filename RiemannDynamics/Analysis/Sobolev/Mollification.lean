/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Sobolev.WeakDeriv
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Smooth approximation in `Lᵖ(ℂ)`

The Sobolev theory needs that smooth, compactly supported functions are dense
in `Lᵖ`. On `ℂ` (with Lebesgue measure) this is the specialization of Mathlib's
general result `MeasureTheory.Lp.dense_hasCompactSupport_contDiff`. We record
the two forms the analytic engine uses:

* `dense_smooth_hasCompactSupport_Lp` — `C^∞_c` functions are dense in
  `Lᵖ ℂ p volume`;
* `exists_contDiff_hasCompactSupport_eLpNorm_sub_le` — the quantitative form:
  any `Lᵖ` function is approximated in `eLpNorm` to arbitrary precision by a
  smooth compactly supported function.

These are the mollification inputs to the Cauchy/Beurling transform estimates
and the quasiconformal regularity arguments downstream.
-/

open MeasureTheory Complex
open scoped ContDiff ENNReal

namespace RiemannDynamics

/-- **Density of `C^∞_c` in `Lᵖ(ℂ)`.** Smooth compactly supported functions are
dense in `Lᵖ ℂ p volume` for `p ≠ ∞`. -/
theorem dense_smooth_hasCompactSupport_Lp {p : ℝ≥0∞} (hp : p ≠ ⊤) [Fact (1 ≤ p)] :
    Dense {F : Lp ℂ p (volume : Measure ℂ) |
      ∃ g : ℂ → ℂ, F =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} := by
  exact MeasureTheory.Lp.dense_hasCompactSupport_contDiff hp

/-- **Quantitative smooth approximation in `Lᵖ(ℂ)`.** Every `Lᵖ` function is
approximated in `eLpNorm` to arbitrary precision by a smooth compactly supported
function. -/
theorem exists_contDiff_hasCompactSupport_eLpNorm_sub_le {p : ℝ≥0∞} (hp : p ≠ ⊤)
    (hp₂ : 1 ≤ p) {f : ℂ → ℂ} (hf : MemLp f p (volume : Measure ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      eLpNorm (f - g) p (volume : Measure ℂ) ≤ ENNReal.ofReal ε := by
  exact hf.exist_eLpNorm_sub_le hp hp₂ hε

end RiemannDynamics

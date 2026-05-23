/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Hyperbolic.DiskMetric
import Mathlib.Analysis.Complex.Schwarz

/-!
# Schwarz–Pick inequality on the unit disk

A holomorphic self-map of the open unit disk `𝔻 = Metric.ball (0 : ℂ) 1`
is non-expansive with respect to the Poincaré hyperbolic distance
defined in `DiskMetric.lean`. The proof reduces — via the Möbius
automorphisms of `𝔻` sending an arbitrary point to the origin — to
the centered Schwarz lemma already available in Mathlib as
`Complex.dist_le_dist_of_mapsTo_ball`.
-/

namespace RiemannDynamics

open Complex Real Metric Set

/-- **Schwarz–Pick inequality.** A holomorphic self-map of the open unit
disk is non-expansive with respect to the Poincaré hyperbolic distance. -/
theorem schwarzPick {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hf : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    hyperbolicDistDisk (f z) (f w) ≤ hyperbolicDistDisk z w := by
  sorry

end RiemannDynamics

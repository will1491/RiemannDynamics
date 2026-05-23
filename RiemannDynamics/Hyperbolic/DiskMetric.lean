/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Defs

/-!
# Poincaré hyperbolic metric on the unit disk

The Poincaré hyperbolic distance on the open unit disk
`𝔻 := Metric.ball (0 : ℂ) 1`, given by the formula

  `d_𝔻(z,w) = 2 · arsinh ( |z − w| / √((1 − |z|²)(1 − |w|²)) )`.

The closed formula is used directly; outside `𝔻` the formula returns the
"junk" value `0` because of Mathlib's convention that
`Real.sqrt` of a negative number is `0`.

We keep the public API minimal: this file only establishes the
elementary distance axioms (self, symmetry, non-negativity, and a
non-degeneracy statement on the disk). The triangle inequality and
the proof that the disk becomes a `MetricSpace` are recorded as
statements but their proofs are deferred to a subsequent pass.

`SchwarzPick.lean` uses this metric to state the Schwarz–Pick
inequality for holomorphic self-maps of `𝔻`.
-/

namespace RiemannDynamics

open Complex Real Metric

/-- The Poincaré hyperbolic distance on the open unit disk
`𝔻 = Metric.ball (0 : ℂ) 1`. -/
noncomputable def hyperbolicDistDisk (z w : ℂ) : ℝ :=
  2 * Real.arsinh (‖z - w‖ / Real.sqrt ((1 - ‖z‖^2) * (1 - ‖w‖^2)))

/-- The hyperbolic distance from a point to itself is zero. -/
theorem hyperbolicDistDisk_self (z : ℂ) : hyperbolicDistDisk z z = 0 := by
  simp [hyperbolicDistDisk, Real.arsinh_zero]

/-- The hyperbolic distance is symmetric. -/
theorem hyperbolicDistDisk_comm (z w : ℂ) :
    hyperbolicDistDisk z w = hyperbolicDistDisk w z := by
  unfold hyperbolicDistDisk
  rw [norm_sub_rev z w, mul_comm (1 - ‖w‖^2) (1 - ‖z‖^2)]

/-- The hyperbolic distance is non-negative. -/
theorem hyperbolicDistDisk_nonneg (z w : ℂ) : 0 ≤ hyperbolicDistDisk z w := by
  unfold hyperbolicDistDisk
  have h1 : 0 ≤ ‖z - w‖ / Real.sqrt ((1 - ‖z‖^2) * (1 - ‖w‖^2)) := by positivity
  have h2 : 0 ≤ Real.arsinh (‖z - w‖ / Real.sqrt ((1 - ‖z‖^2) * (1 - ‖w‖^2))) :=
    Real.arsinh_nonneg_iff.mpr h1
  linarith

/-- On the unit disk, the hyperbolic distance vanishes only on the diagonal. -/
theorem hyperbolicDistDisk_eq_zero_iff {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    hyperbolicDistDisk z w = 0 ↔ z = w := by
  have hz' : ‖z‖ < 1 := by rwa [mem_ball, dist_zero_right] at hz
  have hw' : ‖w‖ < 1 := by rwa [mem_ball, dist_zero_right] at hw
  have hz2 : 0 < 1 - ‖z‖^2 := by nlinarith [norm_nonneg z]
  have hw2 : 0 < 1 - ‖w‖^2 := by nlinarith [norm_nonneg w]
  have hprod : 0 < (1 - ‖z‖^2) * (1 - ‖w‖^2) := mul_pos hz2 hw2
  have hsqrt : 0 < Real.sqrt ((1 - ‖z‖^2) * (1 - ‖w‖^2)) := Real.sqrt_pos.mpr hprod
  refine ⟨fun h => ?_, fun h => h ▸ hyperbolicDistDisk_self z⟩
  unfold hyperbolicDistDisk at h
  have harsh : Real.arsinh
      (‖z - w‖ / Real.sqrt ((1 - ‖z‖^2) * (1 - ‖w‖^2))) = 0 := by linarith
  have hdiv : ‖z - w‖ / Real.sqrt ((1 - ‖z‖^2) * (1 - ‖w‖^2)) = 0 :=
    Real.arsinh_eq_zero_iff.mp harsh
  have hnum : ‖z - w‖ = 0 :=
    (div_eq_zero_iff.mp hdiv).resolve_right hsqrt.ne'
  exact sub_eq_zero.mp (norm_eq_zero.mp hnum)

/-- The triangle inequality for the hyperbolic distance on the disk.
Statement only; the proof typically goes via the conformal isomorphism
between the disk and the upper half-plane and Mathlib's metric structure
on `UpperHalfPlane`. -/
theorem hyperbolicDistDisk_triangle {z w v : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) (hv : v ∈ ball (0 : ℂ) 1) :
    hyperbolicDistDisk z v ≤ hyperbolicDistDisk z w + hyperbolicDistDisk w v := by
  sorry

end RiemannDynamics

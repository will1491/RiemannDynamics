/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Regularity.RingModulus
import RiemannDynamics.QC.Regularity.GeometricDilatation

/-!
# Quasiconformal transport of the round-annulus ring modulus

For a geometrically `K`-quasiconformal homeomorphism `f`, the modulus of the image of the
connecting family of a round annulus is at most `K` times the round-annulus modulus
`2π / log(R/r)`.

The route runs through the pointwise dilatation bound `geometric_pointwise_dilatation`: the
length–area change of variables driven by `‖(Df)⁻¹‖² · det (Df) ≤ K` transports the extremal
density of the source ring to an admissible density for the image connecting family with energy
inflated by at most `K` (`ring_image_modulus_le`). Combined with the closed-form source modulus
`source_ring_modulus` (`= 2π / log(R/r)`), this gives the transported bound.

## Main statements

* `source_ring_modulus` — the round-annulus connecting-family modulus equals `2π / log(R/r)`;
* `ring_image_modulus_le` — the dilatation-controlled transport of the connecting-family modulus;
* `geometric_ring_modulus_transport` — the image ring modulus is at most `K · (2π / log(R/r))`.
-/

open MeasureTheory
open scoped ENNReal NNReal Topology Real

namespace RiemannDynamics

/-- **Closed form of the round-annulus modulus.** For radii `0 < r < R`, the conformal modulus of
the connecting family joining the inner circle `{|z - z₀| = r}` to the outer circle
`{|z - z₀| = R}` inside the round annulus equals `2π / log(R/r)`. This is `ringModulus_roundAnnulus`
read through the definition of `ringModulus` as the connecting-family modulus. -/
theorem source_ring_modulus {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    curveModulus (connectingCurveFamily (innerCircle z₀ r) (outerCircle z₀ R)
        (RoundAnnulus z₀ r R))
      = ENNReal.ofReal (2 * Real.pi / Real.log (R / r)) :=
  ringModulus_roundAnnulus hr hrR

/-- **Dilatation-controlled transport of the connecting-family modulus.** Given the pointwise
dilatation bound `‖(Df)⁻¹‖² · det (Df) ≤ K` almost everywhere (the output of
`geometric_pointwise_dilatation`) and the regularity of a geometrically `K`-quasiconformal
homeomorphism `f`, the image of the connecting family of the round annulus has modulus at most `K`
times the source connecting-family modulus. The image family joins the image inner circle
`f '' innerCircle` to the image outer circle `f '' outerCircle` inside the image annulus
`f '' RoundAnnulus`. The proof is the length–area change of variables: the extremal density of the
source ring is transported to an admissible density for the image family with energy inflated by at
most the dilatation factor `K`. -/
theorem ring_image_modulus_le {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    (hdil : ∀ᵐ z : ℂ,
      ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 * (fderiv ℝ f z).det ≤ K)
    {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    curveModulus (connectingCurveFamily (f '' innerCircle z₀ r) (f '' outerCircle z₀ R)
        (f '' RoundAnnulus z₀ r R))
      ≤ ENNReal.ofReal K * curveModulus (connectingCurveFamily (innerCircle z₀ r)
        (outerCircle z₀ R) (RoundAnnulus z₀ r R)) := by
  sorry

/-- **Quasiconformal transport of the round-annulus modulus.** For a geometrically
`K`-quasiconformal homeomorphism `f`, the modulus of the image of the round-annulus connecting
family is at most `K · (2π / log(R/r))`. This chains the dilatation-controlled transport
`ring_image_modulus_le`, driven by the pointwise dilatation bound
`geometric_pointwise_dilatation`, with the closed-form source modulus `source_ring_modulus`. -/
theorem geometric_ring_modulus_transport {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    curveModulus (connectingCurveFamily (f '' innerCircle z₀ r) (f '' outerCircle z₀ R)
        (f '' RoundAnnulus z₀ r R))
      ≤ ENNReal.ofReal K * ENNReal.ofReal (2 * Real.pi / Real.log (R / r)) := by
  have hdil := geometric_pointwise_dilatation hf
  calc curveModulus (connectingCurveFamily (f '' innerCircle z₀ r) (f '' outerCircle z₀ R)
          (f '' RoundAnnulus z₀ r R))
      ≤ ENNReal.ofReal K * curveModulus (connectingCurveFamily (innerCircle z₀ r)
          (outerCircle z₀ R) (RoundAnnulus z₀ r R)) :=
        ring_image_modulus_le hf hdil hr hrR
    _ = ENNReal.ofReal K * ENNReal.ofReal (2 * Real.pi / Real.log (R / r)) := by
        rw [source_ring_modulus hr hrR]

/-- **(STAR) Shell-ratio bound from quasiconformal quasi-invariance.** For a geometrically
`K`-quasiconformal homeomorphism `f`, the round annulus `a < |z - x₀| < b` is mapped to a ring whose
inner and outer shells have controlled ratio: the outer radius (the farthest image point of the
inner disc `closedBall x₀ a` from `f x₀`) over the inner radius (the distance from `f x₀` to the
image outer sphere `f '' sphere x₀ b`) satisfies, up to the universal constant `60`,
`(outer / inner) ^ 2 / 60 ≤ K · (2π / log (b / a))`.

This is the quadrilateral quasi-invariance of the ring modulus recast as a geometric shell bound:
the transported ring modulus `geometric_ring_modulus_transport` bounds the extremal length of the
connecting family, and comparison with the round-annulus modulus of the image shells converts the
modulus inequality into the shell-ratio inequality (the `60` absorbs the Grötzsch–Teichmüller
comparison constants). The regularity pack (`hae_diff`, `hae_det`) is threaded to match the eventual
proof, which chains `geometric_inverse_conditionN`, `geometric_sliced_noSingular`, the pointwise
dilatation bound, and the L-curve length adapter. -/
theorem geometric_ring_star {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    (hhomeo : IsHomeomorph f)
    (hae_diff : ∀ᵐ z : ℂ, DifferentiableAt ℝ f z)
    (hae_det : ∀ᵐ z : ℂ, 0 < (fderiv ℝ f z).det)
    {x₀ : ℂ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (sSup {r : ℝ | ∃ ζ ∈ f '' Metric.closedBall x₀ a, r = dist ζ (f x₀)}
        / Metric.infDist (f x₀) (f '' Metric.sphere x₀ b)) ^ 2 / 60
      ≤ K * (2 * Real.pi / Real.log (b / a)) := by
  sorry

end RiemannDynamics

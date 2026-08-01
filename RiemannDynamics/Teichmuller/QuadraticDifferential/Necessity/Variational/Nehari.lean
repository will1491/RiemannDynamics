/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Variational.Schwarzian

/-!
# The Nehari bound

An injective holomorphic map on a ball has Schwarzian derivative bounded by the ball's
Poincaré density: `(R² − |z − c|²)² |S f z| ≤ 6 R²`. The route is classical — the
Gronwall area theorem bounds the coefficients of a univalent map of the exterior disk,
the square-root transform turns it into the second-coefficient inequality
`|a₃ − a₂²| ≤ 1` for a normalized univalent map of the disk, the Schwarzian at the
center is `6(a₃ − a₂²)`, and disk automorphisms transport the center bound to every
point. Exhausting the lower half plane by balls yields the half-plane form
`4 y² |S f z| ≤ 6` consumed by the Bers-type map of the variational tier.

* `schwarzian_le_of_injOn_ball` — the Nehari bound on a ball.
* `schwarzian_le_of_injOn_lower` — the Nehari bound on the lower half plane.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-- **The Nehari bound on a ball**: an injective holomorphic map on an open ball
satisfies `(R² − |z − c|²)² |S f z| ≤ 6 R²`. -/
theorem schwarzian_le_of_injOn_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball c R))
    (hinj : Set.InjOn f (Metric.ball c R)) {z : ℂ} (hz : z ∈ Metric.ball c R) :
    (R ^ 2 - ‖z - c‖ ^ 2) ^ 2 * ‖schwarzian f z‖ ≤ 6 * R ^ 2 := by
  sorry

/-- **The Nehari bound on the lower half plane**: an injective holomorphic map on the
open lower half plane satisfies `4 y² |S f z| ≤ 6`. -/
theorem schwarzian_le_of_injOn_lower {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | z.im < 0})
    (hinj : Set.InjOn f {z : ℂ | z.im < 0}) {z : ℂ} (hz : z.im < 0) :
    (2 * z.im) ^ 2 * ‖schwarzian f z‖ ≤ 6 := by
  sorry

end RiemannDynamics

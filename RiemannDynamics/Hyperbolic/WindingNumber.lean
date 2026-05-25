/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Winding number and the argument principle

This file develops the elementary winding-number theory needed for the
`λ : F^o ≅ {Im w > 0}` biholomorphism in `Gamma2FundamentalDomain.lean`.

The main definition is `circleWindingNumber c R w`, which counts how
many times the boundary of the disk `B(c, R)` winds around `w`. For
`w ∈ ball c R` this is `1`; for `w ∉ closedBall c R` this is `0`.

This is the special case of the general winding-number theory; the
piecewise-smooth-contour generalization (needed for `F^o`'s boundary)
is left for a future session.

## Main definitions

* `Complex.circleWindingNumber c R w` — the contour integral
  `(2πi)⁻¹ ∮_{|z−c|=R} (z − w)⁻¹ dz`.

## Main results

* `Complex.circleWindingNumber_inside` — winding number is `1` for
  points strictly inside the circle.
* `Complex.circleWindingNumber_outside` — winding number is `0` for
  points strictly outside the closed disk.

## References

* Standard complex analysis: Ahlfors, Conway, Stein-Shakarchi.
-/

namespace Complex

open MeasureTheory

/-- The winding number of the standard counterclockwise parameterization of
the circle `|z − c| = R` around a point `w`, defined as
`(2πi)⁻¹ ∮_{|z−c|=R} (z − w)⁻¹ dz`. -/
noncomputable def circleWindingNumber (c : ℂ) (R : ℝ) (w : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * ∮ z in C(c, R), (z - w)⁻¹

/-- For a point `w` strictly inside the circle of radius `R` around `c`,
the winding number equals `1`. -/
theorem circleWindingNumber_inside (c : ℂ) {R : ℝ} {w : ℂ} (hw : w ∈ Metric.ball c R) :
    circleWindingNumber c R w = 1 := by
  unfold circleWindingNumber
  rw [circleIntegral.integral_sub_inv_of_mem_ball hw]
  have h_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  field_simp

/-- For a point `w` strictly outside the closed disk of radius `R` around
`c`, the winding number equals `0`. (Cauchy-Goursat applied to the
holomorphic integrand `(z − w)⁻¹` on the closed disk.) -/
theorem circleWindingNumber_outside (c : ℂ) {R : ℝ} (hR : 0 ≤ R) {w : ℂ}
    (hw : w ∉ Metric.closedBall c R) :
    circleWindingNumber c R w = 0 := by
  unfold circleWindingNumber
  have h_diff : DifferentiableOn ℂ (fun z : ℂ => (z - w)⁻¹) (Metric.closedBall c R) := by
    intro z hz
    have hz_ne : z - w ≠ 0 := by
      intro h
      apply hw
      have : z = w := by linear_combination h
      rw [← this]; exact hz
    exact ((differentiableAt_id.sub_const w).inv hz_ne).differentiableWithinAt
  have h_cont : ContinuousOn (fun z : ℂ => (z - w)⁻¹) (Metric.closedBall c R) :=
    h_diff.continuousOn
  have h_integral : (∮ z in C(c, R), (z - w)⁻¹) = 0 := by
    refine circleIntegral_eq_zero_of_differentiable_on_off_countable hR
      Set.countable_empty h_cont ?_
    intro z hz
    have hz_ball : z ∈ Metric.ball c R := hz.1
    have hz_ne : z - w ≠ 0 := by
      intro h
      apply hw
      have : z = w := by linear_combination h
      rw [← this]; exact Metric.ball_subset_closedBall hz_ball
    exact (differentiableAt_id.sub_const w).inv hz_ne
  rw [h_integral, mul_zero]

/-- The winding number of a circle around its own center is `1` (for
positive radius). -/
theorem circleWindingNumber_self (c : ℂ) {R : ℝ} (hR : 0 < R) :
    circleWindingNumber c R c = 1 :=
  circleWindingNumber_inside c (Metric.mem_ball_self hR)

/-! ## Deferred infrastructure

The following statements complete the winding-number / argument-principle
toolkit needed to close `modularLambdaH_image_fundamentalDomainInterior`
(in `Gamma2FundamentalDomain.lean`). They are stated here as deferred
sorries; each has a clear classical proof. The main use is in counting
preimages of `w` under the modular function `λ` inside a fundamental
domain via a contour integral. -/

/-- **Argument principle for circles (deferred).** For a holomorphic
function `f` on a neighborhood of the closed disk `closedBall c R`,
with `f(z) ≠ w` on the sphere `|z − c| = R`, the contour integral
`(2πi)⁻¹ ∮_{C(c, R)} f'(z) / (f(z) − w) dz` equals the number of
preimages of `w` inside the open disk (counted with multiplicity).

The full proof factors through the residue theorem (which itself can
be derived from the Cauchy integral formula applied to the Laurent
expansion of `f'/(f − w)` near each preimage). -/
theorem argumentPrinciple_circle
    (f : ℂ → ℂ) (c : ℂ) {R : ℝ} (_hR : 0 < R) (_w : ℂ)
    (_hf : DifferentiableOn ℂ f (Metric.closedBall c R))
    (_hf_ne_w : ∀ z ∈ Metric.sphere c R, f z ≠ _w) :
    ∃ n : ℕ, (2 * Real.pi * Complex.I)⁻¹ *
      (∮ z in C(c, R), deriv f z / (f z - _w)) = (n : ℂ) := by
  sorry

/-- **Rectangle winding number (deferred).** Analog of `circleWindingNumber`
for an axis-aligned closed rectangle, parameterized counterclockwise. The
value is `1` if `w` is in the open rectangle interior, `0` if `w` is
outside the closed rectangle.

The full proof would parameterize the four sides as `intervalIntegral`s,
sum, and use that the integrand is holomorphic off `w` to apply
Cauchy-Goursat for the outside case and a deformation to a small
circular contour for the inside case. -/
theorem rectangleWindingNumber_inside_eq_one
    (a b c d : ℝ) (_hab : a < b) (_hcd : c < d) {w : ℂ}
    (_hw_re : a < w.re ∧ w.re < b) (_hw_im : c < w.im ∧ w.im < d) :
    (2 * Real.pi * Complex.I)⁻¹ * (
      (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - w)⁻¹) +
      Complex.I * (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) -
      (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - w)⁻¹) -
      Complex.I * (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹))
    = 1 := by
  sorry

end Complex

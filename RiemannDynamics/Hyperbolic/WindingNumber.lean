/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Winding number and the argument principle

Winding-number theory for the `λ : F^o ≅ {Im w > 0}` biholomorphism
in `Gamma2FundamentalDomain.lean`.

## Definitions

* `Complex.circleWindingNumber c R w` — circle case,
  `(2πi)⁻¹ ∮_{|z−c|=R} (z − w)⁻¹ dz`.
* `Complex.pathContourIntegral γ a b f` — contour integral
  `∫_a^b f(γ t) · γ'(t) dt` of `f` along the path `γ : ℝ → ℂ`
  from parameter `a` to `b`.
* `Complex.pathWindingNumber γ a b w` — winding number of a closed
  parameterized path `γ : [a, b] → ℂ` around `w`, defined as
  `(2πi)⁻¹ ∫_a^b γ'(t) / (γ(t) − w) dt`.

## Main results

* `Complex.circleWindingNumber_inside` — winding number `1` for points
  strictly inside the circle (via Mathlib's
  `circleIntegral.integral_sub_inv_of_mem_ball`).
* `Complex.circleWindingNumber_outside` — winding number `0` for
  points strictly outside the closed disk (Cauchy-Goursat on the
  holomorphic integrand).
* `Complex.circleWindingNumber_self` — special case `w = c`.

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

/-! ## Path-integral winding number

The following definitions and theorems extend the toolkit to general
parameterized paths and rectangle / argument-principle versions used
by `modularLambdaH_image_fundamentalDomainInterior` (in
`Gamma2FundamentalDomain.lean`) to count preimages of `w` under the
modular function `λ` inside a fundamental domain. -/

/-- Contour integral of `f : ℂ → ℂ` along a parameterized path
`γ : ℝ → ℂ` from `a` to `b`:
`∫_a^b f(γ(t)) · γ'(t) dt`. -/
noncomputable def pathContourIntegral (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∫ t in a..b, f (γ t) * deriv γ t

/-- Winding number of the parameterized path `γ : [a, b] → ℂ` around a
point `w`. For a closed path `γ` not passing through `w`, this is
integer-valued and equals the number of times `γ` winds around `w`
counterclockwise. -/
noncomputable def pathWindingNumber (γ : ℝ → ℂ) (a b : ℝ) (w : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * pathContourIntegral γ a b (fun z => (z - w)⁻¹)

/-- **Argument principle for circles (analytic form).** For a holomorphic
function `g` on a closed disk (analytic in an open neighborhood of every
point of the disk) that is nonzero on the boundary sphere, the contour
integral `(2πi)⁻¹ ∮_{C(c, R)} g'(z)/g(z) dz` is a non-negative integer,
equal to the count of zeros of `g` inside the open disk (with
multiplicity).

This is the analytic form of the argument principle, with `g` playing the
role of `f − w`. The `AnalyticOnNhd` hypothesis (rather than mere
`DifferentiableOn`) is needed because `deriv g z` at boundary points of
the closed disk is the Fréchet derivative, which requires full
differentiability in a neighborhood, not just differentiability within
the disk.

The proof has the following classical structure (residue theorem):

* By `IsCompact.exists_thickening_subset_open` applied to `closedBall ⊆`
  `{z | AnalyticAt ℂ g z}` (`isOpen_analyticAt`), extract a uniform `δ > 0`
  with `g` analytic on the open thickening `U := thickening δ closedBall`.
  This open set contains `closedBall` and is contained in the analyticity
  domain; shrinking `δ` further if needed (using continuity of `g` and
  `g ≠ 0` on the sphere) one also obtains `g ≠ 0` on the annulus around
  the sphere, so all zeros of `g` in `U` lie in `closedBall(c, R)`,
  which is compact, hence finite.
* Apply `MeromorphicOn.extract_zeros_poles` on `U`: this yields a finite
  Weierstrass-style factorization
  `g =ᶠ[codiscreteWithin U] (∏ᶠ u, (· − u)^{divisor g U u}) • h`
  with `h : ℂ → ℂ` analytic on `U` and non-vanishing on `U`.
* By continuity, the factorization extends from the codiscrete subset
  to all of `closedBall`; in particular it holds on the sphere
  (which contains no zeros).
* Differentiate and divide: by `logDeriv_mul` and `logDeriv_fun_pow`,
  `deriv g / g = ∑ᶠ u, (divisor g U u) / (· − u) + deriv h / h`
  on the sphere.
* Integrate term by term:
  - `∮ 1/(z − u) = 2πi` for each zero `u` inside the disk
    (`circleIntegral.integral_sub_inv_of_mem_ball`), so the rational
    part contributes `2πi · ∑ᶠ u, divisor g U u`.
  - `∮ deriv h / h = 0` because `h` is analytic and non-vanishing on
    `U ⊇ closedBall` (apply RMT4's `cindex_eq_zero`).
* Divide by `2πi`: the result is `∑ᶠ u, divisor g U u`, a non-negative
  integer (`AnalyticOnNhd.divisor_nonneg`).

The full Lean translation is left as future work (~300-500 lines): the
compactness/finiteness arguments alone require ~80 lines, the
`extract_zeros_poles` application and its hypothesis verification ~50
lines, the integrand decomposition via `logDeriv` ~80 lines, and the
per-term integration plus summation ~100 lines. -/
theorem cIntegralLogDeriv_isNat_of_nonzero_on_sphere
    (g : ℂ → ℂ) (c : ℂ) {R : ℝ} (_hR : 0 < R)
    (_hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (_hg_sphere : ∀ z ∈ Metric.sphere c R, g z ≠ 0) :
    ∃ n : ℕ, (2 * Real.pi * Complex.I)⁻¹ *
      (∮ z in C(c, R), deriv g z / g z) = (n : ℂ) := by
  sorry

/-- **Argument principle for circles.** For a holomorphic function `f` on
a neighborhood of `closedBall c R` (analytic at every point of the closed
disk), with `f(z) ≠ w` on the sphere `|z − c| = R`, the contour integral
`(2πi)⁻¹ ∮_{C(c, R)} f'(z) / (f(z) − w) dz` is a natural number, equal to
the count of preimages of `w` inside the open disk (with multiplicity).
Follows from `cIntegralLogDeriv_isNat_of_nonzero_on_sphere` applied to
`g(z) := f(z) − w` (whose derivative coincides with `deriv f` since the
additive constant `w` contributes zero). -/
theorem argumentPrinciple_circle
    (f : ℂ → ℂ) (c : ℂ) {R : ℝ} (_hR : 0 < R) (_w : ℂ)
    (_hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (_hf_ne_w : ∀ z ∈ Metric.sphere c R, f z ≠ _w) :
    ∃ n : ℕ, (2 * Real.pi * Complex.I)⁻¹ *
      (∮ z in C(c, R), deriv f z / (f z - _w)) = (n : ℂ) := by
  have hg : AnalyticOnNhd ℂ (fun z => f z - _w) (Metric.closedBall c R) :=
    fun z hz => (_hf z hz).sub analyticAt_const
  have hg_sphere : ∀ z ∈ Metric.sphere c R, (fun z => f z - _w) z ≠ 0 := by
    intro z hz hzero
    exact _hf_ne_w z hz (sub_eq_zero.mp hzero)
  obtain ⟨n, hn⟩ :=
    cIntegralLogDeriv_isNat_of_nonzero_on_sphere (fun z => f z - _w) c _hR hg hg_sphere
  refine ⟨n, ?_⟩
  rw [← hn]
  congr 1
  apply circleIntegral.integral_congr _hR.le
  intro z _
  change deriv f z / (f z - _w) = deriv (fun y => f y - _w) z / (f z - _w)
  rw [deriv_sub_const _w]

/-- **Rectangle winding number.** The winding number of the
counterclockwise boundary of the closed rectangle `[a, b] × [c, d]`
around an interior point `w` equals `1`.

The four edges are evaluated separately by FTC. On the bottom, top,
and right edges the relevant path stays in `Complex.slitPlane`, so the
principal `Complex.log` antiderivative applies directly. The left
edge `x = a` crosses the negative real axis at `y = w.im` (because
`a < w.re`), so we instead use the translated branch
`logL z := Complex.log(-z)` (analytic for `Re z < 0`); the
contribution from this branch is shifted by `2π i` compared to the
principal log, and supplies the answer. Summing the four edges and
applying `Complex.arg_neg_eq_arg_*_pi_of_im_*` collapses the result to
`2π i`, which divided by `2π i` gives `1`. -/
theorem rectangleWindingNumber_inside_eq_one
    (a b c d : ℝ) (_hab : a < b) (_hcd : c < d) {w : ℂ}
    (hw_re : a < w.re ∧ w.re < b) (hw_im : c < w.im ∧ w.im < d) :
    (2 * Real.pi * Complex.I)⁻¹ * (
      (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - w)⁻¹) +
      Complex.I * (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) -
      (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - w)⁻¹) -
      Complex.I * (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹))
    = 1 := by
  -- 2πi ≠ 0, used for the final division.
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  -- Real/imag formulas on each edge.
  have him_bot : ∀ x : ℝ, ((x : ℂ) + (c : ℂ) * Complex.I - w).im = c - w.im := by
    intro x; simp
  have him_top : ∀ x : ℝ, ((x : ℂ) + (d : ℂ) * Complex.I - w).im = d - w.im := by
    intro x; simp
  have hre_right : ∀ y : ℝ, ((b : ℂ) + (y : ℂ) * Complex.I - w).re = b - w.re := by
    intro y; simp
  have hre_left_neg : ∀ y : ℝ, (-((a : ℂ) + (y : ℂ) * Complex.I - w)).re = w.re - a := by
    intro y; simp
  -- Slit-plane membership.
  have hslit_bot : ∀ x : ℝ, ((x : ℂ) + (c : ℂ) * Complex.I - w) ∈ Complex.slitPlane := by
    intro x
    rw [Complex.mem_slitPlane_iff]
    right
    rw [him_bot]
    intro h; linarith [hw_im.1]
  have hslit_top : ∀ x : ℝ, ((x : ℂ) + (d : ℂ) * Complex.I - w) ∈ Complex.slitPlane := by
    intro x
    rw [Complex.mem_slitPlane_iff]
    right
    rw [him_top]
    intro h; linarith [hw_im.2]
  have hslit_right : ∀ y : ℝ, ((b : ℂ) + (y : ℂ) * Complex.I - w) ∈ Complex.slitPlane := by
    intro y
    rw [Complex.mem_slitPlane_iff]
    left
    rw [hre_right]
    linarith [hw_re.2]
  have hslit_left_neg : ∀ y : ℝ,
      -((a : ℂ) + (y : ℂ) * Complex.I - w) ∈ Complex.slitPlane := by
    intro y
    rw [Complex.mem_slitPlane_iff]
    left
    rw [hre_left_neg]
    linarith [hw_re.1]
  -- Non-vanishing.
  have hne_bot : ∀ x : ℝ, ((x : ℂ) + (c : ℂ) * Complex.I - w) ≠ 0 := by
    intro x heq
    have := him_bot x
    rw [heq] at this; simp at this
    linarith [hw_im.1]
  have hne_top : ∀ x : ℝ, ((x : ℂ) + (d : ℂ) * Complex.I - w) ≠ 0 := by
    intro x heq
    have := him_top x
    rw [heq] at this; simp at this
    linarith [hw_im.2]
  have hne_right : ∀ y : ℝ, ((b : ℂ) + (y : ℂ) * Complex.I - w) ≠ 0 := by
    intro y heq
    have := hre_right y
    rw [heq] at this; simp at this
    linarith [hw_re.2]
  have hne_left_neg : ∀ y : ℝ, -((a : ℂ) + (y : ℂ) * Complex.I - w) ≠ 0 := by
    intro y heq
    have := hre_left_neg y
    rw [heq] at this; simp at this
    linarith [hw_re.1]
  -- Bottom edge: ∫_a^b (x + ci - w)⁻¹ dx = log(b + ci - w) - log(a + ci - w).
  have h_bot : (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - w)⁻¹) =
      Complex.log ((b : ℂ) + (c : ℂ) * Complex.I - w) -
      Complex.log ((a : ℂ) + (c : ℂ) * Complex.I - w) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => Complex.log ((y : ℂ) + (c : ℂ) * Complex.I - w))
    · intro x _
      have h_log := Complex.hasDerivAt_log (hslit_bot x)
      have h_inner : HasDerivAt (fun z : ℂ => z + (c : ℂ) * Complex.I - w) 1 (x : ℂ) := by
        simpa [sub_eq_add_neg, add_assoc] using
          (hasDerivAt_id (x : ℂ)).add_const ((c : ℂ) * Complex.I - w)
      have h_comp := h_log.comp (x : ℂ) h_inner
      simpa using h_comp.comp_ofReal
    · apply Continuous.intervalIntegrable
      exact (by fun_prop : Continuous fun x : ℝ => ((x : ℂ) + (c : ℂ) * Complex.I - w)).inv₀ hne_bot
  -- Top edge: ∫_a^b (x + di - w)⁻¹ dx = log(b + di - w) - log(a + di - w).
  have h_top : (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - w)⁻¹) =
      Complex.log ((b : ℂ) + (d : ℂ) * Complex.I - w) -
      Complex.log ((a : ℂ) + (d : ℂ) * Complex.I - w) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => Complex.log ((y : ℂ) + (d : ℂ) * Complex.I - w))
    · intro x _
      have h_log := Complex.hasDerivAt_log (hslit_top x)
      have h_inner : HasDerivAt (fun z : ℂ => z + (d : ℂ) * Complex.I - w) 1 (x : ℂ) := by
        simpa [sub_eq_add_neg, add_assoc] using
          (hasDerivAt_id (x : ℂ)).add_const ((d : ℂ) * Complex.I - w)
      have h_comp := h_log.comp (x : ℂ) h_inner
      simpa using h_comp.comp_ofReal
    · apply Continuous.intervalIntegrable
      exact (by fun_prop : Continuous fun x : ℝ => ((x : ℂ) + (d : ℂ) * Complex.I - w)).inv₀ hne_top
  -- Right edge: ∫_c^d (b + yi - w)⁻¹ dy = -I · (log(b + di - w) - log(b + ci - w)).
  -- Antiderivative: F(y) = -I · log(b + yi - w). F'(y) = -I · I · (b+yi-w)⁻¹ = (b+yi-w)⁻¹.
  have h_right : (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) =
      (-Complex.I) * Complex.log ((b : ℂ) + (d : ℂ) * Complex.I - w) -
      (-Complex.I) * Complex.log ((b : ℂ) + (c : ℂ) * Complex.I - w) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => (-Complex.I) * Complex.log ((b : ℂ) + (y : ℂ) * Complex.I - w))
    · intro y _
      have h_log := Complex.hasDerivAt_log (hslit_right y)
      have h_inner : HasDerivAt (fun z : ℂ => (b : ℂ) + z * Complex.I - w) Complex.I (y : ℂ) := by
        have h1 : HasDerivAt (fun z : ℂ => z * Complex.I) Complex.I (y : ℂ) := by
          simpa using (hasDerivAt_id (y : ℂ)).mul_const Complex.I
        have h2 : HasDerivAt (fun z : ℂ => (b : ℂ) + z * Complex.I) Complex.I (y : ℂ) := by
          simpa using h1.const_add ((b : ℂ))
        simpa [sub_eq_add_neg] using h2.add_const (-w)
      have h_comp := h_log.comp (y : ℂ) h_inner
      have h_real := h_comp.comp_ofReal
      -- h_real has derivative (b+yi-w)⁻¹ * I.
      have h_mul := h_real.const_mul (-Complex.I)
      -- h_mul has derivative -I * ((b+yi-w)⁻¹ * I).
      -- Show this equals (b+yi-w)⁻¹.
      have h_simp : (-Complex.I) * (((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹ * Complex.I) =
          ((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹ := by
        have h1 : (-Complex.I) * Complex.I = (1 : ℂ) := by
          rw [neg_mul, Complex.I_mul_I, neg_neg]
        linear_combination
          (((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) * h1
      rw [show (-Complex.I) * (((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹ * Complex.I) =
          ((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹ from h_simp] at h_mul
      convert h_mul using 1
    · apply Continuous.intervalIntegrable
      have h_cont : Continuous fun y : ℝ => ((b : ℂ) + (y : ℂ) * Complex.I - w) := by
        fun_prop
      exact h_cont.inv₀ hne_right
  -- Left edge: ∫_c^d (a + yi - w)⁻¹ dy.
  -- Path real part = a - w.re < 0; imag part crosses 0 at y = w.im.
  -- Principal log is discontinuous; use the translated branch log(-z), analytic on
  -- Re z < 0. Antiderivative: F(y) = -I · log(-(a + yi - w)).
  -- F'(y) = -I · log'(-z) · (-I) = -I · (-(a+yi-w))⁻¹ · (-I)
  --       = -I · (-(a+yi-w)⁻¹) · (-I) = (a+yi-w)⁻¹.
  have h_left : (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) =
      (-Complex.I) * Complex.log (-((a : ℂ) + (d : ℂ) * Complex.I - w)) -
      (-Complex.I) * Complex.log (-((a : ℂ) + (c : ℂ) * Complex.I - w)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => (-Complex.I) *
        Complex.log (-((a : ℂ) + (y : ℂ) * Complex.I - w)))
    · intro y _
      have h_log := Complex.hasDerivAt_log (hslit_left_neg y)
      have h_inner : HasDerivAt (fun z : ℂ => -((a : ℂ) + z * Complex.I - w))
          (-Complex.I) (y : ℂ) := by
        have h1 : HasDerivAt (fun z : ℂ => z * Complex.I) Complex.I (y : ℂ) := by
          simpa using (hasDerivAt_id (y : ℂ)).mul_const Complex.I
        have h2 : HasDerivAt (fun z : ℂ => (a : ℂ) + z * Complex.I) Complex.I (y : ℂ) := by
          simpa using h1.const_add ((a : ℂ))
        have h3 : HasDerivAt (fun z : ℂ => (a : ℂ) + z * Complex.I - w) Complex.I (y : ℂ) := by
          simpa [sub_eq_add_neg] using h2.add_const (-w)
        exact h3.neg
      have h_comp := h_log.comp (y : ℂ) h_inner
      have h_real := h_comp.comp_ofReal
      -- h_real has derivative (-(a+yi-w))⁻¹ * (-I).
      have h_mul := h_real.const_mul (-Complex.I)
      -- h_mul has derivative -I * ((-(a+yi-w))⁻¹ * -I).
      have h_simp : (-Complex.I) *
          ((-((a : ℂ) + (y : ℂ) * Complex.I - w))⁻¹ * (-Complex.I)) =
          ((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹ := by
        rw [inv_neg]
        have hII : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by
          rw [neg_mul_neg, Complex.I_mul_I]
        linear_combination -(((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) * hII
      rw [show (-Complex.I) *
            ((-((a : ℂ) + (y : ℂ) * Complex.I - w))⁻¹ * (-Complex.I)) =
            ((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹ from h_simp] at h_mul
      convert h_mul using 1
    · apply Continuous.intervalIntegrable
      have h_cont : Continuous fun y : ℝ => ((a : ℂ) + (y : ℂ) * Complex.I - w) := by
        fun_prop
      have hne_left : ∀ y : ℝ, ((a : ℂ) + (y : ℂ) * Complex.I - w) ≠ 0 := by
        intro y heq
        apply hne_left_neg y
        rw [heq]; ring
      exact h_cont.inv₀ hne_left
  -- Auxiliary: I * I = -1 (for collapsing the I-factors picked up on right/left edges).
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  -- Branch-cut identities for the two left-edge corners: log(-z) - log(z) = ±π·I.
  -- Bottom-left corner: im < 0, so log(-z) = log(z) + π·I.
  have h_log_diff_BL : Complex.log (-((a : ℂ) + (c : ℂ) * Complex.I - w)) -
      Complex.log ((a : ℂ) + (c : ℂ) * Complex.I - w) =
      (Real.pi : ℂ) * Complex.I := by
    have him : ((a : ℂ) + (c : ℂ) * Complex.I - w).im < 0 := by
      have := him_bot a; rw [this]; linarith [hw_im.1]
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.log_re, norm_neg, sub_self,
                 Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                 Complex.I_re, Complex.I_im, mul_zero, zero_mul]
    · simp only [Complex.sub_im, Complex.log_im,
                 Complex.arg_neg_eq_arg_add_pi_of_im_neg him,
                 Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
                 Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero,
                 add_sub_cancel_left]
  -- Top-left corner: im > 0, so log(-z) = log(z) - π·I, i.e. log(z) - log(-z) = π·I.
  have h_log_diff_TL : Complex.log ((a : ℂ) + (d : ℂ) * Complex.I - w) -
      Complex.log (-((a : ℂ) + (d : ℂ) * Complex.I - w)) =
      (Real.pi : ℂ) * Complex.I := by
    have him : 0 < ((a : ℂ) + (d : ℂ) * Complex.I - w).im := by
      have := him_top a; rw [this]; linarith [hw_im.2]
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.log_re, norm_neg, sub_self,
                 Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                 Complex.I_re, Complex.I_im, mul_zero, zero_mul]
    · simp only [Complex.sub_im, Complex.log_im,
                 Complex.arg_neg_eq_arg_sub_pi_of_im_pos him,
                 Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
                 Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
      ring
  -- Sum the four edges: telescoping cancels log of right-column corners, and the
  -- two remaining pairs collapse to 2πI via the branch-cut identities.
  have h_num : (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - w)⁻¹) +
      Complex.I * (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) -
      (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - w)⁻¹) -
      Complex.I * (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) =
      2 * Real.pi * Complex.I := by
    rw [h_bot, h_right, h_top, h_left]
    linear_combination
      (Complex.log ((b : ℂ) + (c : ℂ) * Complex.I - w) -
       Complex.log ((b : ℂ) + (d : ℂ) * Complex.I - w) +
       Complex.log (-((a : ℂ) + (d : ℂ) * Complex.I - w)) -
       Complex.log (-((a : ℂ) + (c : ℂ) * Complex.I - w))) * hII +
      h_log_diff_BL + h_log_diff_TL
  rw [h_num]
  exact inv_mul_cancel₀ hpi

/-! ## Basic properties of `pathContourIntegral` -/

/-- Contour integral of the zero function vanishes. -/
theorem pathContourIntegral_zero (γ : ℝ → ℂ) (a b : ℝ) :
    pathContourIntegral γ a b (fun _ => 0) = 0 := by
  unfold pathContourIntegral
  simp

/-- Contour integral is additive in the integrand. -/
theorem pathContourIntegral_add (γ : ℝ → ℂ) (a b : ℝ) (f g : ℂ → ℂ)
    (hfγ : IntervalIntegrable (fun t => f (γ t) * deriv γ t) MeasureTheory.volume a b)
    (hgγ : IntervalIntegrable (fun t => g (γ t) * deriv γ t) MeasureTheory.volume a b) :
    pathContourIntegral γ a b (fun z => f z + g z) =
    pathContourIntegral γ a b f + pathContourIntegral γ a b g := by
  unfold pathContourIntegral
  simp only [add_mul]
  exact intervalIntegral.integral_add hfγ hgγ

/-- Contour integral is homogeneous: scaling the integrand by a constant
scales the integral. -/
theorem pathContourIntegral_const_smul (γ : ℝ → ℂ) (a b : ℝ) (k : ℂ) (f : ℂ → ℂ) :
    pathContourIntegral γ a b (fun z => k * f z) =
    k * pathContourIntegral γ a b f := by
  unfold pathContourIntegral
  simp only [mul_assoc]
  exact intervalIntegral.integral_const_mul k _

end Complex

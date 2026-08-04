/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Variational.Schwarzian

/-!
# The Gronwall area theorem

A univalent map of the exterior disk `T w = w + b₀ + b₁/w + ⋯` omits a set of positive
area, and the area of the omitted set is `π(1 − Σ n |bₙ|²)`; hence `Σ n |bₙ|² ≤ 1` and in
particular `|b₁| ≤ 1`. The exterior map is carried by its tail function: `T w = w·s(1/w)`
with `s` holomorphic on the unit ball and `s 0 = 1`, and `b₁` is half the second
derivative of `s` at the origin. The area computation runs through the change-of-variables
identity `area (T(annulus)) = ∬ |T'|²`, the circle Parseval expansion, and the squeeze of
the omitted set between images of large circles.

* `integral_circleMap_pow_mul_inv_pow`, `integral_circleMap_pow_mul_curve_deriv` — the
  circle orthogonality relations and integration by parts on the circle.
* `circleIntegral_deriv_mul_inv_sub_eq_zero`,
  `circleIntegral_deriv_mul_inv_sub_eq_two_pi_I` — the winding dichotomy on large
  circles for a near-identity exterior map.
* `lintegral_ball_enorm_inv_sub_le`, `integral_ball_inv_sub_eq_pi_mul_conj` — the disk
  kernel bound and the kernel identity `∫_{ball 0 M} (a₀ − z)⁻¹ dA(z) = π·conj a₀`.
* `abs_laurent_coeff_le_of_injOn` — the first-coefficient bound `|b₁| ≤ 1` of the area
  theorem, in tail-function form.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-- The circle parametrization about the origin in exponential form. -/
theorem circleMap_zero_eq_mul_exp (ρ θ : ℝ) :
    circleMap 0 ρ θ = (ρ:ℂ) * Complex.exp (θ * Complex.I) := by
  simp [circleMap]

/-- Orthogonality of the circle exponentials: `∫_0^{2π} e^{ikθ} dθ = 0` for `k ≠ 0`. -/
theorem integral_exp_int_mul_I_eq_zero (k : ℤ) (hk : k ≠ 0) :
    (∫ θ in (0:ℝ)..(2 * Real.pi), Complex.exp ((k:ℂ) * Complex.I * θ)) = 0 := by
  have hc : ((k:ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr hk) Complex.I_ne_zero
  have h1 := integral_exp_mul_complex (a := 0) (b := 2 * Real.pi) hc
  have h2 : Complex.exp ((k:ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    have h3 := Complex.exp_int_mul_two_pi_mul_I k
    rw [← h3]
    congr 1
    push_cast
    ring
  have h4 : ∀ x : ℝ, ((k:ℂ) * Complex.I) * (x:ℂ) = (k:ℂ) * Complex.I * (x:ℂ) := fun _ => rfl
  rw [show (fun θ : ℝ => Complex.exp ((k:ℂ) * Complex.I * (θ:ℂ))) =
    fun θ : ℝ => Complex.exp (((k:ℂ) * Complex.I) * (θ:ℂ)) from rfl]
  rw [h1, h2]
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self, zero_div]

/-- Monomials in `circleMap 0 ρ` and its inverse in exponential form. -/
theorem circleMap_pow_mul_inv_pow {ρ : ℝ} (hρ0 : 0 < ρ) (m j : ℕ) (θ : ℝ) :
    (circleMap 0 ρ θ) ^ m * ((circleMap 0 ρ θ)⁻¹) ^ j =
      ((ρ:ℂ) ^ m * ((ρ:ℂ)⁻¹) ^ j) *
        Complex.exp ((((m:ℤ) - (j:ℤ)) : ℂ) * Complex.I * θ) := by
  have hexpne : Complex.exp (θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hρne : (ρ:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ0.ne'
  rw [circleMap_zero_eq_mul_exp ρ θ, mul_inv, mul_pow, mul_pow]
  have e1 : (Complex.exp ((θ:ℂ) * Complex.I)) ^ m =
      Complex.exp ((m:ℂ) * ((θ:ℂ) * Complex.I)) := (Complex.exp_nat_mul _ m).symm
  have e2 : ((Complex.exp ((θ:ℂ) * Complex.I))⁻¹) ^ j =
      Complex.exp (-((j:ℂ) * ((θ:ℂ) * Complex.I))) := by
    rw [← Complex.exp_neg, ← Complex.exp_nat_mul]
    congr 1
    ring
  rw [e1, e2]
  rw [show ((ρ:ℂ) ^ m * Complex.exp ((m:ℂ) * ((θ:ℂ) * Complex.I))) *
      (((ρ:ℂ)⁻¹) ^ j * Complex.exp (-((j:ℂ) * ((θ:ℂ) * Complex.I)))) =
      ((ρ:ℂ) ^ m * ((ρ:ℂ)⁻¹) ^ j) *
        (Complex.exp ((m:ℂ) * ((θ:ℂ) * Complex.I)) *
          Complex.exp (-((j:ℂ) * ((θ:ℂ) * Complex.I)))) from by ring]
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Circle orthogonality: `∫_0^{2π} c^m (c⁻¹)^j dθ = 2π·[m = j]` for `c = circleMap 0 ρ`. -/
theorem integral_circleMap_pow_mul_inv_pow {ρ : ℝ} (hρ0 : 0 < ρ) (m j : ℕ) :
    (∫ θ in (0:ℝ)..(2 * Real.pi), (circleMap 0 ρ θ) ^ m * ((circleMap 0 ρ θ)⁻¹) ^ j) =
      if m = j then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  have hcircne : ∀ θ : ℝ, circleMap 0 ρ θ ≠ 0 := fun θ => circleMap_ne_center hρ0.ne'
  rcases eq_or_ne m j with rfl | hne
  · simp only [if_pos]
    have hcongr : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * Real.pi),
        (circleMap 0 ρ θ) ^ m * ((circleMap 0 ρ θ)⁻¹) ^ m = 1 := by
      intro θ _
      rw [← mul_pow, mul_inv_cancel₀ (hcircne θ), one_pow]
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const]
    change ((2 * Real.pi - 0 : ℝ) : ℂ) * 1 = ((2 * Real.pi : ℝ) : ℂ)
    push_cast
    ring
  · simp only [if_neg hne]
    have hcongr : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * Real.pi),
        (circleMap 0 ρ θ) ^ m * ((circleMap 0 ρ θ)⁻¹) ^ j =
        ((ρ:ℂ) ^ m * ((ρ:ℂ)⁻¹) ^ j) *
          Complex.exp ((((m:ℤ) - (j:ℤ)) : ℂ) * Complex.I * θ) := fun θ _ =>
        circleMap_pow_mul_inv_pow hρ0 m j θ
    rw [intervalIntegral.integral_congr hcongr]
    have h1 : (∫ θ in (0:ℝ)..(2 * Real.pi), ((ρ:ℂ) ^ m * ((ρ:ℂ)⁻¹) ^ j) *
        Complex.exp ((((m:ℤ) - (j:ℤ)) : ℂ) * Complex.I * θ)) =
        ((ρ:ℂ) ^ m * ((ρ:ℂ)⁻¹) ^ j) * ∫ θ in (0:ℝ)..(2 * Real.pi),
          Complex.exp ((((m:ℤ) - (j:ℤ)) : ℂ) * Complex.I * θ) :=
      intervalIntegral.integral_const_mul _ _
    rw [h1]
    have h2 : (∫ θ in (0:ℝ)..(2 * Real.pi),
        Complex.exp ((((m:ℤ) - (j:ℤ)) : ℂ) * Complex.I * θ)) = 0 := by
      have h3 := integral_exp_int_mul_I_eq_zero ((m:ℤ) - (j:ℤ))
        (sub_ne_zero.mpr (by exact_mod_cast hne))
      rw [← h3]
      congr 1
      funext θ
      congr 2
      push_cast
      ring
    rw [h2, mul_zero]

/-- Integration by parts on the circle: for a closed curve `θ ↦ f (circleMap 0 ρ θ)`
with derivative `θ ↦ f' (circleMap 0 ρ θ) · (circleMap 0 ρ θ · I)`, the `m`-th moment
of the derivative is `-((m − 1)·I)` times the `m`-th moment of the curve. -/
theorem integral_circleMap_pow_mul_curve_deriv {ρ : ℝ} (hρ0 : 0 < ρ) {f f' : ℂ → ℂ}
    (hd : ∀ θ : ℝ, HasDerivAt (fun t => f (circleMap 0 ρ t))
      (f' (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)) θ)
    (hfc : Continuous fun θ : ℝ => f (circleMap 0 ρ θ))
    (hf'c : Continuous fun θ : ℝ => f' (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))
    (m : ℕ) :
    (∫ θ in (0:ℝ)..(2 * Real.pi), (circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ *
        (f' (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))) =
      -(((m:ℂ) - 1) * Complex.I) * ∫ θ in (0:ℝ)..(2 * Real.pi),
        (circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ * f (circleMap 0 ρ θ) := by
  have hcircne : ∀ θ : ℝ, circleMap 0 ρ θ ≠ 0 := fun θ => circleMap_ne_center hρ0.ne'
  have hcmc : Continuous fun θ : ℝ => (circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ :=
    ((continuous_circleMap 0 ρ).pow m).mul
      ((continuous_circleMap 0 ρ).inv₀ hcircne)
  have hBderiv : ∀ θ : ℝ, HasDerivAt
      (fun t => (circleMap 0 ρ t) ^ m * (circleMap 0 ρ t)⁻¹ * f (circleMap 0 ρ t))
      ((((m:ℂ) - 1) * Complex.I) *
          ((circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ * f (circleMap 0 ρ θ)) +
        (circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ *
          (f' (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))) θ := by
    intro θ
    have hc := hasDerivAt_circleMap 0 ρ θ
    have hcm : HasDerivAt (fun t => (circleMap 0 ρ t) ^ m)
        ((m:ℂ) * (circleMap 0 ρ θ) ^ (m - 1) * (circleMap 0 ρ θ * Complex.I)) θ :=
      hc.pow m
    have hcinv : HasDerivAt (fun t => (circleMap 0 ρ t)⁻¹)
        (-((circleMap 0 ρ θ) ^ 2)⁻¹ * (circleMap 0 ρ θ * Complex.I)) θ :=
      (hasDerivAt_inv (hcircne θ)).comp θ hc
    have hA := hd θ
    have h1 := (hcm.mul hcinv).mul hA
    have hder_eq : ∀ (C X D : ℂ), C ≠ 0 →
        ((m:ℂ) * C ^ (m - 1) * (C * Complex.I) * C⁻¹ +
            C ^ m * (-(C ^ 2)⁻¹ * (C * Complex.I))) * X +
          (C ^ m * C⁻¹) * (D * (C * Complex.I)) =
        (((m:ℂ) - 1) * Complex.I) * (C ^ m * C⁻¹ * X) +
          C ^ m * C⁻¹ * (D * (C * Complex.I)) := by
      intro C X D hC
      have hpowm : (m:ℂ) * C ^ (m - 1) * C = (m:ℂ) * C ^ m := by
        cases m with
        | zero => simp
        | succ n =>
            rw [Nat.add_sub_cancel]
            push_cast
            rw [pow_succ]
            ring
      field_simp
      linear_combination X * hpowm
    have h2 := hder_eq (circleMap 0 ρ θ) (f (circleMap 0 ρ θ))
      (f' (circleMap 0 ρ θ)) (hcircne θ)
    rw [← h2]
    exact h1
  have hintB' : IntervalIntegrable (fun θ : ℝ =>
      (((m:ℂ) - 1) * Complex.I) *
          ((circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ * f (circleMap 0 ρ θ)) +
        (circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ *
          (f' (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)))
      MeasureTheory.volume 0 (2 * Real.pi) := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact (continuous_const.mul (hcmc.mul hfc)).add (hcmc.mul hf'c)
  have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hBderiv θ) hintB'
  have hper : circleMap 0 ρ (2 * Real.pi) = circleMap 0 ρ 0 := by
    have h3 := periodic_circleMap 0 ρ 0
    simpa using h3
  rw [hper, sub_self] at h2
  have h4 : (∫ θ in (0:ℝ)..(2 * Real.pi),
      ((((m:ℂ) - 1) * Complex.I) *
          ((circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ * f (circleMap 0 ρ θ)) +
        (circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ *
          (f' (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)))) =
      (((m:ℂ) - 1) * Complex.I) * (∫ θ in (0:ℝ)..(2 * Real.pi),
          (circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ * f (circleMap 0 ρ θ)) +
        ∫ θ in (0:ℝ)..(2 * Real.pi), (circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ *
          (f' (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)) := by
    have hint1 : IntervalIntegrable (fun θ : ℝ => (((m:ℂ) - 1) * Complex.I) *
        ((circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ * f (circleMap 0 ρ θ)))
        MeasureTheory.volume 0 (2 * Real.pi) := by
      refine Continuous.intervalIntegrable ?_ _ _
      exact continuous_const.mul (hcmc.mul hfc)
    have hint2 : IntervalIntegrable (fun θ : ℝ =>
        (circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ *
          (f' (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)))
        MeasureTheory.volume 0 (2 * Real.pi) := by
      refine Continuous.intervalIntegrable ?_ _ _
      exact hcmc.mul hf'c
    rw [intervalIntegral.integral_add hint1 hint2]
    congr 1
    exact intervalIntegral.integral_const_mul _ _
  rw [h4] at h2
  linear_combination h2

/-- A complex number whose norm is at most `c/S` for all large `S` is zero. -/
theorem eq_zero_of_norm_le_const_div (X : ℂ) (cst S₀ : ℝ) (hc : 0 ≤ cst)
    (hX : ∀ S : ℝ, S₀ ≤ S → ‖X‖ ≤ cst / S) : X = 0 := by
  by_contra hne
  have h0 : 0 < ‖X‖ := norm_pos_iff.mpr hne
  have hS : S₀ ≤ max S₀ (2 * cst / ‖X‖ + 1) := le_max_left _ _
  have h1 := hX _ hS
  have h2 : 0 < 2 * cst / ‖X‖ + 1 := by positivity
  have h3 : 2 * cst / ‖X‖ + 1 ≤ max S₀ (2 * cst / ‖X‖ + 1) := le_max_right _ _
  have h4 : cst / max S₀ (2 * cst / ‖X‖ + 1) ≤ cst / (2 * cst / ‖X‖ + 1) :=
    div_le_div_of_nonneg_left hc h2 h3
  have h5 : cst / (2 * cst / ‖X‖ + 1) < ‖X‖ := by
    rw [div_lt_iff₀ h2]
    have : 2 * cst / ‖X‖ * ‖X‖ = 2 * cst := by field_simp
    nlinarith
  linarith

/-- **Deformation to large circles**: if `f` is differentiable and injective on the
exterior `{1 < ‖w‖}`, stays within `Ms'` of the identity and has derivative bounded
by `Ms + Ms'` far out, and `w·f'(w) − f(w) = −g₀ w` with `g₀` bounded, then the
winding integrand `f'/(f − z)` integrates to zero over the circle of radius `ρ`
whenever `z` is attained by `f` outside that circle. -/
theorem circleIntegral_deriv_mul_inv_sub_eq_zero {f g₀ : ℂ → ℂ} {ρ Ms Ms' : ℝ}
    (hρ : 1 < ρ) (hMs0 : 0 ≤ Ms) (hMs'0 : 0 ≤ Ms')
    (hfd : DifferentiableOn ℂ f {w : ℂ | 1 < ‖w‖})
    (hinj : Set.InjOn f {w : ℂ | 1 < ‖w‖})
    (hid : ∀ w : ℂ, w ∈ {w : ℂ | 1 < ‖w‖} → w * deriv f w - f w = -(g₀ w))
    (hgb : ∀ w : ℂ, 2 ≤ ‖w‖ → ‖g₀ w‖ ≤ Ms')
    (hfsub : ∀ w : ℂ, 2 ≤ ‖w‖ → ‖f w - w‖ ≤ Ms')
    (hf'b : ∀ w : ℂ, 2 ≤ ‖w‖ → ‖deriv f w‖ ≤ Ms + Ms')
    {z : ℂ} (hzI : z ∈ f '' {w : ℂ | ρ < ‖w‖}) :
    (∮ w in C(0, ρ), deriv f w * (f w - z)⁻¹) = 0 := by
  have hρ0 : (0:ℝ) < ρ := lt_trans one_pos hρ
  set U : Set ℂ := {w : ℂ | 1 < ‖w‖} with hUdef
  have hUmem : ∀ w : ℂ, w ∈ U ↔ 1 < ‖w‖ := fun w => Iff.rfl
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hUne : ∀ w : ℂ, w ∈ U → w ≠ 0 := by
    intro w hw h0
    rw [hUmem] at hw
    simp [h0] at hw
    linarith
  have hsphereU : Metric.sphere (0:ℂ) ρ ⊆ U := by
    intro w hw
    rw [Metric.mem_sphere, dist_zero_right] at hw
    rw [hUmem, hw]
    exact hρ
  obtain ⟨w₀, hw₀ρ, hTw₀⟩ := hzI
  rw [Set.mem_setOf_eq] at hw₀ρ
  have hw₀U : w₀ ∈ U := by rw [hUmem]; linarith
  have hw₀0 : w₀ ≠ 0 := hUne w₀ hw₀U
  have hw₀pos : (0:ℝ) < ‖w₀‖ := norm_pos_iff.mpr hw₀0
  set g : ℂ → ℂ := dslope (fun w => f w - z) w₀ with hgdef
  have hgdiff : DifferentiableOn ℂ g U :=
    (Complex.differentiableOn_dslope (hUopen.mem_nhds hw₀U)).mpr (hfd.sub_const z)
  have hganal : AnalyticOnNhd ℂ g U := hgdiff.analyticOnNhd hUopen
  have hg'cont : ContinuousOn (deriv g) U := hganal.deriv.continuousOn
  have hgne : ∀ w : ℂ, w ∈ U → g w ≠ 0 := by
    intro w hwU
    rcases eq_or_ne w w₀ with rfl | hne
    · rw [hgdef, dslope_same]
      have h1 : deriv (fun v => f v - z) w = deriv f w := deriv_sub_const z
      rw [h1]
      exact deriv_ne_zero_of_injOn hUopen hfd hinj hwU
    · rw [hgdef, dslope_of_ne _ hne, slope_def_field]
      refine div_ne_zero ?_ (sub_ne_zero.mpr hne)
      intro heq
      apply hne
      refine hinj hwU hw₀U ?_
      linear_combination heq
  have hfact : ∀ w : ℂ, f w - z = (w - w₀) * g w := by
    intro w
    have h1 := sub_smul_dslope (fun v => f v - z) w₀ w
    rw [smul_eq_mul, ← hgdef] at h1
    rw [hTw₀] at h1
    linear_combination -h1
  have hannsubA : ∀ S : ℝ, Metric.closedBall (0:ℂ) S \ Metric.ball 0 ρ ⊆ U := by
    intro S w hw
    obtain ⟨_, h2⟩ := hw
    rw [Metric.mem_ball, dist_zero_right, not_lt] at h2
    rw [hUmem]; linarith
  -- Split of the integrand on the circle.
  have hsplitF : ∀ w ∈ Metric.sphere (0:ℂ) ρ, deriv f w * (f w - z)⁻¹ =
      (w - w₀)⁻¹ + deriv g w * (g w)⁻¹ := by
    intro w hwS
    have hwU : w ∈ U := hsphereU hwS
    rw [Metric.mem_sphere, dist_zero_right] at hwS
    have hne : w ≠ w₀ := by
      intro heq
      rw [heq] at hwS
      rw [hwS] at hw₀ρ
      exact lt_irrefl _ hw₀ρ
    have hne' : w - w₀ ≠ 0 := sub_ne_zero.mpr hne
    have hgw : g w ≠ 0 := hgne w hwU
    have hgd : DifferentiableAt ℂ g w := (hganal w hwU).differentiableAt
    have hTd : deriv f w = g w + (w - w₀) * deriv g w := by
      have h1 : deriv (fun v => f v - z) w = deriv f w := deriv_sub_const z
      have h2 : (fun v => f v - z) = fun v => (v - w₀) * g v := funext hfact
      have h3 : deriv (fun v => (v - w₀) * g v) w =
          deriv (fun v => v - w₀) w * g w + (w - w₀) * deriv g w :=
        deriv_fun_mul (differentiableAt_fun_id.sub_const w₀) hgd
      have h4 : deriv (fun v : ℂ => v - w₀) w = 1 := by
        rw [deriv_sub_const w₀, deriv_id'']
      rw [← h1, h2, h3, h4, one_mul]
    rw [hfact w, hTd, mul_inv]
    field_simp
    try ring
  have hint1 : CircleIntegrable (fun w => (w - w₀)⁻¹) 0 ρ := by
    refine ContinuousOn.circleIntegrable hρ0.le ?_
    refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
    intro w hw
    rw [Metric.mem_sphere, dist_zero_right] at hw
    refine sub_ne_zero.mpr ?_
    intro heq
    rw [heq] at hw
    rw [hw] at hw₀ρ
    exact lt_irrefl _ hw₀ρ
  have hint2 : CircleIntegrable (fun w => deriv g w * (g w)⁻¹) 0 ρ := by
    refine ContinuousOn.circleIntegrable hρ0.le ?_
    exact (hg'cont.mono hsphereU).mul (ContinuousOn.inv₀
      (hgdiff.continuousOn.mono hsphereU) fun w hw => hgne w (hsphereU hw))
  have hcirc1 : (∮ w in C(0, ρ), deriv f w * (f w - z)⁻¹) =
      (∮ w in C(0, ρ), ((w - w₀)⁻¹ + deriv g w * (g w)⁻¹)) :=
    circleIntegral.integral_congr hρ0.le hsplitF
  have hcirc2 : (∮ w in C(0, ρ), ((w - w₀)⁻¹ + deriv g w * (g w)⁻¹)) =
      (∮ w in C(0, ρ), (w - w₀)⁻¹) + ∮ w in C(0, ρ), deriv g w * (g w)⁻¹ :=
    circleIntegral.integral_add hint1 hint2
  have hpiece1 : (∮ w in C(0, ρ), (w - w₀)⁻¹) = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hρ0.le
      Set.countable_empty ?_ ?_
    · refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right] at hw
      refine sub_ne_zero.mpr ?_
      intro heq
      rw [heq] at hw
      linarith
    · intro w hw
      obtain ⟨hw1, _⟩ := hw
      rw [Metric.mem_ball, dist_zero_right] at hw1
      refine (differentiableAt_fun_id.sub_const w₀).inv (sub_ne_zero.mpr ?_)
      intro heq
      rw [heq] at hw1
      linarith
  -- The `g`-piece vanishes by deformation to large circles.
  have hgFdiff : ∀ w : ℂ, w ∈ U → DifferentiableAt ℂ (fun w => deriv g w * (g w)⁻¹) w := by
    intro w hwU
    exact ((hganal.deriv w hwU).differentiableAt).mul
      (((hganal w hwU).differentiableAt).inv (hgne w hwU))
  have hdeform2 : ∀ S : ℝ, ρ ≤ S → (∮ w in C(0, S), deriv g w * (g w)⁻¹) =
      ∮ w in C(0, ρ), deriv g w * (g w)⁻¹ := by
    intro S hS
    refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hρ0 hS
      Set.countable_empty ?_ ?_
    · exact (hg'cont.mono (hannsubA S)).mul (ContinuousOn.inv₀
        (hgdiff.continuousOn.mono (hannsubA S)) fun w hw => hgne w (hannsubA S hw))
    · intro w hw
      have h2 := hw.1.2
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at h2
      refine hgFdiff w ?_
      rw [hUmem]; linarith
  set CA1 : ℝ := Ms' + ‖w₀‖ + ‖z‖ with hCA1def
  have hCA10 : 0 ≤ CA1 := by
    rw [hCA1def]
    have := norm_nonneg w₀
    have := norm_nonneg z
    linarith
  set CA2 : ℝ := (‖z‖ + Ms') + ‖w₀‖ * (Ms + Ms') with hCA2def
  have hCA20 : 0 ≤ CA2 := by
    rw [hCA2def]
    have h1 := norm_nonneg w₀
    have h2 := norm_nonneg z
    nlinarith
  have hboundA : ∀ S : ℝ, max (max ρ 2) (max (2 * ‖w₀‖) (4 * CA1)) ≤ S →
      ‖∮ w in C(0, ρ), deriv g w * (g w)⁻¹‖ ≤ 2 * Real.pi * (8 * CA2) / S := by
    intro S hS
    have hSρ : ρ ≤ S := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hS
    have hS2 : (2:ℝ) ≤ S := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hS
    have hSw₀ : 2 * ‖w₀‖ ≤ S := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hS
    have hSCA1 : 4 * CA1 ≤ S := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hS
    have hS0 : (0:ℝ) < S := lt_of_lt_of_le two_pos hS2
    have hptwA : ∀ w ∈ Metric.sphere (0:ℂ) S, ‖deriv g w * (g w)⁻¹‖ ≤ 8 * CA2 / S ^ 2 := by
      intro w hw
      rw [Metric.mem_sphere, dist_zero_right] at hw
      have hwU : w ∈ U := by rw [hUmem]; linarith
      have hw2 : 2 ≤ ‖w‖ := by rw [hw]; exact hS2
      have hwV : ‖w₀‖ < ‖w‖ := by rw [hw]; linarith
      have hne : w ≠ w₀ := by
        intro heq
        rw [heq] at hwV
        exact lt_irrefl _ hwV
      have hne' : w - w₀ ≠ 0 := sub_ne_zero.mpr hne
      have hwsub : S / 2 ≤ ‖w - w₀‖ := by
        have h1 : ‖w‖ - ‖w₀‖ ≤ ‖w - w₀‖ := norm_sub_norm_le w w₀
        rw [hw] at h1
        linarith
      -- Lower bound for `‖g w‖`.
      have hgm1 : ‖g w - 1‖ ≤ 2 * CA1 / S := by
        have he : g w - 1 = ((f w - w) + (w₀ - z)) * (w - w₀)⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq₀ hne']
          linear_combination -(hfact w)
        rw [he, norm_mul, norm_inv]
        have hnum : ‖(f w - w) + (w₀ - z)‖ ≤ CA1 := by
          calc ‖(f w - w) + (w₀ - z)‖ ≤ ‖f w - w‖ + ‖w₀ - z‖ := norm_add_le _ _
            _ ≤ Ms' + (‖w₀‖ + ‖z‖) := add_le_add (hfsub w hw2) (norm_sub_le _ _)
            _ = CA1 := by rw [hCA1def]; ring
        have hinv2 : ‖w - w₀‖⁻¹ ≤ (S / 2)⁻¹ := by
          rw [inv_le_inv₀ (by linarith : (0:ℝ) < ‖w - w₀‖) (by linarith : (0:ℝ) < S / 2)]
          exact hwsub
        calc ‖(f w - w) + (w₀ - z)‖ * ‖w - w₀‖⁻¹ ≤ CA1 * (S / 2)⁻¹ :=
              mul_le_mul hnum hinv2 (by positivity) hCA10
          _ = 2 * CA1 / S := by field_simp
      have hgm1half : ‖g w - 1‖ ≤ 2⁻¹ := by
        refine le_trans hgm1 ?_
        rw [div_le_iff₀ hS0]
        linarith
      have hglow : (2:ℝ)⁻¹ ≤ ‖g w‖ := by
        have h1 : ‖(1:ℂ)‖ - ‖1 - g w‖ ≤ ‖1 - (1 - g w)‖ := norm_sub_norm_le 1 (1 - g w)
        have h2 : (1:ℂ) - (1 - g w) = g w := by ring
        have h3 : ‖(1:ℂ) - g w‖ = ‖g w - 1‖ := norm_sub_rev _ _
        rw [h2, h3] at h1
        rw [norm_one] at h1
        linarith [hgm1half]
      have hgpos : (0:ℝ) < ‖g w‖ := lt_of_lt_of_le (by norm_num) hglow
      -- Derivative bound.
      have hg'val : deriv g w = (deriv f w * (w - w₀) - (f w - z)) / (w - w₀) ^ 2 := by
        have hVopen : IsOpen {v : ℂ | ‖w₀‖ < ‖v‖} :=
          isOpen_lt continuous_const continuous_norm
        have heqOn : Set.EqOn g (fun v => (f v - z) / (v - w₀)) {v : ℂ | ‖w₀‖ < ‖v‖} := by
          intro v hv
          rw [Set.mem_setOf_eq] at hv
          have hvne : v - w₀ ≠ 0 := sub_ne_zero.mpr (by
            intro heq
            rw [heq] at hv
            exact lt_irrefl _ hv)
          change g v = (f v - z) / (v - w₀)
          rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq₀ hvne]
          linear_combination -(hfact v)
        have hevent : g =ᶠ[nhds w] fun v => (f v - z) / (v - w₀) :=
          heqOn.eventuallyEq_of_mem (hVopen.mem_nhds hwV)
        have hTzdiff : DifferentiableAt ℂ (fun v => f v - z) w :=
          (hfd.differentiableAt (hUopen.mem_nhds hwU)).sub_const z
        have h1 : deriv g w = deriv (fun v => (f v - z) / (v - w₀)) w := hevent.deriv_eq
        rw [h1, deriv_fun_div hTzdiff (differentiableAt_fun_id.sub_const w₀) hne']
        have h4 : deriv (fun v : ℂ => v - w₀) w = 1 := by
          rw [deriv_sub_const w₀, deriv_id'']
        have h5 : deriv (fun v => f v - z) w = deriv f w := deriv_sub_const z
        rw [h4, h5]
        ring_nf
      have hN : deriv f w * (w - w₀) - (f w - z) =
          (z - g₀ w) - w₀ * deriv f w := by
        linear_combination hid w hwU
      have hNbound : ‖deriv f w * (w - w₀) - (f w - z)‖ ≤ CA2 := by
        rw [hN]
        calc ‖(z - g₀ w) - w₀ * deriv f w‖
            ≤ ‖z - g₀ w‖ + ‖w₀ * deriv f w‖ := norm_sub_le _ _
          _ ≤ (‖z‖ + ‖g₀ w‖) + ‖w₀‖ * ‖deriv f w‖ := by
              rw [norm_mul]
              exact add_le_add (norm_sub_le _ _) le_rfl
          _ ≤ (‖z‖ + Ms') + ‖w₀‖ * (Ms + Ms') := by
              refine add_le_add (add_le_add le_rfl (hgb w hw2)) ?_
              exact mul_le_mul_of_nonneg_left (hf'b w hw2) (norm_nonneg _)
          _ = CA2 := by rw [hCA2def]
      have hg'bound : ‖deriv g w‖ ≤ CA2 / (S / 2) ^ 2 := by
        rw [hg'val, norm_div, norm_pow]
        refine div_le_div₀ hCA20 hNbound (by positivity) ?_
        exact pow_le_pow_left₀ (by positivity) hwsub 2
      have hginv : ‖(g w)⁻¹‖ ≤ 2 := by
        rw [norm_inv]
        rw [show (2:ℝ) = ((2:ℝ)⁻¹)⁻¹ by norm_num]
        exact (inv_le_inv₀ hgpos (by norm_num)).mpr hglow
      calc ‖deriv g w * (g w)⁻¹‖ = ‖deriv g w‖ * ‖(g w)⁻¹‖ := norm_mul _ _
        _ ≤ (CA2 / (S / 2) ^ 2) * 2 := by
            refine mul_le_mul hg'bound hginv (norm_nonneg _) (by positivity)
        _ = 8 * CA2 / S ^ 2 := by field_simp; try ring
    have hcircleA : ‖∮ w in C(0, S), deriv g w * (g w)⁻¹‖ ≤
        2 * Real.pi * S * (8 * CA2 / S ^ 2) :=
      circleIntegral.norm_integral_le_of_norm_le_const hS0.le hptwA
    rw [hdeform2 S hSρ] at hcircleA
    refine le_trans hcircleA (le_of_eq ?_)
    field_simp
    try ring
  have hpiece2 : (∮ w in C(0, ρ), deriv g w * (g w)⁻¹) = 0 :=
    eq_zero_of_norm_le_const_div _ (2 * Real.pi * (8 * CA2))
      (max (max ρ 2) (max (2 * ‖w₀‖) (4 * CA1))) (by positivity) hboundA
  rw [hcirc1, hcirc2, hpiece1, hpiece2]
  ring

/-- **Winding at an omitted value**: if `f` is differentiable on the exterior
`{1 < ‖w‖}`, stays within `Ms'` of the identity far out, and
`w·f'(w) − f(w) = −g₀ w` with `g₀` bounded, then the winding integrand `f'/(f − z)`
integrates to `2πi` over the circle of radius `ρ` for any value `z` with `‖z‖ < M`
omitted by `f` on and outside that circle. -/
theorem circleIntegral_deriv_mul_inv_sub_eq_two_pi_I {f g₀ : ℂ → ℂ} {ρ M Ms' : ℝ}
    (hρ : 1 < ρ) (hM0 : 0 < M) (hMs'0 : 0 ≤ Ms')
    (hfd : DifferentiableOn ℂ f {w : ℂ | 1 < ‖w‖})
    (hid : ∀ w : ℂ, w ∈ {w : ℂ | 1 < ‖w‖} → w * deriv f w - f w = -(g₀ w))
    (hgb : ∀ w : ℂ, 2 ≤ ‖w‖ → ‖g₀ w‖ ≤ Ms')
    (hfsub : ∀ w : ℂ, 2 ≤ ‖w‖ → ‖f w - w‖ ≤ Ms')
    {z : ℂ} (hzM : ‖z‖ < M) (hzN : z ∉ f '' Metric.sphere (0:ℂ) ρ)
    (hzI : z ∉ f '' {w : ℂ | ρ < ‖w‖}) :
    (∮ w in C(0, ρ), deriv f w * (f w - z)⁻¹) = 2 * Real.pi * Complex.I := by
  have hρ0 : (0:ℝ) < ρ := lt_trans one_pos hρ
  set U : Set ℂ := {w : ℂ | 1 < ‖w‖} with hUdef
  have hUmem : ∀ w : ℂ, w ∈ U ↔ 1 < ‖w‖ := fun w => Iff.rfl
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hUne : ∀ w : ℂ, w ∈ U → w ≠ 0 := by
    intro w hw h0
    rw [hUmem] at hw
    simp [h0] at hw
    linarith
  have hT'anal : AnalyticOnNhd ℂ (deriv f) U := (hfd.analyticOnNhd hUopen).deriv
  have hT'cont : ContinuousOn (deriv f) U := hT'anal.continuousOn
  have hnz : ∀ w : ℂ, ρ ≤ ‖w‖ → f w ≠ z := by
    intro w hw hTwz
    rcases eq_or_lt_of_le hw with heq | hlt
    · exact hzN ⟨w, by rw [Metric.mem_sphere, dist_zero_right]; exact heq.symm, hTwz⟩
    · exact hzI ⟨w, hlt, hTwz⟩
  have hannsub : ∀ S : ℝ, Metric.closedBall (0:ℂ) S \ Metric.ball 0 ρ ⊆ U := by
    intro S w hw
    obtain ⟨_, h2⟩ := hw
    rw [Metric.mem_ball, dist_zero_right, not_lt] at h2
    rw [hUmem]; linarith
  have hFcont : ∀ S : ℝ, ContinuousOn (fun w => deriv f w * (f w - z)⁻¹)
      (Metric.closedBall 0 S \ Metric.ball 0 ρ) := by
    intro S
    refine ContinuousOn.mul (hT'cont.mono (hannsub S)) (ContinuousOn.inv₀ ?_ ?_)
    · exact ((hfd.continuousOn.mono (hannsub S)).sub continuousOn_const)
    · intro w hw
      have h2 := hw.2
      rw [Metric.mem_ball, dist_zero_right, not_lt] at h2
      exact sub_ne_zero.mpr (hnz w h2)
  have hFdiff : ∀ w : ℂ, ρ ≤ ‖w‖ →
      DifferentiableAt ℂ (fun w => deriv f w * (f w - z)⁻¹) w := by
    intro w hw
    have hwU : w ∈ U := by rw [hUmem]; linarith
    have h1 : DifferentiableAt ℂ (deriv f) w := (hT'anal w hwU).differentiableAt
    have h2 : DifferentiableAt ℂ f w := hfd.differentiableAt (hUopen.mem_nhds hwU)
    exact h1.mul ((h2.sub_const z).inv (sub_ne_zero.mpr (hnz w hw)))
  have hdeform : ∀ S : ℝ, ρ ≤ S →
      (∮ w in C(0, S), deriv f w * (f w - z)⁻¹) =
        ∮ w in C(0, ρ), deriv f w * (f w - z)⁻¹ := by
    intro S hS
    refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hρ0 hS
      Set.countable_empty (hFcont S) ?_
    intro w hw
    have h2 := hw.1.2
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at h2
    exact hFdiff w h2.le
  set Cnum : ℝ := M + Ms' with hCnumdef
  have hCnum0 : 0 ≤ Cnum := by rw [hCnumdef]; linarith [hM0]
  have hbound : ∀ S : ℝ, max (max ρ 2) (2 * (Ms' + M)) ≤ S →
      ‖(∮ w in C(0, ρ), deriv f w * (f w - z)⁻¹) - 2 * Real.pi * Complex.I‖ ≤
        2 * Real.pi * (2 * Cnum) / S := by
    intro S hS
    have hSρ : ρ ≤ S := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hS
    have hS2 : (2:ℝ) ≤ S := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hS
    have hSC : 2 * (Ms' + M) ≤ S := le_trans (le_max_right _ _) hS
    have hS0 : (0:ℝ) < S := lt_of_lt_of_le two_pos hS2
    have hw0int : (∮ w in C(0, S), (w - 0)⁻¹) = 2 * Real.pi * Complex.I :=
      circleIntegral.integral_sub_inv_of_mem_ball (Metric.mem_ball_self hS0)
    have hptw : ∀ w ∈ Metric.sphere (0:ℂ) S, ‖deriv f w * (f w - z)⁻¹ - (w - 0)⁻¹‖ ≤
        2 * Cnum / S ^ 2 := by
      intro w hw
      rw [Metric.mem_sphere, dist_zero_right] at hw
      have hwU : w ∈ U := by rw [hUmem]; linarith
      have hw2 : 2 ≤ ‖w‖ := by rw [hw]; exact hS2
      have hw0 : w ≠ 0 := hUne w hwU
      have hTz : f w - z ≠ 0 := sub_ne_zero.mpr (hnz w (by rw [hw]; exact hSρ))
      have hkey : ∀ A B C : ℂ, B - z ≠ 0 → w * A - B = -C →
          A * (B - z)⁻¹ - (w - 0)⁻¹ = (z - C) * (w * (B - z))⁻¹ := by
        intro A B C hBz hABC
        have hC : C = B - w * A := by linear_combination hABC
        rw [hC, sub_zero, mul_inv]
        field_simp
        ring
      have halg : deriv f w * (f w - z)⁻¹ - (w - 0)⁻¹ =
          (z - g₀ w) * (w * (f w - z))⁻¹ :=
        hkey (deriv f w) (f w) (g₀ w) hTz (hid w hwU)
      rw [halg, norm_mul, norm_inv, norm_mul]
      have hnum : ‖z - g₀ w‖ ≤ Cnum := by
        calc ‖z - g₀ w‖ ≤ ‖z‖ + ‖g₀ w‖ := norm_sub_le _ _
          _ ≤ M + Ms' := add_le_add hzM.le (hgb w hw2)
      have hTlow : ‖w‖ - Ms' ≤ ‖f w‖ := by
        have h3 := hfsub w hw2
        have h4 : ‖w‖ - ‖f w‖ ≤ ‖f w - w‖ := by
          calc ‖w‖ - ‖f w‖ ≤ ‖w - f w‖ := norm_sub_norm_le w (f w)
            _ = ‖f w - w‖ := by rw [norm_sub_rev]
        linarith
      have hden : S / 2 ≤ ‖f w - z‖ := by
        have h4 : ‖f w‖ - ‖z‖ ≤ ‖f w - z‖ := norm_sub_norm_le (f w) z
        rw [hw] at hTlow
        calc S / 2 = S - S / 2 := by ring
          _ ≤ S - (Ms' + M) := by linarith
          _ ≤ ‖f w - z‖ := by linarith
      have hden0 : (0:ℝ) < S / 2 := by linarith
      have hinvle : (‖w‖ * ‖f w - z‖)⁻¹ ≤ (S * (S / 2))⁻¹ := by
        rw [inv_le_inv₀ (by rw [hw]; positivity) (by positivity)]
        rw [hw]
        exact mul_le_mul_of_nonneg_left hden hS0.le
      calc ‖z - g₀ w‖ * (‖w‖ * ‖f w - z‖)⁻¹
          ≤ Cnum * (S * (S / 2))⁻¹ := by
            refine mul_le_mul hnum hinvle (by positivity) hCnum0
        _ = 2 * Cnum / S ^ 2 := by
            field_simp
    have hint1 : CircleIntegrable (fun w => deriv f w * (f w - z)⁻¹) 0 S := by
      refine ContinuousOn.circleIntegrable hS0.le ((hFcont S).mono ?_)
      intro w hw
      rw [Metric.mem_sphere, dist_zero_right] at hw
      constructor
      · rw [Metric.mem_closedBall, dist_zero_right, hw]
      · rw [Metric.mem_ball, dist_zero_right, hw]
        exact not_lt.mpr hSρ
    have hint2 : CircleIntegrable (fun w : ℂ => (w - 0)⁻¹) 0 S := by
      refine ContinuousOn.circleIntegrable hS0.le ?_
      refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
      intro w hw
      rw [Metric.mem_sphere, dist_zero_right] at hw
      rw [sub_zero]
      intro h0
      rw [h0, norm_zero] at hw
      linarith
    have hsplitInt : (∮ w in C(0, S),
          (deriv f w * (f w - z)⁻¹ - (w - 0)⁻¹)) =
        (∮ w in C(0, S), deriv f w * (f w - z)⁻¹) - ∮ w in C(0, S), (w - 0)⁻¹ :=
      circleIntegral.integral_sub hint1 hint2
    have hcircle : ‖∮ w in C(0, S), (deriv f w * (f w - z)⁻¹ - (w - 0)⁻¹)‖ ≤
        2 * Real.pi * S * (2 * Cnum / S ^ 2) :=
      circleIntegral.norm_integral_le_of_norm_le_const hS0.le hptw
    calc ‖(∮ w in C(0, ρ), deriv f w * (f w - z)⁻¹) - 2 * Real.pi * Complex.I‖
        = ‖(∮ w in C(0, S), deriv f w * (f w - z)⁻¹) - ∮ w in C(0, S), (w - 0)⁻¹‖ := by
          rw [hdeform S hSρ, hw0int]
      _ = ‖∮ w in C(0, S), (deriv f w * (f w - z)⁻¹ - (w - 0)⁻¹)‖ := by
          rw [hsplitInt]
      _ ≤ 2 * Real.pi * S * (2 * Cnum / S ^ 2) := hcircle
      _ = 2 * Real.pi * (2 * Cnum) / S := by
          field_simp
  have hzero := eq_zero_of_norm_le_const_div ((∮ w in C(0, ρ), deriv f w * (f w - z)⁻¹) -
      2 * Real.pi * Complex.I) (2 * Real.pi * (2 * Cnum)) _ (by positivity) hbound
  have := sub_eq_zero.mp hzero
  exact this

/-- The complex polar-coordinate parametrization `(t, θ) ↦ t·e^{iθ}` is continuous. -/
theorem continuous_complexPolarCoord_symm :
    Continuous fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
  have heq : (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
      = fun p : ℝ × ℝ => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I) := by
    funext p
    exact Complex.polarCoord_symm_apply p
  rw [heq]
  fun_prop

/-- The complex polar-coordinate parametrization agrees with `circleMap 0`. -/
theorem complexPolarCoord_symm_eq_circleMap (t θ : ℝ) :
    Complex.polarCoord.symm (t, θ) = circleMap 0 t θ := by
  rw [Complex.polarCoord_symm_apply]
  simp [circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- Radial estimate: the singular kernel `‖u⁻¹‖` integrates over `ball 0 R` to at most
`2πR`. -/
theorem lintegral_ball_enorm_inv_le (R : ℝ) (hR : 0 < R) :
    (∫⁻ u in Metric.ball (0:ℂ) R, ‖u⁻¹‖ₑ) ≤ ENNReal.ofReal (2 * Real.pi * R) := by
  have hpolar := Complex.lintegral_comp_polarCoord_symm
    ((Metric.ball (0:ℂ) R).indicator fun u => ‖u⁻¹‖ₑ)
  have hTm : MeasurableSet (Set.Ioo (0:ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hTsub : Set.Ioo (0:ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi ⊆ polarCoord.target := by
    rintro ⟨t, θ⟩ hp
    obtain ⟨ht, hθ⟩ := Set.mem_prod.mp hp
    rw [polarCoord_target]
    exact Set.mem_prod.mpr ⟨ht.1, hθ⟩
  have hptwise : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • (Metric.ball (0:ℂ) R).indicator (fun u => ‖u⁻¹‖ₑ)
        (Complex.polarCoord.symm p) =
      (Set.Ioo (0:ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator (fun _ => 1) p := by
    rintro ⟨t, θ⟩ hp
    rw [polarCoord_target] at hp
    obtain ⟨ht, hθ⟩ := Set.mem_prod.mp hp
    have ht0 : (0:ℝ) < t := ht
    have hnorm : ‖Complex.polarCoord.symm (t, θ)‖ = t := by
      rw [Complex.norm_polarCoord_symm]; exact abs_of_pos ht0
    by_cases htR : t < R
    · have hmem : Complex.polarCoord.symm (t, θ) ∈ Metric.ball (0:ℂ) R := by
        rw [Metric.mem_ball, dist_zero_right, hnorm]; exact htR
      have hmemT : ((t, θ) : ℝ × ℝ) ∈ Set.Ioo (0:ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi :=
        Set.mem_prod.mpr ⟨⟨ht0, htR⟩, hθ⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmemT, smul_eq_mul,
        ← ofReal_norm_eq_enorm, norm_inv, hnorm, ← ENNReal.ofReal_mul ht0.le,
        mul_inv_cancel₀ ht0.ne', ENNReal.ofReal_one]
    · have hnmem : Complex.polarCoord.symm (t, θ) ∉ Metric.ball (0:ℂ) R := by
        rw [Metric.mem_ball, dist_zero_right, hnorm]; exact htR
      have hnmemT : ((t, θ) : ℝ × ℝ) ∉ Set.Ioo (0:ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi := by
        intro hmemT
        exact htR (Set.mem_prod.mp hmemT).1.2
      rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hnmemT, smul_zero]
  have hsetEq : (∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
      (Metric.ball (0:ℂ) R).indicator (fun u => ‖u⁻¹‖ₑ) (Complex.polarCoord.symm p)) =
      ∫⁻ _p in Set.Ioo (0:ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi, (1:ℝ≥0∞) := by
    rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hptwise,
      setLIntegral_indicator hTm, Set.inter_eq_self_of_subset_left hTsub]
  have hbox : (∫⁻ _p in Set.Ioo (0:ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi, (1:ℝ≥0∞)) =
      ENNReal.ofReal R * ENNReal.ofReal (2 * Real.pi) := by
    rw [setLIntegral_one, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo,
      Real.volume_Ioo]
    congr 1
    · rw [sub_zero]
    · congr 1
      ring
  have hind : (∫⁻ u in Metric.ball (0:ℂ) R, ‖u⁻¹‖ₑ) =
      ∫⁻ u, (Metric.ball (0:ℂ) R).indicator (fun u => ‖u⁻¹‖ₑ) u := by
    rw [lintegral_indicator measurableSet_ball]
  rw [hind, ← hpolar, hsetEq, hbox]
  rw [← ENNReal.ofReal_mul hR.le]
  refine le_of_eq ?_
  congr 1
  ring

/-- The shifted kernel `‖(a₀ − z)⁻¹‖` integrates over `ball 0 M` to at most `4πM` when
`‖a₀‖ ≤ M`. -/
theorem lintegral_ball_enorm_inv_sub_le {M : ℝ} (hM : 0 < M) {a0 : ℂ} (ha0M : ‖a0‖ ≤ M) :
    (∫⁻ z in Metric.ball (0:ℂ) M, ‖(a0 - z)⁻¹‖ₑ) ≤ ENNReal.ofReal (4 * Real.pi * M) := by
  have hsub : Metric.ball (0:ℂ) M ⊆ Metric.ball a0 (2 * M) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖z - a0‖ ≤ ‖z‖ + ‖a0‖ := norm_sub_le _ _
      _ < 2 * M := by linarith
  have htrans : (∫⁻ w in Metric.ball (0:ℂ) (2 * M), ‖(a0 - (a0 + w))⁻¹‖ₑ)
      = ∫⁻ z in Metric.ball a0 (2 * M), ‖(a0 - z)⁻¹‖ₑ := by
    have hmp : MeasurePreserving (fun w : ℂ => a0 + w) volume volume :=
      measurePreserving_add_left volume a0
    have hemb : MeasurableEmbedding (fun w : ℂ => a0 + w) :=
      (Homeomorph.addLeft a0).measurableEmbedding
    have hpre : (fun w : ℂ => a0 + w) ⁻¹' Metric.ball a0 (2 * M) =
        Metric.ball (0:ℂ) (2 * M) := by
      ext w
      simp [Metric.mem_ball, dist_eq_norm]
    rw [← hpre]
    exact hmp.setLIntegral_comp_preimage_emb hemb
      (fun z => ‖(a0 - z)⁻¹‖ₑ) (Metric.ball a0 (2 * M))
  have hsimp : (∫⁻ w in Metric.ball (0:ℂ) (2 * M), ‖(a0 - (a0 + w))⁻¹‖ₑ) =
      ∫⁻ w in Metric.ball (0:ℂ) (2 * M), ‖w⁻¹‖ₑ := by
    refine lintegral_congr fun w => ?_
    have h1 : a0 - (a0 + w) = -w := by ring
    rw [h1, inv_neg, enorm_neg]
  calc (∫⁻ z in Metric.ball (0:ℂ) M, ‖(a0 - z)⁻¹‖ₑ)
      ≤ ∫⁻ z in Metric.ball a0 (2 * M), ‖(a0 - z)⁻¹‖ₑ := lintegral_mono_set hsub
    _ = ∫⁻ w in Metric.ball (0:ℂ) (2 * M), ‖w⁻¹‖ₑ := by rw [← htrans, hsimp]
    _ ≤ ENNReal.ofReal (2 * Real.pi * (2 * M)) :=
        lintegral_ball_enorm_inv_le (2 * M) (by linarith)
    _ = ENNReal.ofReal (4 * Real.pi * M) := by
        congr 1
        ring

/-- **The disk kernel identity**: for `‖a₀‖ < M`,
`∫_{ball 0 M} (a₀ − z)⁻¹ dA(z) = π · conj a₀`. -/
theorem integral_ball_inv_sub_eq_pi_mul_conj {M : ℝ} {a0 : ℂ} (ha0M : ‖a0‖ < M) :
    (∫ z in Metric.ball (0:ℂ) M, (a0 - z)⁻¹) = (Real.pi : ℂ) * (starRingEnd ℂ) a0 := by
  have hM0 : (0:ℝ) < M := lt_of_le_of_lt (norm_nonneg a0) ha0M
  -- Inner circle values.
  have hinner1 : ∀ t : ℝ, 0 < t → t < ‖a0‖ →
      (∫ θ in (0:ℝ)..(2 * Real.pi), (a0 - circleMap 0 t θ)⁻¹) =
        2 * Real.pi * a0⁻¹ := by
    intro t ht htlt
    have hane : ∀ z : ℂ, ‖z‖ ≤ t → a0 - z ≠ 0 := by
      intro z hz h0
      have h1 : z = a0 := by linear_combination -h0
      rw [h1] at hz
      linarith
    have hc : ContinuousOn (fun z => (a0 - z)⁻¹) (Metric.closedBall (0:ℂ) |t|) := by
      refine ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id) ?_
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right, abs_of_pos ht] at hz
      exact hane z hz
    have hd : ∀ z ∈ Metric.ball (0:ℂ) |t| \ (∅ : Set ℂ),
        DifferentiableAt ℂ (fun z => (a0 - z)⁻¹) z := by
      intro z hz
      rw [Set.diff_empty, Metric.mem_ball, dist_zero_right, abs_of_pos ht] at hz
      exact ((differentiableAt_const a0).sub differentiableAt_fun_id).inv (hane z hz.le)
    have hmean := circleAverage_of_differentiable_on_off_countable
      Set.countable_empty hc hd
    rw [Real.circleAverage_def, sub_zero] at hmean
    have h2π : (2 * Real.pi) ≠ 0 := by positivity
    have hmean2 : (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
        (∫ θ in (0:ℝ)..(2 * Real.pi), (a0 - circleMap 0 t θ)⁻¹) = a0⁻¹ := hmean
    have h3 : (∫ θ in (0:ℝ)..(2 * Real.pi), (a0 - circleMap 0 t θ)⁻¹) =
        ((2 * Real.pi : ℝ) : ℂ) * a0⁻¹ := by
      have h4 := congrArg (fun x : ℂ => ((2 * Real.pi : ℝ) : ℂ) * x) hmean2
      simp only at h4
      rw [← mul_assoc] at h4
      have h5 : ((2 * Real.pi : ℝ) : ℂ) * (((2 * Real.pi)⁻¹ : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ h2π, Complex.ofReal_one]
      rw [h5, one_mul] at h4
      exact h4
    rw [h3]
    push_cast
    ring
  have hinner2 : ∀ t : ℝ, 0 < t → ‖a0‖ < t →
      (∫ θ in (0:ℝ)..(2 * Real.pi), (a0 - circleMap 0 t θ)⁻¹) = 0 := by
    intro t ht htgt
    have hwne : ∀ θ : ℝ, circleMap 0 t θ ≠ 0 := by
      intro θ h0
      have h1 := norm_circleMap_zero t θ
      rw [h0, norm_zero, abs_of_pos ht] at h1
      linarith
    have hane : ∀ θ : ℝ, a0 - circleMap 0 t θ ≠ 0 := by
      intro θ h0
      have h1 : ‖circleMap 0 t θ‖ = t := by rw [norm_circleMap_zero, abs_of_pos ht]
      have h2 : circleMap 0 t θ = a0 := by linear_combination -h0
      rw [h2] at h1
      linarith
    have hEint : (∮ w in C(0, t), (w⁻¹ * (a0 - w)⁻¹)) =
        Complex.I * ∫ θ in (0:ℝ)..(2 * Real.pi), (a0 - circleMap 0 t θ)⁻¹ := by
      rw [circleIntegral]
      have hcongr : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * Real.pi), deriv (circleMap 0 t) θ •
          ((circleMap 0 t θ)⁻¹ * (a0 - circleMap 0 t θ)⁻¹) =
          Complex.I * (a0 - circleMap 0 t θ)⁻¹ := by
        intro θ _
        rw [deriv_circleMap, smul_eq_mul]
        field_simp [hwne θ, hane θ]
        try ring
      rw [intervalIntegral.integral_congr hcongr]
      exact intervalIntegral.integral_const_mul _ _
    have hIne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    rcases eq_or_ne a0 0 with rfl | ha0ne
    · have hE0 : (∮ w in C(0, t), (w⁻¹ * ((0:ℂ) - w)⁻¹)) =
          ∮ w in C(0, t), (-1 : ℂ) • ((w - 0) ^ (-2 : ℤ)) := by
        refine circleIntegral.integral_congr ht.le fun w hw => ?_
        rw [Metric.mem_sphere, dist_zero_right] at hw
        have hw0 : w ≠ 0 := by
          intro h0
          rw [h0, norm_zero] at hw
          linarith
        rw [zero_sub, sub_zero, smul_eq_mul]
        rw [zpow_neg, inv_neg]
        field_simp
      have hE1 : (∮ w in C(0, t), (-1 : ℂ) • ((w - 0) ^ (-2 : ℤ))) =
          (-1 : ℂ) • ∮ w in C(0, t), ((w - 0) ^ (-2 : ℤ)) :=
        circleIntegral.integral_smul _ _ _ _
      have hE2 : (∮ w in C(0, t), ((w - 0) ^ (-2 : ℤ))) = 0 :=
        circleIntegral.integral_sub_zpow_of_ne (by norm_num) 0 0 t
      have hEz : Complex.I * (∫ θ in (0:ℝ)..(2 * Real.pi),
          ((0:ℂ) - circleMap 0 t θ)⁻¹) = 0 := by
        rw [← hEint, hE0, hE1, hE2, smul_zero]
      rcases mul_eq_zero.mp hEz with h | h
      · exact absurd h hIne
      · exact h
    · have ha0mem : a0 ∈ Metric.ball (0:ℂ) t := by
        rw [Metric.mem_ball, dist_zero_right]
        exact htgt
      have hsplitPF : ∀ w ∈ Metric.sphere (0:ℂ) t, w⁻¹ * (a0 - w)⁻¹ =
          a0⁻¹ • (w - 0)⁻¹ - a0⁻¹ • (w - a0)⁻¹ := by
        intro w hw
        rw [Metric.mem_sphere, dist_zero_right] at hw
        have hw0 : w ≠ 0 := by
          intro h0
          rw [h0, norm_zero] at hw
          linarith
        have hwa : w - a0 ≠ 0 := by
          intro h0
          have h1 : w = a0 := by linear_combination h0
          rw [h1] at hw
          linarith
        have haw : a0 - w ≠ 0 := by
          intro h0
          have h1 : w = a0 := by linear_combination -h0
          rw [h1] at hw
          linarith
        rw [sub_zero, smul_eq_mul, smul_eq_mul]
        field_simp
        ring
      have hi1 : CircleIntegrable (fun w : ℂ => a0⁻¹ • (w - 0)⁻¹) 0 t := by
        refine ContinuousOn.circleIntegrable ht.le ?_
        refine ContinuousOn.smul continuousOn_const ?_
        refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
        intro w hw
        rw [Metric.mem_sphere, dist_zero_right] at hw
        rw [sub_zero]
        intro h0
        rw [h0, norm_zero] at hw
        linarith
      have hi2 : CircleIntegrable (fun w : ℂ => a0⁻¹ • (w - a0)⁻¹) 0 t := by
        refine ContinuousOn.circleIntegrable ht.le ?_
        refine ContinuousOn.smul continuousOn_const ?_
        refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
        intro w hw
        rw [Metric.mem_sphere, dist_zero_right] at hw
        intro h0
        have h1 : w = a0 := by linear_combination h0
        rw [h1] at hw
        linarith
      have hE3 : (∮ w in C(0, t), (w⁻¹ * (a0 - w)⁻¹)) =
          (∮ w in C(0, t), a0⁻¹ • (w - 0)⁻¹) - ∮ w in C(0, t), a0⁻¹ • (w - a0)⁻¹ := by
        rw [circleIntegral.integral_congr ht.le hsplitPF]
        exact circleIntegral.integral_sub hi1 hi2
      have hE4 : (∮ w in C(0, t), a0⁻¹ • (w - 0)⁻¹) = a0⁻¹ • (2 * Real.pi * Complex.I) := by
        rw [circleIntegral.integral_smul]
        congr 1
        exact circleIntegral.integral_sub_inv_of_mem_ball (Metric.mem_ball_self ht)
      have hE5 : (∮ w in C(0, t), a0⁻¹ • (w - a0)⁻¹) = a0⁻¹ • (2 * Real.pi * Complex.I) := by
        rw [circleIntegral.integral_smul]
        congr 1
        exact circleIntegral.integral_sub_inv_of_mem_ball ha0mem
      have hEz : Complex.I * (∫ θ in (0:ℝ)..(2 * Real.pi),
          (a0 - circleMap 0 t θ)⁻¹) = 0 := by
        rw [← hEint, hE3, hE4, hE5, sub_self]
      rcases mul_eq_zero.mp hEz with h | h
      · exact absurd h hIne
      · exact h
  -- Conversion of the inner integral from `Ioo (-π) π` to `0..2π`.
  have hIooconv : ∀ t : ℝ, (∫ θ in Set.Ioo (-Real.pi) Real.pi,
      (a0 - circleMap 0 t θ)⁻¹) =
      ∫ θ in (0:ℝ)..(2 * Real.pi), (a0 - circleMap 0 t θ)⁻¹ := by
    intro t
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    have hper : Function.Periodic (fun θ : ℝ => (a0 - circleMap 0 t θ)⁻¹) (2 * Real.pi) := by
      intro θ
      simp [periodic_circleMap 0 t θ]
    have h := hper.intervalIntegral_add_eq (-Real.pi) 0
    have h2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
    have h3 : (0:ℝ) + 2 * Real.pi = 2 * Real.pi := by ring
    rw [h2, h3] at h
    exact h
  -- Polar transform of the ball integral to the box.
  have hTmB : MeasurableSet (Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hTsubB : Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi ⊆ polarCoord.target := by
    rintro ⟨t, θ⟩ hp
    obtain ⟨ht, hθ⟩ := Set.mem_prod.mp hp
    rw [polarCoord_target]
    exact Set.mem_prod.mpr ⟨ht.1, hθ⟩
  have hpolarB := Complex.integral_comp_polarCoord_symm
    ((Metric.ball (0:ℂ) M).indicator fun z => (a0 - z)⁻¹)
  have hptwiseB : ∀ p ∈ polarCoord.target,
      p.1 • (Metric.ball (0:ℂ) M).indicator (fun z => (a0 - z)⁻¹)
        (Complex.polarCoord.symm p) =
      (Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
        (fun q => ((q.1 : ℝ) : ℂ) * (a0 - Complex.polarCoord.symm q)⁻¹) p := by
    rintro ⟨t, θ⟩ hp
    rw [polarCoord_target] at hp
    obtain ⟨ht, hθ⟩ := Set.mem_prod.mp hp
    have ht0 : (0:ℝ) < t := ht
    have hnorm : ‖Complex.polarCoord.symm (t, θ)‖ = t := by
      rw [Complex.norm_polarCoord_symm]; exact abs_of_pos ht0
    by_cases htM : t < M
    · have hmem : Complex.polarCoord.symm (t, θ) ∈ Metric.ball (0:ℂ) M := by
        rw [Metric.mem_ball, dist_zero_right, hnorm]; exact htM
      have hmemT : ((t, θ) : ℝ × ℝ) ∈ Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi :=
        Set.mem_prod.mpr ⟨⟨ht0, htM⟩, hθ⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmemT, Complex.real_smul]
    · have hnmem : Complex.polarCoord.symm (t, θ) ∉ Metric.ball (0:ℂ) M := by
        rw [Metric.mem_ball, dist_zero_right, hnorm]; exact htM
      have hnmemT : ((t, θ) : ℝ × ℝ) ∉ Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi := by
        intro hmemT
        exact htM (Set.mem_prod.mp hmemT).1.2
      rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hnmemT,
        Complex.real_smul, mul_zero]
  have hball : (∫ z in Metric.ball (0:ℂ) M, (a0 - z)⁻¹) =
      ∫ q in Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi,
        ((q.1 : ℝ) : ℂ) * (a0 - Complex.polarCoord.symm q)⁻¹ :=
    calc (∫ z in Metric.ball (0:ℂ) M, (a0 - z)⁻¹)
        = ∫ z, (Metric.ball (0:ℂ) M).indicator (fun z => (a0 - z)⁻¹) z :=
          (integral_indicator measurableSet_ball).symm
      _ = ∫ p in polarCoord.target, p.1 • (Metric.ball (0:ℂ) M).indicator
            (fun z => (a0 - z)⁻¹) (Complex.polarCoord.symm p) := hpolarB.symm
      _ = ∫ p in polarCoord.target,
            (Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
              (fun q => ((q.1 : ℝ) : ℂ) * (a0 - Complex.polarCoord.symm q)⁻¹) p :=
          setIntegral_congr_fun polarCoord.open_target.measurableSet hptwiseB
      _ = ∫ q in polarCoord.target ∩ (Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi),
            ((q.1 : ℝ) : ℂ) * (a0 - Complex.polarCoord.symm q)⁻¹ :=
          setIntegral_indicator hTmB
      _ = _ := by rw [Set.inter_eq_self_of_subset_right hTsubB]
  -- Integrability on the box.
  have hFmeas : AEStronglyMeasurable
      (fun q : ℝ × ℝ => ((q.1 : ℝ) : ℂ) * (a0 - Complex.polarCoord.symm q)⁻¹)
      (volume.restrict (Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi)) := by
    refine Measurable.aestronglyMeasurable ?_
    exact (Complex.measurable_ofReal.comp measurable_fst).mul
      ((measurable_const.sub continuous_complexPolarCoord_symm.measurable).inv)
  have hFnormEq : ∀ q ∈ Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi,
      ‖(fun q : ℝ × ℝ => ((q.1 : ℝ) : ℂ) * (a0 - Complex.polarCoord.symm q)⁻¹) q‖ₑ =
      ENNReal.ofReal q.1 •
        (Metric.ball (0:ℂ) M).indicator (fun z => ‖(a0 - z)⁻¹‖ₑ)
          (Complex.polarCoord.symm q) := by
    rintro ⟨t, θ⟩ hq
    obtain ⟨ht, hθ⟩ := Set.mem_prod.mp hq
    have ht0 : (0:ℝ) < t := ht.1
    have hnorm : ‖Complex.polarCoord.symm (t, θ)‖ = t := by
      rw [Complex.norm_polarCoord_symm]; exact abs_of_pos ht0
    have hmem : Complex.polarCoord.symm (t, θ) ∈ Metric.ball (0:ℂ) M := by
      rw [Metric.mem_ball, dist_zero_right, hnorm]; exact ht.2
    rw [Set.indicator_of_mem hmem]
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht0, ENNReal.ofReal_mul ht0.le, smul_eq_mul]
  have hLptwise : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 •
        (Metric.ball (0:ℂ) M).indicator (fun z => ‖(a0 - z)⁻¹‖ₑ)
          (Complex.polarCoord.symm p) =
      (Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
        (fun q => ENNReal.ofReal q.1 •
          (Metric.ball (0:ℂ) M).indicator (fun z => ‖(a0 - z)⁻¹‖ₑ)
            (Complex.polarCoord.symm q)) p := by
    rintro ⟨t, θ⟩ hp
    rw [polarCoord_target] at hp
    obtain ⟨ht, hθ⟩ := Set.mem_prod.mp hp
    have ht0 : (0:ℝ) < t := ht
    have hnorm : ‖Complex.polarCoord.symm (t, θ)‖ = t := by
      rw [Complex.norm_polarCoord_symm]; exact abs_of_pos ht0
    by_cases htM : t < M
    · have hmemT : ((t, θ) : ℝ × ℝ) ∈ Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi :=
        Set.mem_prod.mpr ⟨⟨ht0, htM⟩, hθ⟩
      rw [Set.indicator_of_mem hmemT]
    · have hnmem : Complex.polarCoord.symm (t, θ) ∉ Metric.ball (0:ℂ) M := by
        rw [Metric.mem_ball, dist_zero_right, hnorm]; exact htM
      have hnmemT : ((t, θ) : ℝ × ℝ) ∉
          Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi := by
        intro hmemT
        exact htM (Set.mem_prod.mp hmemT).1.2
      rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hnmemT, smul_zero]
  have hLpolar := Complex.lintegral_comp_polarCoord_symm
    ((Metric.ball (0:ℂ) M).indicator fun z => ‖(a0 - z)⁻¹‖ₑ)
  have hLeq : (∫⁻ z in Metric.ball (0:ℂ) M, ‖(a0 - z)⁻¹‖ₑ) =
      ∫⁻ q in Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal q.1 •
          (Metric.ball (0:ℂ) M).indicator (fun z => ‖(a0 - z)⁻¹‖ₑ)
            (Complex.polarCoord.symm q) :=
    calc (∫⁻ z in Metric.ball (0:ℂ) M, ‖(a0 - z)⁻¹‖ₑ)
        = ∫⁻ z, (Metric.ball (0:ℂ) M).indicator (fun z => ‖(a0 - z)⁻¹‖ₑ) z :=
          (lintegral_indicator measurableSet_ball _).symm
      _ = ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
            (Metric.ball (0:ℂ) M).indicator (fun z => ‖(a0 - z)⁻¹‖ₑ)
              (Complex.polarCoord.symm p) := hLpolar.symm
      _ = ∫⁻ p in polarCoord.target,
            (Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
              (fun q => ENNReal.ofReal q.1 •
                (Metric.ball (0:ℂ) M).indicator (fun z => ‖(a0 - z)⁻¹‖ₑ)
                  (Complex.polarCoord.symm q)) p :=
          setLIntegral_congr_fun polarCoord.open_target.measurableSet hLptwise
      _ = ∫⁻ q in (Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi) ∩ polarCoord.target,
            ENNReal.ofReal q.1 •
              (Metric.ball (0:ℂ) M).indicator (fun z => ‖(a0 - z)⁻¹‖ₑ)
                (Complex.polarCoord.symm q) := setLIntegral_indicator hTmB _
      _ = _ := by rw [Set.inter_eq_self_of_subset_left hTsubB]
  have hFfin : (∫⁻ q in Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi,
      ‖(fun q : ℝ × ℝ => ((q.1 : ℝ) : ℂ) * (a0 - Complex.polarCoord.symm q)⁻¹) q‖ₑ) < ⊤ := by
    rw [setLIntegral_congr_fun hTmB hFnormEq, ← hLeq]
    exact lt_of_le_of_lt (lintegral_ball_enorm_inv_sub_le hM0 ha0M.le) ENNReal.ofReal_lt_top
  have hFint : IntegrableOn
      (fun q : ℝ × ℝ => ((q.1 : ℝ) : ℂ) * (a0 - Complex.polarCoord.symm q)⁻¹)
      (Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi) := ⟨hFmeas, hFfin⟩
  have hmeqB : (volume.restrict (Set.Ioo (0:ℝ) M)).prod
      (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) =
      volume.restrict (Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hiterated : (∫ q in Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi,
      ((q.1 : ℝ) : ℂ) * (a0 - Complex.polarCoord.symm q)⁻¹) =
      ∫ t in Set.Ioo (0:ℝ) M, ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        ((t : ℝ) : ℂ) * (a0 - Complex.polarCoord.symm (t, θ))⁻¹ := by
    rw [← hmeqB]
    exact integral_prod _ (by rw [hmeqB]; exact hFint)
  have haet : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ ‖a0‖ := by
    have h1 : volume ({‖a0‖} : Set ℝ) = 0 := measure_singleton _
    have h2 := MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h1
    filter_upwards [h2] with t ht
    simpa using ht
  have hradcongr : (∫ t in Set.Ioo (0:ℝ) M, ∫ θ in Set.Ioo (-Real.pi) Real.pi,
      ((t : ℝ) : ℂ) * (a0 - Complex.polarCoord.symm (t, θ))⁻¹) =
      ∫ t in Set.Ioo (0:ℝ) M,
        (Set.Iio ‖a0‖).indicator (fun u => (u : ℂ) * (2 * Real.pi * a0⁻¹)) t := by
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [haet] with t hne ht
    have e1 : (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        ((t : ℝ) : ℂ) * (a0 - Complex.polarCoord.symm (t, θ))⁻¹) =
        ((t : ℝ) : ℂ) * ∫ θ in Set.Ioo (-Real.pi) Real.pi, (a0 - circleMap 0 t θ)⁻¹ :=
      calc (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ((t : ℝ) : ℂ) * (a0 - Complex.polarCoord.symm (t, θ))⁻¹)
          = ∫ θ in Set.Ioo (-Real.pi) Real.pi,
              ((t : ℝ) : ℂ) * (a0 - circleMap 0 t θ)⁻¹ := by
            refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
            rw [complexPolarCoord_symm_eq_circleMap t θ]
        _ = ((t : ℝ) : ℂ) * ∫ θ in Set.Ioo (-Real.pi) Real.pi,
              (a0 - circleMap 0 t θ)⁻¹ := integral_const_mul _ _
    rw [e1, hIooconv t]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [hinner1 t ht.1 hlt, Set.indicator_of_mem (Set.mem_Iio.mpr hlt)]
    · rw [hinner2 t ht.1 hgt, mul_zero,
        Set.indicator_of_notMem (by rw [Set.mem_Iio]; exact not_lt.mpr hgt.le)]
  have hfinal : (∫ t in Set.Ioo (0:ℝ) M,
      (Set.Iio ‖a0‖).indicator (fun u => (u : ℂ) * (2 * Real.pi * a0⁻¹)) t) =
      (Real.pi : ℂ) * (starRingEnd ℂ) a0 := by
    rw [setIntegral_indicator measurableSet_Iio]
    have hseteq : Set.Ioo (0:ℝ) M ∩ Set.Iio ‖a0‖ = Set.Ioo 0 ‖a0‖ := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iio]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, lt_trans h2 ha0M⟩, h2⟩
    rw [hseteq]
    rcases eq_or_ne a0 0 with rfl | ha0ne
    · simp
    · have hnorm0 : 0 < ‖a0‖ := norm_pos_iff.mpr ha0ne
      have e2 : (∫ t in Set.Ioo (0:ℝ) ‖a0‖, ((t : ℂ) * (2 * Real.pi * a0⁻¹))) =
          (2 * Real.pi * a0⁻¹) * ∫ t in Set.Ioo (0:ℝ) ‖a0‖, (t : ℂ) :=
        calc (∫ t in Set.Ioo (0:ℝ) ‖a0‖, ((t : ℂ) * (2 * Real.pi * a0⁻¹)))
            = ∫ t in Set.Ioo (0:ℝ) ‖a0‖, (2 * Real.pi * a0⁻¹) * (t : ℂ) := by
              refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
              ring
          _ = (2 * Real.pi * a0⁻¹) * ∫ t in Set.Ioo (0:ℝ) ‖a0‖, (t : ℂ) :=
              integral_const_mul _ _
      have hidInt : IntegrableOn (fun t : ℝ => t) (Set.Ioo (0:ℝ) ‖a0‖) :=
        (continuous_id.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
      have e3 : (∫ t in Set.Ioo (0:ℝ) ‖a0‖, (t : ℂ)) = ((‖a0‖ ^ 2 / 2 : ℝ) : ℂ) := by
        have h4 : (∫ t in Set.Ioo (0:ℝ) ‖a0‖, t) = ‖a0‖ ^ 2 / 2 := by
          rw [← integral_Ioc_eq_integral_Ioo,
            ← intervalIntegral.integral_of_le hnorm0.le, integral_id]
          ring
        have h5 := Complex.ofRealCLM.integral_comp_comm hidInt
        simp only [Complex.ofRealCLM_apply] at h5
        rw [h5, h4]
      rw [e2, e3]
      have hmc : a0 * (starRingEnd ℂ) a0 = ((‖a0‖ : ℝ) : ℂ) ^ 2 := Complex.mul_conj' a0
      field_simp
      push_cast
      linear_combination -hmc
  rw [hball, hiterated, hradcongr, hfinal]

/-- **The Gronwall area theorem, first-coefficient form**: if `s` is holomorphic on the
unit ball with `s 0 = 1` and the exterior map `w ↦ w·s(1/w)` is injective on
`{1 < ‖w‖}`, then the coefficient `b₁ = s''(0)/2` of the exterior expansion satisfies
`|b₁| ≤ 1`. -/
theorem abs_laurent_coeff_le_of_injOn {s : ℂ → ℂ}
    (hs : DifferentiableOn ℂ s (Metric.ball 0 1)) (hs0 : s 0 = 1)
    (hinj : Set.InjOn (fun w => w * s w⁻¹) {w : ℂ | 1 < ‖w‖}) :
    ‖iteratedDeriv 2 s 0‖ ≤ 2 := by
  -- ## Outer reduction: it suffices to bound by `2ρ²` for every `ρ > 1`.
  suffices key : ∀ ρ : ℝ, 1 < ρ → ‖iteratedDeriv 2 s 0‖ ≤ 2 * ρ ^ 2 by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h0 : (0:ℝ) ≤ 1 + ε / 2 := by linarith
    have h1 : (1:ℝ) < Real.sqrt (1 + ε / 2) := by
      nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (1 + ε / 2)]
    have h2 := key _ h1
    rw [Real.sq_sqrt h0] at h2
    linarith
  intro ρ hρ
  have hρ0 : (0:ℝ) < ρ := lt_trans one_pos hρ
  set U : Set ℂ := {w : ℂ | 1 < ‖w‖} with hUdef
  set T : ℂ → ℂ := fun w => w * s w⁻¹ with hTdef
  have hUmem : ∀ w : ℂ, w ∈ U ↔ 1 < ‖w‖ := fun w => Iff.rfl
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hUne : ∀ w : ℂ, w ∈ U → w ≠ 0 := by
    intro w hw h0
    rw [hUmem] at hw
    simp [h0] at hw
    linarith
  have hUinv : ∀ w : ℂ, w ∈ U → w⁻¹ ∈ Metric.ball (0:ℂ) 1 := by
    intro w hw
    rw [hUmem] at hw
    rw [Metric.mem_ball, dist_zero_right, norm_inv]
    exact inv_lt_one_of_one_lt₀ hw
  -- ## Differentiability and analyticity of `T` on `U`.
  have hTdiff : DifferentiableOn ℂ T U := by
    rw [hTdef]
    refine DifferentiableOn.mul differentiableOn_id ?_
    have hinv : DifferentiableOn ℂ (fun w : ℂ => w⁻¹) U :=
      differentiableOn_inv.mono fun w hw => hUne w hw
    exact hs.comp hinv fun w hw => hUinv w hw
  have hTanal : AnalyticOnNhd ℂ T U := hTdiff.analyticOnNhd hUopen
  have hT'anal : AnalyticOnNhd ℂ (deriv T) U := hTanal.deriv
  have hT'cont : ContinuousOn (deriv T) U := hT'anal.continuousOn
  have hsdiffAt : ∀ w : ℂ, w ∈ U → DifferentiableAt ℂ s w⁻¹ := fun w hw =>
    hs.differentiableAt (Metric.isOpen_ball.mem_nhds (hUinv w hw))
  have hsderiv : ∀ w : ℂ, w ∈ U → HasDerivAt T (s w⁻¹ - deriv s w⁻¹ * w⁻¹) w := by
    intro w hw
    have hw0 : w ≠ 0 := hUne w hw
    have h1 : HasDerivAt (fun u : ℂ => u⁻¹) (-(w ^ 2)⁻¹) w := hasDerivAt_inv hw0
    have h2 : HasDerivAt s (deriv s w⁻¹) w⁻¹ := (hsdiffAt w hw).hasDerivAt
    have h3 : HasDerivAt (fun u : ℂ => s u⁻¹) (deriv s w⁻¹ * -(w ^ 2)⁻¹) w := h2.comp w h1
    have h4 := (hasDerivAt_id w).mul h3
    have h5 : 1 * s w⁻¹ + w * (deriv s w⁻¹ * -(w ^ 2)⁻¹) = s w⁻¹ - deriv s w⁻¹ * w⁻¹ := by
      field_simp
      ring
    rw [← h5]
    exact h4
  have hTderiv : ∀ w : ℂ, w ∈ U → deriv T w = s w⁻¹ - deriv s w⁻¹ * w⁻¹ := fun w hw =>
    (hsderiv w hw).deriv
  -- ## Bounds on `s` and `deriv s` on the closed ball of radius `1/2`.
  have hhalf : Metric.closedBall (0:ℂ) 2⁻¹ ⊆ Metric.ball (0:ℂ) 1 :=
    Metric.closedBall_subset_ball (by norm_num)
  have hscont : ContinuousOn s (Metric.closedBall (0:ℂ) 2⁻¹) := (hs.mono hhalf).continuousOn
  have hs'cont : ContinuousOn (deriv s) (Metric.closedBall (0:ℂ) 2⁻¹) :=
    ((hs.analyticOnNhd Metric.isOpen_ball).deriv.continuousOn).mono hhalf
  obtain ⟨Ms, hMs⟩ := (isCompact_closedBall (0:ℂ) 2⁻¹).exists_bound_of_continuousOn hscont
  obtain ⟨Ms', hMs'⟩ := (isCompact_closedBall (0:ℂ) 2⁻¹).exists_bound_of_continuousOn hs'cont
  have hMs0 : 0 ≤ Ms :=
    le_trans (norm_nonneg _) (hMs 0 (Metric.mem_closedBall_self (by norm_num)))
  have hMs'0 : 0 ≤ Ms' :=
    le_trans (norm_nonneg _) (hMs' 0 (Metric.mem_closedBall_self (by norm_num)))
  have hinvhalf : ∀ w : ℂ, 2 ≤ ‖w‖ → w⁻¹ ∈ Metric.closedBall (0:ℂ) 2⁻¹ := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right, norm_inv]
    have h0 : (0:ℝ) < ‖w‖ := lt_of_lt_of_le (by norm_num) hw
    rw [inv_le_inv₀ h0 (by norm_num)]
    exact hw
  -- Mean value bound: `‖T w − w‖ ≤ Ms'` for `‖w‖ ≥ 2`.
  have hTsub : ∀ w : ℂ, 2 ≤ ‖w‖ → ‖T w - w‖ ≤ Ms' := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro h; rw [h] at hw; simp at hw; linarith
    have hmv : ‖s w⁻¹ - s 0‖ ≤ Ms' * ‖w⁻¹ - 0‖ := by
      refine Convex.norm_image_sub_le_of_norm_deriv_le (fun x hx => ?_) hMs'
        (convex_closedBall _ _) (Metric.mem_closedBall_self (by norm_num)) (hinvhalf w hw)
      exact hs.differentiableAt (Metric.isOpen_ball.mem_nhds (hhalf hx))
    have heq : T w - w = w * (s w⁻¹ - s 0) := by
      rw [hTdef, hs0]; ring
    rw [heq, norm_mul]
    rw [sub_zero, norm_inv] at hmv
    calc ‖w‖ * ‖s w⁻¹ - s 0‖ ≤ ‖w‖ * (Ms' * ‖w‖⁻¹) :=
          mul_le_mul_of_nonneg_left hmv (norm_nonneg _)
      _ = Ms' := by
          field_simp
  have hT'bound : ∀ w : ℂ, 2 ≤ ‖w‖ → ‖deriv T w‖ ≤ Ms + Ms' := by
    intro w hw
    have hwU : w ∈ U := by rw [hUmem]; linarith
    rw [hTderiv w hwU]
    have h1 : ‖s w⁻¹‖ ≤ Ms := hMs _ (hinvhalf w hw)
    have h2 : ‖deriv s w⁻¹ * w⁻¹‖ ≤ Ms' * 1 := by
      rw [norm_mul]
      refine mul_le_mul (hMs' _ (hinvhalf w hw)) ?_ (norm_nonneg _) hMs'0
      rw [norm_inv]
      refine inv_le_one_of_one_le₀ (by linarith)
    calc ‖s w⁻¹ - deriv s w⁻¹ * w⁻¹‖ ≤ ‖s w⁻¹‖ + ‖deriv s w⁻¹ * w⁻¹‖ := norm_sub_le _ _
      _ ≤ Ms + Ms' * 1 := add_le_add h1 h2
      _ = Ms + Ms' := by ring
  -- The exact identity `w·T'(w) − T(w) = −s'(w⁻¹)`.
  have hwTT : ∀ w : ℂ, w ∈ U → w * deriv T w - T w = -(deriv s w⁻¹) := by
    intro w hw
    have hw0 : w ≠ 0 := hUne w hw
    rw [hTderiv w hw, hTdef]
    field_simp
    ring
  -- ## Bounds on the circle of radius `ρ`.
  have hsphereU : Metric.sphere (0:ℂ) ρ ⊆ U := by
    intro w hw
    rw [Metric.mem_sphere, dist_zero_right] at hw
    rw [hUmem, hw]
    exact hρ
  have hcircU : ∀ θ : ℝ, circleMap 0 ρ θ ∈ U := fun θ =>
    hsphereU (circleMap_mem_sphere 0 hρ0.le θ)
  obtain ⟨MT, hMT⟩ := (isCompact_sphere (0:ℂ) ρ).exists_bound_of_continuousOn
    (hTdiff.continuousOn.mono hsphereU)
  obtain ⟨MA, hMA⟩ := (isCompact_sphere (0:ℂ) ρ).exists_bound_of_continuousOn
    (hT'cont.mono hsphereU)
  have hMT0 : 0 ≤ MT := by
    have hmem : (ρ:ℂ) ∈ Metric.sphere (0:ℂ) ρ := by
      simp [Complex.norm_real, abs_of_pos hρ0]
    exact le_trans (norm_nonneg _) (hMT _ hmem)
  set M : ℝ := MT + 1 with hMdef
  have hM0 : 0 < M := by rw [hMdef]; linarith
  have hTcircM : ∀ θ : ℝ, ‖T (circleMap 0 ρ θ)‖ < M := by
    intro θ
    have := hMT _ (circleMap_mem_sphere 0 hρ0.le θ)
    rw [hMdef]; linarith
  -- ## The power series of `s` at the origin, at radius `rr ∈ (ρ⁻¹, 1)`.
  set rrR : ℝ := (1 + ρ⁻¹) / 2 with hrrRdef
  have hρinv1 : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ
  have hρinv0 : 0 < ρ⁻¹ := inv_pos.mpr hρ0
  have hrr0 : 0 < rrR := by rw [hrrRdef]; linarith
  have hrr1 : rrR < 1 := by rw [hrrRdef]; linarith
  have hrrρ : ρ⁻¹ < rrR := by rw [hrrRdef]; linarith
  set rrN : NNReal := ⟨rrR, hrr0.le⟩ with hrrNdef
  have hrrNcoe : (rrN : ℝ) = rrR := rfl
  have hrrN0 : 0 < rrN := by
    rw [← NNReal.coe_lt_coe, hrrNcoe, NNReal.coe_zero]
    exact hrr0
  have hsball : DifferentiableOn ℂ s (Metric.closedBall 0 (rrN : ℝ)) := by
    refine hs.mono (Metric.closedBall_subset_ball ?_)
    rw [hrrNcoe]; exact hrr1
  have hps : HasFPowerSeriesOnBall s (cauchyPowerSeries s 0 (rrN : ℝ)) 0 rrN :=
    hsball.hasFPowerSeriesOnBall hrrN0
  set a : ℕ → ℂ := fun m => (cauchyPowerSeries s 0 (rrN : ℝ)).coeff m with hadef
  have ha0 : a 0 = 1 := by
    have h1 : (cauchyPowerSeries s 0 (rrN : ℝ)).coeff 0 = s 0 := hps.coeff_zero 1
    rw [hadef]
    rw [hs0] at h1
    exact h1
  -- Coefficient bounds `‖a m‖ ≤ Msr · rrR⁻ᵐ`.
  obtain ⟨Msr, hMsr⟩ := (isCompact_sphere (0:ℂ) rrR).exists_bound_of_continuousOn
    ((hs.mono (Metric.sphere_subset_closedBall.trans
      (Metric.closedBall_subset_ball hrr1))).continuousOn)
  have hMsr0 : 0 ≤ Msr := by
    have hmem : (rrR:ℂ) ∈ Metric.sphere (0:ℂ) rrR := by
      simp [Complex.norm_real, abs_of_pos hrr0]
    exact le_trans (norm_nonneg _) (hMsr _ hmem)
  have hacoeff : ∀ m : ℕ, ‖a m‖ ≤ Msr * (rrR⁻¹) ^ m := by
    intro m
    have h1 : ‖a m‖ ≤ ‖cauchyPowerSeries s 0 (rrN : ℝ) m‖ := by
      rw [hadef]
      calc ‖(cauchyPowerSeries s 0 (rrN : ℝ)).coeff m‖
          = ‖(cauchyPowerSeries s 0 (rrN : ℝ)) m (fun _ => 1)‖ := rfl
        _ ≤ ‖(cauchyPowerSeries s 0 (rrN : ℝ)) m‖ * ∏ _i : Fin m, ‖(1:ℂ)‖ :=
            ContinuousMultilinearMap.le_opNorm _ _
        _ = ‖(cauchyPowerSeries s 0 (rrN : ℝ)) m‖ := by simp
    have h2 := norm_cauchyPowerSeries_le s 0 (rrN : ℝ) m
    have hcont : Continuous fun θ : ℝ => ‖s (circleMap 0 (rrN : ℝ) θ)‖ := by
      have hmap : ∀ θ : ℝ, circleMap 0 (rrN : ℝ) θ ∈ Metric.ball (0:ℂ) 1 := by
        intro θ
        have h7 : (0:ℝ) ≤ (rrN : ℝ) := hrr0.le
        have := circleMap_mem_sphere (0:ℂ) h7 θ
        rw [Metric.mem_sphere, dist_zero_right] at this
        rw [Metric.mem_ball, dist_zero_right, this, hrrNcoe]
        exact hrr1
      exact ((hs.continuousOn).comp_continuous (continuous_circleMap _ _) hmap).norm
    have h3 : (∫ θ in (0:ℝ)..(2 * Real.pi), ‖s (circleMap 0 (rrN : ℝ) θ)‖) ≤
        2 * Real.pi * Msr := by
      have hb : ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), ‖s (circleMap 0 (rrN : ℝ) θ)‖ ≤ Msr := by
        intro θ _
        apply hMsr
        have h7 : (0:ℝ) ≤ (rrN : ℝ) := hrr0.le
        have := circleMap_mem_sphere (0:ℂ) h7 θ
        rwa [hrrNcoe] at this
      calc (∫ θ in (0:ℝ)..(2 * Real.pi), ‖s (circleMap 0 (rrN : ℝ) θ)‖)
          ≤ ∫ _θ in (0:ℝ)..(2 * Real.pi), Msr := by
            refine intervalIntegral.integral_mono_on Real.two_pi_pos.le
              (hcont.intervalIntegrable _ _) (intervalIntegrable_const) hb
        _ = 2 * Real.pi * Msr := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
            ring
    have h4 : ((2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
        ‖s (circleMap 0 (rrN : ℝ) θ)‖) * |(rrN : ℝ)|⁻¹ ^ m ≤ Msr * (rrR⁻¹) ^ m := by
      have h5 : |(rrN : ℝ)| = rrR := by rw [hrrNcoe]; exact abs_of_pos hrr0
      rw [h5]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have h6 : (0:ℝ) < 2 * Real.pi := Real.two_pi_pos
      rw [inv_mul_le_iff₀ h6]
      calc (∫ θ in (0:ℝ)..(2 * Real.pi), ‖s (circleMap 0 (rrN : ℝ) θ)‖)
          ≤ 2 * Real.pi * Msr := h3
        _ = 2 * Real.pi * Msr := rfl
    exact le_trans h1 (le_trans h2 h4)
  -- The Laurent expansion of `T` on the circle of radius `ρ`.
  have hcircnorm : ∀ θ : ℝ, ‖circleMap 0 ρ θ‖ = ρ := by
    intro θ
    rw [norm_circleMap_zero, abs_of_pos hρ0]
  have hcircne : ∀ θ : ℝ, circleMap 0 ρ θ ≠ 0 := by
    intro θ h0
    have := hcircnorm θ
    rw [h0, norm_zero] at this
    linarith
  have hasumT : ∀ θ : ℝ, HasSum
      (fun m => a m * ((circleMap 0 ρ θ)⁻¹) ^ m * circleMap 0 ρ θ)
      (T (circleMap 0 ρ θ)) := by
    intro θ
    have hy : (circleMap 0 ρ θ)⁻¹ ∈ Metric.eball (0:ℂ) (rrN : ℝ≥0∞) := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm_eq_enorm,
        ← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _) |>.mpr ?_
      rw [norm_inv, hcircnorm, hrrNcoe]
      exact hrrρ
    have h1 := hps.hasSum hy
    rw [zero_add] at h1
    simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff] at h1
    have h4 := h1.mul_right (circleMap 0 ρ θ)
    have h5 : T (circleMap 0 ρ θ) = s (circleMap 0 ρ θ)⁻¹ * circleMap 0 ρ θ := by
      rw [hTdef]; ring
    have h6 : (fun m => a m * ((circleMap 0 ρ θ)⁻¹) ^ m * circleMap 0 ρ θ) =
        fun m => (((circleMap 0 ρ θ)⁻¹) ^ m •
          (cauchyPowerSeries s 0 (rrN : ℝ)).coeff m) * circleMap 0 ρ θ := by
      funext m
      rw [smul_eq_mul, hadef]
      ring
    rw [h5, h6]
    exact h4
  -- ## The real coefficient series.
  set u : ℕ → ℝ := fun m => ((m:ℝ) - 1) * ‖a m‖ ^ 2 * (ρ ^ 2 * ((ρ⁻¹) ^ 2) ^ m) with hudef
  have hxgeom : ((rrR * ρ)⁻¹ ^ 2 : ℝ) < 1 := by
    have h1 : (1:ℝ) < rrR * ρ := by
      have h2 : ρ⁻¹ * ρ < rrR * ρ := mul_lt_mul_of_pos_right hrrρ hρ0
      rwa [inv_mul_cancel₀ hρ0.ne'] at h2
    have h2 : (rrR * ρ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
    have h3 : (0:ℝ) < (rrR * ρ)⁻¹ := by positivity
    nlinarith
  have hxgeom0 : (0:ℝ) ≤ (rrR * ρ)⁻¹ ^ 2 := by positivity
  have husum : Summable u := by
    have hbig : Summable fun m : ℕ =>
        Msr ^ 2 * ρ ^ 2 * (((m:ℝ) + 1) * ((rrR * ρ)⁻¹ ^ 2) ^ m) := by
      refine Summable.mul_left _ ?_
      have hx1 : ‖((rrR * ρ)⁻¹ ^ 2 : ℝ)‖ < 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hxgeom0]
        exact hxgeom
      have hs1 := summable_pow_mul_geometric_of_norm_lt_one 1 hx1
      have hs2 := summable_pow_mul_geometric_of_norm_lt_one 0 hx1
      have := hs1.add hs2
      refine this.congr fun m => ?_
      ring
    refine Summable.of_norm_bounded hbig ?_
    intro m
    rw [Real.norm_eq_abs]
    simp only [hudef]
    have h1 : |((m:ℝ) - 1) * ‖a m‖ ^ 2 * (ρ ^ 2 * ((ρ⁻¹) ^ 2) ^ m)| ≤
        ((m:ℝ) + 1) * ‖a m‖ ^ 2 * (ρ ^ 2 * ((ρ⁻¹) ^ 2) ^ m) := by
      rw [abs_mul, abs_mul]
      have e1 : |((m:ℝ) - 1)| ≤ (m:ℝ) + 1 := by
        rw [abs_le]
        have := Nat.cast_nonneg (α := ℝ) m
        constructor <;> linarith
      have e2 : |‖a m‖ ^ 2| = ‖a m‖ ^ 2 := abs_of_nonneg (sq_nonneg _)
      have e3 : |ρ ^ 2 * ((ρ⁻¹) ^ 2) ^ m| = ρ ^ 2 * ((ρ⁻¹) ^ 2) ^ m :=
        abs_of_nonneg (by positivity)
      rw [e2, e3]
      have e4 : (0:ℝ) ≤ ‖a m‖ ^ 2 * (ρ ^ 2 * ((ρ⁻¹) ^ 2) ^ m) := by positivity
      calc |((m:ℝ) - 1)| * ‖a m‖ ^ 2 * (ρ ^ 2 * ((ρ⁻¹) ^ 2) ^ m)
          = |((m:ℝ) - 1)| * (‖a m‖ ^ 2 * (ρ ^ 2 * ((ρ⁻¹) ^ 2) ^ m)) := by ring
        _ ≤ ((m:ℝ) + 1) * (‖a m‖ ^ 2 * (ρ ^ 2 * ((ρ⁻¹) ^ 2) ^ m)) :=
            mul_le_mul_of_nonneg_right e1 e4
        _ = ((m:ℝ) + 1) * ‖a m‖ ^ 2 * (ρ ^ 2 * ((ρ⁻¹) ^ 2) ^ m) := by ring
    have h2 : ((m:ℝ) + 1) * ‖a m‖ ^ 2 * (ρ ^ 2 * ((ρ⁻¹) ^ 2) ^ m) ≤
        Msr ^ 2 * ρ ^ 2 * (((m:ℝ) + 1) * ((rrR * ρ)⁻¹ ^ 2) ^ m) := by
      have e1 : ‖a m‖ ^ 2 ≤ (Msr * (rrR⁻¹) ^ m) ^ 2 := by
        have := hacoeff m
        nlinarith [norm_nonneg (a m), this]
      have e2 : ((m:ℝ) + 1) * ‖a m‖ ^ 2 * (ρ ^ 2 * ((ρ⁻¹) ^ 2) ^ m) ≤
          ((m:ℝ) + 1) * (Msr * (rrR⁻¹) ^ m) ^ 2 * (ρ ^ 2 * ((ρ⁻¹) ^ 2) ^ m) := by
        have e3 : (0:ℝ) ≤ ((m:ℝ) + 1) := by positivity
        have e4 : (0:ℝ) ≤ ρ ^ 2 * ((ρ⁻¹) ^ 2) ^ m := by positivity
        have e5 : ((m:ℝ) + 1) * ‖a m‖ ^ 2 ≤ ((m:ℝ) + 1) * (Msr * (rrR⁻¹) ^ m) ^ 2 :=
          mul_le_mul_of_nonneg_left e1 e3
        exact mul_le_mul_of_nonneg_right e5 e4
      refine le_trans e2 (le_of_eq ?_)
      ring_nf
    exact le_trans h1 h2
  set US : ℝ := ∑' m, u m with hUSdef
  -- ## The image of the circle is a null set.
  have hNnull : volume (T '' Metric.sphere (0:ℂ) ρ) = 0 := by
    have hsm : MeasurableSet (Metric.sphere (0:ℂ) ρ) := Metric.isClosed_sphere.measurableSet
    have hf' : ∀ w ∈ Metric.sphere (0:ℂ) ρ, HasFDerivWithinAt T (fderiv ℝ T w)
        (Metric.sphere (0:ℂ) ρ) w := by
      intro w hw
      have hwU : w ∈ U := hsphereU hw
      have h1 : HasDerivAt T (deriv T w) w :=
        (hTdiff.differentiableAt (hUopen.mem_nhds hwU)).hasDerivAt
      exact ((h1.complexToReal_fderiv).differentiableAt.hasFDerivAt).hasFDerivWithinAt
    have hinjS : Set.InjOn T (Metric.sphere (0:ℂ) ρ) := hinj.mono hsphereU
    have h1 := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hsm hf'
      hinjS (fun _ => 1)
    have h2 : volume (Metric.sphere (0:ℂ) ρ) = 0 := Measure.addHaar_sphere volume 0 ρ
    rw [setLIntegral_one] at h1
    rw [h1, setLIntegral_measure_zero _ _ h2]
  -- ## Case A of the dichotomy: `z` in the image of the open exterior.
  have hcaseA : ∀ z : ℂ, z ∉ T '' Metric.sphere (0:ℂ) ρ → z ∈ T '' {w : ℂ | ρ < ‖w‖} →
      (∮ w in C(0, ρ), deriv T w * (T w - z)⁻¹) = 0 := fun z _ hzI =>
    circleIntegral_deriv_mul_inv_sub_eq_zero hρ hMs0 hMs'0 hTdiff hinj hwTT
      (fun w hw => hMs' _ (hinvhalf w hw)) hTsub hT'bound hzI
  -- ## Case B of the dichotomy: `z` in the omitted set.
  have hcaseB : ∀ z : ℂ, ‖z‖ < M → z ∉ T '' Metric.sphere (0:ℂ) ρ →
      z ∉ T '' {w : ℂ | ρ < ‖w‖} →
      (∮ w in C(0, ρ), deriv T w * (T w - z)⁻¹) = 2 * Real.pi * Complex.I :=
    fun z hzM hzN hzI =>
    circleIntegral_deriv_mul_inv_sub_eq_two_pi_I hρ hM0 hMs'0 hTdiff hwTT
      (fun w hw => hMs' _ (hinvhalf w hw)) hTsub hzM hzN hzI
  -- ## The double-integral integrand and its integrability.
  set G : ℂ → ℝ → ℂ := fun z θ => circleMap 0 ρ θ * Complex.I *
    (deriv T (circleMap 0 ρ θ) * (T (circleMap 0 ρ θ) - z)⁻¹) with hGdef
  have hMA0 : 0 ≤ MA := by
    have hmem : (ρ:ℂ) ∈ Metric.sphere (0:ℂ) ρ := by
      simp [Complex.norm_real, abs_of_pos hρ0]
    exact le_trans (norm_nonneg _) (hMA _ hmem)
  have hGmeas : Measurable (Function.uncurry G) := by
    have hc1 : Continuous fun θ : ℝ => circleMap 0 ρ θ * Complex.I *
        deriv T (circleMap 0 ρ θ) := by
      refine Continuous.mul ((continuous_circleMap 0 ρ).mul continuous_const) ?_
      exact hT'cont.comp_continuous (continuous_circleMap 0 ρ) hcircU
    have hc2 : Continuous fun θ : ℝ => T (circleMap 0 ρ θ) := by
      exact hTdiff.continuousOn.comp_continuous (continuous_circleMap 0 ρ) hcircU
    have h1 : Function.uncurry G = fun p : ℂ × ℝ =>
        (circleMap 0 ρ p.2 * Complex.I * deriv T (circleMap 0 ρ p.2)) *
          (T (circleMap 0 ρ p.2) - p.1)⁻¹ := by
      funext p
      rw [Function.uncurry, hGdef]
      ring
    rw [h1]
    exact ((hc1.measurable.comp measurable_snd)).mul
      (((hc2.measurable.comp measurable_snd).sub measurable_fst).inv)
  have hGint : Integrable (Function.uncurry G)
      ((volume.restrict (Metric.ball (0:ℂ) M)).prod
        (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) := by
    refine ⟨hGmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have h1 : (∫⁻ p, ‖Function.uncurry G p‖ₑ
        ∂((volume.restrict (Metric.ball (0:ℂ) M)).prod
          (volume.restrict (Set.Ioc 0 (2 * Real.pi))))) =
        ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ∫⁻ z in Metric.ball (0:ℂ) M, ‖G z θ‖ₑ :=
      lintegral_prod_symm _ hGmeas.enorm.aemeasurable
    rw [h1]
    have h2 : ∀ θ : ℝ, (∫⁻ z in Metric.ball (0:ℂ) M, ‖G z θ‖ₑ) ≤
        ENNReal.ofReal (ρ * MA) * ENNReal.ofReal (4 * Real.pi * M) := by
      intro θ
      have h3 : ∀ z : ℂ, ‖G z θ‖ₑ ≤ ENNReal.ofReal (ρ * MA) *
          ‖(T (circleMap 0 ρ θ) - z)⁻¹‖ₑ := by
        intro z
        have h4 : G z θ = (circleMap 0 ρ θ * Complex.I * deriv T (circleMap 0 ρ θ)) *
            (T (circleMap 0 ρ θ) - z)⁻¹ := by
          rw [hGdef]; ring
        rw [h4, enorm_mul]
        refine mul_le_mul_left ?_ _
        rw [← ofReal_norm_eq_enorm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero,
          abs_of_pos hρ0]
        exact mul_le_mul_of_nonneg_left
          (hMA _ (circleMap_mem_sphere 0 hρ0.le θ)) hρ0.le
      calc (∫⁻ z in Metric.ball (0:ℂ) M, ‖G z θ‖ₑ)
          ≤ ∫⁻ z in Metric.ball (0:ℂ) M, ENNReal.ofReal (ρ * MA) *
              ‖(T (circleMap 0 ρ θ) - z)⁻¹‖ₑ := lintegral_mono h3
        _ = ENNReal.ofReal (ρ * MA) *
              ∫⁻ z in Metric.ball (0:ℂ) M, ‖(T (circleMap 0 ρ θ) - z)⁻¹‖ₑ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (ρ * MA) * ENNReal.ofReal (4 * Real.pi * M) :=
            mul_le_mul_right (lintegral_ball_enorm_inv_sub_le hM0 (hTcircM θ).le) _
    calc (∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ∫⁻ z in Metric.ball (0:ℂ) M, ‖G z θ‖ₑ)
        ≤ ∫⁻ _θ in Set.Ioc 0 (2 * Real.pi), ENNReal.ofReal (ρ * MA) *
            ENNReal.ofReal (4 * Real.pi * M) := lintegral_mono fun θ => h2 θ
      _ = ENNReal.ofReal (ρ * MA) * ENNReal.ofReal (4 * Real.pi * M) *
            volume (Set.Ioc (0:ℝ) (2 * Real.pi)) := setLIntegral_const _ _
      _ < ⊤ := by
          rw [Real.volume_Ioc]
          exact ENNReal.mul_lt_top
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
            ENNReal.ofReal_lt_top
  -- ## Parseval: the exact value of the circle energy integral.
  -- Derivative of the circle image curve.
  have hAderiv : ∀ θ : ℝ, HasDerivAt (fun t => T (circleMap 0 ρ t))
      (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)) θ := by
    intro θ
    have h1 := hasDerivAt_circleMap 0 ρ θ
    have h2 : HasDerivAt T (deriv T (circleMap 0 ρ θ)) (circleMap 0 ρ θ) :=
      (hTdiff.differentiableAt (hUopen.mem_nhds (hcircU θ))).hasDerivAt
    exact h2.comp θ h1
  have hAcont : Continuous fun θ : ℝ => T (circleMap 0 ρ θ) :=
    hTdiff.continuousOn.comp_continuous (continuous_circleMap 0 ρ) hcircU
  have hA'cont : Continuous fun θ : ℝ =>
      deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I) :=
    (hT'cont.comp_continuous (continuous_circleMap 0 ρ) hcircU).mul
      ((continuous_circleMap 0 ρ).mul continuous_const)
  -- Integration by parts: the `E`-integrals in terms of the Fourier coefficients of `A`.
  have hEval : ∀ m : ℕ, (∫ θ in (0:ℝ)..(2 * Real.pi),
      (circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ *
        (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))) =
      -(((m:ℂ) - 1) * Complex.I) * ∫ θ in (0:ℝ)..(2 * Real.pi),
        (circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ * T (circleMap 0 ρ θ) := fun m =>
    integral_circleMap_pow_mul_curve_deriv hρ0 (f := T) (f' := deriv T)
      hAderiv hAcont hA'cont m
  have hq0 : (0:ℝ) ≤ (rrR * ρ)⁻¹ := by positivity
  have hq1 : (rrR * ρ)⁻¹ < 1 := by
    have h1 : (1:ℝ) < rrR * ρ := by
      have h2 : ρ⁻¹ * ρ < rrR * ρ := mul_lt_mul_of_pos_right hrrρ hρ0
      rwa [inv_mul_cancel₀ hρ0.ne'] at h2
    exact inv_lt_one_of_one_lt₀ h1
  -- The Fourier coefficients of the boundary curve.
  have hFm : ∀ m : ℕ, (∫ θ in (0:ℝ)..(2 * Real.pi),
      (circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ * T (circleMap 0 ρ θ)) =
      ((2 * Real.pi : ℝ) : ℂ) * a m := by
    intro m
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
    have hpt2 : ∀ θ : ℝ, HasSum
        (fun j => a j * ((circleMap 0 ρ θ) ^ m * ((circleMap 0 ρ θ)⁻¹) ^ j))
        ((circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ * T (circleMap 0 ρ θ)) := by
      intro θ
      have h1 := (hasumT θ).mul_left ((circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹)
      have h2 : (fun j => (circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ *
          (a j * ((circleMap 0 ρ θ)⁻¹) ^ j * circleMap 0 ρ θ)) =
          fun j => a j * ((circleMap 0 ρ θ) ^ m * ((circleMap 0 ρ θ)⁻¹) ^ j) := by
        funext j
        have hcne := hcircne θ
        field_simp
        try ring
      rw [h2] at h1
      exact h1
    have hmeas2 : ∀ j : ℕ, AEStronglyMeasurable
        (fun θ : ℝ => a j * ((circleMap 0 ρ θ) ^ m * ((circleMap 0 ρ θ)⁻¹) ^ j))
        (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
      intro j
      refine Continuous.aestronglyMeasurable ?_
      exact continuous_const.mul (((continuous_circleMap 0 ρ).pow m).mul
        (((continuous_circleMap 0 ρ).inv₀ hcircne).pow j))
    have hbnd2 : ∀ (j : ℕ) (θ : ℝ),
        ‖a j * ((circleMap 0 ρ θ) ^ m * ((circleMap 0 ρ θ)⁻¹) ^ j)‖ ≤
        (Msr * ρ ^ m) * ((rrR * ρ)⁻¹) ^ j := by
      intro j θ
      rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_inv, hcircnorm θ]
      have h1 := hacoeff j
      have h2 : (0:ℝ) ≤ ρ ^ m * (ρ⁻¹) ^ j := by positivity
      calc ‖a j‖ * (ρ ^ m * (ρ⁻¹) ^ j) ≤ (Msr * rrR⁻¹ ^ j) * (ρ ^ m * (ρ⁻¹) ^ j) :=
            mul_le_mul_of_nonneg_right h1 h2
        _ = (Msr * ρ ^ m) * ((rrR * ρ)⁻¹) ^ j := by
            rw [mul_inv, mul_pow]
            ring
    have hswap2 : (∫ θ in Set.Ioc (0:ℝ) (2 * Real.pi),
        (circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ * T (circleMap 0 ρ θ)) =
        ∑' j, ∫ θ in Set.Ioc (0:ℝ) (2 * Real.pi),
          a j * ((circleMap 0 ρ θ) ^ m * ((circleMap 0 ρ θ)⁻¹) ^ j) := by
      rw [← integral_tsum hmeas2 ?_]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
        exact ((hpt2 θ).tsum_eq).symm
      · have hb : ∀ j : ℕ, (∫⁻ θ in Set.Ioc (0:ℝ) (2 * Real.pi),
            ‖a j * ((circleMap 0 ρ θ) ^ m * ((circleMap 0 ρ θ)⁻¹) ^ j)‖ₑ) ≤
            ENNReal.ofReal ((Msr * ρ ^ m) * ((rrR * ρ)⁻¹) ^ j * (2 * Real.pi)) := by
          intro j
          calc (∫⁻ θ in Set.Ioc (0:ℝ) (2 * Real.pi),
                ‖a j * ((circleMap 0 ρ θ) ^ m * ((circleMap 0 ρ θ)⁻¹) ^ j)‖ₑ)
              ≤ ∫⁻ _θ in Set.Ioc (0:ℝ) (2 * Real.pi),
                  ENNReal.ofReal ((Msr * ρ ^ m) * ((rrR * ρ)⁻¹) ^ j) := by
                refine lintegral_mono fun θ => ?_
                rw [← ofReal_norm_eq_enorm]
                exact ENNReal.ofReal_le_ofReal (hbnd2 j θ)
            _ = ENNReal.ofReal ((Msr * ρ ^ m) * ((rrR * ρ)⁻¹) ^ j) *
                  volume (Set.Ioc (0:ℝ) (2 * Real.pi)) := setLIntegral_const _ _
            _ = ENNReal.ofReal ((Msr * ρ ^ m) * ((rrR * ρ)⁻¹) ^ j * (2 * Real.pi)) := by
                rw [Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
        refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hb) ?_)
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) ?_]
        · exact ENNReal.ofReal_lt_top
        · exact ((summable_geometric_of_lt_one hq0 hq1).mul_left _).mul_right _
    rw [hswap2]
    have hperj : ∀ j : ℕ, (∫ θ in Set.Ioc (0:ℝ) (2 * Real.pi),
        a j * ((circleMap 0 ρ θ) ^ m * ((circleMap 0 ρ θ)⁻¹) ^ j)) =
        a j * (if m = j then ((2 * Real.pi : ℝ) : ℂ) else 0) := by
      intro j
      calc (∫ θ in Set.Ioc (0:ℝ) (2 * Real.pi),
            a j * ((circleMap 0 ρ θ) ^ m * ((circleMap 0 ρ θ)⁻¹) ^ j))
          = a j * ∫ θ in Set.Ioc (0:ℝ) (2 * Real.pi),
              (circleMap 0 ρ θ) ^ m * ((circleMap 0 ρ θ)⁻¹) ^ j := integral_const_mul _ _
        _ = a j * (if m = j then ((2 * Real.pi : ℝ) : ℂ) else 0) := by
            rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le,
              integral_circleMap_pow_mul_inv_pow hρ0 m j]
    rw [tsum_congr hperj]
    have hite : (fun j => a j * (if m = j then ((2 * Real.pi : ℝ) : ℂ) else 0)) =
        fun j => if j = m then a j * ((2 * Real.pi : ℝ) : ℂ) else 0 := by
      funext j
      by_cases h : j = m
      · subst h
        simp
      · have h2 : ¬(m = j) := fun hh => h hh.symm
        simp [h, h2]
    rw [hite, tsum_ite_eq]
    ring
  have hKpar : (∫ θ in (0:ℝ)..(2 * Real.pi), (starRingEnd ℂ) (T (circleMap 0 ρ θ)) *
      (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))) =
      -(2 * Real.pi * Complex.I) * ((US : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
    have hpt1 : ∀ θ : ℝ, HasSum
        (fun m => (starRingEnd ℂ) (a m * ((circleMap 0 ρ θ)⁻¹) ^ m * circleMap 0 ρ θ) *
          (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)))
        ((starRingEnd ℂ) (T (circleMap 0 ρ θ)) *
          (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))) := by
      intro θ
      have h1 := (hasumT θ).mapL Complex.conjCLE.toContinuousLinearMap
      have h2 : ∀ x : ℂ, Complex.conjCLE.toContinuousLinearMap x = (starRingEnd ℂ) x :=
        fun _ => rfl
      simp only [h2] at h1
      exact h1.mul_right _
    have hmeas1 : ∀ m : ℕ, AEStronglyMeasurable
        (fun θ : ℝ => (starRingEnd ℂ) (a m * ((circleMap 0 ρ θ)⁻¹) ^ m * circleMap 0 ρ θ) *
          (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)))
        (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
      intro m
      refine Continuous.aestronglyMeasurable (Continuous.mul ?_ hA'cont)
      have hconjc : Continuous fun z : ℂ => (starRingEnd ℂ) z := by fun_prop
      exact hconjc.comp
        ((continuous_const.mul (((continuous_circleMap 0 ρ).inv₀ hcircne).pow m)).mul
          (continuous_circleMap 0 ρ))
    have hbnd1 : ∀ (m : ℕ) (θ : ℝ),
        ‖(starRingEnd ℂ) (a m * ((circleMap 0 ρ θ)⁻¹) ^ m * circleMap 0 ρ θ) *
          (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))‖ ≤
        (Msr * ρ * (MA * ρ)) * ((rrR * ρ)⁻¹) ^ m := by
      intro m θ
      rw [norm_mul, Complex.norm_conj, norm_mul, norm_mul, norm_pow, norm_inv,
        hcircnorm θ, norm_mul, norm_mul, Complex.norm_I, mul_one, hcircnorm θ]
      have h1 : ‖a m‖ * (ρ⁻¹) ^ m * ρ ≤ (Msr * ρ) * ((rrR * ρ)⁻¹) ^ m := by
        have h2 := hacoeff m
        have h3 : (0:ℝ) ≤ (ρ⁻¹) ^ m * ρ := by positivity
        calc ‖a m‖ * (ρ⁻¹) ^ m * ρ = ‖a m‖ * ((ρ⁻¹) ^ m * ρ) := by ring
          _ ≤ (Msr * rrR⁻¹ ^ m) * ((ρ⁻¹) ^ m * ρ) := mul_le_mul_of_nonneg_right h2 h3
          _ = (Msr * ρ) * ((rrR * ρ)⁻¹) ^ m := by
              rw [mul_inv, mul_pow]
              ring
      have h4 : ‖deriv T (circleMap 0 ρ θ)‖ * ρ ≤ MA * ρ :=
        mul_le_mul_of_nonneg_right (hMA _ (circleMap_mem_sphere 0 hρ0.le θ)) hρ0.le
      have h5 : (0:ℝ) ≤ ‖a m‖ * (ρ⁻¹) ^ m * ρ := by positivity
      have h6 : (0:ℝ) ≤ ‖deriv T (circleMap 0 ρ θ)‖ * ρ := by positivity
      calc ‖a m‖ * (ρ⁻¹) ^ m * ρ * (‖deriv T (circleMap 0 ρ θ)‖ * ρ)
          ≤ (Msr * ρ) * ((rrR * ρ)⁻¹) ^ m * (MA * ρ) :=
            mul_le_mul h1 h4 h6 (by positivity)
        _ = (Msr * ρ * (MA * ρ)) * ((rrR * ρ)⁻¹) ^ m := by ring
    have hswap1 : (∫ θ in Set.Ioc (0:ℝ) (2 * Real.pi),
        (starRingEnd ℂ) (T (circleMap 0 ρ θ)) *
          (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))) =
        ∑' m, ∫ θ in Set.Ioc (0:ℝ) (2 * Real.pi),
          (starRingEnd ℂ) (a m * ((circleMap 0 ρ θ)⁻¹) ^ m * circleMap 0 ρ θ) *
            (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)) := by
      rw [← integral_tsum hmeas1 ?_]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
        exact ((hpt1 θ).tsum_eq).symm
      · have hb : ∀ m : ℕ, (∫⁻ θ in Set.Ioc (0:ℝ) (2 * Real.pi),
            ‖(starRingEnd ℂ) (a m * ((circleMap 0 ρ θ)⁻¹) ^ m * circleMap 0 ρ θ) *
              (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))‖ₑ) ≤
            ENNReal.ofReal ((Msr * ρ * (MA * ρ)) * ((rrR * ρ)⁻¹) ^ m * (2 * Real.pi)) := by
          intro m
          calc (∫⁻ θ in Set.Ioc (0:ℝ) (2 * Real.pi),
                ‖(starRingEnd ℂ) (a m * ((circleMap 0 ρ θ)⁻¹) ^ m * circleMap 0 ρ θ) *
                  (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))‖ₑ)
              ≤ ∫⁻ _θ in Set.Ioc (0:ℝ) (2 * Real.pi),
                  ENNReal.ofReal ((Msr * ρ * (MA * ρ)) * ((rrR * ρ)⁻¹) ^ m) := by
                refine lintegral_mono fun θ => ?_
                rw [← ofReal_norm_eq_enorm]
                exact ENNReal.ofReal_le_ofReal (hbnd1 m θ)
            _ = ENNReal.ofReal ((Msr * ρ * (MA * ρ)) * ((rrR * ρ)⁻¹) ^ m) *
                  volume (Set.Ioc (0:ℝ) (2 * Real.pi)) := setLIntegral_const _ _
            _ = ENNReal.ofReal ((Msr * ρ * (MA * ρ)) * ((rrR * ρ)⁻¹) ^ m *
                  (2 * Real.pi)) := by
                rw [Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
        refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hb) ?_)
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) ?_]
        · exact ENNReal.ofReal_lt_top
        · exact ((summable_geometric_of_lt_one hq0 hq1).mul_left _).mul_right _
    rw [hswap1]
    have hconjc : ∀ θ : ℝ, (starRingEnd ℂ) (circleMap 0 ρ θ) =
        (ρ:ℂ) ^ 2 * (circleMap 0 ρ θ)⁻¹ := by
      intro θ
      have hρne : (ρ:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ0.ne'
      rw [circleMap_zero_eq_mul_exp ρ θ, map_mul, Complex.conj_ofReal]
      have h1 : (starRingEnd ℂ) ((θ:ℂ) * Complex.I) = -((θ:ℂ) * Complex.I) := by
        rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
        ring
      rw [← Complex.exp_conj, h1, Complex.exp_neg, mul_inv]
      have hexpne : Complex.exp ((θ:ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
      field_simp
      try ring
    have hperm : ∀ m : ℕ, (∫ θ in Set.Ioc (0:ℝ) (2 * Real.pi),
        (starRingEnd ℂ) (a m * ((circleMap 0 ρ θ)⁻¹) ^ m * circleMap 0 ρ θ) *
          (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))) =
        -(2 * Real.pi * Complex.I) * ((u m : ℝ) : ℂ) := by
      intro m
      have hct : ∀ θ : ℝ,
          (starRingEnd ℂ) (a m * ((circleMap 0 ρ θ)⁻¹) ^ m * circleMap 0 ρ θ) *
            (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)) =
          ((starRingEnd ℂ) (a m) * ((ρ:ℂ) ^ 2 * (((ρ:ℂ)⁻¹) ^ 2) ^ m)) *
            ((circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ *
              (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))) := by
        intro θ
        rw [map_mul, map_mul, map_pow, map_inv₀, hconjc θ]
        have hcne := hcircne θ
        have hρne : (ρ:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ0.ne'
        field_simp
        ring
      calc (∫ θ in Set.Ioc (0:ℝ) (2 * Real.pi),
            (starRingEnd ℂ) (a m * ((circleMap 0 ρ θ)⁻¹) ^ m * circleMap 0 ρ θ) *
              (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)))
          = ∫ θ in Set.Ioc (0:ℝ) (2 * Real.pi),
              ((starRingEnd ℂ) (a m) * ((ρ:ℂ) ^ 2 * (((ρ:ℂ)⁻¹) ^ 2) ^ m)) *
                ((circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ *
                  (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))) :=
            setIntegral_congr_fun measurableSet_Ioc fun θ _ => hct θ
        _ = ((starRingEnd ℂ) (a m) * ((ρ:ℂ) ^ 2 * (((ρ:ℂ)⁻¹) ^ 2) ^ m)) *
              ∫ θ in Set.Ioc (0:ℝ) (2 * Real.pi),
                (circleMap 0 ρ θ) ^ m * (circleMap 0 ρ θ)⁻¹ *
                  (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)) :=
            integral_const_mul _ _
        _ = ((starRingEnd ℂ) (a m) * ((ρ:ℂ) ^ 2 * (((ρ:ℂ)⁻¹) ^ 2) ^ m)) *
              (-(((m:ℂ) - 1) * Complex.I) * (((2 * Real.pi : ℝ) : ℂ) * a m)) := by
            rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le, hEval m, hFm m]
        _ = -(2 * Real.pi * Complex.I) * ((u m : ℝ) : ℂ) := by
            simp only [hudef]
            have hmc : a m * (starRingEnd ℂ) (a m) = ((‖a m‖ : ℝ) : ℂ) ^ 2 :=
              Complex.mul_conj' (a m)
            push_cast
            linear_combination (-(2 * (Real.pi:ℂ) * Complex.I * ((m:ℂ) - 1)) *
              ((ρ:ℂ) ^ 2 * (((ρ:ℂ)⁻¹) ^ 2) ^ m)) * hmc
    rw [tsum_congr hperm]
    have hfs : HasSum (fun m => -(2 * Real.pi * Complex.I) * ((u m : ℝ) : ℂ))
        (-(2 * Real.pi * Complex.I) * ((US : ℝ) : ℂ)) := by
      have h1 := (husum.hasSum).mapL Complex.ofRealCLM
      have h2 : ∀ x : ℝ, Complex.ofRealCLM x = (x:ℂ) := fun _ => rfl
      simp only [h2] at h1
      rw [← hUSdef] at h1
      exact h1.mul_left _
    exact hfs.tsum_eq
  -- ## Identification of the circle integral with the inner `θ`-integral.
  have hIoc : ∀ z : ℂ, (∫ θ in Set.Ioc 0 (2 * Real.pi), G z θ) =
      ∮ w in C(0, ρ), deriv T w * (T w - z)⁻¹ := by
    intro z
    rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le]
    simp only [circleIntegral, deriv_circleMap, smul_eq_mul, hGdef]
  -- ## Fubini: the double integral evaluates via the kernel identity.
  have hswap := MeasureTheory.integral_integral_swap hGint
  have hinner : ∀ θ : ℝ, (∫ z in Metric.ball (0:ℂ) M, G z θ) =
      (Real.pi : ℂ) * ((starRingEnd ℂ) (T (circleMap 0 ρ θ)) *
        (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))) := by
    intro θ
    have h1 : (∫ z in Metric.ball (0:ℂ) M, G z θ) =
        (circleMap 0 ρ θ * Complex.I * deriv T (circleMap 0 ρ θ)) *
          ∫ z in Metric.ball (0:ℂ) M, (T (circleMap 0 ρ θ) - z)⁻¹ :=
      calc (∫ z in Metric.ball (0:ℂ) M, G z θ)
          = ∫ z in Metric.ball (0:ℂ) M, (circleMap 0 ρ θ * Complex.I *
              deriv T (circleMap 0 ρ θ)) * (T (circleMap 0 ρ θ) - z)⁻¹ := by
            refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
            rw [hGdef]; ring
        _ = _ := integral_const_mul _ _
    rw [h1, integral_ball_inv_sub_eq_pi_mul_conj (hTcircM θ)]
    ring
  have hJval : (∫ z in Metric.ball (0:ℂ) M, ∫ θ in Set.Ioc 0 (2 * Real.pi), G z θ) =
      (Real.pi : ℂ) * (-(2 * Real.pi * Complex.I) * ((US : ℝ) : ℂ)) := by
    rw [hswap]
    have h1 : ∀ θ ∈ Set.Ioc (0:ℝ) (2 * Real.pi), (∫ z in Metric.ball (0:ℂ) M, G z θ) =
        (Real.pi : ℂ) * ((starRingEnd ℂ) (T (circleMap 0 ρ θ)) *
          (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))) := fun θ _ => hinner θ
    calc (∫ θ in Set.Ioc 0 (2 * Real.pi), ∫ z in Metric.ball (0:ℂ) M, G z θ)
        = ∫ θ in Set.Ioc 0 (2 * Real.pi), (Real.pi : ℂ) *
            ((starRingEnd ℂ) (T (circleMap 0 ρ θ)) *
              (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))) :=
          setIntegral_congr_fun measurableSet_Ioc h1
      _ = (Real.pi : ℂ) * ∫ θ in Set.Ioc 0 (2 * Real.pi),
            (starRingEnd ℂ) (T (circleMap 0 ρ θ)) *
              (deriv T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)) :=
          integral_const_mul _ _
      _ = (Real.pi : ℂ) * (-(2 * Real.pi * Complex.I) * ((US : ℝ) : ℂ)) := by
          rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le, hKpar]
  -- ## The a.e. dichotomy on the ball.
  have haeN : ∀ᵐ z ∂(volume.restrict (Metric.ball (0:ℂ) M)),
      z ∉ T '' Metric.sphere (0:ℂ) ρ := by
    refine Filter.Eventually.filter_mono (MeasureTheory.ae_mono Measure.restrict_le_self) ?_
    exact (MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hNnull)
  have hae : ∀ᵐ z ∂(volume.restrict (Metric.ball (0:ℂ) M)),
      (∫ θ in Set.Ioc 0 (2 * Real.pi), G z θ) = 0 ∨
      (∫ θ in Set.Ioc 0 (2 * Real.pi), G z θ) = 2 * Real.pi * Complex.I := by
    filter_upwards [haeN, ae_restrict_mem measurableSet_ball] with z hzN hzB
    rw [hIoc z]
    by_cases himg : z ∈ T '' {w : ℂ | ρ < ‖w‖}
    · exact Or.inl (hcaseA z hzN himg)
    · refine Or.inr (hcaseB z ?_ hzN himg)
      rwa [Metric.mem_ball, dist_zero_right] at hzB
  -- ## Positivity of the real part.
  have h2πI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hφint : Integrable (fun z => ∫ θ in Set.Ioc 0 (2 * Real.pi), G z θ)
      (volume.restrict (Metric.ball (0:ℂ) M)) := hGint.integral_prod_left
  have hre : 0 ≤ (((2 * Real.pi * Complex.I))⁻¹ *
      ∫ z in Metric.ball (0:ℂ) M, ∫ θ in Set.Ioc 0 (2 * Real.pi), G z θ).re := by
    have hint2 : Integrable (fun z => (2 * Real.pi * Complex.I)⁻¹ *
        ∫ θ in Set.Ioc 0 (2 * Real.pi), G z θ)
        (volume.restrict (Metric.ball (0:ℂ) M)) := hφint.const_mul _
    have hcomm := Complex.reCLM.integral_comp_comm hint2
    have hnn : 0 ≤ ∫ z in Metric.ball (0:ℂ) M, Complex.reCLM
        ((2 * Real.pi * Complex.I)⁻¹ * ∫ θ in Set.Ioc 0 (2 * Real.pi), G z θ) := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [hae] with z hz
      rcases hz with hz | hz
      · rw [hz]; simp
      · rw [hz, inv_mul_cancel₀ h2πI]; simp
    calc (0:ℝ) ≤ ∫ z in Metric.ball (0:ℂ) M, Complex.reCLM
          ((2 * Real.pi * Complex.I)⁻¹ * ∫ θ in Set.Ioc 0 (2 * Real.pi), G z θ) := hnn
      _ = Complex.reCLM ((2 * Real.pi * Complex.I)⁻¹ *
            ∫ z in Metric.ball (0:ℂ) M, ∫ θ in Set.Ioc 0 (2 * Real.pi), G z θ) := by
          rw [hcomm]
          exact congrArg Complex.reCLM (integral_const_mul _ _)
      _ = _ := rfl
  -- ## Conclusion: `US ≤ 0`.
  have hUSle : US ≤ 0 := by
    have hval : (((2 * Real.pi * Complex.I))⁻¹ *
        ∫ z in Metric.ball (0:ℂ) M, ∫ θ in Set.Ioc 0 (2 * Real.pi), G z θ).re =
        -(Real.pi * US) := by
      rw [hJval]
      have heq : (2 * Real.pi * Complex.I)⁻¹ *
          ((Real.pi : ℂ) * (-(2 * Real.pi * Complex.I) * ((US : ℝ) : ℂ))) =
          -((Real.pi * US : ℝ) : ℂ) := by
        push_cast
        field_simp
      rw [heq]
      simp
    rw [hval] at hre
    have h1 : Real.pi * US ≤ 0 := by linarith
    by_contra hcon
    push Not at hcon
    nlinarith [Real.pi_pos]
  -- ## Extract the `m = 2` term.
  have hu0 : u 0 = -(ρ ^ 2) := by
    simp only [hudef]
    norm_num [ha0]
  have hu1 : u 1 = 0 := by
    simp only [hudef]
    norm_num
  have husum1 : Summable fun k => u (k + 1) := (summable_nat_add_iff 1).mpr husum
  have husum2 : Summable fun k => u (k + 2) := (summable_nat_add_iff 2).mpr husum
  have hsplit : US = u 0 + (u 1 + ∑' k, u (k + 2)) := by
    have e1 := husum.tsum_eq_zero_add
    have e2 := husum1.tsum_eq_zero_add
    rw [hUSdef, e1, e2]
  have hunn : ∀ j : ℕ, 0 ≤ u (j + 2) := by
    intro j
    simp only [hudef]
    have h1 : ((j + 2 : ℕ) : ℝ) - 1 = (j : ℝ) + 1 := by push_cast; ring
    rw [h1]
    positivity
  have hterm : u 2 ≤ ∑' k, u (k + 2) := by
    have := husum2.le_tsum 0 fun j hj => hunn j
    simpa using this
  have hu2v : u 2 = ‖a 2‖ ^ 2 * (ρ ^ 2 * ((ρ⁻¹) ^ 2) ^ 2) := by
    rw [hudef]; push_cast; ring
  have ha2sq : ‖a 2‖ ^ 2 ≤ ρ ^ 4 := by
    have h1 : u 2 ≤ ρ ^ 2 := by linarith [hterm, hUSle, hu0, hu1, hsplit.ge, hsplit.le]
    rw [hu2v] at h1
    have h2 : ρ ^ 2 * ((ρ⁻¹) ^ 2) ^ 2 = (ρ ^ 2)⁻¹ := by
      field_simp
    rw [h2] at h1
    have h3 : (0:ℝ) < ρ ^ 2 := by positivity
    have h4 : ‖a 2‖ ^ 2 * (ρ ^ 2)⁻¹ * ρ ^ 2 ≤ ρ ^ 2 * ρ ^ 2 :=
      mul_le_mul_of_nonneg_right h1 h3.le
    rw [mul_assoc, inv_mul_cancel₀ h3.ne', mul_one] at h4
    calc ‖a 2‖ ^ 2 ≤ ρ ^ 2 * ρ ^ 2 := h4
      _ = ρ ^ 4 := by ring
  have ha2 : ‖a 2‖ ≤ ρ ^ 2 := by
    have h1 : ‖a 2‖ = Real.sqrt (‖a 2‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    have h2 : Real.sqrt (ρ ^ 4) = ρ ^ 2 := by
      rw [show ρ ^ 4 = (ρ ^ 2) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    rw [h1, ← h2]
    exact Real.sqrt_le_sqrt ha2sq
  -- ## The coefficient is half the second derivative.
  have hiter : iteratedDeriv 2 s 0 = 2 * a 2 := by
    have h1 := hps.factorial_smul (1:ℂ) 2
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, one_pow, one_smul] at h1
    have h2 : iteratedDeriv 2 s 0 = iteratedFDeriv ℂ 2 s 0 fun _ => 1 := rfl
    rw [h2, ← h1, hadef]
    simp [Nat.factorial, nsmul_eq_mul]
  rw [hiter, norm_mul]
  have : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [this]
  linarith [ha2]

end RiemannDynamics

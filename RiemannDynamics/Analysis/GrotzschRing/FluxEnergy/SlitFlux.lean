/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.GrotzschRing.FluxEnergy.BankRegularity

/-!
# Slit-chart flux and energy for the Grötzsch potential

The Grötzsch potential `v` is harmonic only off the slit `[0, s]`, so the full-circle identities of
`FluxEnergy.Basic` (`ringFlux`, `dirichletEnergy_roundAnnulus_eq_ringFlux_sub`) are unavailable
below the slit tip.  This file works in the slit chart instead: the geometric angle `θ` runs over
`(0, 2π)`, and for `ξ₂ ≤ log s` the log-polar rectangle `openSlitBox ξ₁ ξ₂` is carried into the
ring by `exp`.  Truncating the angle window to `[a, b] ⊆ (0, 2π)` keeps the flux away from the two
slit banks and makes it differentiable in the log-radius `ξ`; the bank bounds of
`FluxEnergy.BankRegularity` (`exists_bound_gradC_annulus`, `exists_bound_on_stripBox`) then let the
window be opened back up to the full circle.  The limit identifies the increment of `ringFluxSlit`
with the Dirichlet energy of a round sub-annulus, and shows that flux is nondecreasing in `ξ`.

## Main definitions

* `RiemannDynamics.openSlitBox` — the open log-polar rectangle
  `{w | ξ₁ < Re w ∧ Re w < ξ₂ ∧ 0 < Im w ∧ Im w < 2π}`: the slit-adapted chart, whose angle is
  measured from the positive real axis rather than from `−π`.
* `RiemannDynamics.truncFlux` — the truncated slit flux `truncFlux v a b ξ`, the integral over the
  angle window `θ ∈ (a, b)` of `v (e^{ξ+θi}) * Re (expGrad v (ξ+θi))`.
* `RiemannDynamics.sliceEnergy` — the single-circle energy density `sliceEnergy v ξ`, the integral
  of `‖expGrad v (ξ+θi)‖²` over the whole angle range `θ ∈ (0, 2π)`.

## Main results

* `RiemannDynamics.exp_mem_grotzschRing_slitBox` — for `0 < s < 1`, a log-radius `ξ < log s` and a
  geometric angle `θ` with `0 < θ < 2π`, the point `e^{ξ+θi}` lies in `grotzschRing s`.  Both angle
  bounds are load-bearing: at `θ = 0` and at `θ = 2π` the point falls on the closed slit.
* `RiemannDynamics.hasDerivAt_truncFlux` — for `0 < s < 1`, `v` harmonic on a neighbourhood of
  `grotzschRing s` and continuous on its closure, a log-radius with `e^ξ < s` and `ξ < 0`, and a
  window `0 < a ≤ b < 2π`, the map `ξ ↦ truncFlux v a b ξ` is differentiable, with derivative the
  boundary term `v * Im (expGrad v)` at `b` minus at `a`, plus `∫_{(a,b)} ‖expGrad v‖²`; this
  value is packaged as `RiemannDynamics.truncFluxDeriv`.
* `RiemannDynamics.ringFluxSlit_eq` — for every `v` and `ξ`, with no harmonicity or boundary
  hypothesis, `ringFluxSlit v ξ` is the integral of `v (e^{ξ+θi}) * Re (expGrad v (ξ+θi))` over
  `θ ∈ (0, 2π)`; this is the bridge from the `fderiv` form of the definition to `expGrad`.
* `RiemannDynamics.ringFluxSlit_sub_eq_integral` — for `0 < s < 1` and `v` harmonic on a
  neighbourhood of `grotzschRing s`, continuous on its closure, `0` on `grotzschInner s`, `1` on
  `grotzschOuter` and valued in `[0, 1]` on the ring, and for `ξ₁ ≤ ξ₂` with `e^{ξ₂} < s`, the
  increment `ringFluxSlit v ξ₂ − ringFluxSlit v ξ₁` equals `∫ ξ in ξ₁..ξ₂, sliceEnergy v ξ`.
* `RiemannDynamics.dirichletEnergy_roundAnnulus_eq_ringFluxSlit_sub` — under exactly those
  hypotheses, the Dirichlet energy of `v` over `RoundAnnulus 0 (e^{ξ₁}) (e^{ξ₂})` equals
  `ENNReal.ofReal (ringFluxSlit v ξ₂ − ringFluxSlit v ξ₁)`.  That annulus meets the slit, so the
  full-circle identity of `FluxEnergy.Basic` does not cover it.
* `RiemannDynamics.ringFluxSlit_monotoneOn` — for `0 < s < 1` and the same five hypotheses on `v`
  (harmonic, continuous up to the closure, `0` inside, `1` outside, valued in `[0, 1]`), but with
  no relation imposed between two log-radii, `ringFluxSlit v` is nondecreasing on `Iio (log s)`.
-/

open MeasureTheory Set ENNReal Filter Topology Complex

open scoped Real ENNReal

noncomputable section

namespace RiemannDynamics

/-! ### The exponential image of the slit box lies in the Grötzsch ring -/

/-- For `ξ < log s` and geometric angle `θ ∈ (0, 2π)`, the point `e^{ξ+θi}` avoids the slit and
lies in the Grötzsch ring: its modulus `e^ξ` is below `s < 1`, and off the endpoints `θ = 0, 2π`
the point is not on the closed slit (positive real axis segment). -/
theorem exp_mem_grotzschRing_slitBox {s ξ θ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ : ξ < Real.log s) (hθ0 : 0 < θ) (hθ2 : θ < 2 * π) :
    Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s := by
  have hnorm : ‖Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)‖ = Real.exp ξ := by
    rw [Complex.norm_exp, re_logPolar]
  have hlt1 : Real.exp ξ < 1 := by
    calc Real.exp ξ < Real.exp (Real.log s) := Real.exp_lt_exp.mpr hξ
      _ = s := Real.exp_log hs0
      _ < 1 := hs1
  have hlts : Real.exp ξ < s := by
    calc Real.exp ξ < Real.exp (Real.log s) := Real.exp_lt_exp.mpr hξ
      _ = s := Real.exp_log hs0
  refine ⟨mem_ball_zero_iff.mpr (by rw [hnorm]; exact hlt1), fun hslit => ?_⟩
  have hslit' : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschInner s := hslit
  rw [grotzschInner_eq hs0.le] at hslit'
  obtain ⟨him, hre0, _⟩ := hslit'
  -- the imaginary part is `e^ξ sin θ`; it vanishes only at `θ = π`, where the real part is negative
  have himval : (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im = Real.exp ξ * Real.sin θ := by
    rw [Complex.exp_im, re_logPolar, im_logPolar]
  have hreval : (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re = Real.exp ξ * Real.cos θ := by
    rw [Complex.exp_re, re_logPolar, im_logPolar]
  rw [himval] at him
  have hsin0 : Real.sin θ = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact absurd h (Real.exp_pos ξ).ne'
    · exact h
  -- on `(0, 2π)` the sine vanishes only at `π`, where `cos π = -1`, contradicting `re ≥ 0`
  rcases lt_trichotomy θ π with hθπ | hθπ | hθπ
  · exact absurd hsin0 (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ).ne'
  · rw [hreval, hθπ, Real.cos_pi] at hre0
    nlinarith [Real.exp_pos ξ]
  · have hsinneg : Real.sin θ < 0 := by
      have := Real.sin_pos_of_pos_of_lt_pi (x := θ - π) (by linarith) (by linarith)
      rw [Real.sin_sub_pi] at this
      linarith
    exact absurd hsin0 hsinneg.ne

/-- The **open slit box** `{ξ₁ < Re w < ξ₂, 0 < Im w < 2π}` of log-polar parameters. -/
def openSlitBox (ξ₁ ξ₂ : ℝ) : Set ℂ :=
  {w : ℂ | ξ₁ < w.re ∧ w.re < ξ₂ ∧ 0 < w.im ∧ w.im < 2 * π}

/-- The open slit box `openSlitBox ξ₁ ξ₂`, i.e. the open rectangle `(ξ₁, ξ₂) × (0, 2π)` in `ℂ`,
is an open set. -/
theorem isOpen_openSlitBox (ξ₁ ξ₂ : ℝ) : IsOpen (openSlitBox ξ₁ ξ₂) := by
  have h1 : IsOpen {w : ℂ | ξ₁ < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {w : ℂ | w.re < ξ₂} := isOpen_lt Complex.continuous_re continuous_const
  have h3 : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have h4 : IsOpen {w : ℂ | w.im < 2 * π} := isOpen_lt Complex.continuous_im continuous_const
  have : openSlitBox ξ₁ ξ₂ = {w : ℂ | ξ₁ < w.re} ∩ {w : ℂ | w.re < ξ₂}
      ∩ {w : ℂ | 0 < w.im} ∩ {w : ℂ | w.im < 2 * π} := by
    ext w; simp only [openSlitBox, Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
  rw [this]
  exact ((h1.inter h2).inter h3).inter h4

/-- **Holomorphy of the log-polar gradient on the slit box.** For the Grötzsch potential `v`
(harmonic on the ring), `expGrad v` is complex-differentiable at every point of the open slit box
whose log-radius is below `log s`. -/
theorem expGrad_differentiableAt_slitBox {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) {w : ℂ}
    (h1 : w.re < Real.log s) (h2 : 0 < w.im) (h3 : w.im < 2 * π) :
    DifferentiableAt ℂ (expGrad v) w := by
  have hw : w = ((w.re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hmem : Complex.exp w ∈ grotzschRing s := by
    rw [hw]
    exact exp_mem_grotzschRing_slitBox hs0 hs1 h1 h2 h3
  have hg : DifferentiableAt ℂ (gradC v) (Complex.exp w) :=
    (gradC_differentiableOn hvh).differentiableAt
      ((isOpen_grotzschRing hs0.le).mem_nhds hmem)
  exact ((hg.comp w (Complex.differentiable_exp w)).mul (Complex.differentiable_exp w))

/-- `expGrad v` is continuous on the open slit box. -/
theorem continuousOn_expGrad_slitBox {s ξ₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) (hξ₂ : ξ₂ ≤ Real.log s)
    {ξ₁ : ℝ} :
    ContinuousOn (expGrad v) (openSlitBox ξ₁ ξ₂) := fun _w hw =>
  (expGrad_differentiableAt_slitBox hs0 hs1 hvh (lt_of_lt_of_le hw.2.1 hξ₂) hw.2.2.1
    hw.2.2.2).continuousAt.continuousWithinAt

/-- The derivative of `expGrad v` is continuous on the open slit box. -/
theorem continuousOn_deriv_expGrad_slitBox {s ξ₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) (hξ₂ : ξ₂ ≤ Real.log s)
    {ξ₁ : ℝ} :
    ContinuousOn (deriv (expGrad v)) (openSlitBox ξ₁ ξ₂) := by
  have hdiff : DifferentiableOn ℂ (expGrad v) (openSlitBox ξ₁ ξ₂) := fun w hw =>
    (expGrad_differentiableAt_slitBox hs0 hs1 hvh (lt_of_lt_of_le hw.2.1 hξ₂) hw.2.2.1
      hw.2.2.2).differentiableWithinAt
  have hanalytic := hdiff.analyticOnNhd (isOpen_openSlitBox _ _)
  exact (hanalytic.deriv_of_isOpen (isOpen_openSlitBox _ _)).continuousOn

/-- **Off-axis bound for `expGrad v` on the slit box.** For log-radii in `[ξ₁, ξ₂]` with
`e^{ξ₂} < s` and any angle `θ` whose point is off the real axis, `‖expGrad v (ξ+θi)‖` is bounded
by a single constant: the modulus factor `e^ξ` is bounded on `[ξ₁, ξ₂]` and `‖gradC v‖` is bounded
off the axis on the closed annulus. -/
theorem exists_bound_expGrad_slitBox {s ξ₁ ξ₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ₂ : Real.exp ξ₂ < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1) :
    ∃ C : ℝ, ∀ ξ ∈ Icc ξ₁ ξ₂, ∀ θ : ℝ, Real.sin θ ≠ 0 →
      ‖expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨Cg, hCg⟩ := exists_bound_gradC_annulus (r₁ := Real.exp ξ₁) (r₂ := Real.exp ξ₂)
    hs0 hs1 (Real.exp_pos ξ₁) hξ₂ hvh hvc hv0 hv1
  refine ⟨Real.exp ξ₂ * max Cg 0, fun ξ hξ θ hθ => ?_⟩
  set z : ℂ := Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) with hz
  have hznorm : ‖z‖ = Real.exp ξ := by rw [hz, Complex.norm_exp, re_logPolar]
  have hzim : z.im ≠ 0 := by
    rw [hz, Complex.exp_im, re_logPolar, im_logPolar]
    exact mul_ne_zero (Real.exp_pos ξ).ne' hθ
  have hr1 : Real.exp ξ₁ ≤ ‖z‖ := by rw [hznorm]; exact Real.exp_le_exp.mpr hξ.1
  have hr2 : ‖z‖ ≤ Real.exp ξ₂ := by rw [hznorm]; exact Real.exp_le_exp.mpr hξ.2
  have hgbound : ‖gradC v z‖ ≤ max Cg 0 := le_trans (hCg z hr1 hr2 hzim) (le_max_left _ _)
  have heq : expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I) = gradC v z * z := rfl
  rw [heq, norm_mul, hznorm]
  calc ‖gradC v z‖ * Real.exp ξ ≤ (max Cg 0) * Real.exp ξ₂ := by
        apply mul_le_mul hgbound (Real.exp_le_exp.mpr hξ.2) (Real.exp_pos ξ).le
          (le_max_right _ _)
    _ = Real.exp ξ₂ * max Cg 0 := by ring

/-- The pullback `w ↦ v(e^w)` is continuous on the left half-plane `{Re w < 0}` when `v` is
continuous on the closed unit disk: the exponential maps that half-plane into the open disk. -/
theorem continuous_slice_uexp_of_continuousOn_closedBall {v : ℂ → ℝ}
    (hvc : ContinuousOn v (Metric.closedBall (0 : ℂ) 1)) {ξ : ℝ} (hξ : ξ < 0) :
    Continuous fun θ : ℝ => v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro θ
  have hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp, re_logPolar]
    exact le_of_lt (by calc Real.exp ξ < Real.exp 0 := Real.exp_lt_exp.mpr hξ
      _ = 1 := Real.exp_zero)
  have hmemint : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp, re_logPolar]
    exact by calc Real.exp ξ < Real.exp 0 := Real.exp_lt_exp.mpr hξ
      _ = 1 := Real.exp_zero
  have hnb : Metric.closedBall (0 : ℂ) 1
      ∈ 𝓝 (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hmemint) Metric.ball_subset_closedBall
  have hcv : ContinuousAt v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := hvc.continuousAt hnb
  have hg : ContinuousAt (fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by
    fun_prop
  exact ContinuousAt.comp hcv hg

/-! ### The slit-chart flux derivative via limiting integration by parts -/

/-- The log-polar point `ξ + θ·I` lies in the open slit box `{ξ₁ < Re < ξ₂, 0 < Im < 2π}` for
`ξ₁ < ξ < ξ₂` and `θ ∈ (0, 2π)`. -/
theorem logPolar_mem_openSlitBox {ξ₁ ξ₂ ξ θ : ℝ} (h1 : ξ₁ < ξ) (h2 : ξ < ξ₂)
    (hθ1 : 0 < θ) (hθ2 : θ < 2 * π) :
    ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ openSlitBox ξ₁ ξ₂ := by
  simp only [openSlitBox, Set.mem_ofPred_eq, re_logPolar, im_logPolar]
  exact ⟨h1, h2, hθ1, hθ2⟩

/-- A horizontal slice `θ ↦ F(ξ+θi)` over `(0, 2π)` of a function continuous on the open slit
box is continuous there. -/
theorem continuousOn_slice_of_continuousOn_openSlitBox {F : ℂ → ℝ} {ξ₁ ξ₂ : ℝ}
    (hF : ContinuousOn F (openSlitBox ξ₁ ξ₂)) {ξ : ℝ} (h1 : ξ₁ < ξ) (h2 : ξ < ξ₂) :
    ContinuousOn (fun θ : ℝ => F ((ξ : ℂ) + (θ : ℂ) * Complex.I)) (Ioo 0 (2 * π)) := by
  intro θ hθ
  refine ContinuousAt.continuousWithinAt (ContinuousAt.comp ?_ (by fun_prop))
  exact hF.continuousAt ((isOpen_openSlitBox _ _).mem_nhds
    (logPolar_mem_openSlitBox h1 h2 hθ.1 hθ.2))

/-- The endpoint offsets `π/(n+2)` tend to `0`. -/
theorem tendsto_piDivShrink : Tendsto (fun n : ℕ => π / ((n : ℝ) + 2)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have hc : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have := hc.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]; push_cast; ring_nf
  have hmul : Tendsto (fun n : ℕ => π * ((1 : ℝ) / ((n : ℝ) + 2))) atTop (𝓝 (π * 0)) :=
    h.const_mul π
  rw [mul_zero] at hmul
  refine hmul.congr fun n => ?_
  rw [mul_one_div]

/-- **Endpoint-shrinking limit of the full-circle integral.** For a bounded measurable integrand
`f` on `(0, 2π)`, the integral over the shrunk interval `(π/(n+2), 2π − π/(n+2))` tends to the
integral over `(0, 2π)`: dominated convergence with the constant bound on the finite measure
`(0, 2π)`. -/
theorem tendsto_setIntegral_slitShrink {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Ioo 0 (2 * π))))
    (hbound : ∀ᵐ θ ∂(volume.restrict (Ioo 0 (2 * π))), ‖f θ‖ ≤ M) :
    Tendsto (fun n : ℕ => ∫ θ in Ioo (π / ((n : ℝ) + 2)) (2 * π - π / ((n : ℝ) + 2)), f θ)
      atTop (𝓝 (∫ θ in Ioo 0 (2 * π), f θ)) := by
  have hπ := Real.pi_pos
  set aₙ : ℕ → ℝ := fun n => π / ((n : ℝ) + 2) with haₙ
  have hsub : ∀ n : ℕ, Ioo (aₙ n) (2 * π - aₙ n) ⊆ Ioo 0 (2 * π) := by
    intro n θ hθ
    have hpn : (0 : ℝ) < aₙ n := by positivity
    exact ⟨lt_trans hpn hθ.1, lt_of_lt_of_le hθ.2 (by linarith)⟩
  -- rewrite each integral as an integral of the indicator over `(0, 2π)`
  set F : ℕ → ℝ → ℝ := fun n => (Ioo (aₙ n) (2 * π - aₙ n)).indicator f with hF
  have hFint : ∀ n : ℕ,
      (∫ θ in Ioo (aₙ n) (2 * π - aₙ n), f θ) = ∫ θ in Ioo 0 (2 * π), F n θ := by
    intro n
    rw [hF, setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_self_of_subset_right (hsub n)]
  have hlimeq : (∫ θ in Ioo 0 (2 * π), f θ)
      = ∫ θ in Ioo 0 (2 * π), (Ioo 0 (2 * π)).indicator f θ := by
    rw [setIntegral_indicator measurableSet_Ioo, Set.inter_self]
  rw [hlimeq]
  refine (tendsto_integral_filter_of_norm_le_const (μ := volume.restrict (Ioo 0 (2 * π)))
    ?_ ?_ ?_).congr (fun n => (hFint n).symm)
  · exact Eventually.of_forall fun n =>
      (hmeas.indicator measurableSet_Ioo)
  · refine ⟨M, Eventually.of_forall fun n => ?_⟩
    filter_upwards [hbound] with θ hθb
    simp only [hF]
    by_cases hmem : θ ∈ Ioo (aₙ n) (2 * π - aₙ n)
    · rw [Set.indicator_of_mem hmem]; exact hθb
    · rw [Set.indicator_of_notMem hmem, norm_zero]; exact hM
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => ?_)
    rw [Set.indicator_of_mem hθ]
    -- eventually `θ ∈ Ioo (aₙ n) (2π − aₙ n)`, so `F n θ = f θ`
    have haθ : ∀ᶠ n : ℕ in atTop, aₙ n < min θ (2 * π - θ) := by
      have hminpos : 0 < min θ (2 * π - θ) := lt_min hθ.1 (by linarith [hθ.2])
      exact tendsto_piDivShrink.eventually_lt_const hminpos
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [haθ] with n hn
    have h1 : aₙ n < θ := lt_of_lt_of_le hn (min_le_left _ _)
    have h2 : θ < 2 * π - aₙ n := by
      have := lt_of_lt_of_le hn (min_le_right _ _); linarith
    have hmem : θ ∈ Ioo (aₙ n) (2 * π - aₙ n) := ⟨h1, h2⟩
    simp only [hF, Set.indicator_of_mem hmem]

/-- **Slit-chart angular derivative of the pullback.** For the Grötzsch potential `v` and a
log-radius `ξ < log s`, the pullback `θ ↦ v(e^{ξ+θi})` has angular derivative
`−Im (expGrad v (ξ+θi))` at every geometric angle `θ ∈ (0, 2π)`. -/
theorem hasDerivAt_uexp_angular_slit {s ξ θ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ : ξ < Real.log s) (hθ1 : 0 < θ) (hθ2 : θ < 2 * π) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) :
    HasDerivAt (fun t : ℝ => v (Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)))
      (-(expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im) θ :=
  hasDerivAt_uexp_angular (differentiableAt_of_harmonicOnNhd hvh
    (exp_mem_grotzschRing_slitBox hs0 hs1 hξ hθ1 hθ2))

/-- **Slit-chart angular derivative of `Im (expGrad v)`.** For the Grötzsch potential `v` and a
log-radius `ξ < log s`, the map `θ ↦ Im (expGrad v (ξ+θi))` has angular derivative
`Re (deriv (expGrad v) (ξ+θi))` at every geometric angle `θ ∈ (0, 2π)`. -/
theorem hasDerivAt_im_expGrad_angular_slit {s ξ θ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ : ξ < Real.log s) (hθ1 : 0 < θ) (hθ2 : θ < 2 * π) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) :
    HasDerivAt (fun t : ℝ => (expGrad v ((ξ : ℂ) + (t : ℂ) * Complex.I)).im)
      ((deriv (expGrad v) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) θ := by
  have hD := hasDerivAt_expGrad_angular (u := v) (ξ := ξ) (θ := θ)
    (expGrad_differentiableAt_slitBox hs0 hs1 hvh (by rw [re_logPolar]; exact hξ)
      (by rw [im_logPolar]; exact hθ1) (by rw [im_logPolar]; exact hθ2))
  have hcomp := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hD
  simpa [Function.comp, Complex.mul_im] using! hcomp

/-- **Angular integration by parts on a closed subinterval of the slit chart.** For the Grötzsch
potential `v` and a log-radius `ξ` with `e^ξ < s`, on a closed subinterval `[a, b] ⊆ (0, 2π)` the
angle integral of `v(e^{ξ+θi}) · Re (deriv (expGrad v))` equals the boundary term
`[v · Im (expGrad v)]_a^b` plus the integral of `(Im (expGrad v))²`. -/
theorem integral_uexp_re_deriv_expGrad_slit_Icc {s ξ a b : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξs : Real.exp ξ < s) (hξ0 : ξ < 0) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 2 * π) :
    ∫ θ in a..b, v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (deriv (expGrad v) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re
      = v (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
          * (expGrad v ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
        - v (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
            * (expGrad v ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
        + ∫ θ in a..b, (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
  have hπ := Real.pi_pos
  have hξlog : ξ < Real.log s := (Real.lt_log_iff_exp_lt hs0).mpr hξs
  have hvcball : ContinuousOn v (Metric.closedBall (0 : ℂ) 1) := by
    rwa [← closure_grotzschRing hs0.le]
  -- continuity of the three slice factors on `[a, b]`
  have hcont_f : ContinuousOn (fun θ : ℝ => v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (uIcc a b) :=
    (continuous_slice_uexp_of_continuousOn_closedBall hvcball hξ0).continuousOn
  have hIcc : uIcc a b ⊆ Ioo 0 (2 * π) := by
    rw [uIcc_of_le hab]
    exact fun θ hθ => ⟨lt_of_lt_of_le ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩
  have hcont_g : ContinuousOn (fun θ : ℝ => (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im)
      (uIcc a b) := by
    have hbox : ContinuousOn (fun w : ℂ => (expGrad v w).im) (openSlitBox (ξ - 1) (Real.log s)) :=
      Complex.continuous_im.comp_continuousOn
        (continuousOn_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1))
    exact (continuousOn_slice_of_continuousOn_openSlitBox hbox
      (by linarith : ξ - 1 < ξ) hξlog).mono hIcc
  have hcont_g' : ContinuousOn
      (fun θ : ℝ => (deriv (expGrad v) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (uIcc a b) := by
    have hbox : ContinuousOn (fun w : ℂ => (deriv (expGrad v) w).re)
        (openSlitBox (ξ - 1) (Real.log s)) :=
      Complex.continuous_re.comp_continuousOn
        (continuousOn_deriv_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1))
    exact (continuousOn_slice_of_continuousOn_openSlitBox hbox
      (by linarith : ξ - 1 < ξ) hξlog).mono hIcc
  -- pointwise derivatives on the open interval
  have hf' : ∀ θ ∈ Ioo (min a b) (max a b),
      HasDerivAt (fun t : ℝ => v (Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)))
        (-(expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im) θ := by
    intro θ hθ
    rw [min_eq_left hab, max_eq_right hab] at hθ
    exact hasDerivAt_uexp_angular_slit hs0 hs1 hξlog (lt_trans ha hθ.1)
      (lt_trans hθ.2 hb) hvh
  have hg' : ∀ θ ∈ Ioo (min a b) (max a b),
      HasDerivAt (fun t : ℝ => (expGrad v ((ξ : ℂ) + (t : ℂ) * Complex.I)).im)
        ((deriv (expGrad v) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) θ := by
    intro θ hθ
    rw [min_eq_left hab, max_eq_right hab] at hθ
    exact hasDerivAt_im_expGrad_angular_slit hs0 hs1 hξlog (lt_trans ha hθ.1)
      (lt_trans hθ.2 hb) hvh
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hcont_f hcont_g hf' hg'
    (hcont_g.neg.intervalIntegrable) (hcont_g'.intervalIntegrable)
  have halg : ∫ θ in a..b, (-(expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im)
      * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im
      = - ∫ θ in a..b, (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun θ _ => by ring
  rw [hIBP, halg]
  ring

/-- The pullback `v(e^{ξ+θi})` vanishes at the slit endpoints `θ = 0` and `θ = 2π`: the point
`e^ξ` lies on the slit `[0, s]` when `e^ξ ≤ s`, and `e^{ξ+2πi} = e^ξ`. -/
theorem uexp_slit_endpoint_zero {s ξ : ℝ} (hξs : Real.exp ξ ≤ s) {v : ℂ → ℝ}
    (hv0 : ∀ z : ℂ, z.im = 0 → 0 ≤ z.re → z.re ≤ s → v z = 0) :
    v (Complex.exp ((ξ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) = 0
      ∧ v (Complex.exp ((ξ : ℂ) + ((2 * π : ℝ) : ℂ) * Complex.I)) = 0 := by
  have hexp0 : Complex.exp ((ξ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) = ((Real.exp ξ : ℝ) : ℂ) := by
    rw [show ((ξ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) = (ξ : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
  have hexp2 : Complex.exp ((ξ : ℂ) + ((2 * π : ℝ) : ℂ) * Complex.I)
      = ((Real.exp ξ : ℝ) : ℂ) := by
    rw [show ((ξ : ℂ) + ((2 * π : ℝ) : ℂ) * Complex.I)
        = (ξ : ℂ) + 2 * (π : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one, ← Complex.ofReal_exp]
  have hzero : v ((Real.exp ξ : ℝ) : ℂ) = 0 := by
    refine hv0 _ (by simp) ?_ ?_
    · rw [Complex.ofReal_re]; exact (Real.exp_pos ξ).le
    · rw [Complex.ofReal_re]; exact hξs
  exact ⟨by rw [hexp0, hzero], by rw [hexp2, hzero]⟩

/-! ### Conjugation symmetry of the log-polar gradient and its derivative -/

/-- **Conjugation of the holomorphic gradient.** For a conjugation-invariant potential `v`
(as the Grötzsch potential is), the holomorphic gradient satisfies
`gradC v (z̄) = conj (gradC v z)` at interior points. -/
theorem gradC_conj_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    {z : ℂ} (hz : z ∈ grotzschRing s) :
    gradC v ((starRingEnd ℂ) z) = (starRingEnd ℂ) (gradC v z) := by
  have hconjz : (starRingEnd ℂ) z ∈ grotzschRing s := conj_mem_grotzschRing hs0.le hz
  -- near `z`, `v ∘ conj = v`
  have hnb : (fun w => v ((starRingEnd ℂ) w)) =ᶠ[𝓝 z] v := by
    filter_upwards [(isOpen_grotzschRing hs0.le).mem_nhds hz] with w hw
    exact grotzschPotential_conj hs0 hs1 hvh hvc hv0 hv1 w (subset_closure hw)
  have hdvcz : DifferentiableAt ℝ v ((starRingEnd ℂ) z) :=
    differentiableAt_of_harmonicOnNhd hvh hconjz
  have hconjd : HasFDerivAt (fun w : ℂ => (starRingEnd ℂ) w)
      (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap) z := by
    have := Complex.conjLIE.toContinuousLinearEquiv.hasFDerivAt (x := z)
    refine this.congr_fderiv ?_
    ext w
    simp [Complex.conjLIE_apply]
  have hcomp : HasFDerivAt v
      ((fderiv ℝ v ((starRingEnd ℂ) z)).comp
        (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap)) z :=
    (hdvcz.hasFDerivAt.comp z hconjd).congr_of_eventuallyEq hnb.symm
  have hfeq : fderiv ℝ v z
      = (fderiv ℝ v ((starRingEnd ℂ) z)).comp
          (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap) := hcomp.fderiv
  -- evaluate `gradC` using `fderiv v z = (fderiv v z̄) ∘ conj`
  have hcoe : ∀ x : ℂ, (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap) x
      = (starRingEnd ℂ) x := fun x => by
    simp [Complex.conjLIE_apply]
  have hval1 : (fderiv ℝ v z) 1 = (fderiv ℝ v ((starRingEnd ℂ) z)) 1 := by
    rw [hfeq, ContinuousLinearMap.comp_apply, hcoe, map_one]
  have hvalI : (fderiv ℝ v z) Complex.I = -(fderiv ℝ v ((starRingEnd ℂ) z)) Complex.I := by
    rw [hfeq, ContinuousLinearMap.comp_apply, hcoe, Complex.conj_I, map_neg]
  rw [gradC, gradC, hval1, hvalI]
  simp only [map_sub, map_mul, Complex.conj_I, Complex.ofReal_neg, map_neg,
    Complex.conj_ofReal]
  ring

/-- **Conjugation of the log-polar gradient.** For a conjugation-invariant potential `v`, the
log-polar holomorphic gradient satisfies `expGrad v (w̄) = conj (expGrad v w)` whenever `e^w`
lies in the ring. -/
theorem expGrad_conj_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    {w : ℂ} (hw : Complex.exp w ∈ grotzschRing s) :
    expGrad v ((starRingEnd ℂ) w) = (starRingEnd ℂ) (expGrad v w) := by
  have hexpconj : Complex.exp ((starRingEnd ℂ) w) = (starRingEnd ℂ) (Complex.exp w) := by
    rw [← Complex.exp_conj]
  rw [expGrad, expGrad, hexpconj, gradC_conj_eq hs0 hs1 hvh hvc hv0 hv1 hw, map_mul]

/-- **Holomorphy of the log-polar gradient over the ring.** For the Grötzsch potential `v`,
`expGrad v` is complex-differentiable at every `w` whose exponential lies in the ring. -/
theorem expGrad_differentiableAt_ring {s : ℝ} (hs0 : 0 < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) {w : ℂ}
    (hw : Complex.exp w ∈ grotzschRing s) :
    DifferentiableAt ℂ (expGrad v) w := by
  have hg : DifferentiableAt ℂ (gradC v) (Complex.exp w) :=
    (gradC_differentiableOn hvh).differentiableAt
      ((isOpen_grotzschRing hs0.le).mem_nhds hw)
  exact ((hg.comp w (Complex.differentiable_exp w)).mul (Complex.differentiable_exp w))

/-- **Conjugation of the derivative of the log-polar gradient.** For a conjugation-invariant
potential `v`, the derivative of `expGrad v` satisfies
`deriv (expGrad v) (w̄) = conj (deriv (expGrad v) w)` at points where `e^w` and a neighborhood
lie in the ring. -/
theorem deriv_expGrad_conj_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    {w : ℂ} (hw : Complex.exp w ∈ grotzschRing s) :
    deriv (expGrad v) ((starRingEnd ℂ) w) = (starRingEnd ℂ) (deriv (expGrad v) w) := by
  have hdw : HasDerivAt (expGrad v) (deriv (expGrad v) w) w :=
    (expGrad_differentiableAt_ring hs0 hvh hw).hasDerivAt
  -- `conj ∘ expGrad v ∘ conj` has derivative `conj (deriv (expGrad v) w)` at `conj w`
  have hconj := hdw.conj_conj
  -- near `conj w`, `conj ∘ expGrad v ∘ conj = expGrad v`
  have hopen : IsOpen {x : ℂ | Complex.exp x ∈ grotzschRing s} :=
    (isOpen_grotzschRing hs0.le).preimage Complex.continuous_exp
  have hmemcw : (starRingEnd ℂ) w ∈ {x : ℂ | Complex.exp x ∈ grotzschRing s} := by
    change Complex.exp ((starRingEnd ℂ) w) ∈ grotzschRing s
    rw [Complex.exp_conj]; exact conj_mem_grotzschRing hs0.le hw
  have hnb : (⇑(starRingEnd ℂ) ∘ expGrad v ∘ ⇑(starRingEnd ℂ))
      =ᶠ[𝓝 ((starRingEnd ℂ) w)] expGrad v := by
    filter_upwards [hopen.mem_nhds hmemcw] with x hx
    have hxring : Complex.exp x ∈ grotzschRing s := hx
    -- `expGrad v (conj x) = conj (expGrad v x)`
    have heq := expGrad_conj_eq hs0 hs1 hvh hvc hv0 hv1 hxring
    simp only [Function.comp_apply, heq, Complex.conj_conj]
  have hconj' : HasDerivAt (expGrad v) ((starRingEnd ℂ) (deriv (expGrad v) w))
      ((starRingEnd ℂ) w) := hconj.congr_of_eventuallyEq hnb.symm
  exact hconj'.deriv

/-! ### Continuity of the flux integrand on interior slit boxes -/

/-- Every point of the strip box `{ξ₁ < Re < ξ₂, a ≤ Im ≤ b}` with `ξ₂ ≤ log s`,
`0 < a`, `b < 2π` has its exponential in the Grötzsch ring. -/
theorem stripBox_exp_mem_grotzschRing {s ξ₁ ξ₂ a b : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ₂ : ξ₂ ≤ Real.log s) (ha : 0 < a) (hb : b < 2 * π) {w : ℂ}
    (hw : w ∈ stripBox ξ₁ ξ₂ a b) :
    Complex.exp w ∈ grotzschRing s := by
  obtain ⟨_, hre, him1, him2⟩ := hw
  have hwrepr : w = ((w.re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hwrepr]
  exact exp_mem_grotzschRing_slitBox hs0 hs1 (lt_of_lt_of_le hre hξ₂)
    (lt_of_lt_of_le ha him1) (lt_of_le_of_lt him2 hb)

/-- The pullback `w ↦ v(e^w)` is continuous on any interior slit strip box. -/
theorem continuousOn_uexp_stripBox {s ξ₁ ξ₂ a b : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ₂ : ξ₂ ≤ Real.log s) (ha : 0 < a) (hb : b < 2 * π) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) :
    ContinuousOn (fun w => v (Complex.exp w)) (stripBox ξ₁ ξ₂ a b) := by
  intro w hw
  have hmem := stripBox_exp_mem_grotzschRing hs0 hs1 hξ₂ ha hb hw
  have hc : ContinuousAt v (Complex.exp w) := (hvh _ hmem).1.continuousAt
  exact (hc.comp Complex.continuous_exp.continuousAt).continuousWithinAt

/-- `expGrad v` is continuous on any interior slit strip box. -/
theorem continuousOn_expGrad_stripBox {s ξ₁ ξ₂ a b : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ₂ : ξ₂ ≤ Real.log s) (ha : 0 < a) (hb : b < 2 * π) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) :
    ContinuousOn (expGrad v) (stripBox ξ₁ ξ₂ a b) := fun _w hw =>
  (expGrad_differentiableAt_ring hs0 hvh
    (stripBox_exp_mem_grotzschRing hs0 hs1 hξ₂ ha hb hw)).continuousAt.continuousWithinAt

/-- The derivative of `expGrad v` is continuous on any interior slit strip box. -/
theorem continuousOn_deriv_expGrad_stripBox {s ξ₁ ξ₂ a b : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ₂ : ξ₂ ≤ Real.log s) (ha : 0 < a) (hb : b < 2 * π) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) :
    ContinuousOn (deriv (expGrad v)) (stripBox ξ₁ ξ₂ a b) := by
  intro w hw
  obtain ⟨hre1, hre2, him1, him2⟩ := hw
  have hmemopen : w ∈ openSlitBox ξ₁ (Real.log s) :=
    ⟨hre1, lt_of_lt_of_le hre2 hξ₂, lt_of_lt_of_le ha him1, lt_of_le_of_lt him2 hb⟩
  exact ((continuousOn_deriv_expGrad_slitBox hs0 hs1 hvh (le_refl _)).continuousAt
    ((isOpen_openSlitBox _ _).mem_nhds hmemopen)).continuousWithinAt

/-! ### The truncated slit flux and its derivative -/

/-- The **truncated slit flux** of `v` over the angle window `(a, b)`: the angle integral of
`v(e^{ξ+θi}) · Re (expGrad v (ξ+θi))`. -/
def truncFlux (v : ℂ → ℝ) (a b ξ : ℝ) : ℝ :=
  ∫ θ in Ioo a b, v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
    * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re

/-- **Derivative of the truncated slit flux.** For the Grötzsch potential `v` and a window
`[a, b] ⊆ (0, 2π)`, at a log-radius `ξ < log s`, `ξ < 0`, the truncated flux has derivative the
window integral of `|expGrad v|²`: differentiation under the integral sign gives
`(Re expGrad)² + v · Re (deriv expGrad)`, and the angular integration by parts on the closed
window `[a, b]` converts the second term into the boundary term plus `(Im expGrad)²`. -/
theorem hasDerivAt_truncFlux {s a b ξ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξs : Real.exp ξ < s) (hξ0 : ξ < 0) (ha : 0 < a) (hab : a ≤ b) (hb : b < 2 * π)
    {v : ℂ → ℝ} (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s))) :
    HasDerivAt (truncFlux v a b)
      (v (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
          * (expGrad v ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
        - v (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
            * (expGrad v ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
        + ∫ θ in Ioo a b, Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))) ξ := by
  have hπ := Real.pi_pos
  have hξlog : ξ < Real.log s := (Real.lt_log_iff_exp_lt hs0).mpr hξs
  -- work over the strip box `{ξ − 1 < Re < log s, a ≤ Im ≤ b}`
  set ξ₁ : ℝ := ξ - 1 with hξ₁
  set ξ₂ : ℝ := Real.log s with hξ₂
  have hξ₂le : ξ₂ ≤ Real.log s := le_refl _
  have hGcont : ContinuousOn (fun w => v (Complex.exp w) * (expGrad v w).re)
      (stripBox ξ₁ ξ₂ a b) :=
    (continuousOn_uexp_stripBox hs0 hs1 hξ₂le ha hb hvh).mul
      (Complex.continuous_re.comp_continuousOn
        (continuousOn_expGrad_stripBox hs0 hs1 hξ₂le ha hb hvh))
  have hG'cont : ContinuousOn
      (fun w => (expGrad v w).re ^ 2 + v (Complex.exp w) * (deriv (expGrad v) w).re)
      (stripBox ξ₁ ξ₂ a b) :=
    (((Complex.continuous_re.comp_continuousOn
        (continuousOn_expGrad_stripBox hs0 hs1 hξ₂le ha hb hvh)).pow 2).add
      ((continuousOn_uexp_stripBox hs0 hs1 hξ₂le ha hb hvh).mul
        (Complex.continuous_re.comp_continuousOn
          (continuousOn_deriv_expGrad_stripBox hs0 hs1 hξ₂le ha hb hvh))))
  -- product rule along each radial line
  have hd : ∀ x θ : ℝ, ξ₁ < x → x < ξ₂ → a < θ → θ < b →
      HasDerivAt (fun y : ℝ => v (Complex.exp ((y : ℂ) + (θ : ℂ) * Complex.I))
          * (expGrad v ((y : ℂ) + (θ : ℂ) * Complex.I)).re)
        ((expGrad v ((x : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2
          + v (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))
            * (deriv (expGrad v) ((x : ℂ) + (θ : ℂ) * Complex.I)).re) x := by
    intro x θ hx1 hx2 hθ1 hθ2
    have hmemring : Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s :=
      exp_mem_grotzschRing_slitBox hs0 hs1 hx2 (lt_trans ha hθ1) (lt_trans hθ2 hb)
    have hu' := hasDerivAt_uexp_radial (u := v) (ξ := x) (θ := θ)
      (differentiableAt_of_harmonicOnNhd hvh hmemring)
    have hD := hasDerivAt_expGrad_radial (u := v) (ξ := x) (θ := θ)
      (expGrad_differentiableAt_ring hs0 hvh hmemring)
    have hDre : HasDerivAt (fun y : ℝ => (expGrad v ((y : ℂ) + (θ : ℂ) * Complex.I)).re)
        ((deriv (expGrad v) ((x : ℂ) + (θ : ℂ) * Complex.I)).re) x := by
      have hcomp := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hD
      simpa [Function.comp] using! hcomp
    refine (hu'.mul hDre).congr_deriv ?_
    ring
  have hDUI := hasDerivAt_integral_stripBox hab hGcont hG'cont hd
    (show ξ₁ < ξ by rw [hξ₁]; linarith) hξlog
  -- convert the derivative value via the slit-chart integration by parts
  have hint1 : IntegrableOn
      (fun θ : ℝ => (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2) (Ioo a b) := by
    have hsl := continuousOn_slice_of_continuousOn_openSlitBox
      (Complex.continuous_re.comp_continuousOn
        (continuousOn_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1)))
      (by linarith : ξ - 1 < ξ) hξlog
    exact (((hsl.pow 2).mono (fun θ hθ =>
      ⟨lt_of_lt_of_le ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩)).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self)
  have hint2 : IntegrableOn
      (fun θ : ℝ => v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (deriv (expGrad v) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (Ioo a b) := by
    have hslv := (continuous_slice_uexp_of_continuousOn_closedBall
      (by rwa [← closure_grotzschRing hs0.le] : ContinuousOn v (Metric.closedBall (0 : ℂ) 1))
      hξ0).continuousOn (s := Icc a b)
    have hsld := continuousOn_slice_of_continuousOn_openSlitBox
      (Complex.continuous_re.comp_continuousOn
        (continuousOn_deriv_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1)))
      (by linarith : ξ - 1 < ξ) hξlog
    exact ((hslv.mul ((hsld.mono (fun θ hθ =>
      ⟨lt_of_lt_of_le ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩)))).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self)
  have hint3 : IntegrableOn
      (fun θ : ℝ => (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2) (Ioo a b) := by
    have hsl := continuousOn_slice_of_continuousOn_openSlitBox
      (Complex.continuous_im.comp_continuousOn
        (continuousOn_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1)))
      (by linarith : ξ - 1 < ξ) hξlog
    exact (((hsl.pow 2).mono (fun θ hθ =>
      ⟨lt_of_lt_of_le ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩)).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self)
  have hval : (∫ θ in Ioo a b,
      ((expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2
        + v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
          * (deriv (expGrad v) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re))
      = v (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
          * (expGrad v ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
        - v (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
            * (expGrad v ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
        + ∫ θ in Ioo a b, Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
    rw [integral_add hint1 hint2]
    -- convert the second term via the slit integration by parts (in `Ioo` form)
    have hIBP := integral_uexp_re_deriv_expGrad_slit_Icc hs0 hs1 hξs hξ0 hvh hvc ha hab hb
    have hIBP' : (∫ θ in Ioo a b, v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
          * (deriv (expGrad v) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
        = v (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
            * (expGrad v ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
          - v (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
              * (expGrad v ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
          + ∫ θ in Ioo a b, (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
      rw [integral_Ioo_eq_intervalIntegral hab, hIBP,
        integral_Ioo_eq_intervalIntegral hab]
    rw [hIBP']
    have hnormeq : (∫ θ in Ioo a b, (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2)
          + ∫ θ in Ioo a b, (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2
        = ∫ θ in Ioo a b, Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
      rw [← integral_add hint1 hint3]
      refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
      simp only [Complex.normSq_apply]; ring
    linarith [hnormeq]
  rw [hval] at hDUI
  exact hDUI

/-- The derivative value of the truncated slit flux: the angular boundary term of the integration
by parts plus the window integral of the squared log-polar gradient. -/
def truncFluxDeriv (v : ℂ → ℝ) (a b ξ : ℝ) : ℝ :=
  v (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
      * (expGrad v ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
    - v (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
    + ∫ θ in Ioo a b, Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))

/-- Continuity in the log-radius of the pullback `ξ ↦ v(e^{ξ+θi})` at a ring point. -/
theorem continuousAt_uexp_line {θ ξ : ℝ} {s : ℝ} {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s) :
    ContinuousAt (fun x : ℝ => v (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))) ξ :=
  (hasDerivAt_uexp_radial (differentiableAt_of_harmonicOnNhd hvh hmem)).continuousAt

/-- Continuity in the log-radius of `ξ ↦ expGrad v (ξ+θi)` at a ring point. -/
theorem continuousAt_expGrad_line {s θ ξ : ℝ} (hs0 : 0 < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s) :
    ContinuousAt (fun x : ℝ => expGrad v ((x : ℂ) + (θ : ℂ) * Complex.I)) ξ :=
  (hasDerivAt_expGrad_radial (expGrad_differentiableAt_ring hs0 hvh hmem)).continuousAt

/-- **Continuity of the truncated-flux derivative.** For the Grötzsch potential `v` and a window
`[a, b] ⊆ (0, 2π)`, the derivative value `truncFluxDeriv v a b` is continuous on the half-line
`(−∞, log s)`. -/
theorem continuousOn_truncFluxDeriv {s a b : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 2 * π) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) :
    ContinuousOn (truncFluxDeriv v a b) (Iio (Real.log s)) := by
  have hπ := Real.pi_pos
  -- the boundary factors are continuous in `ξ` (fixed angle in `(0, 2π)`)
  have hbdry : ∀ θ : ℝ, 0 < θ → θ < 2 * π →
      ContinuousOn (fun ξ : ℝ => v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im) (Iio (Real.log s)) := by
    intro θ hθ1 hθ2 ξ hξ
    have hξlt : ξ < Real.log s := hξ
    have hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s :=
      exp_mem_grotzschRing_slitBox hs0 hs1 hξlt hθ1 hθ2
    have hcv := continuousAt_uexp_line hvh hmem
    have hcg : ContinuousAt
        (fun ξ : ℝ => (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im) ξ :=
      Complex.continuous_im.continuousAt.comp (continuousAt_expGrad_line hs0 hvh hmem)
    exact (hcv.mul hcg).continuousWithinAt
  -- the window integral of `normSq` is continuous in `ξ`
  have hint : ContinuousOn (fun ξ : ℝ =>
      ∫ θ in Ioo a b, Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (Iio (Real.log s)) := by
    intro ξ₀ hξ₀
    have hξ₀lt : ξ₀ < Real.log s := hξ₀
    obtain ⟨δ, hδpos, hδsub⟩ := exists_closed_slab (show ξ₀ - 1 < ξ₀ by linarith) hξ₀lt
    have hcont : ContinuousOn (fun w => Complex.normSq (expGrad v w))
        (stripBox (ξ₀ - 1) (Real.log s) a b) :=
      Complex.continuous_normSq.comp_continuousOn
        (continuousOn_expGrad_stripBox hs0 hs1 (le_refl _) ha hb hvh)
    obtain ⟨C, hC⟩ := exists_bound_on_stripBox hcont hδsub
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_of_dominated (bound := fun _ => C)
    · filter_upwards [Iio_mem_nhds hξ₀lt] with ξ hξ
      have hξlt : ξ < Real.log s := hξ
      have hsl := continuousOn_slice_of_continuousOn_openSlitBox
        (Complex.continuous_normSq.comp_continuousOn
          (continuousOn_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1)))
        (show ξ - 1 < ξ by linarith) hξlt
      have hIoosub : Ioo a b ⊆ Ioo 0 (2 * π) :=
        fun θ hθ => ⟨lt_trans ha hθ.1, lt_trans hθ.2 hb⟩
      exact (hsl.mono hIoosub).aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [Metric.ball_mem_nhds ξ₀ hδpos] with ξ hξ
      have hξ' : ξ ∈ Icc (ξ₀ - δ) (ξ₀ + δ) := by
        rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hξ
        exact ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
      refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => ?_)
      exact hC ξ hξ' θ (Ioo_subset_Icc_self hθ)
    · exact integrableOn_const (hs := measure_Ioo_lt_top.ne)
    · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => ?_)
      have hmem : Complex.exp ((ξ₀ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s :=
        exp_mem_grotzschRing_slitBox hs0 hs1 hξ₀lt (lt_trans ha hθ.1) (lt_trans hθ.2 hb)
      exact Complex.continuous_normSq.continuousAt.comp (continuousAt_expGrad_line hs0 hvh hmem)
  exact ((hbdry b (lt_of_lt_of_le ha hab) hb).sub (hbdry a ha (lt_of_le_of_lt hab hb))).add hint

/-- **Fundamental theorem of calculus for the truncated slit flux.** For the Grötzsch potential
`v` and a window `[a, b] ⊆ (0, 2π)`, on the half-line of log-radii below `log s` the increment of
the truncated flux is the integral of its derivative value. -/
theorem truncFlux_sub_eq_integral {s a b ξ₁ ξ₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 2 * π) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (h12 : ξ₁ ≤ ξ₂) (hξ₂ : ξ₂ < 0) (hξ₂s : ξ₂ < Real.log s) :
    truncFlux v a b ξ₂ - truncFlux v a b ξ₁
      = ∫ ξ in ξ₁..ξ₂, truncFluxDeriv v a b ξ := by
  have hsub : Icc ξ₁ ξ₂ ⊆ Iio (Real.log s) := fun x hx => lt_of_le_of_lt hx.2 hξ₂s
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_).symm
  · rw [uIcc_of_le h12] at hx
    have hxlt : x < Real.log s := lt_of_le_of_lt hx.2 hξ₂s
    have hxexp : Real.exp x < s := (Real.lt_log_iff_exp_lt hs0).mp hxlt
    have hx0 : x < 0 := lt_of_le_of_lt hx.2 hξ₂
    have := hasDerivAt_truncFlux hs0 hs1 hxexp hx0 ha hab hb hvh hvc
    exact this
  · exact ((continuousOn_truncFluxDeriv hs0 hs1 ha hab hb hvh).mono
      (by rw [uIcc_of_le h12]; exact hsub)).intervalIntegrable

/-- The slit-chart ring flux in log-polar form: `ringFluxSlit v ξ` is the angle integral
`∫_{(0,2π)} v(e^{ξ+θi}) · Re (expGrad v (ξ+θi))`. -/
theorem ringFluxSlit_eq (v : ℂ → ℝ) (ξ : ℝ) :
    ringFluxSlit v ξ = ∫ θ in Ioo 0 (2 * π),
      v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re := by
  unfold ringFluxSlit
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
  rw [fderiv_eq_re_gradC_mul]
  rfl

/-- `truncFlux v a b ξ` equals `ringFluxSlit v ξ` restricted to the window `(a, b)`. -/
theorem truncFlux_eq_setIntegral (v : ℂ → ℝ) (a b ξ : ℝ) :
    truncFlux v a b ξ = ∫ θ in Ioo a b,
      v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re := rfl

/-- The single-circle energy density `ξ ↦ ∫_{(0,2π)} |expGrad v (ξ+θi)|²`. -/
def sliceEnergy (v : ℂ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ θ in Ioo 0 (2 * π), Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))

/-- **The angle at the shrink endpoint has nonzero sine, eventually.** For `θ ∈ (0, π)`,
`sin θ ≠ 0`. -/
theorem sin_ne_zero_of_mem_Ioo_pi {θ : ℝ} (h1 : 0 < θ) (h2 : θ < π) : Real.sin θ ≠ 0 :=
  (Real.sin_pos_of_pos_of_lt_pi h1 h2).ne'

/-- **A.e. bound for `sin θ ≠ 0` on `(0, 2π)`.** The sine vanishes on `(0, 2π)` only at `θ = π`,
a single point, so `sin θ ≠ 0` holds almost everywhere on the window. -/
theorem ae_sin_ne_zero_Ioo :
    ∀ᵐ θ ∂(volume.restrict (Ioo 0 (2 * π))), Real.sin θ ≠ 0 := by
  have hnull : volume ({π} : Set ℝ) = 0 := by simp
  refine (ae_restrict_iff' measurableSet_Ioo).mpr ?_
  filter_upwards [(measure_eq_zero_iff_ae_notMem.mp hnull)] with θ hθπ hmem
  have hθ : θ ∈ Ioo 0 (2 * π) := hmem
  rcases lt_trichotomy θ π with hlt | heq | hgt
  · exact sin_ne_zero_of_mem_Ioo_pi hθ.1 hlt
  · exact absurd (by rw [heq]; rfl : θ ∈ ({π} : Set ℝ)) hθπ
  · have := Real.sin_pos_of_pos_of_lt_pi (x := θ - π) (by linarith) (by linarith [hθ.2])
    rw [Real.sin_sub_pi] at this
    linarith

/-- **Convergence of the truncated flux to the slit flux.** For the Grötzsch potential `v` with
values in `[0, 1]`, at a log-radius `ξ` with `e^ξ < s`, the truncated flux over the shrinking
windows converges to the slit-chart flux. -/
theorem tendsto_truncFlux_ringFluxSlit {s ξ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξs : Real.exp ξ < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    (hvrange : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1) :
    Tendsto (fun n : ℕ =>
      truncFlux v (π / ((n : ℝ) + 2)) (2 * π - π / ((n : ℝ) + 2)) ξ)
      atTop (𝓝 (ringFluxSlit v ξ)) := by
  have hπ := Real.pi_pos
  obtain ⟨M, hM⟩ := exists_bound_expGrad_slitBox (ξ₁ := ξ) (ξ₂ := ξ) hs0 hs1 hξs hvh hvc hv0 hv1
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _)
    (hM ξ (left_mem_Icc.mpr (le_refl ξ)) (π / 2)
      (sin_ne_zero_of_mem_Ioo_pi (by linarith) (by linarith)))
  rw [ringFluxSlit_eq]
  have hf : (fun θ : ℝ => v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
      * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
      = fun θ : ℝ => v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re := rfl
  -- the integrand is a.e. measurable and bounded on `(0, 2π)`
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
      (volume.restrict (Ioo 0 (2 * π))) := by
    have hslv : ContinuousOn (fun θ : ℝ => v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
        (Ioo 0 (2 * π)) :=
      (continuous_slice_uexp_of_continuousOn_closedBall
        (by rwa [← closure_grotzschRing hs0.le] : ContinuousOn v (Metric.closedBall (0 : ℂ) 1))
        (by linarith [(Real.exp_lt_one_iff.mp (lt_trans hξs hs1))] : ξ < 0)).continuousOn
    have hsl := continuousOn_slice_of_continuousOn_openSlitBox
      (Complex.continuous_re.comp_continuousOn
        (continuousOn_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1)))
      (by linarith : ξ - 1 < ξ) ((Real.lt_log_iff_exp_lt hs0).mpr hξs)
    exact (hslv.mul hsl).aestronglyMeasurable measurableSet_Ioo
  have hbound : ∀ᵐ (θ : ℝ) ∂((volume : Measure ℝ).restrict (Ioo 0 (2 * π))),
      ‖v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re‖ ≤ M := by
    have hmemfilter : ∀ᵐ (θ : ℝ) ∂((volume : Measure ℝ).restrict (Ioo 0 (2 * π))),
        θ ∈ Ioo 0 (2 * π) := (ae_restrict_iff' measurableSet_Ioo).mpr
      (Eventually.of_forall fun θ hθ => hθ)
    filter_upwards [ae_sin_ne_zero_Ioo, hmemfilter] with θ hsin hθ
    have hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s :=
      exp_mem_grotzschRing_slitBox hs0 hs1 ((Real.lt_log_iff_exp_lt hs0).mpr hξs) hθ.1 hθ.2
    have hv1' : |v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [(hvrange _ hmem).1], (hvrange _ hmem).2⟩
    have hre : |(expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re| ≤ M :=
      le_trans (Complex.abs_re_le_norm _) (hM ξ (left_mem_Icc.mpr (le_refl ξ)) θ hsin)
    rw [Real.norm_eq_abs, abs_mul]
    calc |v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))|
          * |(expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re|
        ≤ 1 * M := mul_le_mul hv1' hre (abs_nonneg _) (by norm_num)
      _ = M := one_mul M
  exact tendsto_setIntegral_slitShrink hMnn hmeas hbound

/-- **Pointwise convergence of the truncated-flux derivative to the slice energy.** For the
Grötzsch potential `v`, at a log-radius `ξ` with `e^ξ < s`, the truncated-flux derivative over
the shrinking windows converges to the single-circle energy density: the boundary terms vanish
because the potential vanishes at the slit endpoints while `Im (expGrad v)` stays bounded, and the
window energy converges to the full-circle energy. -/
theorem tendsto_truncFluxDeriv_sliceEnergy {s ξ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξs : Real.exp ξ < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1) :
    Tendsto (fun n : ℕ =>
      truncFluxDeriv v (π / ((n : ℝ) + 2)) (2 * π - π / ((n : ℝ) + 2)) ξ)
      atTop (𝓝 (sliceEnergy v ξ)) := by
  have hπ := Real.pi_pos
  have hξ0 : ξ < 0 := by
    have := Real.exp_lt_one_iff.mp (lt_trans hξs hs1); linarith
  have hξlog : ξ < Real.log s := (Real.lt_log_iff_exp_lt hs0).mpr hξs
  have hv0' : ∀ z : ℂ, z.im = 0 → 0 ≤ z.re → z.re ≤ s → v z = 0 := fun z hzi hz0 hzs =>
    hv0 z (by rw [grotzschInner_eq hs0.le]; exact ⟨hzi, hz0, hzs⟩)
  set aₙ : ℕ → ℝ := fun n => π / ((n : ℝ) + 2) with haₙ
  obtain ⟨M, hM⟩ := exists_bound_expGrad_slitBox (ξ₁ := ξ) (ξ₂ := ξ) hs0 hs1 hξs hvh hvc hv0 hv1
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _)
    (hM ξ (left_mem_Icc.mpr (le_refl ξ)) (π / 2)
      (sin_ne_zero_of_mem_Ioo_pi (by linarith) (by linarith)))
  -- the window energy converges to the full-circle energy
  have hwin : Tendsto (fun n : ℕ =>
      ∫ θ in Ioo (aₙ n) (2 * π - aₙ n),
        Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      atTop (𝓝 (sliceEnergy v ξ)) := by
    have hmeas : AEStronglyMeasurable
        (fun θ : ℝ => Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
        (volume.restrict (Ioo 0 (2 * π))) := by
      have hsl := continuousOn_slice_of_continuousOn_openSlitBox
        (Complex.continuous_normSq.comp_continuousOn
          (continuousOn_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1)))
        (by linarith : ξ - 1 < ξ) hξlog
      exact hsl.aestronglyMeasurable measurableSet_Ioo
    have hbound : ∀ᵐ (θ : ℝ) ∂((volume : Measure ℝ).restrict (Ioo 0 (2 * π))),
        ‖Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))‖ ≤ M ^ 2 := by
      filter_upwards [ae_sin_ne_zero_Ioo] with θ hsin
      have hb := hM ξ (left_mem_Icc.mpr (le_refl ξ)) θ hsin
      rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _),
        Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)), hb, hMnn]
    exact tendsto_setIntegral_slitShrink (by positivity) hmeas hbound
  -- the boundary terms vanish
  obtain ⟨hva0, hvb0⟩ := uexp_slit_endpoint_zero hξs.le hv0'
  have hbdry : Tendsto (fun n : ℕ =>
      v (Complex.exp ((ξ : ℂ) + ((2 * π - aₙ n : ℝ) : ℂ) * Complex.I))
          * (expGrad v ((ξ : ℂ) + ((2 * π - aₙ n : ℝ) : ℂ) * Complex.I)).im
        - v (Complex.exp ((ξ : ℂ) + ((aₙ n : ℝ) : ℂ) * Complex.I))
            * (expGrad v ((ξ : ℂ) + ((aₙ n : ℝ) : ℂ) * Complex.I)).im)
      atTop (𝓝 0) := by
    -- `v(e^{ξ+aₙi}) → 0` and `Im(expGrad)` bounded, so each product → 0
    have hvcont : Continuous fun θ : ℝ => v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) :=
      continuous_slice_uexp_of_continuousOn_closedBall
        (by rwa [← closure_grotzschRing hs0.le]) hξ0
    have haₙ0 : Tendsto aₙ atTop (𝓝 0) := tendsto_piDivShrink
    have hb2π : Tendsto (fun n => 2 * π - aₙ n) atTop (𝓝 (2 * π)) := by
      have := haₙ0.const_sub (2 * π); simpa using this
    -- `v` at the moving endpoints tends to the endpoint values `0`
    have hva : Tendsto (fun n => v (Complex.exp ((ξ : ℂ) + ((aₙ n : ℝ) : ℂ) * Complex.I)))
        atTop (𝓝 0) := by
      have hc := (hvcont.tendsto 0).comp haₙ0
      simp only [Function.comp_def, hva0] at hc
      exact hc
    have hvb : Tendsto (fun n => v (Complex.exp ((ξ : ℂ) + ((2 * π - aₙ n : ℝ) : ℂ) * Complex.I)))
        atTop (𝓝 0) := by
      have hc := (hvcont.tendsto (2 * π)).comp hb2π
      simp only [Function.comp_def, hvb0] at hc
      exact hc
    -- boundedness of `Im (expGrad)` at the moving endpoints
    have hboundedA : ∀ᶠ n : ℕ in atTop,
        ‖(expGrad v ((ξ : ℂ) + ((aₙ n : ℝ) : ℂ) * Complex.I)).im‖ ≤ M := by
      filter_upwards [haₙ0.eventually_lt_const (show (0:ℝ) < π by linarith),
        eventually_gt_atTop 0] with n hlt _
      have hpos : 0 < aₙ n := by positivity
      exact le_trans (Complex.abs_im_le_norm _)
        (hM ξ (left_mem_Icc.mpr (le_refl ξ)) (aₙ n) (sin_ne_zero_of_mem_Ioo_pi hpos hlt))
    have hboundedB : ∀ᶠ n : ℕ in atTop,
        ‖(expGrad v ((ξ : ℂ) + ((2 * π - aₙ n : ℝ) : ℂ) * Complex.I)).im‖ ≤ M := by
      filter_upwards [haₙ0.eventually_lt_const (show (0:ℝ) < π by linarith)] with n hlt
      have hpos : 0 < aₙ n := by positivity
      have hgt : π < 2 * π - aₙ n := by linarith
      have hlt2 : 2 * π - aₙ n < 2 * π := by linarith
      have hsin : Real.sin (2 * π - aₙ n) ≠ 0 := by
        have := Real.sin_pos_of_pos_of_lt_pi (x := 2 * π - aₙ n - π) (by linarith) (by linarith)
        rw [Real.sin_sub_pi] at this; linarith
      exact le_trans (Complex.abs_im_le_norm _)
        (hM ξ (left_mem_Icc.mpr (le_refl ξ)) (2 * π - aₙ n) hsin)
    have hlimz : Tendsto (fun n : ℕ => ‖v (Complex.exp ((ξ : ℂ)
        + ((aₙ n : ℝ) : ℂ) * Complex.I))‖ * M) atTop (𝓝 0) := by
      have := hva.norm.mul_const M; simpa using this
    have hlimzB : Tendsto (fun n : ℕ => ‖v (Complex.exp ((ξ : ℂ)
        + ((2 * π - aₙ n : ℝ) : ℂ) * Complex.I))‖ * M) atTop (𝓝 0) := by
      have := hvb.norm.mul_const M; simpa using this
    have hprodA : Tendsto (fun n => v (Complex.exp ((ξ : ℂ) + ((aₙ n : ℝ) : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + ((aₙ n : ℝ) : ℂ) * Complex.I)).im) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hlimz
      filter_upwards [hboundedA] with n hn
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    have hprodB : Tendsto (fun n => v (Complex.exp ((ξ : ℂ)
        + ((2 * π - aₙ n : ℝ) : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + ((2 * π - aₙ n : ℝ) : ℂ) * Complex.I)).im) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hlimzB
      filter_upwards [hboundedB] with n hn
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    have := hprodB.sub hprodA
    simpa using this
  -- combine: truncFluxDeriv = boundary + window energy
  have hcomb := hbdry.add hwin
  rw [zero_add] at hcomb
  refine hcomb.congr fun n => ?_
  rw [truncFluxDeriv]

/-- **Uniform bound on the truncated-flux derivative.** With the log-polar gradient bound `M` on
the closed slab `[ξ₁, ξ₂]`, and `v` valued in `[0, 1]`, the truncated-flux derivative is bounded
by `2M + 2π·M²` uniformly over the shrinking windows and over `ξ ∈ [ξ₁, ξ₂]`. -/
theorem truncFluxDeriv_norm_le {s ξ₁ ξ₂ a b ξ M : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξlt : ξ < Real.log s) (ha : 0 < a) (hab : a ≤ b) (hb : b < 2 * π) {v : ℂ → ℝ}
    (hvrange : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1)
    (hM : ∀ ξ ∈ Icc ξ₁ ξ₂, ∀ θ : ℝ, Real.sin θ ≠ 0 →
      ‖expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)‖ ≤ M) (hMnn : 0 ≤ M)
    (hξIcc : ξ ∈ Icc ξ₁ ξ₂) (hsa : Real.sin a ≠ 0) (hsb : Real.sin b ≠ 0) :
    ‖truncFluxDeriv v a b ξ‖ ≤ 2 * M + 2 * π * M ^ 2 := by
  have hπ := Real.pi_pos
  -- bound on the boundary factor at an off-axis angle in `(0, 2π)`
  have hbdry : ∀ θ : ℝ, 0 < θ → θ < 2 * π → Real.sin θ ≠ 0 →
      ‖v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im‖ ≤ M := by
    intro θ hθ1 hθ2 hsin
    have hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s :=
      exp_mem_grotzschRing_slitBox hs0 hs1 hξlt hθ1 hθ2
    have hv1' : |v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith [(hvrange _ hmem).1], (hvrange _ hmem).2⟩
    have him : |(expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im| ≤ M :=
      le_trans (Complex.abs_im_le_norm _) (hM ξ hξIcc θ hsin)
    rw [Real.norm_eq_abs, abs_mul]
    calc |v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))|
          * |(expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im|
        ≤ 1 * M := mul_le_mul hv1' him (abs_nonneg _) (by norm_num)
      _ = M := one_mul M
  -- bound on the window energy integral (a.e. away from `θ = π`)
  have hwin : ‖∫ θ in Ioo a b, Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))‖
      ≤ 2 * π * M ^ 2 := by
    have hbd : ∀ᵐ (θ : ℝ) ∂(volume.restrict (Ioo a b)),
        ‖Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))‖ ≤ M ^ 2 := by
      have hsubset : Ioo a b ⊆ Ioo 0 (2 * π) :=
        fun θ hθ => ⟨lt_trans ha hθ.1, lt_trans hθ.2 hb⟩
      have hsub : ∀ᵐ (θ : ℝ) ∂((volume : Measure ℝ).restrict (Ioo a b)), Real.sin θ ≠ 0 :=
        ae_mono (Measure.restrict_mono hsubset (le_refl _)) ae_sin_ne_zero_Ioo
      filter_upwards [hsub] with θ hsin
      have hb2 := hM ξ hξIcc θ hsin
      rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _),
        Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)), hb2, hMnn]
    have hnorm := norm_setIntegral_le_of_norm_le_const_ae (μ := volume) (s := Ioo a b)
      (C := M ^ 2) measure_Ioo_lt_top hbd
    have hvol : (volume : Measure ℝ).real (Ioo a b) ≤ 2 * π := by
      rw [measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]; linarith
    calc ‖∫ θ in Ioo a b, Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))‖
        ≤ M ^ 2 * (volume : Measure ℝ).real (Ioo a b) := hnorm
      _ ≤ M ^ 2 * (2 * π) := mul_le_mul_of_nonneg_left hvol (by positivity)
      _ = 2 * π * M ^ 2 := by ring
  rw [truncFluxDeriv]
  calc ‖_ + _‖ ≤ ‖v (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
          * (expGrad v ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
        - v (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
            * (expGrad v ((ξ : ℂ) + (a : ℂ) * Complex.I)).im‖
      + ‖∫ θ in Ioo a b, Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))‖ :=
        norm_add_le _ _
    _ ≤ (M + M) + 2 * π * M ^ 2 := by
        refine add_le_add (le_trans (norm_sub_le _ _) (add_le_add
          (hbdry b (lt_of_lt_of_le ha hab) hb hsb) (hbdry a ha (lt_of_le_of_lt hab hb) hsa))) hwin
    _ = 2 * M + 2 * π * M ^ 2 := by ring

/-- **Slit flux increment as a slice-energy integral.** For the Grötzsch potential `v` with values
in `[0, 1]`, on the log-radii below `log s` the increment of the slit-chart flux equals the
integral of the single-circle energy density: the truncated-window fundamental theorem of calculus
passes to the limit, the interior integrals converging by bounded convergence with the log-polar
gradient bound. -/
theorem ringFluxSlit_sub_eq_integral {s ξ₁ ξ₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ₂s : Real.exp ξ₂ < s) (h12 : ξ₁ ≤ ξ₂) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    (hvrange : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1) :
    ringFluxSlit v ξ₂ - ringFluxSlit v ξ₁ = ∫ ξ in ξ₁..ξ₂, sliceEnergy v ξ := by
  have hπ := Real.pi_pos
  have hξ₂log : ξ₂ < Real.log s := (Real.lt_log_iff_exp_lt hs0).mpr hξ₂s
  have hξ₂0 : ξ₂ < 0 := by
    have := Real.exp_lt_one_iff.mp (lt_trans hξ₂s hs1); linarith
  set aₙ : ℕ → ℝ := fun n => π / ((n : ℝ) + 2) with haₙ
  have haₙpos : ∀ n, 0 < aₙ n := fun n => by positivity
  have haₙle : ∀ n, aₙ n ≤ 2 * π - aₙ n := by
    intro n
    have h2 : aₙ n ≤ π / 2 := by
      rw [haₙ, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
  have haₙlt : ∀ n, 2 * π - aₙ n < 2 * π := fun n => by linarith [haₙpos n]
  -- slab bound on `expGrad` over `[ξ₁, ξ₂]`
  obtain ⟨M, hM⟩ := exists_bound_expGrad_slitBox (ξ₁ := ξ₁) (ξ₂ := ξ₂) hs0 hs1 hξ₂s hvh hvc hv0 hv1
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _)
    (hM ξ₂ (right_mem_Icc.mpr h12) (π / 2)
      (sin_ne_zero_of_mem_Ioo_pi (by linarith) (by linarith)))
  -- the per-`n` fundamental theorem of calculus
  have hFTC : ∀ n : ℕ, truncFlux v (aₙ n) (2 * π - aₙ n) ξ₂
      - truncFlux v (aₙ n) (2 * π - aₙ n) ξ₁
      = ∫ ξ in ξ₁..ξ₂, truncFluxDeriv v (aₙ n) (2 * π - aₙ n) ξ := fun n =>
    truncFlux_sub_eq_integral hs0 hs1 (haₙpos n) (haₙle n) (haₙlt n) hvh hvc h12 hξ₂0 hξ₂log
  -- LHS converges to the slit-flux increment
  have hLHS : Tendsto (fun n : ℕ => truncFlux v (aₙ n) (2 * π - aₙ n) ξ₂
      - truncFlux v (aₙ n) (2 * π - aₙ n) ξ₁) atTop
      (𝓝 (ringFluxSlit v ξ₂ - ringFluxSlit v ξ₁)) :=
    (tendsto_truncFlux_ringFluxSlit hs0 hs1 hξ₂s hvh hvc hv0 hv1 hvrange).sub
      (tendsto_truncFlux_ringFluxSlit hs0 hs1 (lt_of_le_of_lt (Real.exp_le_exp.mpr h12) hξ₂s)
        hvh hvc hv0 hv1 hvrange)
  -- RHS converges to the slice-energy integral, by bounded convergence over `[ξ₁, ξ₂]`
  -- eventual nonzero-sine of the shrink endpoints (needed for the uniform bound)
  have hsaₙ : ∀ n : ℕ, Real.sin (aₙ n) ≠ 0 := by
    intro n
    have h2 : aₙ n ≤ π / 2 := by
      rw [haₙ, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    exact sin_ne_zero_of_mem_Ioo_pi (haₙpos n) (by linarith)
  have hsbₙ : ∀ n : ℕ, Real.sin (2 * π - aₙ n) ≠ 0 := by
    intro n
    have h2 : aₙ n ≤ π / 2 := by
      rw [haₙ, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have := Real.sin_pos_of_pos_of_lt_pi (x := 2 * π - aₙ n - π)
      (by linarith [haₙpos n]) (by linarith [haₙpos n])
    rw [Real.sin_sub_pi] at this; linarith
  have hRHS : Tendsto (fun n : ℕ => ∫ ξ in ξ₁..ξ₂, truncFluxDeriv v (aₙ n) (2 * π - aₙ n) ξ)
      atTop (𝓝 (∫ ξ in ξ₁..ξ₂, sliceEnergy v ξ)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ => 2 * M + 2 * π * M ^ 2) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      have hmono : Set.uIoc ξ₁ ξ₂ ⊆ Iio (Real.log s) := by
        rw [Set.uIoc_of_le h12]; exact fun ξ hξ => lt_of_le_of_lt hξ.2 hξ₂log
      exact ((continuousOn_truncFluxDeriv hs0 hs1 (haₙpos n) (haₙle n) (haₙlt n) hvh).mono
        hmono).aestronglyMeasurable measurableSet_uIoc
    · refine Eventually.of_forall fun n => Eventually.of_forall fun ξ hξ => ?_
      rw [Set.uIoc_of_le h12] at hξ
      have hξlt : ξ < Real.log s := lt_of_le_of_lt hξ.2 hξ₂log
      have hξIcc : ξ ∈ Icc ξ₁ ξ₂ := ⟨le_of_lt hξ.1, hξ.2⟩
      exact truncFluxDeriv_norm_le hs0 hs1 hξlt (haₙpos n) (haₙle n) (haₙlt n)
        hvrange hM hMnn hξIcc (hsaₙ n) (hsbₙ n)
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun ξ hξ => ?_
      rw [Set.uIoc_of_le h12] at hξ
      have hξs' : Real.exp ξ < s := lt_of_le_of_lt (Real.exp_le_exp.mpr hξ.2) hξ₂s
      exact tendsto_truncFluxDeriv_sliceEnergy hs0 hs1 hξs' hvh hvc hv0 hv1
  have heq := tendsto_nhds_unique
    (by simpa only [hFTC] using hRHS) hLHS
  exact heq.symm

/-- The squared log-polar gradient integrand is `2π`-periodic in the angle. -/
theorem normSq_expGrad_periodic (v : ℂ → ℝ) (ξ : ℝ) :
    Function.Periodic
      (fun θ : ℝ => Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (2 * π) := by
  intro θ
  have hexp : Complex.exp ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
    rw [show ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
        = ((ξ : ℂ) + (θ : ℂ) * Complex.I) + 2 * (π : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_periodic _]
  simp only [expGrad, hexp]

/-- The single-circle energy density in the collar chart: the slice energy over `(0, 2π)` equals
the angle integral of `|expGrad v|²` over `(−π, π)`. -/
theorem sliceEnergy_eq_neg_pi_pi (v : ℂ → ℝ) (ξ : ℝ) :
    sliceEnergy v ξ
      = ∫ θ in Ioo (-π) π, Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
  have hπ := Real.pi_pos
  unfold sliceEnergy
  rw [integral_Ioo_eq_intervalIntegral (by linarith : (0 : ℝ) ≤ 2 * π),
    integral_Ioo_eq_intervalIntegral (by linarith : -π ≤ π)]
  have hkey := (normSq_expGrad_periodic v ξ).intervalIntegral_add_eq 0 (-π)
  have hend : -π + 2 * π = π := by ring
  rw [zero_add, hend] at hkey
  exact hkey

/-- **Continuity of the slice energy on the slit chart.** For the Grötzsch potential `v` with
values in `[0, 1]`, the single-circle energy density `sliceEnergy v` is continuous on
`(−∞, log s)`. -/
theorem continuousOn_sliceEnergy {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1) :
    ContinuousOn (sliceEnergy v) (Iio (Real.log s)) := by
  have hπ := Real.pi_pos
  unfold sliceEnergy
  intro ξ₀ hξ₀
  have hξ₀lt : ξ₀ < Real.log s := hξ₀
  obtain ⟨δ, hδpos, hδsub⟩ := exists_closed_slab (show ξ₀ - 1 < ξ₀ by linarith) hξ₀lt
  -- slab bound on `expGrad` over `[ξ₀ − δ, ξ₀ + δ]`; hence a constant bound `M²` on `normSq`
  have hξ₂mem : ξ₀ + δ ∈ Icc (ξ₀ - δ) (ξ₀ + δ) := ⟨by linarith, le_refl _⟩
  have hξ₂lt : ξ₀ + δ < Real.log s := (hδsub hξ₂mem).2
  have hexpξ₂ : Real.exp (ξ₀ + δ) < s := (Real.lt_log_iff_exp_lt hs0).mp hξ₂lt
  obtain ⟨M, hM⟩ := exists_bound_expGrad_slitBox (ξ₁ := ξ₀ - δ) (ξ₂ := ξ₀ + δ) hs0 hs1
    hexpξ₂ hvh hvc hv0 hv1
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_of_dominated (bound := fun _ => M ^ 2)
  · filter_upwards [Iio_mem_nhds hξ₀lt] with ξ hξ
    have hξlt : ξ < Real.log s := hξ
    have hsl := continuousOn_slice_of_continuousOn_openSlitBox
      (Complex.continuous_normSq.comp_continuousOn
        (continuousOn_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1)))
      (by linarith : ξ - 1 < ξ) hξlt
    exact hsl.aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [Metric.ball_mem_nhds ξ₀ hδpos] with ξ hξ
    have hξ' : ξ ∈ Icc (ξ₀ - δ) (ξ₀ + δ) := by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hξ
      exact ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
    filter_upwards [ae_sin_ne_zero_Ioo] with θ hsin
    have hb := hM ξ hξ' θ hsin
    rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)), hb,
      le_trans (norm_nonneg _) (hM ξ hξ' (π / 2)
        (sin_ne_zero_of_mem_Ioo_pi (by linarith) (by linarith)))]
  · exact integrableOn_const (hs := measure_Ioo_lt_top.ne)
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => ?_)
    have hmem : Complex.exp ((ξ₀ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s :=
      exp_mem_grotzschRing_slitBox hs0 hs1 hξ₀lt hθ.1 hθ.2
    exact Complex.continuous_normSq.continuousAt.comp (continuousAt_expGrad_line hs0 hvh hmem)

/-- Integrability of the squared log-polar gradient slice over `(0, 2π)` at a slit-chart
log-radius `ξ < log s`, from the a.e. constant bound off the axis. -/
theorem integrableOn_normSq_expGrad_slit {s ξ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξs : Real.exp ξ < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1) :
    IntegrableOn (fun θ : ℝ => Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (Ioo 0 (2 * π)) := by
  have hπ := Real.pi_pos
  have hξlog : ξ < Real.log s := (Real.lt_log_iff_exp_lt hs0).mpr hξs
  obtain ⟨M, hM⟩ := exists_bound_expGrad_slitBox (ξ₁ := ξ) (ξ₂ := ξ) hs0 hs1 hξs hvh hvc hv0 hv1
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (volume.restrict (Ioo 0 (2 * π))) := by
    have hsl := continuousOn_slice_of_continuousOn_openSlitBox
      (Complex.continuous_normSq.comp_continuousOn
        (continuousOn_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1)))
      (by linarith : ξ - 1 < ξ) hξlog
    exact hsl.aestronglyMeasurable measurableSet_Ioo
  refine ⟨hmeas, HasFiniteIntegral.restrict_of_bounded (C := M ^ 2) measure_Ioo_lt_top ?_⟩
  filter_upwards [ae_sin_ne_zero_Ioo] with θ hsin
  have hb := hM ξ (left_mem_Icc.mpr (le_refl ξ)) θ hsin
  rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)), hb,
    le_trans (norm_nonneg _) (hM ξ (left_mem_Icc.mpr (le_refl ξ)) (π / 2)
      (sin_ne_zero_of_mem_Ioo_pi (by linarith) (by linarith)))]

/-- **Flux–energy identity on slit sub-annuli.** For the Grötzsch potential `v` and log-radii
`ξ₁ ≤ ξ₂` with `e^{ξ₂} < s`, the Dirichlet energy of `v` over the round sub-annulus
`{e^{ξ₁} < |z| < e^{ξ₂}}` (which lies below the slit tip, so `v` is not harmonic across it) equals
the slit-chart flux increment `ringFluxSlit v ξ₂ − ringFluxSlit v ξ₁`. -/
theorem dirichletEnergy_roundAnnulus_eq_ringFluxSlit_sub {s ξ₁ ξ₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ₂s : Real.exp ξ₂ < s) (h12 : ξ₁ ≤ ξ₂) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    (hvrange : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1) :
    dirichletEnergy v (RoundAnnulus 0 (Real.exp ξ₁) (Real.exp ξ₂))
      = ENNReal.ofReal (ringFluxSlit v ξ₂ - ringFluxSlit v ξ₁) := by
  have hπ := Real.pi_pos
  have hξ₂log : ξ₂ < Real.log s := (Real.lt_log_iff_exp_lt hs0).mpr hξ₂s
  rw [dirichletEnergy_roundAnnulus_eq_lintegral v ξ₁ ξ₂]
  -- inner bridge: the `(0, 2π)` slice energy `ofReal` matches the `(−π, π)` lintegral
  have hinner : ∀ ξ ∈ Ioo ξ₁ ξ₂,
      (∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal (Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
      = ENNReal.ofReal (sliceEnergy v ξ) := by
    intro ξ hξ
    have hξ₂s' : Real.exp ξ < s := lt_of_lt_of_le (Real.exp_lt_exp.mpr hξ.2) hξ₂s.le
    -- the `(−π, π)` and `(0, 2π)` charts give the same real integral
    obtain ⟨M, hM⟩ := exists_bound_expGrad_slitBox (ξ₁ := ξ) (ξ₂ := ξ) hs0 hs1 hξ₂s'
      hvh hvc hv0 hv1
    have hMnn : 0 ≤ M := le_trans (norm_nonneg _)
      (hM ξ (left_mem_Icc.mpr (le_refl ξ)) (π / 2)
        (sin_ne_zero_of_mem_Ioo_pi (by linarith) (by linarith)))
    have hmeasfun : Measurable
        (fun θ : ℝ => Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))) := by
      have h1 : Measurable fun θ : ℝ => Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
        (Complex.continuous_exp.comp (by fun_prop)).measurable
      have h2 : Measurable fun θ : ℝ => expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
        ((measurable_gradC v).comp h1).mul h1
      exact Complex.continuous_normSq.measurable.comp h2
    have hintNeg : IntegrableOn
        (fun θ : ℝ => Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
        (Ioo (-π) π) := by
      refine Measure.integrableOn_of_bounded (M := M ^ 2) measure_Ioo_lt_top.ne
        hmeasfun.aestronglyMeasurable ?_
      have hae : ∀ᵐ (θ : ℝ) ∂((volume : Measure ℝ).restrict (Ioo (-π) π)), Real.sin θ ≠ 0 := by
        have hnull : volume ({(0:ℝ), π} : Set ℝ) = 0 :=
          ((Set.finite_singleton π).insert 0).measure_zero _
        refine (ae_restrict_iff' measurableSet_Ioo).mpr ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with θ hθn hθ
        rcases lt_trichotomy θ 0 with hneg | hz | hpos
        · rcases lt_trichotomy θ (-π) with _ | _ | h3
          · linarith [hθ.1]
          · linarith [hθ.1]
          · have := Real.sin_pos_of_pos_of_lt_pi (x := θ + π) (by linarith) (by linarith [hθ.2])
            rw [Real.sin_add_pi] at this; linarith
        · exact absurd (show θ ∈ ({(0:ℝ), π} : Set ℝ) from Set.mem_insert_iff.mpr (Or.inl hz))
            hθn
        · rcases lt_trichotomy θ π with h3 | h3 | h3
          · exact (Real.sin_pos_of_pos_of_lt_pi hpos h3).ne'
          · exact absurd (show θ ∈ ({(0:ℝ), π} : Set ℝ) from
              Set.mem_insert_iff.mpr (Or.inr h3)) hθn
          · linarith [hθ.2]
      filter_upwards [hae] with θ hsin
      have hb := hM ξ (left_mem_Icc.mpr (le_refl ξ)) θ hsin
      rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)), hb, hMnn]
    rw [← ofReal_integral_eq_lintegral_ofReal hintNeg
      (ae_of_all _ fun θ => Complex.normSq_nonneg _), sliceEnergy_eq_neg_pi_pi]
  rw [setLIntegral_congr_fun measurableSet_Ioo hinner]
  -- outer bridge and the fundamental theorem of calculus for the slit flux
  have hsub : Icc ξ₁ ξ₂ ⊆ Iio (Real.log s) := fun x hx => lt_of_le_of_lt hx.2 hξ₂log
  have hScont : ContinuousOn (sliceEnergy v) (Icc ξ₁ ξ₂) :=
    (continuousOn_sliceEnergy hs0 hs1 hvh hvc hv0 hv1).mono hsub
  have hSint : IntegrableOn (sliceEnergy v) (Ioo ξ₁ ξ₂) :=
    (hScont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hSnn : ∀ ξ : ℝ, 0 ≤ sliceEnergy v ξ := fun ξ =>
    setIntegral_nonneg measurableSet_Ioo fun θ _ => Complex.normSq_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal hSint (ae_of_all _ fun ξ => hSnn ξ)]
  congr 1
  rw [integral_Ioo_eq_intervalIntegral h12,
    ← ringFluxSlit_sub_eq_integral hs0 hs1 hξ₂s h12 hvh hvc hv0 hv1 hvrange]

/-- **Monotonicity of the slit-chart flux.** For the Grötzsch potential `v` with values in
`[0, 1]`, the slit-chart flux is nondecreasing on `(−∞, log s)`: its increments are Dirichlet
energies, hence nonnegative. -/
theorem ringFluxSlit_monotoneOn {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    (hvrange : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1) :
    MonotoneOn (ringFluxSlit v) (Iio (Real.log s)) := by
  intro x hx y hy hxy
  have hys : Real.exp y < s := (Real.lt_log_iff_exp_lt hs0).mp hy
  have hFTC := ringFluxSlit_sub_eq_integral hs0 hs1 hys hxy hvh hvc hv0 hv1 hvrange
  have hnn : (0 : ℝ) ≤ ∫ ξ in x..y, sliceEnergy v ξ :=
    intervalIntegral.integral_nonneg hxy fun ξ _ =>
      setIntegral_nonneg measurableSet_Ioo fun θ _ => Complex.normSq_nonneg _
  linarith [hFTC, hnn]

end RiemannDynamics

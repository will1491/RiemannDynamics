/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.GrotzschRing.FluxEnergy.Basic

/-!
# Boundary flux limits and bank regularity of the Grötzsch potential

This middle chunk turns the flux calculus of `FluxEnergy.Basic` into the two regularity facts the
rest of the Grötzsch development consumes.  The first half runs the outer logarithmic barrier: for
a ring potential equal to `1` on the unit circle the circle mean is exactly `2π + b·ξ`, the ring
flux tends to the slope `b` there, and the Dirichlet energy of the whole collar `{s < |z| < 1}` is
an explicit supremum of flux deficits.  The second half proves an odd-reflection principle across
the real axis and applies it at an interior slit point: the odd reflection `reflectReal v` of the
Grötzsch potential is harmonic on a ball straddling the bank, which bounds `‖gradC v‖` off the
real axis on compact annuli strictly inside the slit.  Two pieces of infrastructure introduced
here are reused by `FluxEnergy.SlitFlux`: the `stripBox` toolbox for differentiating under the
integral sign over an arbitrary angle window, and the slit-chart flux `ringFluxSlit`.

## Main definitions

* `RiemannDynamics.stripBox` — the log-polar box `{w | a < Re w < b, c ≤ Im w ≤ d}`, open in the
  log-radius and closed in the angle.  `continuousOn_slice_of_continuousOn_stripBox` and
  `exists_bound_on_stripBox` are its slice-continuity and compact-slab bound API.
* `RiemannDynamics.ringFluxSlit` — the ring flux at log-radius `ξ` taken in the slit chart: the
  integral over the geometric angle `θ ∈ (0, 2π)` of `u(e^{ξ+iθ})` times the derivative of `u` in
  the direction of that same point, i.e. the scale-invariant radial derivative `r ∂_r u`.  It
  agrees with `ringFlux` for every `u` and `ξ`, with no hypotheses at all, by
  `ringFluxSlit_eq_ringFlux`, the integrand being `2π`-periodic in the angle.
* `RiemannDynamics.reflectReal` — the odd reflection of `v : ℂ → ℝ` across the real axis: `v z`
  when `0 ≤ Im z`, and `−v (conj z)` when `Im z < 0`.  It is odd under conjugation whenever `v`
  vanishes on the whole real axis (`reflectReal_conj`).

## Main results

* `RiemannDynamics.hasDerivAt_integral_stripBox` — differentiation under the integral sign over an
  arbitrary angle window.  If `c ≤ d`, both `G` and `G'` are continuous on `stripBox a b c d`, and
  for every `x ∈ (a, b)` and every interior angle `θ ∈ (c, d)` the horizontal slice
  `y ↦ G (y + θi)` has derivative `G' (x + θi)` at `x`, then `ξ ↦ ∫_{(c,d)} G (ξ + θi) dθ` has
  derivative `∫_{(c,d)} G' (ξ₀ + θi) dθ` at every `ξ₀ ∈ (a, b)`.
* `RiemannDynamics.exists_logCircleMean_slope` — for `0 < r₀ < 1` and `u` harmonic on the collar
  `{r₀ < |z| < 1}`, continuous on the closed collar `{r₀ ≤ |z| ≤ 1}` and equal to `1` on the unit
  circle, the affine circle mean has intercept exactly `2π`: some slope `b` satisfies
  `logCircleMean 0 u ξ = 2π + b·ξ` at every `ξ ∈ (log r₀, 0)`.  No bound on the range of `u` is
  required here.
* `RiemannDynamics.ringFlux_tendsto_slope` — for `0 < r₀ < 1` and `u` harmonic on the collar,
  continuous on the closed collar, equal to `1` on the unit circle, with `0 ≤ u ≤ 1` on the collar
  and `logCircleMean 0 u ξ = 2π + b·ξ` on `(log r₀, 0)`, the ring flux `ringFlux u ξ` tends to `b`
  as `ξ → 0⁻`.  The range bound is load-bearing: it drives the logarithmic barrier and the squeeze
  on the deficit square mean.
* `RiemannDynamics.dirichletEnergy_fullAnnulus_eq_iSup` — for `0 < s < 1` and `v` harmonic on
  `{s < |z| < 1}`, continuous on `{s ≤ |z| ≤ 1}`, equal to `1` on the unit circle, with
  `0 ≤ v ≤ 1` on the annulus and circle mean `2π + b·ξ` on `(log s, 0)`, the Dirichlet energy of
  the whole annulus is `⨆ n, ENNReal.ofReal (b − ringFlux v ξₙ)` along the exhausting log-radii
  `ξₙ = (log s)·(n+1)/(n+2)`, which decrease to `log s`.
* `RiemannDynamics.harmonicOnNhd_of_odd_reflection` — let `c` be fixed by conjugation and
  `0 < R`.  A function `h` continuous on `closedBall c R`, harmonic on the part of `ball c R` off
  the real axis, vanishing at every point of `closedBall c R` with zero imaginary part, and
  satisfying `h (conj z) = −h z` at every point of `closedBall c R`, is harmonic on `ball c R`.
* `RiemannDynamics.exists_bound_gradC_annulus` — for `0 < s < 1`, a Grötzsch potential `v`
  (harmonic on `grotzschRing s`, continuous on its closure, `0` on the slit `[0, s]` and `1` on
  the unit circle) and radii `0 < r₁` and `r₂ < s`, a single constant bounds `‖gradC v z‖` at
  every `z` with `r₁ ≤ ‖z‖ ≤ r₂` and `Im z ≠ 0`.  The hypothesis `Im z ≠ 0` is essential — nothing
  is asserted on the slit — and `0 < r₁`, `r₂ < s` keep the annulus clear of both slit endpoints.
-/

open MeasureTheory Set ENNReal Filter Topology Complex

open scoped Real ENNReal

noncomputable section

namespace RiemannDynamics

/-! ### The outer logarithmic barrier -/

/-- The logarithm of the norm is harmonic away from the origin: `log ‖z‖` is locally the real
part of a holomorphic branch of the complex logarithm. -/
theorem harmonicAt_log_norm {z : ℂ} (hz : z ≠ 0) :
    InnerProductSpace.HarmonicAt (fun w : ℂ => Real.log ‖w‖) z := by
  simpa using AnalyticAt.harmonicAt_log_norm (f := id) (analyticAt_id) hz

/-- The closed collar `{r ≤ |z| ≤ R}` is a closed set. -/
theorem isClosed_closedCollar (r R : ℝ) :
    IsClosed {z : ℂ | r ≤ dist z 0 ∧ dist z 0 ≤ R} := by
  have h1 : IsClosed {z : ℂ | r ≤ dist z 0} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  have h2 : IsClosed {z : ℂ | dist z 0 ≤ R} :=
    isClosed_le (continuous_id.dist continuous_const) continuous_const
  exact h1.inter h2

/-- **Outer logarithmic barrier.** For a ring potential `u` — harmonic on the collar annulus
`{r₀ < |z| < 1}`, continuous on the closed collar, nonnegative, equal to `1` on the unit
circle — the deficit `1 − u` is dominated on the outer sub-annulus `{r₁ < |z| < 1}` by the
harmonic barrier `log |z| / log r₁`, which vanishes on the unit circle and equals `1` on the
circle of radius `r₁`. -/
theorem one_sub_le_log_barrier {u : ℂ → ℝ} {r₀ r₁ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hnn : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z)
    (hr₁ : r₀ < r₁) (hr₁1 : r₁ < 1) :
    ∀ z ∈ RoundAnnulus 0 r₁ 1, 1 - u z ≤ Real.log (dist z 0) / Real.log r₁ := by
  have hr₁0 : 0 < r₁ := lt_trans h0 hr₁
  have hlogr₁ : Real.log r₁ < 0 := Real.log_neg hr₁0 hr₁1
  have hfeq : ∀ z : ℂ, ((fun _ : ℂ => (1 : ℝ)) - u
      - (Real.log r₁)⁻¹ • fun w : ℂ => Real.log ‖w‖) z
      = 1 - u z - Real.log (dist z 0) / Real.log r₁ := by
    intro z
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dist_zero_right]
    ring
  set f : ℂ → ℝ := (fun _ : ℂ => (1 : ℝ)) - u
    - (Real.log r₁)⁻¹ • fun w : ℂ => Real.log ‖w‖ with hf
  have hUsub : RoundAnnulus 0 r₁ 1 ⊆ RoundAnnulus 0 r₀ 1 := fun z hz =>
    ⟨lt_trans hr₁ hz.1, hz.2⟩
  have hUK : RoundAnnulus 0 r₁ 1 ⊆ {z : ℂ | r₁ ≤ dist z 0 ∧ dist z 0 ≤ 1} := fun z hz =>
    ⟨hz.1.le, hz.2.le⟩
  have hclU : closure (RoundAnnulus 0 r₁ 1) ⊆ {z : ℂ | r₁ ≤ dist z 0 ∧ dist z 0 ≤ 1} :=
    closure_minimal hUK (isClosed_closedCollar r₁ 1)
  -- the comparison function is harmonic on the outer sub-annulus
  have hharm : InnerProductSpace.HarmonicOnNhd f (RoundAnnulus 0 r₁ 1) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro hc
      have h1 : r₁ < dist x 0 := hx.1
      rw [hc, dist_self] at h1
      exact absurd h1 (not_lt.mpr hr₁0.le)
    exact ((InnerProductSpace.harmonicAt_const (1 : ℝ)).sub (hu x (hUsub hx))).sub
      ((harmonicAt_log_norm hx0).const_smul)
  -- continuity on the closure of the outer sub-annulus
  have hfc : ContinuousOn f (closure (RoundAnnulus 0 r₁ 1)) := by
    have hfc' : ContinuousOn (fun z : ℂ => 1 - u z - Real.log (dist z 0) / Real.log r₁)
        {z : ℂ | r₁ ≤ dist z 0 ∧ dist z 0 ≤ 1} := by
      refine (continuousOn_const.sub (hcont.mono fun z hz =>
        ⟨le_trans hr₁.le hz.1, hz.2⟩)).sub (ContinuousOn.div_const ?_ _)
      intro z hz
      have hz0 : dist z 0 ≠ 0 := (lt_of_lt_of_le hr₁0 hz.1).ne'
      have hdc : ContinuousAt (fun w : ℂ => dist w 0) z := by fun_prop
      exact (hdc.log hz0).continuousWithinAt
    exact (hfc'.mono hclU).congr fun z _ => hfeq z
  -- the boundary bound: `f ≤ 0` on the two frontier circles
  have hle : ∀ z ∈ frontier (RoundAnnulus 0 r₁ 1), f z ≤ 0 := by
    intro z hz
    rw [(isOpen_roundAnnulus 0 r₁ 1).frontier_eq] at hz
    have hzK := hclU hz.1
    have hcases : dist z 0 = r₁ ∨ dist z 0 = 1 := by
      rcases lt_or_eq_of_le hzK.1 with h1 | h1
      · rcases lt_or_eq_of_le hzK.2 with h2 | h2
        · exact absurd ⟨h1, h2⟩ hz.2
        · exact Or.inr h2
      · exact Or.inl h1.symm
    rw [show f z = 1 - u z - Real.log (dist z 0) / Real.log r₁ from hfeq z]
    rcases hcases with h | h
    · have hnnz : 0 ≤ u z := hnn z ⟨h ▸ hr₁, h ▸ hr₁1⟩
      rw [h, div_self hlogr₁.ne]
      linarith
    · have huz : u z = 1 := hone z (by simpa [grotzschOuter, Metric.mem_sphere] using h)
      rw [h, huz, Real.log_one, zero_div]
      norm_num
  -- maximum principle
  intro z hz
  have hmax := SubharmonicOn.le_of_frontier_le (isOpen_roundAnnulus 0 r₁ 1)
    (Metric.isBounded_ball.subset fun w hw => Metric.mem_ball.mpr hw.2)
    (HarmonicOnNhd.subharmonicOn hharm) hfc hle z hz
  rw [show f z = 1 - u z - Real.log (dist z 0) / Real.log r₁ from hfeq z] at hmax
  linarith

/-- The logarithmic barrier along circles: at log-radius `ξ ∈ (log r₁, 0)` the deficit of the
ring potential satisfies `1 − u(e^{ξ+iθ}) ≤ ξ / log r₁` at every angle. -/
theorem one_sub_uexp_le_barrier {u : ℂ → ℝ} {r₀ r₁ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hnn : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z)
    (hr₁ : r₀ < r₁) (hr₁1 : r₁ < 1)
    {ξ : ℝ} (hξ1 : Real.log r₁ < ξ) (hξ2 : ξ < 0) (θ : ℝ) :
    1 - u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) ≤ ξ / Real.log r₁ := by
  have hr₁0 : 0 < r₁ := lt_trans h0 hr₁
  have hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ RoundAnnulus 0 r₁ 1 :=
    exp_mem_roundAnnulus hr₁0 (by rw [re_logPolar]; exact hξ1)
      (by rw [re_logPolar]; exact hξ2)
  have hbar := one_sub_le_log_barrier h0 hu hcont hone hnn hr₁ hr₁1 _ hmem
  have hdist : dist (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) 0 = Real.exp ξ := by
    rw [dist_zero_right, Complex.norm_exp, re_logPolar]
  rwa [hdist, Real.log_exp] at hbar

/-- **Derivative of the deficit square mean.** For `u` harmonic on the collar annulus with circle
mean `2π + b·ξ`, the angle integral `ξ ↦ ∫_{(−π,π)} (1 − u(e^{ξ+iθ}))² dθ` has derivative
`2·(ringFlux u ξ − b)` at every `ξ ∈ (log r₀, 0)`: differentiation under the integral sign gives
the integrand `−2·(1 − u)·Re (expGrad u)`, and the angle integral of `Re (expGrad u)` is the
slope `b`. -/
theorem hasDerivAt_integral_one_sub_sq {u : ℂ → ℝ} {r₀ b : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hslope : ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + b * ξ)
    {ξ : ℝ} (hξ : ξ ∈ Ioo (Real.log r₀) 0) :
    HasDerivAt (fun x : ℝ => ∫ θ in Ioo (-π) π,
        (1 - u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))) ^ 2)
      (2 * (ringFlux u ξ - b)) ξ := by
  have hGcont : ContinuousOn (fun w => (1 - u (Complex.exp w)) ^ 2)
      {w : ℂ | Real.log r₀ < w.re ∧ w.re < 0} :=
    (continuousOn_const.sub (continuousOn_uexp h0 hu)).pow 2
  have hG'cont : ContinuousOn
      (fun w => -2 * ((1 - u (Complex.exp w)) * (expGrad u w).re))
      {w : ℂ | Real.log r₀ < w.re ∧ w.re < 0} :=
    continuousOn_const.mul ((continuousOn_const.sub (continuousOn_uexp h0 hu)).mul
      (continuousOn_expGrad_re h0 hu))
  have hd : ∀ x θ' : ℝ, Real.log r₀ < x → x < 0 →
      HasDerivAt (fun y : ℝ => (1 - u (Complex.exp ((y : ℂ) + (θ' : ℂ) * Complex.I))) ^ 2)
        (-2 * ((1 - u (Complex.exp ((x : ℂ) + (θ' : ℂ) * Complex.I)))
          * (expGrad u ((x : ℂ) + (θ' : ℂ) * Complex.I)).re)) x := by
    intro x θ' hx1 hx2
    have hu' := hasDerivAt_uexp_radial (u := u) (ξ := x) (θ := θ')
      (differentiableAt_of_harmonicOnNhd hu
        (exp_mem_roundAnnulus h0 (by rw [re_logPolar]; exact hx1)
          (by rw [re_logPolar]; exact hx2)))
    have hpow := (hu'.const_sub 1).pow 2
    refine hpow.congr_deriv ?_
    push_cast
    ring
  have hDUI := hasDerivAt_integral_logStrip hGcont hG'cont hd hξ.1 hξ.2
  have hint1 : IntegrableOn (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
      (Ioo (-π) π) :=
    ((continuous_slice_of_continuousOn_logStrip (continuousOn_expGrad_re h0 hu) hξ.1
      hξ.2).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hint2 : IntegrableOn (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
      * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (Ioo (-π) π) :=
    (((continuous_slice_of_continuousOn_logStrip (continuousOn_uexp h0 hu) hξ.1 hξ.2).mul
      (continuous_slice_of_continuousOn_logStrip (continuousOn_expGrad_re h0 hu) hξ.1
        hξ.2)).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hval : (∫ θ in Ioo (-π) π,
      -2 * ((1 - u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
        * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re))
      = 2 * (ringFlux u ξ - b) := by
    rw [integral_const_mul]
    have hsplit : (∫ θ in Ioo (-π) π,
        (1 - u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
          * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
        = (∫ θ in Ioo (-π) π, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
          - ∫ θ in Ioo (-π) π, u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
              * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re := by
      rw [← integral_sub hint1 hint2]
      congr 1
      funext θ
      ring
    rw [hsplit, integral_expGrad_re_eq_slope h0 hu hslope hξ, ← ringFlux_eq]
    ring
  rw [hval] at hDUI
  exact hDUI

/-- **Boundary limit of the ring flux.** For a ring potential `u` — harmonic on the collar
annulus, continuous on the closed collar, with values in `[0, 1]`, equal to `1` on the unit
circle — whose circle mean is `2π + b·ξ` in the log-radius, the ring flux tends to the slope `b`
at the unit circle: the deficit square mean `ψ(ξ) = ∫ (1−u)² dθ` is `O(ξ²)` by the logarithmic
barrier, its derivative is `2·(ringFlux − b)`, and the monotonicity of the flux squeezes
`ringFlux − b → 0`. -/
theorem ringFlux_tendsto_slope {u : ℂ → ℝ} {r₀ b : ℝ} (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hrange : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z ∧ u z ≤ 1)
    (hslope : ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + b * ξ) :
    Tendsto (ringFlux u) (𝓝[<] (0 : ℝ)) (𝓝 b) := by
  have hπpos := Real.pi_pos
  set r₁ : ℝ := (r₀ + 1) / 2 with hr₁def
  have hr₁ : r₀ < r₁ := by rw [hr₁def]; linarith
  have hr₁1 : r₁ < 1 := by rw [hr₁def]; linarith
  have hr₁0 : 0 < r₁ := lt_trans h0 hr₁
  have hL : Real.log r₁ < 0 := Real.log_neg hr₁0 hr₁1
  have hLr₀ : Real.log r₀ < Real.log r₁ := Real.log_lt_log h0 hr₁
  set C : ℝ := 2 * π / (Real.log r₁) ^ 2 with hCdef
  set ψ : ℝ → ℝ := fun x => ∫ θ in Ioo (-π) π,
      (1 - u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))) ^ 2 with hψdef
  have hψnn : ∀ x : ℝ, 0 ≤ ψ x := fun x =>
    setIntegral_nonneg measurableSet_Ioo fun θ _ => sq_nonneg _
  -- quadratic decay of the deficit square mean from the logarithmic barrier
  have hψbound : ∀ x ∈ Ioo (Real.log r₁) 0, ψ x ≤ C * x ^ 2 := by
    intro x hx
    have hbound : ∀ θ ∈ Ioo (-π) π,
        ‖(1 - u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))) ^ 2‖
          ≤ (x / Real.log r₁) ^ 2 := by
      intro θ _
      have hmem : Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ RoundAnnulus 0 r₀ 1 :=
        exp_mem_roundAnnulus h0 (by rw [re_logPolar]; exact lt_trans hLr₀ hx.1)
          (by rw [re_logPolar]; exact hx.2)
      have h01 := hrange _ hmem
      have hbar := one_sub_uexp_le_barrier h0 hu hcont hone
        (fun z hz => (hrange z hz).1) hr₁ hr₁1 hx.1 hx.2 θ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [hbar, h01.2]
    have hnorm := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (-π) π)
      (C := (x / Real.log r₁) ^ 2) measure_Ioo_lt_top hbound
    have hvol : (volume : Measure ℝ).real (Ioo (-π) π) = 2 * π := by
      rw [measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [hvol] at hnorm
    calc ψ x ≤ ‖ψ x‖ := le_abs_self _
      _ ≤ (x / Real.log r₁) ^ 2 * (2 * π) := hnorm
      _ = C * x ^ 2 := by rw [hCdef, div_pow]; field_simp
  have hderiv : ∀ t ∈ Ioo (Real.log r₀) 0, HasDerivAt ψ (2 * (ringFlux u t - b)) t :=
    fun t ht => hasDerivAt_integral_one_sub_sq h0 hu hslope ht
  have hmono := ringFlux_monotoneOn h0 hu
  have hFluxCont : ∀ t ∈ Ioo (Real.log r₀) 0,
      ContinuousAt (fun s : ℝ => 2 * (ringFlux u s - b)) t := by
    intro t ht
    have h1 : ContinuousAt (ringFlux u) t := (hasDerivAt_ringFlux h0 hu ht.1 ht.2).continuousAt
    exact continuousAt_const.mul (h1.sub continuousAt_const)
  have hFTC : ∀ {x y : ℝ}, x ∈ Ioo (Real.log r₀) 0 → y ∈ Ioo (Real.log r₀) 0 → x ≤ y →
      ψ y - ψ x = ∫ t in x..y, 2 * (ringFlux u t - b) := by
    intro x y hx hy hxy
    have hsub : Icc x y ⊆ Ioo (Real.log r₀) 0 := fun t ht =>
      ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hderiv t (hsub (by rwa [uIcc_of_le hxy] at ht)))
      (ContinuousOn.intervalIntegrable fun t ht =>
        (hFluxCont t (hsub (by rwa [uIcc_of_le hxy] at ht))).continuousWithinAt)).symm
  -- upper squeeze bound on `(log r₁, 0)`
  have hupper : ∀ ξ ∈ Ioo (Real.log r₁) 0, ringFlux u ξ - b ≤ C * (-ξ) / 4 := by
    intro ξ hξmem
    have hξneg : ξ < 0 := hξmem.2
    have hξIoo : ξ ∈ Ioo (Real.log r₀) 0 := ⟨lt_trans hLr₀ hξmem.1, hξneg⟩
    have hhalfIoo : ξ / 2 ∈ Ioo (Real.log r₀) 0 := ⟨lt_trans hξIoo.1 (by linarith), by linarith⟩
    have hhalfL : ξ / 2 ∈ Ioo (Real.log r₁) 0 := ⟨lt_trans hξmem.1 (by linarith), by linarith⟩
    have hle2 : ξ ≤ ξ / 2 := by linarith
    have hsub : Icc ξ (ξ / 2) ⊆ Ioo (Real.log r₀) 0 := fun t ht =>
      ⟨lt_of_lt_of_le hξIoo.1 ht.1, lt_of_le_of_lt ht.2 hhalfIoo.2⟩
    have hint : IntervalIntegrable (fun t => 2 * (ringFlux u t - b)) volume ξ (ξ / 2) :=
      ContinuousOn.intervalIntegrable fun t ht =>
        (hFluxCont t (hsub (by rwa [uIcc_of_le hle2] at ht))).continuousWithinAt
    have hmonoInt : (∫ _ in ξ..(ξ / 2), 2 * (ringFlux u ξ - b))
        ≤ ∫ t in ξ..(ξ / 2), 2 * (ringFlux u t - b) := by
      refine intervalIntegral.integral_mono_on hle2 intervalIntegrable_const hint fun t ht => ?_
      have := hmono hξIoo (hsub ht) ht.1
      linarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmonoInt
    have hkey : (ξ / 2 - ξ) * (2 * (ringFlux u ξ - b)) ≤ C * (ξ / 2) ^ 2 :=
      hmonoInt.trans (by linarith [hFTC hξIoo hhalfIoo hle2, hψbound _ hhalfL, hψnn ξ])
    nlinarith [hkey, hξneg]
  -- lower squeeze bound on `(log r₁ / 2, 0)`
  have hlower : ∀ ξ ∈ Ioo (Real.log r₁ / 2) 0, 2 * C * ξ ≤ ringFlux u ξ - b := by
    intro ξ hξmem
    have hξneg : ξ < 0 := hξmem.2
    have h2ξL : 2 * ξ ∈ Ioo (Real.log r₁) 0 := ⟨by linarith [hξmem.1], by linarith⟩
    have h2ξIoo : 2 * ξ ∈ Ioo (Real.log r₀) 0 := ⟨lt_trans hLr₀ h2ξL.1, h2ξL.2⟩
    have hξIoo : ξ ∈ Ioo (Real.log r₀) 0 := ⟨by linarith [h2ξIoo.1], hξneg⟩
    have hle2 : 2 * ξ ≤ ξ := by linarith
    have hsub : Icc (2 * ξ) ξ ⊆ Ioo (Real.log r₀) 0 := fun t ht =>
      ⟨lt_of_lt_of_le h2ξIoo.1 ht.1, lt_of_le_of_lt ht.2 hξIoo.2⟩
    have hint : IntervalIntegrable (fun t => 2 * (ringFlux u t - b)) volume (2 * ξ) ξ :=
      ContinuousOn.intervalIntegrable fun t ht =>
        (hFluxCont t (hsub (by rwa [uIcc_of_le hle2] at ht))).continuousWithinAt
    have hmonoInt : (∫ t in (2 * ξ)..ξ, 2 * (ringFlux u t - b))
        ≤ ∫ _ in (2 * ξ)..ξ, 2 * (ringFlux u ξ - b) := by
      refine intervalIntegral.integral_mono_on hle2 hint intervalIntegrable_const fun t ht => ?_
      have := hmono (hsub ht) hξIoo ht.2
      linarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmonoInt
    have hkey : -(C * (2 * ξ) ^ 2) ≤ (ξ - 2 * ξ) * (2 * (ringFlux u ξ - b)) :=
      le_trans (by linarith [hFTC h2ξIoo hξIoo hle2, hψbound _ h2ξL, hψnn ξ]) hmonoInt
    nlinarith [hkey, hξneg]
  -- squeeze
  have hL2 : Real.log r₁ / 2 < 0 := by linarith
  have hup' : ∀ᶠ ξ in 𝓝[<] (0 : ℝ), ringFlux u ξ ≤ b + C * (-ξ) / 4 := by
    filter_upwards [Ioo_mem_nhdsLT hL2] with ξ hξ
    have h' := hupper ξ ⟨by linarith [hξ.1], hξ.2⟩
    linarith
  have hlo' : ∀ᶠ ξ in 𝓝[<] (0 : ℝ), b + 2 * C * ξ ≤ ringFlux u ξ := by
    filter_upwards [Ioo_mem_nhdsLT hL2] with ξ hξ
    have h' := hlower ξ hξ
    linarith
  have htop : Tendsto (fun ξ : ℝ => b + C * (-ξ) / 4) (𝓝[<] (0 : ℝ)) (𝓝 b) := by
    have hc : Continuous fun ξ : ℝ => b + C * (-ξ) / 4 := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))
    simpa using this
  have hbot : Tendsto (fun ξ : ℝ => b + 2 * C * ξ) (𝓝[<] (0 : ℝ)) (𝓝 b) := by
    have hc : Continuous fun ξ : ℝ => b + 2 * C * ξ := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hbot htop hlo' hup'

/-- **The collar circle mean is `2π + b·ξ`.** For a ring potential harmonic on the collar
annulus, continuous on the closed collar, equal to `1` on the unit circle, the affine circle
mean has intercept `2π` at the unit circle: there is a slope `b` with
`logCircleMean 0 u ξ = 2π + b·ξ` on `(log r₀, 0)`. -/
theorem exists_logCircleMean_slope {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1) :
    ∃ b : ℝ, ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + b * ξ := by
  obtain ⟨a, b, hab⟩ := logCircleMean_affineOn h0 h1 hu
  have hlim := logCircleMean_tendsto_two_pi h0 h1 hcont hone
  have hlog : Real.log r₀ < 0 := Real.log_neg h0 h1
  have haff : Tendsto (fun ξ : ℝ => a + b * ξ) (𝓝[<] (0 : ℝ)) (𝓝 a) := by
    have hc : Continuous fun ξ : ℝ => a + b * ξ := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))
    simpa using this
  have hcong : Tendsto (fun ξ => logCircleMean 0 u ξ) (𝓝[<] (0 : ℝ)) (𝓝 a) := by
    refine haff.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hlog] with ξ hξ
    exact (hab ξ hξ).symm
  have ha : a = 2 * π := tendsto_nhds_unique hcong hlim
  exact ⟨b, fun ξ hξ => by rw [hab ξ hξ, ha]⟩

/-- **Exact outer-collar energy.** For a ring potential with values in `[0, 1]`, equal to `1` on
the unit circle, whose circle mean is `2π + b·ξ`, the Dirichlet energy over the outer collar
`{e^{ξ₁} < |z| < 1}` equals `b − ringFlux u ξ₁` exactly: the flux increments to the exhausting
radii converge to the boundary flux `b`. -/
theorem dirichletEnergy_outerCollar_eq_ofReal_sub {u : ℂ → ℝ} {r₀ b : ℝ} (h0 : 0 < r₀)
    (h1 : r₀ < 1)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hrange : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z ∧ u z ≤ 1)
    (hslope : ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + b * ξ)
    {ξ₁ : ℝ} (hξ₁ : ξ₁ ∈ Ioo (Real.log r₀) 0) :
    dirichletEnergy u (RoundAnnulus 0 (Real.exp ξ₁) 1)
      = ENNReal.ofReal (b - ringFlux u ξ₁) := by
  rw [dirichletEnergy_outerCollar_eq_iSup_ringFlux h0 hu hξ₁.1 hξ₁.2]
  have hmem : ∀ n : ℕ, ξ₁ / (n + 1) ∈ Ioo (Real.log r₀) 0 := by
    intro n
    constructor
    · refine lt_of_lt_of_le hξ₁.1 ?_
      have h1n : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [Nat.cast_nonneg (α := ℝ) n]
      calc ξ₁ = ξ₁ * 1 := by ring
        _ ≤ ξ₁ * (1 / ((n : ℝ) + 1)) := mul_le_mul_of_nonpos_left h1n hξ₁.2.le
        _ = ξ₁ / ((n : ℝ) + 1) := by ring
    · exact div_neg_of_neg_of_pos hξ₁.2 (by positivity)
  have hseqmono : Monotone fun n : ℕ =>
      ENNReal.ofReal (ringFlux u (ξ₁ / (n + 1)) - ringFlux u ξ₁) := by
    intro n m hnm
    refine ENNReal.ofReal_le_ofReal ?_
    have hle : ξ₁ / ((n : ℝ) + 1) ≤ ξ₁ / ((m : ℝ) + 1) := by
      have hd : ((n : ℝ) + 1) ≤ ((m : ℝ) + 1) := by
        have hcast : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
        linarith
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)
        (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
      exact mul_le_mul_of_nonpos_left hd hξ₁.2.le
    have := ringFlux_monotoneOn h0 hu (hmem n) (hmem m) hle
    linarith
  have htendsto : Tendsto (fun n : ℕ => ENNReal.ofReal (ringFlux u (ξ₁ / (n + 1))
      - ringFlux u ξ₁)) atTop (𝓝 (ENNReal.ofReal (b - ringFlux u ξ₁))) := by
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    refine Tendsto.sub_const ?_ _
    refine (ringFlux_tendsto_slope h0 h1 hu hcont hone hrange hslope).comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Eventually.of_forall fun n => Set.mem_Iio.mpr (hmem n).2)
    have h0' : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hmul := h0'.const_mul ξ₁
    simpa [one_div, div_eq_mul_inv] using hmul
  exact tendsto_nhds_unique (tendsto_atTop_iSup hseqmono) htendsto

/-! ### Null sets and energy over sets differing by a null set -/

/-- The real axis `{z : ℂ | z.im = 0}` has planar Lebesgue measure zero: it is a proper real
subspace of `ℂ`. -/
theorem volume_realAxis_eq_zero :
    (volume : Measure ℂ) {z : ℂ | z.im = 0} = 0 := by
  have hker : {z : ℂ | z.im = 0} = (LinearMap.ker Complex.imCLM.toLinearMap : Set ℂ) := by
    ext z
    simp [LinearMap.mem_ker]
  rw [hker]
  refine MeasureTheory.Measure.addHaar_submodule _ _ ?_
  intro htop
  have hI : Complex.I ∈ (⊤ : Submodule ℝ ℂ) := Submodule.mem_top
  rw [← htop, LinearMap.mem_ker] at hI
  simp at hI

/-- The Grötzsch slit `grotzschInner s` has planar Lebesgue measure zero: it lies in the real
axis. -/
theorem volume_grotzschInner_eq_zero {s : ℝ} (hs0 : 0 ≤ s) :
    (volume : Measure ℂ) (grotzschInner s) = 0 := by
  refine measure_mono_null (fun z hz => ?_) volume_realAxis_eq_zero
  rw [grotzschInner_eq hs0] at hz
  exact hz.1

/-- The Dirichlet energy is unchanged when the domain is enlarged or shrunk by a null set. -/
theorem dirichletEnergy_congr_ae {u : ℂ → ℝ} {U V : Set ℂ}
    (h : U =ᵐ[volume] V) : dirichletEnergy u U = dirichletEnergy u V := by
  unfold dirichletEnergy
  rw [Measure.restrict_congr_set h]

/-- The Grötzsch ring differs from the open unit disk by the null slit, so their Dirichlet
energies agree. -/
theorem dirichletEnergy_grotzschRing_eq_ball {u : ℂ → ℝ} {s : ℝ} (hs0 : 0 ≤ s) :
    dirichletEnergy u (grotzschRing s) = dirichletEnergy u (Metric.ball (0 : ℂ) 1) := by
  refine dirichletEnergy_congr_ae ?_
  rw [ae_eq_set]
  refine ⟨measure_mono_null (fun z hz => absurd hz.1.1 hz.2) measure_empty, ?_⟩
  refine measure_mono_null (fun z hz => ?_) (volume_grotzschInner_eq_zero hs0)
  by_contra hno
  exact hz.2 ⟨hz.1, hno⟩

/-- The circle `{z : ℂ | dist z 0 = s}` has planar Lebesgue measure zero. -/
theorem volume_sphere_eq_zero (s : ℝ) :
    (volume : Measure ℂ) {z : ℂ | dist z 0 = s} = 0 := by
  have hle : {z : ℂ | dist z 0 = s} ⊆ Metric.sphere (0 : ℂ) s := fun z hz =>
    Metric.mem_sphere.mpr hz
  exact measure_mono_null hle (MeasureTheory.Measure.addHaar_sphere _ _ _)

/-- **Radial split of the disk energy.** For any potential `u`, the Dirichlet energy over the
open unit disk splits along the circle `|z| = s` into the inner-disk energy and the outer round
annulus energy: the separating circle is null. -/
theorem dirichletEnergy_ball_split {u : ℂ → ℝ} {s : ℝ} (hs1 : s < 1) :
    dirichletEnergy u (Metric.ball (0 : ℂ) 1)
      = dirichletEnergy u (Metric.ball (0 : ℂ) s)
        + dirichletEnergy u (RoundAnnulus 0 s 1) := by
  unfold dirichletEnergy
  set g : ℂ → ℝ≥0∞ := fun z => (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2 with hg
  have hballmeas : MeasurableSet (Metric.ball (0 : ℂ) s) := Metric.isOpen_ball.measurableSet
  have hannmeas : MeasurableSet (RoundAnnulus 0 s 1) := (isOpen_roundAnnulus _ _ _).measurableSet
  have hdisj : Disjoint (Metric.ball (0 : ℂ) s) (RoundAnnulus 0 s 1) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    exact absurd hz' (fun h => absurd (Metric.mem_ball.mp hz) (not_lt.mpr h.1.le))
  have hsplit : Metric.ball (0 : ℂ) 1
      =ᵐ[volume] (Metric.ball (0 : ℂ) s ∪ RoundAnnulus 0 s 1 : Set ℂ) := by
    rw [ae_eq_set]
    refine ⟨measure_mono_null (fun z hz => ?_) (volume_sphere_eq_zero s), ?_⟩
    · have hzball : dist z 0 < 1 := Metric.mem_ball.mp hz.1
      have hznotin : z ∉ Metric.ball (0 : ℂ) s ∪ RoundAnnulus 0 s 1 := hz.2
      rw [Set.mem_union, Metric.mem_ball, not_or] at hznotin
      have h1 : ¬ dist z 0 < s := hznotin.1
      have h2 : ¬ (s < dist z 0 ∧ dist z 0 < 1) := hznotin.2
      have : ¬ s < dist z 0 := fun h => h2 ⟨h, hzball⟩
      exact le_antisymm (not_lt.mp this) (not_lt.mp h1)
    · refine measure_mono_null (fun z hz => ?_) measure_empty
      exfalso
      rcases hz.1 with hb | ha
      · exact hz.2 (Metric.mem_ball.mpr (lt_trans (Metric.mem_ball.mp hb) hs1))
      · exact hz.2 (Metric.mem_ball.mpr ha.2)
  rw [Measure.restrict_congr_set hsplit, ← lintegral_union hannmeas hdisj]

/-- The full outer annulus `{s < |z| < 1}` is the monotone union of the sub-annuli whose inner
radii `e^{ξ_n} ↓ s` shrink toward `s`, where `ξ_n = (log s)·(n+1)/(n+2)`. -/
theorem roundAnnulus_full_eq_iUnion {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    RoundAnnulus 0 s 1
      = ⋃ n : ℕ, RoundAnnulus 0 (Real.exp (Real.log s * (n + 1) / (n + 2))) 1 := by
  have hL : Real.log s < 0 := Real.log_neg hs0 hs1
  have hlt0 : ∀ n : ℕ, Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2) < 0 := by
    intro n
    rw [mul_div_assoc]
    exact mul_neg_of_neg_of_pos hL (by positivity)
  have hgtL : ∀ n : ℕ, Real.log s < Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
    intro n
    have hc : ((n : ℝ) + 1) / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    rw [mul_div_assoc]
    calc Real.log s = Real.log s * 1 := by ring
      _ < Real.log s * (((n : ℝ) + 1) / ((n : ℝ) + 2)) := mul_lt_mul_of_neg_left hc hL
  have hexp : ∀ n : ℕ, Real.exp (Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2)) < 1 := fun n =>
    Real.exp_lt_one_iff.mpr (hlt0 n)
  have hgt : ∀ n : ℕ, s < Real.exp (Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2)) := fun n =>
    (Real.log_lt_iff_lt_exp hs0).mp (hgtL n)
  ext z
  simp only [RoundAnnulus, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨h1, h2⟩
    have hzpos : 0 < dist z 0 := lt_trans hs0 h1
    have hlog : Real.log s < Real.log (dist z 0) := Real.log_lt_log hs0 h1
    -- pick `n` large enough that `ξ_n < log (dist z 0)`
    have htend : Filter.Tendsto
        (fun n : ℕ => Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2)) Filter.atTop
        (𝓝 (Real.log s)) := by
      have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 2)) Filter.atTop
          (𝓝 1) := by
        have hz : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have hz2 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) Filter.atTop (𝓝 0) := by
          have := (hz.comp (Filter.tendsto_add_atTop_nat 1))
          refine this.congr fun n => ?_
          simp only [Function.comp_apply]
          push_cast
          ring_nf
        have hsub := (tendsto_const_nhds (x := (1 : ℝ))).sub hz2
        rw [sub_zero] at hsub
        refine hsub.congr fun n => ?_
        have hne : ((n : ℝ) + 2) ≠ 0 := by positivity
        field_simp
        ring
      have h2 := (h1.const_mul (Real.log s))
      simp only [mul_one] at h2
      convert h2 using 2 with n
      ring
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2) < Real.log (dist z 0) :=
      htend.eventually_lt_const hlog
    obtain ⟨n, hn⟩ := hev.exists
    refine ⟨n, ?_, h2⟩
    calc Real.exp (Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2))
        < Real.exp (Real.log (dist z 0)) := Real.exp_lt_exp.mpr hn
      _ = dist z 0 := Real.exp_log hzpos
  · rintro ⟨n, h1, h2⟩
    exact ⟨lt_trans (hgt n) h1, h2⟩

/-- **Exact outer-annulus energy.** For a ring potential `v` on the Grötzsch ring with values in
`[0, 1]`, equal to `1` on the unit circle, whose circle mean is `2π + b·ξ`, the Dirichlet energy
over the full outer annulus `{s < |z| < 1}` is the supremum of the flux increments up to the
exhausting inner radii `e^{ξ_n} ↓ s`. -/
theorem dirichletEnergy_fullAnnulus_eq_iSup {v : ℂ → ℝ} {s b : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hu : InnerProductSpace.HarmonicOnNhd v (RoundAnnulus 0 s 1))
    (hcont : ContinuousOn v {z : ℂ | s ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, v z = 1)
    (hrange : ∀ z ∈ RoundAnnulus 0 s 1, 0 ≤ v z ∧ v z ≤ 1)
    (hslope : ∀ ξ ∈ Ioo (Real.log s) 0, logCircleMean 0 v ξ = 2 * π + b * ξ) :
    dirichletEnergy v (RoundAnnulus 0 s 1)
      = ⨆ n : ℕ, ENNReal.ofReal (b - ringFlux v (Real.log s * (n + 1) / (n + 2))) := by
  have hL : Real.log s < 0 := Real.log_neg hs0 hs1
  set ξf : ℕ → ℝ := fun n => Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2) with hξf
  have hξmem : ∀ n : ℕ, ξf n ∈ Ioo (Real.log s) 0 := by
    intro n
    refine ⟨?_, ?_⟩
    · have hc : ((n : ℝ) + 1) / ((n : ℝ) + 2) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      have : Real.log s * 1 < Real.log s * (((n : ℝ) + 1) / ((n : ℝ) + 2)) :=
        mul_lt_mul_of_neg_left hc hL
      simp only [hξf, mul_one] at this ⊢
      calc Real.log s = Real.log s * 1 := by ring
        _ < Real.log s * (((n : ℝ) + 1) / ((n : ℝ) + 2)) := mul_lt_mul_of_neg_left hc hL
        _ = Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2) := by ring
    · have hpos : 0 < ((n : ℝ) + 1) / ((n : ℝ) + 2) := by positivity
      simp only [hξf]
      rw [mul_div_assoc]
      exact mul_neg_of_neg_of_pos hL hpos
  have hgmeas : Measurable fun z : ℂ => ((‖fderiv ℝ v z‖₊ : ℝ≥0∞)) ^ 2 := by
    have heq : (fun z : ℂ => ((‖fderiv ℝ v z‖₊ : ℝ≥0∞)) ^ 2)
        = fun z => ENNReal.ofReal (Complex.normSq (gradC v z)) :=
      funext fun z => nnnorm_fderiv_sq_eq_ofReal_normSq_gradC v z
    rw [heq]
    exact ENNReal.measurable_ofReal.comp
      (Complex.continuous_normSq.measurable.comp (measurable_gradC v))
  have hmono : Monotone fun n : ℕ => RoundAnnulus 0 (Real.exp (ξf n)) 1 := by
    intro n m hnm z hz
    refine ⟨lt_of_le_of_lt (Real.exp_le_exp.mpr ?_) hz.1, hz.2⟩
    have hcast : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
    simp only [hξf]
    rw [mul_div_assoc, mul_div_assoc]
    apply mul_le_mul_of_nonpos_left _ hL.le
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hcast]
  calc dirichletEnergy v (RoundAnnulus 0 s 1)
      = ∫⁻ z in ⋃ n : ℕ, RoundAnnulus 0 (Real.exp (ξf n)) 1,
          ((‖fderiv ℝ v z‖₊ : ℝ≥0∞)) ^ 2 := by
        rw [← roundAnnulus_full_eq_iUnion hs0 hs1]
        rfl
    _ = ⨆ n : ℕ, ∫⁻ z in RoundAnnulus 0 (Real.exp (ξf n)) 1,
          ((‖fderiv ℝ v z‖₊ : ℝ≥0∞)) ^ 2 :=
        lintegral_iUnion_of_monotone (fun n => (isOpen_roundAnnulus _ _ _).measurableSet)
          hmono hgmeas
    _ = ⨆ n : ℕ, ENNReal.ofReal (b - ringFlux v (ξf n)) := by
        refine iSup_congr fun n => ?_
        have := dirichletEnergy_outerCollar_eq_ofReal_sub hs0 hs1 hu hcont hone hrange hslope
          (hξmem n)
        exact this

/-! ### Angle-generalized differentiation under the integral sign -/

/-- The **log-polar strip box** `{a < Re w < b, c ≤ Im w ≤ d}`: the vertical strip of
log-radii `(a, b)`, closed in the angle direction over `[c, d]`. -/
def stripBox (a b c d : ℝ) : Set ℂ :=
  {w : ℂ | a < w.re ∧ w.re < b ∧ c ≤ w.im ∧ w.im ≤ d}

/-- Continuity of a horizontal slice `t ↦ F (x + t·I)` over `[c, d]` of a function continuous on
the strip box. -/
theorem continuousOn_slice_of_continuousOn_stripBox {F : ℂ → ℝ} {a b c d : ℝ}
    (hF : ContinuousOn F (stripBox a b c d)) {x : ℝ} (hx1 : a < x) (hx2 : x < b) :
    ContinuousOn (fun t : ℝ => F ((x : ℂ) + (t : ℂ) * Complex.I)) (Icc c d) := by
  have hmapsto : Set.MapsTo (fun t : ℝ => ((x : ℂ) + (t : ℂ) * Complex.I))
      (Icc c d) (stripBox a b c d) := by
    intro s hs
    simp only [stripBox, Set.mem_ofPred_eq, re_logPolar, im_logPolar]
    exact ⟨hx1, hx2, hs.1, hs.2⟩
  exact hF.comp (by fun_prop) hmapsto

/-- A function continuous on the strip box is bounded on every compact slab
`[ξ₀ − δ, ξ₀ + δ] × [c, d]` contained in the strip box. -/
theorem exists_bound_on_stripBox {F : ℂ → ℝ} {a b c d : ℝ}
    (hF : ContinuousOn F (stripBox a b c d)) {δ ξ₀ : ℝ}
    (hδsub : Icc (ξ₀ - δ) (ξ₀ + δ) ⊆ Ioo a b) :
    ∃ C : ℝ, ∀ x ∈ Icc (ξ₀ - δ) (ξ₀ + δ), ∀ t ∈ Icc c d,
      ‖F ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  have hmap : Continuous fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
  set K : Set ℂ := (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) ''
    (Icc (ξ₀ - δ) (ξ₀ + δ) ×ˢ Icc c d) with hK
  have hKcpt : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image hmap
  have hKsub : K ⊆ stripBox a b c d := by
    rintro w ⟨p, hp, rfl⟩
    have hmem := hδsub hp.1
    simp only [stripBox, Set.mem_ofPred_eq, re_logPolar, im_logPolar]
    exact ⟨hmem.1, hmem.2, hp.2.1, hp.2.2⟩
  obtain ⟨C, hC⟩ := hKcpt.exists_bound_of_continuousOn (hF.mono hKsub)
  exact ⟨C, fun x hx t ht => hC _ ⟨(x, t), ⟨hx, ht⟩, rfl⟩⟩

/-- **Angle-generalized differentiation under the integral sign.** For an integrand `G` continuous
on the strip box `{a < Re w < b, c ≤ Im w ≤ d}`, with radial-derivative function `G'` continuous
there and equal to the radial derivative of `G` along each horizontal line at every interior angle
`θ ∈ (c, d)`, the angle integral `ξ ↦ ∫_{(c,d)} G(ξ+θi) dθ` has derivative
`∫_{(c,d)} G'(ξ₀+θi) dθ` at every `ξ₀ ∈ (a, b)`. -/
theorem hasDerivAt_integral_stripBox {G G' : ℂ → ℝ} {a b c d ξ₀ : ℝ} (hcd : c ≤ d)
    (hG : ContinuousOn G (stripBox a b c d))
    (hG' : ContinuousOn G' (stripBox a b c d))
    (hd : ∀ x θ : ℝ, a < x → x < b → c < θ → θ < d →
      HasDerivAt (fun y : ℝ => G ((y : ℂ) + (θ : ℂ) * Complex.I))
        (G' ((x : ℂ) + (θ : ℂ) * Complex.I)) x)
    (ha : a < ξ₀) (hb : ξ₀ < b) :
    HasDerivAt (fun ξ : ℝ => ∫ θ in Ioo c d, G ((ξ : ℂ) + (θ : ℂ) * Complex.I))
      (∫ θ in Ioo c d, G' ((ξ₀ : ℂ) + (θ : ℂ) * Complex.I)) ξ₀ := by
  obtain ⟨δ, hδpos, hδsub⟩ := exists_closed_slab ha hb
  obtain ⟨C, hC⟩ := exists_bound_on_stripBox hG' hδsub
  have hball : ∀ x ∈ Metric.ball ξ₀ δ, x ∈ Icc (ξ₀ - δ) (ξ₀ + δ) := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hGslice : ∀ x : ℝ, a < x → x < b →
      ContinuousOn (fun t : ℝ => G ((x : ℂ) + (t : ℂ) * Complex.I)) (Icc c d) :=
    fun x hx1 hx2 => continuousOn_slice_of_continuousOn_stripBox hG hx1 hx2
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := c) (b := d) (bound := fun _ => C)
    (F := fun (x : ℝ) (t : ℝ) => G ((x : ℂ) + (t : ℂ) * Complex.I))
    (F' := fun (x : ℝ) (t : ℝ) => G' ((x : ℂ) + (t : ℂ) * Complex.I))
    (Metric.ball_mem_nhds ξ₀ hδpos)
    ?_ ?_ ?_ ?_ ?_ ?_
  · have hfun : (fun ξ : ℝ => ∫ θ in Ioo c d, G ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        = fun ξ : ℝ => ∫ θ in c..d, G ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
      funext fun ξ => integral_Ioo_eq_intervalIntegral hcd _
    rw [hfun, integral_Ioo_eq_intervalIntegral hcd]
    exact hmain.2
  · filter_upwards [Ioo_mem_nhds ha hb] with x hx
    rw [Set.uIoc_of_le hcd]
    exact ((hGslice x hx.1 hx.2).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · exact ((hGslice ξ₀ ha hb).intervalIntegrable_of_Icc hcd)
  · rw [Set.uIoc_of_le hcd]
    exact ((continuousOn_slice_of_continuousOn_stripBox hG' ha hb).mono
      Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · refine Eventually.of_forall fun t ht x hx => ?_
    rw [Set.uIoc_of_le hcd] at ht
    exact hC x (hball x hx) t (Ioc_subset_Icc_self ht)
  · exact intervalIntegrable_const
  · have hnull : volume ({d} : Set ℝ) = 0 := by simp
    filter_upwards [(measure_eq_zero_iff_ae_notMem.mp hnull)] with t htne ht x hx
    rw [Set.uIoc_of_le hcd] at ht
    have hmem := hδsub (hball x hx)
    have htd : t ≠ d := fun h => htne (by rw [h]; exact rfl)
    exact hd x t hmem.1 hmem.2 ht.1 (lt_of_le_of_ne ht.2 htd)

/-! ### The slit-chart ring flux -/

/-- The **slit-chart ring flux** of a potential `u` at log-radius `ξ`: the angle integral of
`u · (r ∂_r u)` over the circle of radius `e^ξ`, parametrised by the geometric angle
`θ ∈ (0, 2π)` measured from the positive real axis — the chart adapted to a slit on the
positive real axis. -/
def ringFluxSlit (u : ℂ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ θ in Ioo 0 (2 * π),
    u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
      * fderiv ℝ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
          (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))

/-- The flux integrand is `2π`-periodic in the angle. -/
theorem fluxIntegrand_periodic (u : ℂ → ℝ) (ξ : ℝ) :
    Function.Periodic (fun θ : ℝ =>
      u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * fderiv ℝ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
            (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (2 * π) := by
  intro θ
  have hexp : Complex.exp ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
    have h : ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
        = ((ξ : ℂ) + (θ : ℂ) * Complex.I) + 2 * (π : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.exp_periodic _]
  simp only [hexp]

/-- **Chart gluing for the ring flux.** The slit-chart flux (angles in `(0, 2π)`) equals the
collar-chart flux (angles in `(−π, π)`): the flux integrand is `2π`-periodic in the angle, so
the two full-circle parametrisations integrate identically. -/
theorem ringFluxSlit_eq_ringFlux (u : ℂ → ℝ) (ξ : ℝ) :
    ringFluxSlit u ξ = ringFlux u ξ := by
  have hπ := Real.pi_pos
  unfold ringFluxSlit ringFlux
  rw [integral_Ioo_eq_intervalIntegral (by linarith : (0 : ℝ) ≤ 2 * π),
    integral_Ioo_eq_intervalIntegral (by linarith : -π ≤ π)]
  have hkey := (fluxIntegrand_periodic u ξ).intervalIntegral_add_eq 0 (-π)
  have hend : -π + 2 * π = π := by ring
  rw [zero_add, hend] at hkey
  exact hkey

/-! ### The collar of the Grötzsch ring -/

/-- The collar annulus `{s < |z| < 1}` avoids the slit `[0, s]`: it is contained in the
Grötzsch ring. -/
theorem roundAnnulus_subset_grotzschRing {s : ℝ} (hs0 : 0 ≤ s) :
    RoundAnnulus 0 s 1 ⊆ grotzschRing s := by
  intro z hz
  refine ⟨Metric.mem_ball.mpr hz.2, fun hmem => ?_⟩
  obtain ⟨a, c, _, hc, hac, rfl⟩ := hmem
  have hnorm : dist (a • (0 : ℂ) + c • (s : ℂ)) 0 ≤ s := by
    have hzero : a • (0 : ℂ) + c • (s : ℂ) = ((c * s : ℝ) : ℂ) := by
      simp [Complex.real_smul]
    rw [dist_zero_right, hzero, Complex.norm_real]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc hs0)]
    calc c * s ≤ 1 * s := mul_le_mul_of_nonneg_right (by linarith) hs0
      _ = s := one_mul s
  exact absurd hz.1 (not_lt.mpr hnorm)

/-- **Collar flux data for the Grötzsch potential.** For a potential `v` of the Grötzsch ring —
harmonic on the ring, continuous on the closed disk, `1` on the unit circle, with values in
`[0, 1]` — there is a slope `b` such that on the collar `(log s, 0)` the circle mean is
`2π + b·ξ`, the ring flux tends to `b` at the unit circle, and the outer-collar Dirichlet
energy is exactly `b − ringFlux v ξ`. -/
theorem grotzschPotential_collar_energy {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    (hvrange : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1) :
    ∃ b : ℝ, (∀ ξ ∈ Ioo (Real.log s) 0, logCircleMean 0 v ξ = 2 * π + b * ξ) ∧
      Tendsto (ringFlux v) (𝓝[<] (0 : ℝ)) (𝓝 b) ∧
      ∀ ξ ∈ Ioo (Real.log s) 0,
        dirichletEnergy v (RoundAnnulus 0 (Real.exp ξ) 1)
          = ENNReal.ofReal (b - ringFlux v ξ) := by
  have hsub := roundAnnulus_subset_grotzschRing hs0.le
  have hu : InnerProductSpace.HarmonicOnNhd v (RoundAnnulus 0 s 1) := fun z hz => hvh z (hsub hz)
  have hcont : ContinuousOn v {z : ℂ | s ≤ dist z 0 ∧ dist z 0 ≤ 1} := by
    refine hvc.mono fun z hz => ?_
    rw [closure_grotzschRing hs0.le]
    exact Metric.mem_closedBall.mpr hz.2
  have hrange : ∀ z ∈ RoundAnnulus 0 s 1, 0 ≤ v z ∧ v z ≤ 1 := fun z hz => hvrange z (hsub hz)
  obtain ⟨b, hb⟩ := exists_logCircleMean_slope hs0 hs1 hu hcont hv1
  exact ⟨b, hb, ringFlux_tendsto_slope hs0 hs1 hu hcont hv1 hrange hb,
    fun ξ hξ => dirichletEnergy_outerCollar_eq_ofReal_sub hs0 hs1 hu hcont hv1 hrange hb hξ⟩

/-! ### Odd reflection across the real axis: the Poisson integral of odd data -/

/-- The Poisson kernel about a conjugation-fixed centre is invariant under simultaneous
conjugation of the interior and boundary points. -/
theorem poissonKernel_conj {c : ℂ} (hc : (starRingEnd ℂ) c = c) (w z : ℂ) :
    poissonKernel c ((starRingEnd ℂ) w) ((starRingEnd ℂ) z) = poissonKernel c w z := by
  rw [poissonKernel_def, poissonKernel_def]
  have key : ∀ a : ℂ, ‖(starRingEnd ℂ) a - c‖ = ‖a - c‖ := by
    intro a
    calc ‖(starRingEnd ℂ) a - c‖ = ‖(starRingEnd ℂ) a - (starRingEnd ℂ) c‖ := by rw [hc]
      _ = ‖(starRingEnd ℂ) (a - c)‖ := by rw [map_sub]
      _ = ‖a - c‖ := RCLike.norm_conj _
  have h3 : ‖(starRingEnd ℂ) z - c - ((starRingEnd ℂ) w - c)‖ = ‖z - c - (w - c)‖ := by
    have hl : (starRingEnd ℂ) z - c - ((starRingEnd ℂ) w - c) = (starRingEnd ℂ) (z - w) := by
      rw [map_sub]
      ring
    have hr : z - c - (w - c) = z - w := by ring
    rw [hl, hr, RCLike.norm_conj]
  rw [key z, key w, h3]

/-- Conjugation reverses the angle of the circle parametrisation about a conjugation-fixed
centre. -/
theorem conj_circleMap {c : ℂ} (hc : (starRingEnd ℂ) c = c) (R θ : ℝ) :
    (starRingEnd ℂ) (circleMap c R θ) = circleMap c R (-θ) := by
  unfold circleMap
  rw [map_add, hc, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, Complex.conj_ofReal]
  have harg : (θ : ℂ) * -Complex.I = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [harg]

/-- **The Poisson integral of odd boundary data is odd.** About a conjugation-fixed centre, if
the boundary data is odd under conjugation on the circle, so is the Poisson integral:
`P(z̄) = −P(z)`. -/
theorem poissonIntegral_conj_neg {g : ℂ → ℝ} {c : ℂ} (hc : (starRingEnd ℂ) c = c) {R : ℝ}
    (hR : 0 ≤ R) (hodd : ∀ z ∈ Metric.sphere c R, g ((starRingEnd ℂ) z) = -g z) (w : ℂ) :
    poissonIntegral g c R ((starRingEnd ℂ) w) = -poissonIntegral g c R w := by
  unfold poissonIntegral
  rw [Real.circleAverage_def, Real.circleAverage_def, smul_eq_mul, smul_eq_mul, ← mul_neg]
  congr 1
  have hpt : ∀ θ : ℝ,
      poissonKernel c ((starRingEnd ℂ) w) (circleMap c R θ) * g (circleMap c R θ)
        = -(poissonKernel c w (circleMap c R (-θ)) * g (circleMap c R (-θ))) := by
    intro θ
    have hz := conj_circleMap hc R (-θ)
    rw [neg_neg] at hz
    rw [← hz, poissonKernel_conj hc, hodd _ (circleMap_mem_sphere c hR (-θ))]
    ring
  have hper : Function.Periodic
      (fun θ : ℝ => poissonKernel c w (circleMap c R θ) * g (circleMap c R θ)) (2 * π) :=
    (periodic_circleMap c R).comp fun z => poissonKernel c w z * g z
  calc ∫ θ in (0 : ℝ)..2 * π,
      poissonKernel c ((starRingEnd ℂ) w) (circleMap c R θ) * g (circleMap c R θ)
      = ∫ θ in (0 : ℝ)..2 * π,
          -(poissonKernel c w (circleMap c R (-θ)) * g (circleMap c R (-θ))) :=
        intervalIntegral.integral_congr fun θ _ => hpt θ
    _ = -∫ θ in (0 : ℝ)..2 * π,
          poissonKernel c w (circleMap c R (-θ)) * g (circleMap c R (-θ)) :=
        intervalIntegral.integral_neg
    _ = -∫ θ in (-(2 * π))..(-(0 : ℝ)),
          poissonKernel c w (circleMap c R θ) * g (circleMap c R θ) := by
        congr 1
        exact intervalIntegral.integral_comp_neg (a := 0) (b := 2 * π)
          (f := fun t : ℝ => poissonKernel c w (circleMap c R t) * g (circleMap c R t))
    _ = -∫ θ in (0 : ℝ)..2 * π,
          poissonKernel c w (circleMap c R θ) * g (circleMap c R θ) := by
        have hgl := hper.intervalIntegral_add_eq (-(2 * π)) 0
        have he1 : -(2 * π) + 2 * π = 0 := by ring
        have he2 : (0 : ℝ) + 2 * π = 2 * π := by ring
        rw [he1, he2] at hgl
        rw [neg_zero, hgl]

open Classical in
/-- The Dirichlet solution on a disk glued to its boundary data: the Poisson integral on the
open ball, the boundary data outside. -/
noncomputable def dirichletGlue (g : ℂ → ℝ) (c : ℂ) (R : ℝ) : ℂ → ℝ :=
  (Metric.ball c R).piecewise (poissonIntegral g c R) g

/-- On the open ball `ball c R`, the glued Dirichlet solution `dirichletGlue g c R` equals the
Poisson integral `poissonIntegral g c R` of the boundary data. -/
theorem dirichletGlue_eq_poisson {g : ℂ → ℝ} {c : ℂ} {R : ℝ} {z : ℂ}
    (hz : z ∈ Metric.ball c R) : dirichletGlue g c R z = poissonIntegral g c R z := by
  simp [dirichletGlue, Set.piecewise, hz]

/-- Off the open ball `ball c R` (on its boundary circle and its exterior), the glued Dirichlet
solution `dirichletGlue g c R` equals the boundary data `g`. -/
theorem dirichletGlue_eq_boundary {g : ℂ → ℝ} {c : ℂ} {R : ℝ} {z : ℂ}
    (hz : z ∉ Metric.ball c R) : dirichletGlue g c R z = g z := by
  simp [dirichletGlue, Set.piecewise, hz]

/-- Points of the sphere are not in the open ball. -/
theorem notMem_ball_of_mem_sphere {c z : ℂ} {R : ℝ} (hz : z ∈ Metric.sphere c R) :
    z ∉ Metric.ball c R := by
  intro hmem
  have h' : dist z c < R := Metric.mem_ball.mp hmem
  rw [Metric.mem_sphere.mp hz] at h'
  exact lt_irrefl R h'

/-- The glued Dirichlet solution is harmonic on the open ball. -/
theorem dirichletGlue_harmonicOnNhd (g : ℂ → ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hg : ContinuousOn g (Metric.sphere c R)) :
    InnerProductSpace.HarmonicOnNhd (dirichletGlue g c R) (Metric.ball c R) := by
  intro z hz
  have hP := poissonIntegral_harmonicOn g c hR hg z hz
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hP
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
  exact (dirichletGlue_eq_poisson hy).symm

/-- The glued Dirichlet solution is continuous on the closed ball: harmonicity gives interior
continuity, and the boundary limit of the Poisson integral matches the boundary data. -/
theorem dirichletGlue_continuousOn (g : ℂ → ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hg : ContinuousOn g (Metric.sphere c R)) :
    ContinuousOn (dirichletGlue g c R) (Metric.closedBall c R) := by
  intro z hz
  rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hz) with hlt | heq
  · have hzball : z ∈ Metric.ball c R := Metric.mem_ball.mpr hlt
    refine ContinuousAt.continuousWithinAt ?_
    have hP : ContinuousAt (poissonIntegral g c R) z :=
      (poissonIntegral_harmonicOn g c hR hg z hzball).1.continuousAt
    refine hP.congr ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hzball] with y hy
    exact (dirichletGlue_eq_poisson hy).symm
  · have hzs : z ∈ Metric.sphere c R := Metric.mem_sphere.mpr heq
    have h1 : ContinuousWithinAt (dirichletGlue g c R) (Metric.ball c R) z := by
      have hb := poissonIntegral_tendsto_boundary g c hR hg hzs
      have hgz : dirichletGlue g c R z = g z :=
        dirichletGlue_eq_boundary (notMem_ball_of_mem_sphere hzs)
      change Tendsto _ _ _
      rw [hgz]
      refine hb.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (dirichletGlue_eq_poisson hy).symm
    have h2 : ContinuousWithinAt (dirichletGlue g c R) (Metric.sphere c R) z := by
      refine (hg z hzs).congr ?_ ?_
      · intro y hy
        exact dirichletGlue_eq_boundary (notMem_ball_of_mem_sphere hy)
      · exact dirichletGlue_eq_boundary (notMem_ball_of_mem_sphere hzs)
    have hu := h1.union h2
    rwa [Metric.ball_union_sphere] at hu

/-- **Odd harmonic reflection across the real axis.** A function continuous on a closed disk
about a conjugation-fixed centre, harmonic off the real axis, vanishing on the real diameter,
and odd under conjugation is harmonic on the whole open disk: it agrees there with the Poisson
integral of its boundary values, by the maximum principle on the two half-disks and the odd
symmetry of the Poisson integral. -/
theorem harmonicOnNhd_of_odd_reflection {h : ℂ → ℝ} {c : ℂ} (hc : (starRingEnd ℂ) c = c)
    {R : ℝ} (hR : 0 < R)
    (hharm : InnerProductSpace.HarmonicOnNhd h {z | z ∈ Metric.ball c R ∧ z.im ≠ 0})
    (hcont : ContinuousOn h (Metric.closedBall c R))
    (hzero : ∀ z ∈ Metric.closedBall c R, z.im = 0 → h z = 0)
    (hodd : ∀ z ∈ Metric.closedBall c R, h ((starRingEnd ℂ) z) = -h z) :
    InnerProductSpace.HarmonicOnNhd h (Metric.ball c R) := by
  have hg : ContinuousOn h (Metric.sphere c R) := hcont.mono Metric.sphere_subset_closedBall
  have hPharm := dirichletGlue_harmonicOnNhd h c hR hg
  have hPcont := dirichletGlue_continuousOn h c hR hg
  -- oddness of the Poisson solution, hence its vanishing on the real diameter
  have hPodd : ∀ w ∈ Metric.ball c R,
      dirichletGlue h c R ((starRingEnd ℂ) w) = -dirichletGlue h c R w := by
    intro w hw
    have hwconj : (starRingEnd ℂ) w ∈ Metric.ball c R := by
      rw [Metric.mem_ball] at hw ⊢
      calc dist ((starRingEnd ℂ) w) c = dist ((starRingEnd ℂ) w) ((starRingEnd ℂ) c) := by
            rw [hc]
        _ = dist w c := by rw [dist_eq_norm, ← map_sub, RCLike.norm_conj, ← dist_eq_norm]
        _ < R := hw
    rw [dirichletGlue_eq_poisson hwconj, dirichletGlue_eq_poisson hw]
    exact poissonIntegral_conj_neg hc hR.le
      (fun z hz => hodd z (Metric.sphere_subset_closedBall hz)) w
  have hPzero : ∀ w ∈ Metric.ball c R, w.im = 0 → dirichletGlue h c R w = 0 := by
    intro w hw him
    have hwfix : (starRingEnd ℂ) w = w := Complex.conj_eq_iff_im.mpr him
    have hval := hPodd w hw
    rw [hwfix] at hval
    linarith
  -- maximum-principle comparison on a half-disk
  have key : ∀ S : Set ℂ, IsOpen S → (∀ z ∈ S, z.im ≠ 0) →
      (∀ z, z ∈ closure (Metric.ball c R ∩ S) → z ∉ Metric.ball c R ∩ S →
        z ∈ Metric.sphere c R ∨ z.im = 0) →
      ∀ w ∈ Metric.ball c R ∩ S, h w = dirichletGlue h c R w := by
    intro S hSopen hSim hfr w hw
    have hUopen : IsOpen (Metric.ball c R ∩ S) := Metric.isOpen_ball.inter hSopen
    have hUbdd : Bornology.IsBounded (Metric.ball c R ∩ S) :=
      Metric.isBounded_ball.subset Set.inter_subset_left
    have hclosU : closure (Metric.ball c R ∩ S) ⊆ Metric.closedBall c R :=
      closure_minimal (Set.inter_subset_left.trans Metric.ball_subset_closedBall)
        Metric.isClosed_closedBall
    have hdiff1 : InnerProductSpace.HarmonicOnNhd (fun z => h z - dirichletGlue h c R z)
        (Metric.ball c R ∩ S) := fun z hz =>
      (hharm z ⟨hz.1, hSim z hz.2⟩).sub (hPharm z hz.1)
    have hdiff2 : InnerProductSpace.HarmonicOnNhd (fun z => dirichletGlue h c R z - h z)
        (Metric.ball c R ∩ S) := fun z hz =>
      (hPharm z hz.1).sub (hharm z ⟨hz.1, hSim z hz.2⟩)
    have hfrbound : ∀ z ∈ frontier (Metric.ball c R ∩ S), h z - dirichletGlue h c R z = 0 := by
      intro z hz
      rw [hUopen.frontier_eq] at hz
      have hzcb : z ∈ Metric.closedBall c R := hclosU hz.1
      rcases hfr z hz.1 hz.2 with hs | him
      · rw [dirichletGlue_eq_boundary (notMem_ball_of_mem_sphere hs), sub_self]
      · rw [hzero z hzcb him]
        rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hzcb) with hlt | heq
        · rw [hPzero z (Metric.mem_ball.mpr hlt) him]
          ring
        · rw [dirichletGlue_eq_boundary
            (notMem_ball_of_mem_sphere (Metric.mem_sphere.mpr heq)), hzero z hzcb him]
          ring
    have hle1 := SubharmonicOn.le_of_frontier_le hUopen hUbdd
      (HarmonicOnNhd.subharmonicOn hdiff1)
      ((hcont.mono hclosU).sub (hPcont.mono hclosU))
      (fun z hz => le_of_eq (hfrbound z hz)) w hw
    have hfrbound2 : ∀ z ∈ frontier (Metric.ball c R ∩ S),
        dirichletGlue h c R z - h z ≤ 0 := by
      intro z hz
      have := hfrbound z hz
      linarith
    have hle2 := SubharmonicOn.le_of_frontier_le hUopen hUbdd
      (HarmonicOnNhd.subharmonicOn hdiff2)
      ((hPcont.mono hclosU).sub (hcont.mono hclosU))
      hfrbound2 w hw
    linarith
  -- frontier classification for the upper and lower half-disks
  have hfrUp : ∀ z, z ∈ closure (Metric.ball c R ∩ {z : ℂ | 0 < z.im}) →
      z ∉ Metric.ball c R ∩ {z : ℂ | 0 < z.im} → z ∈ Metric.sphere c R ∨ z.im = 0 := by
    intro z hzclos hznot
    have hzmem : z ∈ Metric.closedBall c R ∩ {z : ℂ | 0 ≤ z.im} := by
      refine closure_minimal (Set.inter_subset_inter Metric.ball_subset_closedBall
        fun y hy => le_of_lt hy) (Metric.isClosed_closedBall.inter
          (isClosed_le continuous_const Complex.continuous_im)) hzclos
    have him0 : (0 : ℝ) ≤ z.im := hzmem.2
    rcases eq_or_lt_of_le him0 with him | him
    · exact Or.inr him.symm
    · refine Or.inl (Metric.mem_sphere.mpr ?_)
      rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hzmem.1) with hlt | heq
      · exact absurd ⟨Metric.mem_ball.mpr hlt, him⟩ hznot
      · exact heq
  have hfrLow : ∀ z, z ∈ closure (Metric.ball c R ∩ {z : ℂ | z.im < 0}) →
      z ∉ Metric.ball c R ∩ {z : ℂ | z.im < 0} → z ∈ Metric.sphere c R ∨ z.im = 0 := by
    intro z hzclos hznot
    have hzmem : z ∈ Metric.closedBall c R ∩ {z : ℂ | z.im ≤ 0} := by
      refine closure_minimal (Set.inter_subset_inter Metric.ball_subset_closedBall
        fun y hy => le_of_lt hy) (Metric.isClosed_closedBall.inter
          (isClosed_le Complex.continuous_im continuous_const)) hzclos
    have him0 : z.im ≤ (0 : ℝ) := hzmem.2
    rcases eq_or_lt_of_le him0 with him | him
    · exact Or.inr him
    · refine Or.inl (Metric.mem_sphere.mpr ?_)
      rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hzmem.1) with hlt | heq
      · exact absurd ⟨Metric.mem_ball.mpr hlt, him⟩ hznot
      · exact heq
  -- equality with the Poisson solution on the whole disk
  have hball_eq : ∀ w ∈ Metric.ball c R, h w = dirichletGlue h c R w := by
    intro w hw
    rcases lt_trichotomy w.im 0 with hneg | him | hpos
    · exact key {z : ℂ | z.im < 0} (isOpen_lt Complex.continuous_im continuous_const)
        (fun z hz => ne_of_lt hz) hfrLow w ⟨hw, hneg⟩
    · rw [hzero w (Metric.ball_subset_closedBall hw) him, hPzero w hw him]
    · exact key {z : ℂ | 0 < z.im} (isOpen_lt continuous_const Complex.continuous_im)
        (fun z hz => ne_of_gt hz) hfrUp w ⟨hw, hpos⟩
  intro z hz
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp (hPharm z hz)
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
  exact (hball_eq y hy).symm

/-! ### Bank regularity of the log-polar gradient via odd reflection -/

/-- The **odd reflection across the real axis** of a real function: `v` on the closed upper
half-plane, minus `v` of the conjugate on the lower half-plane. -/
noncomputable def reflectReal (v : ℂ → ℝ) (z : ℂ) : ℝ :=
  if 0 ≤ z.im then v z else -v ((starRingEnd ℂ) z)

/-- The odd reflection agrees with `v` on the closed upper half-plane. -/
theorem reflectReal_of_im_nonneg {v : ℂ → ℝ} {z : ℂ} (hz : 0 ≤ z.im) :
    reflectReal v z = v z := by
  simp [reflectReal, hz]

/-- The odd reflection is odd under conjugation whenever `v` vanishes on the real axis. -/
theorem reflectReal_conj {v : ℂ → ℝ} (hv0 : ∀ z : ℂ, z.im = 0 → v z = 0) (z : ℂ) :
    reflectReal v ((starRingEnd ℂ) z) = -reflectReal v z := by
  simp only [reflectReal, Complex.conj_im, Complex.conj_conj]
  rcases lt_trichotomy z.im 0 with h | h | h
  · rw [if_pos (by linarith : 0 ≤ -z.im), if_neg (by linarith : ¬ 0 ≤ z.im), neg_neg]
  · rw [if_pos (by rw [h, neg_zero]), if_pos (le_of_eq h.symm)]
    have hz : (starRingEnd ℂ) z = z := Complex.conj_eq_iff_im.mpr h
    rw [hz, hv0 z h, neg_zero]
  · rw [if_neg (by linarith : ¬ 0 ≤ -z.im), if_pos (le_of_lt h)]

/-- The odd reflection vanishes on the real axis when `v` does. -/
theorem reflectReal_zero_of_im_zero {v : ℂ → ℝ} (hv0 : ∀ z : ℂ, z.im = 0 → v z = 0)
    {z : ℂ} (hz : z.im = 0) : reflectReal v z = 0 := by
  rw [reflectReal_of_im_nonneg (le_of_eq hz.symm), hv0 z hz]

/-- **Bank ball geometry.** At an interior slit point `x₀ ∈ (0, s)` (on the positive real axis),
the ball of radius `min x₀ (s − x₀)` about `x₀` lies in the open unit disk and meets the slit only
in its real diameter: off the real axis it is contained in the Grötzsch ring. -/
theorem ball_bank_subset_grotzschRing {s x₀ : ℝ} (hs1 : s < 1) (hx0 : 0 < x₀) (hxs : x₀ < s) :
    (∀ z ∈ Metric.ball ((x₀ : ℝ) : ℂ) (min x₀ (s - x₀)), 0 < z.re ∧ z.re < s ∧ ‖z‖ < 1) ∧
      {z : ℂ | z ∈ Metric.ball ((x₀ : ℝ) : ℂ) (min x₀ (s - x₀)) ∧ z.im ≠ 0} ⊆ grotzschRing s := by
  set ρ : ℝ := min x₀ (s - x₀) with hρ
  have hρpos : 0 < ρ := lt_min hx0 (by linarith)
  have hρ1 : ρ ≤ x₀ := min_le_left _ _
  have hρ2 : ρ ≤ s - x₀ := min_le_right _ _
  have hcore : ∀ z ∈ Metric.ball ((x₀ : ℝ) : ℂ) ρ, 0 < z.re ∧ z.re < s ∧ ‖z‖ < 1 := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hre : |z.re - x₀| ≤ ‖z - (x₀ : ℂ)‖ := by
      have := Complex.abs_re_le_norm (z - (x₀ : ℂ))
      simpa [Complex.sub_re] using this
    have hre1 : |z.re - x₀| < ρ := lt_of_le_of_lt hre hz
    rw [abs_sub_lt_iff] at hre1
    refine ⟨by linarith [hre1.1, hρ1], by linarith [hre1.2, hρ2], ?_⟩
    calc ‖z‖ = ‖(z - (x₀ : ℂ)) + (x₀ : ℂ)‖ := by ring_nf
      _ ≤ ‖z - (x₀ : ℂ)‖ + ‖(x₀ : ℂ)‖ := norm_add_le _ _
      _ < ρ + x₀ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; linarith
      _ ≤ s := by linarith [hρ2]
      _ < 1 := hs1
  refine ⟨hcore, fun z hz => ?_⟩
  obtain ⟨hzball, hzim⟩ := hz
  obtain ⟨hre0, hres, hnorm⟩ := hcore z hzball
  refine ⟨mem_ball_zero_iff.mpr hnorm, fun hslit => ?_⟩
  have hslit' : z ∈ grotzschInner s := hslit
  rw [grotzschInner_eq (le_of_lt (lt_trans hx0 hxs))] at hslit'
  exact hzim hslit'.1

/-- **Continuity of the odd reflection on the bank ball.** For the Grötzsch potential `v` (harmonic
on the ring, continuous on the closed disk, zero on the slit), the odd reflection `reflectReal v`
is continuous on the closed bank ball about an interior slit point `x₀ ∈ (0, s)`. -/
theorem continuousOn_reflectReal_bankBall {s x₀ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hx0 : 0 < x₀) (hxs : x₀ < s) {v : ℂ → ℝ}
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z : ℂ, z.im = 0 → 0 ≤ z.re → z.re ≤ s → v z = 0) :
    ContinuousOn (reflectReal v) (Metric.closedBall ((x₀ : ℝ) : ℂ) (min x₀ (s - x₀))) := by
  set ρ : ℝ := min x₀ (s - x₀) with hρ
  have hρpos : 0 < ρ := lt_min hx0 (by linarith)
  have hρ1 : ρ ≤ x₀ := min_le_left _ _
  have hρ2 : ρ ≤ s - x₀ := min_le_right _ _
  -- the closed ball lies in the closed unit disk and every point has real part in (0, s)
  have hclsub : ∀ z ∈ Metric.closedBall ((x₀ : ℝ) : ℂ) ρ,
      0 ≤ z.re ∧ z.re ≤ s ∧ ‖z‖ < 1 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre : |z.re - x₀| ≤ ‖z - (x₀ : ℂ)‖ := by
      have := Complex.abs_re_le_norm (z - (x₀ : ℂ)); simpa [Complex.sub_re] using this
    have hre1 : |z.re - x₀| ≤ ρ := le_trans hre hz
    rw [abs_le] at hre1
    refine ⟨by linarith [hre1.1, hρ1], by linarith [hre1.2, hρ2], ?_⟩
    calc ‖z‖ = ‖(z - (x₀ : ℂ)) + (x₀ : ℂ)‖ := by ring_nf
      _ ≤ ‖z - (x₀ : ℂ)‖ + ‖(x₀ : ℂ)‖ := norm_add_le _ _
      _ ≤ ρ + x₀ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; linarith
      _ ≤ s := by linarith [hρ2]
      _ < 1 := hs1
  have hvc' : ContinuousOn v (Metric.closedBall (0 : ℂ) 1) := by
    rwa [← closure_grotzschRing hs0.le]
  have hcball : Metric.closedBall ((x₀ : ℝ) : ℂ) ρ ⊆ Metric.closedBall (0 : ℂ) 1 :=
    fun z hz => Metric.mem_closedBall.mpr (by
      rw [dist_zero_right]; exact le_of_lt (hclsub z hz).2.2)
  have hvcball : ContinuousOn v (Metric.closedBall ((x₀ : ℝ) : ℂ) ρ) := hvc'.mono hcball
  -- continuity of `-v ∘ conj` on the ball
  have hconjmaps : Set.MapsTo (starRingEnd ℂ) (Metric.closedBall ((x₀ : ℝ) : ℂ) ρ)
      (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right, RCLike.norm_conj]
    exact le_of_lt (hclsub z hz).2.2
  have hnegconjc : ContinuousOn (fun z => -v ((starRingEnd ℂ) z))
      (Metric.closedBall ((x₀ : ℝ) : ℂ) ρ) :=
    (hvc'.comp Complex.continuous_conj.continuousOn hconjmaps).neg
  -- glue on the closed upper and lower half-balls
  have hup : ContinuousOn (reflectReal v)
      (Metric.closedBall ((x₀ : ℝ) : ℂ) ρ ∩ {z : ℂ | 0 ≤ z.im}) := by
    refine (hvcball.mono Set.inter_subset_left).congr fun z hz => ?_
    exact reflectReal_of_im_nonneg hz.2
  have hlow : ContinuousOn (reflectReal v)
      (Metric.closedBall ((x₀ : ℝ) : ℂ) ρ ∩ {z : ℂ | z.im ≤ 0}) := by
    refine (hnegconjc.mono Set.inter_subset_left).congr fun z hz => ?_
    have hzle : z.im ≤ 0 := hz.2
    have hbz := hclsub z hz.1
    rcases eq_or_lt_of_le hzle with him | him
    · have hvz : v z = 0 := hv0 z him hbz.1 hbz.2.1
      rw [reflectReal_of_im_nonneg (le_of_eq him.symm), hvz]
      have hzfix : (starRingEnd ℂ) z = z := Complex.conj_eq_iff_im.mpr him
      change (0 : ℝ) = -v ((starRingEnd ℂ) z)
      rw [hzfix, hvz, neg_zero]
    · rw [reflectReal, if_neg (by linarith)]
  have hcover : Metric.closedBall ((x₀ : ℝ) : ℂ) ρ
      = (Metric.closedBall ((x₀ : ℝ) : ℂ) ρ ∩ {z : ℂ | 0 ≤ z.im})
        ∪ (Metric.closedBall ((x₀ : ℝ) : ℂ) ρ ∩ {z : ℂ | z.im ≤ 0}) := by
    rw [← Set.inter_union_distrib_left]
    ext z; simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · intro hz; exact ⟨hz, le_total 0 z.im⟩
    · intro hz; exact hz.1
  rw [hcover]
  refine hup.union_of_isClosed hlow ?_ ?_
  · exact (Metric.isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im))
  · exact (Metric.isClosed_closedBall.inter (isClosed_le Complex.continuous_im continuous_const))

/-- **Harmonicity of the odd reflection off the real axis.** On the bank ball about an interior
slit point, away from the real axis the odd reflection of the Grötzsch potential is harmonic: on
the upper half it equals `v` (harmonic on the ring), on the lower half `−v ∘ conj` (harmonic since
conjugation is an isometry). -/
theorem harmonicOnNhd_reflectReal_offAxis {s x₀ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hx0 : 0 < x₀) (hxs : x₀ < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) :
    InnerProductSpace.HarmonicOnNhd (reflectReal v)
      {z | z ∈ Metric.ball ((x₀ : ℝ) : ℂ) (min x₀ (s - x₀)) ∧ z.im ≠ 0} := by
  obtain ⟨_, hsub⟩ := ball_bank_subset_grotzschRing hs1 hx0 hxs
  intro z hz
  obtain ⟨hzball, hzim⟩ := hz
  have hzring : z ∈ grotzschRing s := hsub ⟨hzball, hzim⟩
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · -- lower half: `reflectReal v = -v ∘ conj` near `z`, harmonic by conjugation symmetry
    have hconjring : (starRingEnd ℂ) z ∈ grotzschRing s := conj_mem_grotzschRing hs0.le hzring
    have hharmconj : InnerProductSpace.HarmonicAt (fun w => v ((starRingEnd ℂ) w)) z := by
      have hpt : InnerProductSpace.HarmonicAt v (Complex.conjLIE z) := by
        rw [show Complex.conjLIE z = (starRingEnd ℂ) z from Complex.conjLIE_apply z]
        exact hvh _ hconjring
      have h := harmonicAt_comp_linearIsometryEquiv Complex.conjLIE hpt
      refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp h
      exact Filter.Eventually.of_forall fun y => by
        simp [Function.comp_apply, Complex.conjLIE_apply]
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hharmconj.neg
    filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hneg] with y hy
    rw [Pi.neg_apply, reflectReal, if_neg (by exact not_le.mpr hy)]
  · exact absurd hzero hzim
  · -- upper half: `reflectReal v = v` near `z`, harmonic on the ring
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp (hvh z hzring)
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hpos] with y hy
    rw [reflectReal_of_im_nonneg (le_of_lt hy)]

/-- **The odd reflection is harmonic across the bank.** By the odd-reflection principle, the odd
reflection of the Grötzsch potential is harmonic on the entire bank ball about an interior slit
point, in particular across the real axis. -/
theorem harmonicOnNhd_reflectReal_bankBall {s x₀ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hx0 : 0 < x₀) (hxs : x₀ < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z : ℂ, z.im = 0 → 0 ≤ z.re → z.re ≤ s → v z = 0) :
    InnerProductSpace.HarmonicOnNhd (reflectReal v)
      (Metric.ball ((x₀ : ℝ) : ℂ) (min x₀ (s - x₀))) := by
  set ρ : ℝ := min x₀ (s - x₀) with hρ
  have hρpos : 0 < ρ := lt_min hx0 (by linarith)
  have hcfix : (starRingEnd ℂ) ((x₀ : ℝ) : ℂ) = ((x₀ : ℝ) : ℂ) :=
    Complex.conj_eq_iff_im.mpr (by simp)
  -- inside the closed bank ball every point has real part in `[0, s]`
  have hclre : ∀ z ∈ Metric.closedBall ((x₀ : ℝ) : ℂ) ρ, 0 ≤ z.re ∧ z.re ≤ s := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre : |z.re - x₀| ≤ ‖z - (x₀ : ℂ)‖ := by
      have := Complex.abs_re_le_norm (z - (x₀ : ℂ)); simpa [Complex.sub_re] using this
    have hre1 : |z.re - x₀| ≤ ρ := le_trans hre hz
    rw [abs_le] at hre1
    exact ⟨by linarith [hre1.1, min_le_left x₀ (s - x₀)],
      by linarith [hre1.2, min_le_right x₀ (s - x₀)]⟩
  refine harmonicOnNhd_of_odd_reflection hcfix hρpos
    (harmonicOnNhd_reflectReal_offAxis hs0 hs1 hx0 hxs hvh)
    (continuousOn_reflectReal_bankBall hs0 hs1 hx0 hxs hvc hv0) ?_ ?_
  · intro z hzcl hzim
    have hbz := hclre z hzcl
    rw [reflectReal_of_im_nonneg (le_of_eq hzim.symm), hv0 z hzim hbz.1 hbz.2]
  · intro z hzcl
    simp only [reflectReal, Complex.conj_im, Complex.conj_conj]
    rcases lt_trichotomy z.im 0 with h | h | h
    · rw [if_pos (by linarith : 0 ≤ -z.im), if_neg (by linarith : ¬ 0 ≤ z.im), neg_neg]
    · have hbz := hclre z hzcl
      rw [if_pos (by rw [h, neg_zero]), if_pos (le_of_eq h.symm)]
      have hzfix : (starRingEnd ℂ) z = z := Complex.conj_eq_iff_im.mpr h
      rw [hzfix, hv0 z h hbz.1 hbz.2, neg_zero]
    · rw [if_neg (by linarith : ¬ 0 ≤ -z.im), if_pos (le_of_lt h)]

/-- The norm of the holomorphic gradient equals the operator norm of the real Fréchet derivative. -/
theorem norm_gradC_eq_norm_fderiv (v : ℂ → ℝ) (z : ℂ) :
    ‖gradC v z‖ = ‖fderiv ℝ v z‖ := by
  have hnorm : ‖fderiv ℝ v z‖ ^ 2 = Complex.normSq (gradC v z) := by
    have hbasis := Complex.orthonormalBasisOneI.norm_dual (fderiv ℝ v z)
    rw [Fin.sum_univ_two] at hbasis
    simp only [Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hbasis
    rw [hbasis]
    simp only [gradC, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hgnorm : ‖gradC v z‖ ^ 2 = Complex.normSq (gradC v z) := (Complex.normSq_eq_norm_sq _).symm
  nlinarith [hnorm, hgnorm, norm_nonneg (gradC v z), norm_nonneg (fderiv ℝ v z)]

/-- **Conjugation invariance of the gradient norm.** For a potential invariant under conjugation on
the closed disk (as the Grötzsch potential is), the norm of the holomorphic gradient is the same at
conjugate interior points. -/
theorem norm_gradC_conj {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    {z : ℂ} (hz : z ∈ grotzschRing s) :
    ‖gradC v ((starRingEnd ℂ) z)‖ = ‖gradC v z‖ := by
  have hconjz : (starRingEnd ℂ) z ∈ grotzschRing s := conj_mem_grotzschRing hs0.le hz
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
  rw [norm_gradC_eq_norm_fderiv, norm_gradC_eq_norm_fderiv, hfeq,
    LinearIsometryEquiv.toContinuousLinearMap_toLinearIsometry,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

/-- **Local off-axis bound for the gradient near the annulus.** For the Grötzsch potential `v` and
a point `z₀` of the closed annulus `{r₁ ≤ |z| ≤ r₂}` with `0 < r₁` and `r₂ < s`, there is a
neighbourhood of `z₀` and a constant bounding `‖gradC v‖` off the real axis: away from the slit `v`
is harmonic, near an interior slit point the odd reflection is harmonic across the bank and the
gradient norm is conjugation-invariant. -/
theorem exists_localBound_gradC {s r₁ r₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hr₁ : 0 < r₁) (hr₂ : r₂ < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    {z₀ : ℂ} (hz₀ : r₁ ≤ ‖z₀‖ ∧ ‖z₀‖ ≤ r₂) :
    ∃ U ∈ 𝓝 z₀, ∃ C : ℝ, ∀ z ∈ U, z.im ≠ 0 → ‖gradC v z‖ ≤ C := by
  have hz₀norm1 : ‖z₀‖ < 1 := lt_trans (lt_of_le_of_lt hz₀.2 hr₂) hs1
  have hz₀pos : 0 < ‖z₀‖ := lt_of_lt_of_le hr₁ hz₀.1
  by_cases hax : z₀.im = 0 ∧ 0 ≤ z₀.re ∧ z₀.re ≤ s
  · -- interior slit point: `z₀.re ∈ (0, s)`; reflect across the bank
    obtain ⟨him, hre0, _⟩ := hax
    have hnre : ‖z₀‖ = z₀.re := by
      have hz₀re : z₀ = ((z₀.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
      rw [hz₀re, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hre0, Complex.ofReal_re]
    have hrepos : 0 < z₀.re := by rw [hnre] at hz₀pos; exact hz₀pos
    have hres : z₀.re < s := by rw [hnre] at hz₀; exact lt_of_le_of_lt hz₀.2 hr₂
    have hz₀eq : ((z₀.re : ℝ) : ℂ) = z₀ := (Complex.ext (by simp) (by simp [him])).symm
    set x₀ : ℝ := z₀.re with hx₀
    set ρ : ℝ := min x₀ (s - x₀) with hρ
    have hρpos : 0 < ρ := lt_min hrepos (by linarith)
    have hWharm := harmonicOnNhd_reflectReal_bankBall hs0 hs1 hrepos hres hvh hvc
      (fun z hz hz0 hzs => hv0 z (by rw [grotzschInner_eq hs0.le]; exact ⟨hz, hz0, hzs⟩))
    -- `gradC (reflectReal v)` is continuous on the ball, hence bounded on a smaller closed ball
    have hgWcont : ContinuousOn (gradC (reflectReal v))
        (Metric.ball ((x₀ : ℝ) : ℂ) ρ) := fun z hz =>
      ((gradC_differentiableOn hWharm).differentiableAt
        (Metric.isOpen_ball.mem_nhds hz)).continuousAt.continuousWithinAt
    set ρ' : ℝ := ρ / 2 with hρ'
    have hρ'pos : 0 < ρ' := by positivity
    have hsubball : Metric.closedBall ((x₀ : ℝ) : ℂ) ρ' ⊆ Metric.ball ((x₀ : ℝ) : ℂ) ρ :=
      fun z hz => Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by
        rw [hρ']; linarith))
    obtain ⟨C, hC⟩ := (isCompact_closedBall _ _).exists_bound_of_continuousOn
      (hgWcont.mono hsubball)
    -- the closed ball `closedBall x₀ ρ'` is symmetric under conjugation
    have hconjcb : ∀ z ∈ Metric.closedBall ((x₀ : ℝ) : ℂ) ρ',
        (starRingEnd ℂ) z ∈ Metric.closedBall ((x₀ : ℝ) : ℂ) ρ' := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
      have : (starRingEnd ℂ) z - (x₀ : ℂ) = (starRingEnd ℂ) (z - (x₀ : ℂ)) := by
        rw [map_sub, Complex.conj_ofReal]
      rw [this, RCLike.norm_conj]; exact hz
    obtain ⟨_, hringsub⟩ := ball_bank_subset_grotzschRing hs1 hrepos hres
    -- `gradC v` bounded on the upper part of the ball by `C`
    have hupbound : ∀ z ∈ Metric.closedBall ((x₀ : ℝ) : ℂ) ρ', 0 < z.im →
        ‖gradC v z‖ ≤ C := by
      intro z hzcb hup
      have hgeq : gradC v z = gradC (reflectReal v) z := by
        have hnb : v =ᶠ[𝓝 z] reflectReal v := by
          filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hup]
            with w hw
          rw [reflectReal_of_im_nonneg (le_of_lt hw)]
        rw [gradC, gradC, hnb.fderiv_eq]
      rw [hgeq]; exact hC z hzcb
    have hnbhd : Metric.ball ((x₀ : ℝ) : ℂ) ρ' ∈ 𝓝 z₀ := by
      rw [← hz₀eq]; exact Metric.ball_mem_nhds _ hρ'pos
    refine ⟨Metric.ball ((x₀ : ℝ) : ℂ) ρ', hnbhd, C, fun z hzU hzim => ?_⟩
    have hzcb : z ∈ Metric.closedBall ((x₀ : ℝ) : ℂ) ρ' := Metric.ball_subset_closedBall hzU
    rcases lt_trichotomy z.im 0 with hlow | hz0 | hup
    · -- lower half: conjugation invariance reduces to the upper bound at `conj z`
      have hzring : z ∈ grotzschRing s := hringsub ⟨hsubball hzcb, hzim⟩
      rw [← norm_gradC_conj hs0 hs1 hvh hvc hv0 hv1 hzring]
      exact hupbound _ (hconjcb z hzcb) (by simp [Complex.conj_im]; linarith)
    · exact absurd hz0 hzim
    · exact hupbound z hzcb hup
  · -- off-slit point: `z₀ ∈ grotzschRing s`, `gradC v` continuous there
    have hz₀ring : z₀ ∈ grotzschRing s := by
      refine ⟨mem_ball_zero_iff.mpr hz₀norm1, fun hslit => ?_⟩
      have hslit' : z₀ ∈ grotzschInner s := hslit
      rw [grotzschInner_eq hs0.le] at hslit'
      exact hax hslit'
    have hcont : ContinuousAt (fun z => ‖gradC v z‖) z₀ :=
      (((gradC_differentiableOn hvh).differentiableAt
        ((isOpen_grotzschRing hs0.le).mem_nhds hz₀ring)).continuousAt).norm
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδpos, hδ⟩ := hcont 1 one_pos
    refine ⟨Metric.ball z₀ δ, Metric.ball_mem_nhds _ hδpos, ‖gradC v z₀‖ + 1, fun z hz _ => ?_⟩
    have := hδ (Metric.mem_ball.mp hz)
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]

/-- **Global off-axis gradient bound on the closed annulus.** The holomorphic gradient of the
Grötzsch potential is bounded, off the real axis, on the closed annulus `{r₁ ≤ |z| ≤ r₂}` with
`0 < r₁` and `r₂ < s`: the local bounds patch together by compactness. -/
theorem exists_bound_gradC_annulus {s r₁ r₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hr₁ : 0 < r₁) (hr₂ : r₂ < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1) :
    ∃ C : ℝ, ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ → z.im ≠ 0 → ‖gradC v z‖ ≤ C := by
  set A : Set ℂ := {z : ℂ | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂} with hA
  have hAcompact : IsCompact A := by
    have h1 : IsClosed {z : ℂ | r₁ ≤ ‖z‖} := isClosed_le continuous_const continuous_norm
    have h2 : IsClosed {z : ℂ | ‖z‖ ≤ r₂} := isClosed_le continuous_norm continuous_const
    refine (Metric.isCompact_of_isClosed_isBounded (h1.inter h2) ?_)
    refine (Metric.isBounded_iff.mpr ⟨2 * r₂, fun x hx y hy => ?_⟩)
    calc dist x y ≤ ‖x‖ + ‖y‖ := by rw [dist_eq_norm]; exact (norm_sub_le x y)
      _ ≤ 2 * r₂ := by have := hx.2; have := hy.2; linarith
  -- local bounds at every point of the annulus
  have hloc : ∀ z₀ ∈ A, ∃ U ∈ 𝓝 z₀, ∃ C : ℝ, ∀ z ∈ U, z.im ≠ 0 → ‖gradC v z‖ ≤ C :=
    fun z₀ hz₀ => exists_localBound_gradC hs0 hs1 hr₁ hr₂ hvh hvc hv0 hv1 hz₀
  choose! U hU C hC using hloc
  obtain ⟨t, htA, htcov⟩ := hAcompact.elim_nhds_subcover U (fun z hz => hU z hz)
  refine ⟨t.sum (fun z => max (C z) 0), fun z hz1 hz2 hzim => ?_⟩
  have hzA : z ∈ A := ⟨hz1, hz2⟩
  obtain ⟨z₀, hz₀t, hz₀U⟩ := Set.mem_iUnion₂.mp (htcov hzA)
  have hbound : ‖gradC v z‖ ≤ C z₀ := hC z₀ (htA z₀ hz₀t) z hz₀U hzim
  calc ‖gradC v z‖ ≤ C z₀ := hbound
    _ ≤ max (C z₀) 0 := le_max_left _ _
    _ ≤ t.sum (fun z => max (C z) 0) :=
        Finset.single_le_sum (fun i _ => le_max_right _ _) hz₀t

end RiemannDynamics

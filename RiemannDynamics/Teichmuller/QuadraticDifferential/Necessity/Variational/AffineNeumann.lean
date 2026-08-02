/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Variational.Schwarzian
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Symmetrize

/-!
# Neumann-series toolkit for affine Beltrami families

Supporting lemmas for the affine solution family: analyticity and termwise
differentiation of geometrically bounded power series, integrability of the quartic
kernel, differentiation of Cauchy-type integrals under the integral sign, the affine
Neumann tier producing the principal-solution power series with geometric bounds,
affine post-composition of quasiconformal solutions, uniform bounds for normalized
quasiconformal maps on balls, and the Vitali upgrade from pointwise to locally uniform
convergence for bounded holomorphic families.

* `exists_principal_solution_power_series` — the fixed-point coefficient fields with
  geometric bounds and the principal-solution power series.
* `tendstoLocallyUniformlyOn_of_bounded_of_tendsto` — the Vitali upgrade.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-- An `Lᵖ` function vanishing outside a ball lies in `L^q` for every exponent
`q ≤ p`. -/
theorem memLp_mono_exponent_of_ball_support (u : ℂ → ℂ) (p q : ℝ≥0∞) (R : ℝ)
    (hqp : q ≤ p) (hu : MemLp u p volume) (husupp : ∀ z : ℂ, R < ‖z‖ → u z = 0) :
    MemLp u q volume := by
  classical
  have hBmeas : MeasurableSet (Metric.closedBall (0 : ℂ) (max R 0)) :=
    measurableSet_closedBall
  haveI : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℂ) (max R 0))) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hind : u = (Metric.closedBall (0 : ℂ) (max R 0)).indicator u := by
    funext ζ
    by_cases hζ : ζ ∈ Metric.closedBall (0 : ℂ) (max R 0)
    · rw [Set.indicator_of_mem hζ]
    · rw [Set.indicator_of_notMem hζ]
      refine husupp ζ ?_
      have hm : max R 0 < ‖ζ‖ := by
        simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hζ
      exact lt_of_le_of_lt (le_max_left R 0) hm
  rw [hind]
  exact (memLp_indicator_iff_restrict hBmeas).2 ((hu.restrict _).mono_exponent hqp)

/-- A series `∑ tⁿ⁺¹ aₙ` with geometrically bounded coefficients is analytic wherever
`‖t₀‖ * ρ < 1`. -/
theorem analyticAt_tsum_pow_succ_mul_of_le_geometric (a : ℕ → ℂ) (M ρ : ℝ)
    (hρ : 0 ≤ ρ) (hbound : ∀ n : ℕ, ‖a n‖ ≤ M * ρ ^ n) (t₀ : ℂ) (ht₀ : ‖t₀‖ * ρ < 1) :
    AnalyticAt ℂ (fun t : ℂ => ∑' n : ℕ, t ^ (n + 1) * a n) t₀ := by
  classical
  have hM : 0 ≤ M := le_trans (norm_nonneg (a 0)) (by simpa using hbound 0)
  obtain ⟨r, hr₁, hr₂⟩ : ∃ r : ℝ, ‖t₀‖ < r ∧ r * ρ ≤ 1 := by
    rcases eq_or_lt_of_le hρ with hρ0 | hρpos
    · exact ⟨‖t₀‖ + 1, by linarith, by rw [← hρ0, mul_zero]; norm_num⟩
    · have hinv : ‖t₀‖ < ρ⁻¹ := by
        have h2 : ‖t₀‖ * ρ * ρ⁻¹ < 1 * ρ⁻¹ :=
          mul_lt_mul_of_pos_right ht₀ (inv_pos.mpr hρpos)
        rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hρpos), mul_one, one_mul] at h2
      refine ⟨(‖t₀‖ + ρ⁻¹) / 2, by linarith, ?_⟩
      have hrle : (‖t₀‖ + ρ⁻¹) / 2 ≤ ρ⁻¹ := by linarith
      calc (‖t₀‖ + ρ⁻¹) / 2 * ρ ≤ ρ⁻¹ * ρ := mul_le_mul_of_nonneg_right hrle hρ
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hρpos)
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg t₀) hr₁
  have hle : ENNReal.ofReal r ≤ (FormalMultilinearSeries.ofScalars ℂ a).radius := by
    have hb : ∀ n : ℕ, ‖FormalMultilinearSeries.ofScalars ℂ a n‖ * (r.toNNReal : ℝ) ^ n ≤ M := by
      intro n
      rw [FormalMultilinearSeries.ofScalars_norm ℂ a n, Real.coe_toNNReal r hr0.le]
      calc ‖a n‖ * r ^ n ≤ M * ρ ^ n * r ^ n :=
            mul_le_mul_of_nonneg_right (hbound n) (pow_nonneg hr0.le n)
        _ = M * (ρ * r) ^ n := by rw [mul_pow]; ring
        _ ≤ M * 1 := mul_le_mul_of_nonneg_left
            (pow_le_one₀ (mul_nonneg hρ hr0.le) (by rw [mul_comm]; exact hr₂)) hM
        _ = M := mul_one M
    exact (FormalMultilinearSeries.ofScalars ℂ a).le_radius_of_bound M hb
  have hrad_pos : 0 < (FormalMultilinearSeries.ofScalars ℂ a).radius :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hr0) hle
  have hmem : t₀ ∈ Metric.eball (0 : ℂ) (FormalMultilinearSeries.ofScalars ℂ a).radius := by
    apply Metric.eball_subset_eball hle
    rw [Metric.mem_eball, edist_lt_ofReal, dist_zero_right]
    exact hr₁
  have hsum_an : AnalyticAt ℂ (FormalMultilinearSeries.ofScalars ℂ a).sum t₀ :=
    ((FormalMultilinearSeries.ofScalars ℂ a).hasFPowerSeriesOnBall
      hrad_pos).analyticAt_of_mem hmem
  have hfun : (fun t : ℂ => ∑' n : ℕ, t ^ (n + 1) * a n)
      = fun t : ℂ => t * (FormalMultilinearSeries.ofScalars ℂ a).sum t := by
    funext t
    have hps : (FormalMultilinearSeries.ofScalars ℂ a).sum t = ∑' n : ℕ, a n * t ^ n := by
      have h := FormalMultilinearSeries.ofScalars_sum_eq a t
      simp only [smul_eq_mul] at h
      exact h
    calc ∑' n : ℕ, t ^ (n + 1) * a n
        = ∑' n : ℕ, t * (a n * t ^ n) := tsum_congr fun n => by ring
      _ = t * ∑' n : ℕ, a n * t ^ n := tsum_mul_left
      _ = t * (FormalMultilinearSeries.ofScalars ℂ a).sum t := by rw [hps]
  rw [hfun]
  exact analyticAt_id.mul hsum_an

/-- A series `∑ tⁿ cₙ` with geometrically bounded tail coefficients is analytic
wherever `‖t₀‖ * ρ < 1`. -/
theorem analyticAt_tsum_pow_mul_of_le_geometric (c : ℕ → ℂ) (M ρ : ℝ) (hρ : 0 ≤ ρ)
    (hb : ∀ n : ℕ, ‖c (n + 1)‖ ≤ M * ρ ^ n) (t₀ : ℂ) (ht₀ : ‖t₀‖ * ρ < 1) :
    AnalyticAt ℂ (fun t : ℂ => ∑' n : ℕ, t ^ n * c n) t₀ := by
  classical
  have hAn : AnalyticAt ℂ (fun t : ℂ => c 0 + ∑' n : ℕ, t ^ (n + 1) * c (n + 1)) t₀ :=
    analyticAt_const.add
      (analyticAt_tsum_pow_succ_mul_of_le_geometric (fun n => c (n + 1)) M ρ hρ hb t₀ ht₀)
  refine hAn.congr ?_
  have hopen : IsOpen {t : ℂ | ‖t‖ * ρ < 1} :=
    isOpen_lt (continuous_norm.mul continuous_const) continuous_const
  have hmem : t₀ ∈ {t : ℂ | ‖t‖ * ρ < 1} := ht₀
  filter_upwards [hopen.mem_nhds hmem] with t ht
  have ht' : ‖t‖ * ρ < 1 := ht
  have h1 : Summable (fun n : ℕ => t ^ (n + 1) * c (n + 1)) := by
    refine Summable.of_norm_bounded (g := fun n => ‖t‖ * M * (‖t‖ * ρ) ^ n) ?_ ?_
    · exact (summable_geometric_of_lt_one (by positivity) ht').mul_left _
    · intro n
      calc ‖t ^ (n + 1) * c (n + 1)‖ = ‖t‖ ^ (n + 1) * ‖c (n + 1)‖ := by
            rw [norm_mul, norm_pow]
        _ ≤ ‖t‖ ^ (n + 1) * (M * ρ ^ n) :=
            mul_le_mul_of_nonneg_left (hb n) (pow_nonneg (norm_nonneg t) _)
        _ = ‖t‖ * M * (‖t‖ * ρ) ^ n := by rw [mul_pow, pow_succ]; ring
  have hsum : Summable (fun n : ℕ => t ^ n * c n) := (summable_nat_add_iff 1).mp h1
  change c 0 + ∑' n : ℕ, t ^ (n + 1) * c (n + 1) = ∑' n : ℕ, t ^ n * c n
  rw [hsum.tsum_eq_zero_add]
  simp

/-- The derivative at the origin of `t ↦ ∑ tⁿ cₙ` with geometrically bounded tail
coefficients is the linear coefficient `c 1`. -/
theorem hasDerivAt_tsum_pow_mul_of_le_geometric (c : ℕ → ℂ) (M ρ : ℝ) (hρ : 0 ≤ ρ)
    (hb : ∀ n : ℕ, ‖c (n + 1)‖ ≤ M * ρ ^ n) :
    HasDerivAt (fun t : ℂ => ∑' n : ℕ, t ^ n * c n) (c 1) 0 := by
  classical
  have hGb : ∀ n : ℕ, ‖c (n + 1 + 1)‖ ≤ M * ρ * ρ ^ n := by
    intro n
    calc ‖c (n + 1 + 1)‖ ≤ M * ρ ^ (n + 1) := hb (n + 1)
      _ = M * ρ * ρ ^ n := by rw [pow_succ]; ring
  have hG : AnalyticAt ℂ (fun t : ℂ => ∑' n : ℕ, t ^ n * c (n + 1)) 0 :=
    analyticAt_tsum_pow_mul_of_le_geometric (fun n => c (n + 1)) (M * ρ) ρ hρ hGb 0 (by simp)
  have hG0 : (∑' n : ℕ, (0 : ℂ) ^ n * c (n + 1)) = c 1 := by
    rw [tsum_eq_single 0 (fun n hn => by rw [zero_pow hn, zero_mul])]
    simp
  have hDer : HasDerivAt (fun t : ℂ => c 0 + t * ∑' n : ℕ, t ^ n * c (n + 1)) (c 1) 0 := by
    have h1 := (hasDerivAt_id (0 : ℂ)).mul hG.differentiableAt.hasDerivAt
    have h1' : HasDerivAt (fun t : ℂ => t * ∑' n : ℕ, t ^ n * c (n + 1)) (c 1) 0 := by
      convert h1 using 1
      rw [hG0]
      simp
    exact h1'.const_add (c 0)
  refine hDer.congr_of_eventuallyEq ?_
  have hopen : IsOpen {t : ℂ | ‖t‖ * ρ < 1} :=
    isOpen_lt (continuous_norm.mul continuous_const) continuous_const
  have hmem : (0 : ℂ) ∈ {t : ℂ | ‖t‖ * ρ < 1} := by simp
  filter_upwards [hopen.mem_nhds hmem] with t ht
  have ht' : ‖t‖ * ρ < 1 := ht
  have h1 : Summable (fun n : ℕ => t ^ (n + 1) * c (n + 1)) := by
    refine Summable.of_norm_bounded (g := fun n => ‖t‖ * M * (‖t‖ * ρ) ^ n) ?_ ?_
    · exact (summable_geometric_of_lt_one (by positivity) ht').mul_left _
    · intro n
      calc ‖t ^ (n + 1) * c (n + 1)‖ = ‖t‖ ^ (n + 1) * ‖c (n + 1)‖ := by
            rw [norm_mul, norm_pow]
        _ ≤ ‖t‖ ^ (n + 1) * (M * ρ ^ n) :=
            mul_le_mul_of_nonneg_left (hb n) (pow_nonneg (norm_nonneg t) _)
        _ = ‖t‖ * M * (‖t‖ * ρ) ^ n := by rw [mul_pow, pow_succ]; ring
  have hsum : Summable (fun n : ℕ => t ^ n * c n) := (summable_nat_add_iff 1).mp h1
  change (∑' n : ℕ, t ^ n * c n) = c 0 + t * ∑' n : ℕ, t ^ n * c (n + 1)
  rw [hsum.tsum_eq_zero_add]
  congr 1
  · simp
  · calc ∑' n : ℕ, t ^ (n + 1) * c (n + 1)
        = ∑' n : ℕ, t * (t ^ n * c (n + 1)) := tsum_congr fun n => by ring
      _ = t * ∑' n : ℕ, t ^ n * c (n + 1) := tsum_mul_left

/-- The quartic kernel `‖ζ - z‖⁻⁴` is integrable over the upper half plane whenever
`z` lies in the open lower half plane. -/
theorem integrable_inv_norm_sub_pow_four_of_im_neg (z : ℂ) (hz : z.im < 0) :
    Integrable (fun ζ : ℂ => (‖ζ - z‖ ^ (4 : ℕ))⁻¹)
      (volume.restrict {ζ : ℂ | 0 < ζ.im}) := by
  classical
  have hd0 : 0 < -z.im := by linarith
  have hdist : ∀ ζ : ℂ, 0 < ζ.im → -z.im ≤ ‖ζ - z‖ := by
    intro ζ hζ
    have h1 : -z.im ≤ (ζ - z).im := by rw [Complex.sub_im]; linarith
    exact h1.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))
  have hjap : Integrable (fun w : ℂ => (1 + ‖w‖) ^ (-(4 : ℝ))) := by
    refine integrable_one_add_norm ?_
    rw [Complex.finrank_real_complex]
    norm_num
  have htrans : Integrable (fun ζ : ℂ => (1 + ‖ζ - z‖) ^ (-(4 : ℝ))) :=
    hjap.comp_sub_right z
  have hUmeas : MeasurableSet {ζ : ℂ | 0 < ζ.im} :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  refine Integrable.mono'
    (g := fun ζ : ℂ => (1 + (-z.im)⁻¹) ^ (4 : ℕ) * (1 + ‖ζ - z‖) ^ (-(4 : ℝ)))
    ((htrans.const_mul _).restrict) ?_ ?_
  · exact ((((continuous_id.sub continuous_const).norm.pow 4).measurable).inv
      ).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem hUmeas] with ζ hζ
    have hζ' : (0 : ℝ) < ζ.im := hζ
    have ht0 : 0 < ‖ζ - z‖ := lt_of_lt_of_le hd0 (hdist ζ hζ')
    have hrp : (1 + ‖ζ - z‖) ^ (-(4 : ℝ)) = ((1 + ‖ζ - z‖) ^ (4 : ℕ))⁻¹ := by
      rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
        Real.rpow_natCast]
    have h4 : (1 + ‖ζ - z‖) ^ (4 : ℕ) ≤ (1 + (-z.im)⁻¹) ^ 4 * ‖ζ - z‖ ^ 4 := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ 4
      have h5 : 1 ≤ ‖ζ - z‖ * (-z.im)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hd0, one_mul]
        exact hdist ζ hζ'
      calc 1 + ‖ζ - z‖ ≤ ‖ζ - z‖ * (-z.im)⁻¹ + ‖ζ - z‖ := by linarith
        _ = (1 + (-z.im)⁻¹) * ‖ζ - z‖ := by ring
    have h6 : (‖ζ - z‖ ^ (4 : ℕ))⁻¹
        ≤ (1 + (-z.im)⁻¹) ^ (4 : ℕ) * ((1 + ‖ζ - z‖) ^ (4 : ℕ))⁻¹ := by
      have h5 : ((1 + (-z.im)⁻¹) ^ (4 : ℕ) * ‖ζ - z‖ ^ (4 : ℕ))⁻¹
          ≤ ((1 + ‖ζ - z‖) ^ (4 : ℕ))⁻¹ := inv_anti₀ (by positivity) h4
      have h7 := mul_le_mul_of_nonneg_left h5
        (by positivity : (0 : ℝ) ≤ (1 + (-z.im)⁻¹) ^ (4 : ℕ))
      rwa [mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at h7
    rw [Real.norm_of_nonneg (by positivity), hrp]
    exact h6

/-- **Differentiation under the integral sign**: for a density in `Lᵖ` (`2 < p < ∞`)
vanishing outside a ball and on the closed lower half plane, the map
`w ↦ ∫ u ζ / (ζ - w)^k` has the expected derivative at lower-half-plane points. -/
theorem hasDerivAt_integral_div_sub_pow (u : ℂ → ℂ) (p : ℝ≥0∞) (R : ℝ) (hp : 2 < p)
    (hu : MemLp u p volume) (hsupp : ∀ z : ℂ, R < ‖z‖ → u z = 0)
    (hupp : ∀ z : ℂ, z.im ≤ 0 → u z = 0) (k : ℕ) (z : ℂ) (hz : z.im < 0) :
    HasDerivAt (fun w : ℂ => ∫ ζ : ℂ, u ζ / (ζ - w) ^ k)
      ((k : ℂ) * ∫ ζ : ℂ, u ζ / (ζ - z) ^ (k + 1)) z := by
  classical
  have hd0 : (0 : ℝ) < -z.im / 2 := by
    have : 0 < -z.im := by linarith
    linarith
  have hu1 : MemLp u 1 volume :=
    memLp_mono_exponent_of_ball_support u p 1 R (le_of_lt (lt_trans ENNReal.one_lt_two hp)) hu hsupp
  have huI : Integrable u volume := memLp_one_iff_integrable.mp hu1
  have humeas : AEStronglyMeasurable u volume := hu.1
  -- the kernel is uniformly separated from the support near `z`
  have hkey : ∀ x : ℂ, x ∈ Metric.ball z (-z.im / 2) → ∀ ζ : ℂ, u ζ ≠ 0 →
      -z.im / 2 ≤ ‖ζ - x‖ := by
    intro x hx ζ hζ
    have hζim : 0 < ζ.im := by
      by_contra hcon
      exact hζ (hupp ζ (le_of_not_gt hcon))
    have hxz : ‖x - z‖ < -z.im / 2 := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      exact hx
    have hxim : x.im < -z.im / 2 + z.im := by
      have h1 : x.im - z.im ≤ ‖x - z‖ := by
        calc x.im - z.im ≤ |x.im - z.im| := le_abs_self _
          _ = |(x - z).im| := by rw [Complex.sub_im]
          _ ≤ ‖x - z‖ := Complex.abs_im_le_norm _
      linarith
    have h2 : -z.im / 2 ≤ (ζ - x).im := by
      rw [Complex.sub_im]
      have : -z.im / 2 + z.im = z.im / 2 - z.im + z.im := by ring
      nlinarith only [hζim, hxim, hxz]
    exact h2.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))
  have hzself : z ∈ Metric.ball z (-z.im / 2) := Metric.mem_ball_self hd0
  have hmeasF : ∀ (m : ℕ) (x : ℂ),
      AEStronglyMeasurable (fun ζ : ℂ => u ζ / (ζ - x) ^ m) volume := by
    intro m x
    have h1 : (fun ζ : ℂ => u ζ / (ζ - x) ^ m) = fun ζ : ℂ => u ζ * ((ζ - x) ^ m)⁻¹ := by
      funext ζ
      rw [div_eq_mul_inv]
    rw [h1]
    exact humeas.mul (((measurable_id.sub_const x).pow_const m).inv).aestronglyMeasurable
  have hbnd_gen : ∀ (m : ℕ) (x : ℂ), x ∈ Metric.ball z (-z.im / 2) → ∀ ζ : ℂ,
      ‖u ζ / (ζ - x) ^ m‖ ≤ ((-z.im / 2) ^ m)⁻¹ * ‖u ζ‖ := by
    intro m x hx ζ
    by_cases hζ : u ζ = 0
    · rw [hζ, zero_div, norm_zero]
      positivity
    · have h1 : (-z.im / 2) ^ m ≤ ‖ζ - x‖ ^ m :=
        pow_le_pow_left₀ hd0.le (hkey x hx ζ hζ) m
      have h2 : (0 : ℝ) < (-z.im / 2) ^ m := by positivity
      rw [norm_div, norm_pow, div_le_iff₀ (lt_of_lt_of_le h2 h1)]
      have h3 : ((-z.im / 2) ^ m)⁻¹ * ‖u ζ‖ * (-z.im / 2) ^ m
          ≤ ((-z.im / 2) ^ m)⁻¹ * ‖u ζ‖ * ‖ζ - x‖ ^ m :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h4 : ((-z.im / 2) ^ m)⁻¹ * ‖u ζ‖ * (-z.im / 2) ^ m = ‖u ζ‖ := by
        rw [mul_comm (((-z.im / 2) ^ m)⁻¹) ‖u ζ‖, mul_assoc,
          inv_mul_cancel₀ h2.ne', mul_one]
      linarith
  have hFint : ∀ m : ℕ, Integrable (fun ζ : ℂ => u ζ / (ζ - z) ^ m) volume := by
    intro m
    refine Integrable.mono' ((huI.norm).const_mul (((-z.im / 2) ^ m)⁻¹))
      (hmeasF m z) ?_
    exact Filter.Eventually.of_forall (hbnd_gen m z hzself)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x ζ => u ζ / (ζ - x) ^ k)
    (F' := fun x ζ => (k : ℂ) * (u ζ / (ζ - x) ^ (k + 1)))
    (x₀ := z) (μ := volume)
    (bound := fun ζ => (k : ℝ) * (((-z.im / 2) ^ (k + 1))⁻¹ * ‖u ζ‖))
    (Metric.ball_mem_nhds z hd0)
    (Filter.Eventually.of_forall fun x => hmeasF k x)
    (hFint k)
    (((hmeasF (k + 1) z).const_mul _))
    ?_ ?_ ?_
  · have h2 := hmain.2
    beta_reduce at h2
    have h3 : (∫ a : ℂ, (k : ℂ) * (u a / (a - z) ^ (k + 1)))
        = (k : ℂ) * ∫ a : ℂ, u a / (a - z) ^ (k + 1) := integral_const_mul _ _
    rw [h3] at h2
    exact h2
  · refine Filter.Eventually.of_forall fun ζ => fun x hx => ?_
    beta_reduce
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hbnd_gen (k + 1) x hx ζ) (Nat.cast_nonneg k)
  · exact (huI.norm.const_mul _).const_mul _
  · refine Filter.Eventually.of_forall fun ζ => fun x hx => ?_
    beta_reduce
    by_cases hζ : u ζ = 0
    · simp only [hζ, zero_div, mul_zero]
      exact hasDerivAt_const x 0
    · have hne : ζ - x ≠ 0 := by
        have h1 := hkey x hx ζ hζ
        intro hcon
        rw [hcon, norm_zero] at h1
        linarith
      have hg : HasDerivAt (fun x' : ℂ => ζ - x') (-1) x := by
        simpa using (hasDerivAt_id x).const_sub ζ
      have hzp := hasDerivAt_zpow (-(k : ℤ)) (ζ - x) (Or.inl hne)
      have hcomp := HasDerivAt.comp x hzp hg
      have hfun : (fun x' : ℂ => u ζ / (ζ - x') ^ k)
          = fun x' : ℂ => u ζ * ((fun y : ℂ => y ^ (-(k : ℤ))) ∘ fun x' : ℂ => ζ - x') x' := by
        funext x'
        simp only [Function.comp_apply]
        rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
      rw [hfun]
      have hval : (k : ℂ) * (u ζ / (ζ - x) ^ (k + 1))
          = u ζ * ((((-(k : ℤ)) : ℤ) : ℂ) * (ζ - x) ^ (-(k : ℤ) - 1) * (-1)) := by
        have hzp1 : (ζ - x) ^ (-(k : ℤ) - 1) = ((ζ - x) ^ (k + 1))⁻¹ := by
          rw [show -(k : ℤ) - 1 = -(((k + 1 : ℕ) : ℤ)) by push_cast; ring, zpow_neg,
            zpow_natCast]
        rw [hzp1, div_eq_mul_inv]
        push_cast
        ring
      rw [hval]
      exact hcomp.const_mul (u ζ)

/-- The Cauchy transform of an `Lᵖ` density (`2 < p < ∞`) vanishing outside a ball
and on the closed lower half plane is holomorphic on the open lower half plane. -/
theorem differentiableOn_cauchyTransform_lower (u : ℂ → ℂ) (p : ℝ≥0∞) (R : ℝ)
    (hp : 2 < p) (hu : MemLp u p volume)
    (hsupp : ∀ z : ℂ, R < ‖z‖ → u z = 0) (hupp : ∀ z : ℂ, z.im ≤ 0 → u z = 0) :
    DifferentiableOn ℂ (cauchyTransform u) {z : ℂ | z.im < 0} := by
  classical
  intro z hz
  have hz' : z.im < 0 := hz
  have hCT : cauchyTransform u
      = fun w : ℂ => -(1 / (Real.pi : ℂ)) * ∫ ζ : ℂ, u ζ / (ζ - w) ^ 1 := by
    funext w
    rw [cauchyTransform]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    change u ζ / (ζ - w) = u ζ / (ζ - w) ^ 1
    rw [pow_one]
  rw [hCT]
  exact (((hasDerivAt_integral_div_sub_pow u p R hp hu hsupp hupp 1 z hz').const_mul
    (-(1 / (Real.pi : ℂ)))).differentiableAt).differentiableWithinAt

/-- The third derivative of the Cauchy transform of an upper-supported `Lᵖ` density
is the quartic-kernel integral `-(6/π) ∫ u ζ / (ζ - z)⁴` on the lower half plane. -/
theorem iteratedDeriv_three_cauchyTransform (u : ℂ → ℂ) (p : ℝ≥0∞) (R : ℝ)
    (hp : 2 < p) (hu : MemLp u p volume)
    (hsupp : ∀ z : ℂ, R < ‖z‖ → u z = 0) (hupp : ∀ z : ℂ, z.im ≤ 0 → u z = 0)
    (z : ℂ) (hz : z.im < 0) :
    iteratedDeriv 3 (cauchyTransform u) z
      = -(6 / (Real.pi : ℂ)) * ∫ ζ : ℂ, u ζ / (ζ - z) ^ 4 := by
  classical
  have hLopen : IsOpen {w : ℂ | w.im < 0} :=
    isOpen_lt Complex.continuous_im continuous_const
  have hI : ∀ (m : ℕ), 1 ≤ m → ∀ w : ℂ, w.im < 0 →
      HasDerivAt (fun w' : ℂ => ∫ ζ : ℂ, u ζ / (ζ - w') ^ m)
        ((m : ℂ) * ∫ ζ : ℂ, u ζ / (ζ - w) ^ (m + 1)) w :=
    fun m _ w hw => hasDerivAt_integral_div_sub_pow u p R hp hu hsupp hupp m w hw
  have hCT : cauchyTransform u
      = fun w : ℂ => -(1 / (Real.pi : ℂ)) * ∫ ζ : ℂ, u ζ / (ζ - w) ^ 1 := by
    funext w
    rw [cauchyTransform]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    change u ζ / (ζ - w) = u ζ / (ζ - w) ^ 1
    rw [pow_one]
  have hD1 : ∀ w : ℂ, w.im < 0 → deriv (cauchyTransform u) w
      = -(1 / (Real.pi : ℂ)) * ((1 : ℕ) * ∫ ζ : ℂ, u ζ / (ζ - w) ^ 2) := by
    intro w hw
    rw [hCT]
    exact ((hI 1 le_rfl w hw).const_mul (-(1 / (Real.pi : ℂ)))).deriv
  have hD2 : ∀ w : ℂ, w.im < 0 → deriv (deriv (cauchyTransform u)) w
      = -(1 / (Real.pi : ℂ)) * ((2 : ℕ) * ∫ ζ : ℂ, u ζ / (ζ - w) ^ 3) := by
    intro w hw
    have hev : deriv (cauchyTransform u) =ᶠ[nhds w]
        fun w' : ℂ => -(1 / (Real.pi : ℂ)) * ((1 : ℕ) * ∫ ζ : ℂ, u ζ / (ζ - w') ^ 2) := by
      filter_upwards [hLopen.mem_nhds hw] with x hx using hD1 x hx
    rw [hev.deriv_eq]
    have h2 : HasDerivAt
        (fun w' : ℂ => -(1 / (Real.pi : ℂ)) * ((1 : ℕ) * ∫ ζ : ℂ, u ζ / (ζ - w') ^ 2))
        (-(1 / (Real.pi : ℂ)) * ((1 : ℕ) * ((2 : ℕ) * ∫ ζ : ℂ, u ζ / (ζ - w) ^ 3))) w := by
      have h3 := ((hI 2 (by norm_num) w hw).const_mul ((1 : ℕ) : ℂ)).const_mul
        (-(1 / (Real.pi : ℂ)))
      exact h3
    rw [h2.deriv]
    push_cast
    ring
  have hD3 : deriv (deriv (deriv (cauchyTransform u))) z
      = -(6 / (Real.pi : ℂ)) * ∫ ζ : ℂ, u ζ / (ζ - z) ^ 4 := by
    have hev : deriv (deriv (cauchyTransform u)) =ᶠ[nhds z]
        fun w' : ℂ => -(1 / (Real.pi : ℂ)) * ((2 : ℕ) * ∫ ζ : ℂ, u ζ / (ζ - w') ^ 3) := by
      filter_upwards [hLopen.mem_nhds hz] with x hx using hD2 x hx
    rw [hev.deriv_eq]
    have h2 : HasDerivAt
        (fun w' : ℂ => -(1 / (Real.pi : ℂ)) * ((2 : ℕ) * ∫ ζ : ℂ, u ζ / (ζ - w') ^ 3))
        (-(1 / (Real.pi : ℂ)) * ((2 : ℕ) * ((3 : ℕ) * ∫ ζ : ℂ, u ζ / (ζ - z) ^ 4))) z := by
      have h3 := ((hI 3 (by norm_num) z hz).const_mul ((2 : ℕ) : ℂ)).const_mul
        (-(1 / (Real.pi : ℂ)))
      exact h3
    rw [h2.deriv]
    push_cast
    ring
  have hID : iteratedDeriv 3 (cauchyTransform u) z
      = deriv (deriv (deriv (cauchyTransform u))) z := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
      show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hID, hD3]

/-- **The affine Neumann tier**: a compactly supported affine coefficient family with
small base supremum admits fixed-point coefficient fields with geometric bounds whose
power series in the parameter is a principal solution; when the base vanishes, the
zeroth field is zero and the first is the Cauchy transform of the direction. -/
theorem exists_principal_solution_power_series (κ' ν' : ℂ → ℂ) (R M' : ℝ)
    (hκm : Measurable κ') (hνm : Measurable ν')
    (hκs : ∀ z : ℂ, R < ‖z‖ → κ' z = 0) (hνs : ∀ z : ℂ, R < ‖z‖ → ν' z = 0)
    (hκu : ∀ z : ℂ, z.im ≤ 0 → κ' z = 0) (hνu : ∀ z : ℂ, z.im ≤ 0 → ν' z = 0)
    (hκb : eLpNormEssSup κ' volume < 1) (hνM : ∀ z : ℂ, ‖ν' z‖ ≤ M') (hM0 : 0 < M') :
    ∃ (ε : ℝ) (c : ℕ → ℂ → ℂ) (Mc ρc : ℝ), 0 < ε ∧ 0 ≤ ρc ∧ 0 ≤ Mc ∧ ε * ρc < 1 ∧
      (∀ (n : ℕ) (z : ℂ), ‖c (n + 1) z‖ ≤ Mc * ρc ^ n) ∧
      (∀ z : ℂ, ‖c 0 z‖ ≤ Mc) ∧
      (∀ n : ℕ, DifferentiableOn ℂ (c n) {z : ℂ | z.im < 0}) ∧
      (∀ s : ℂ, ‖s‖ < ε → ∃ bs : BeltramiCoeff, (∀ z : ℂ, bs.μ z = κ' z + s * ν' z) ∧
        IsPrincipalSolution bs (fun z => z + ∑' n : ℕ, s ^ n * c n z)) ∧
      ((∀ z : ℂ, κ' z = 0) → (∀ z : ℂ, c 0 z = 0) ∧
        (∀ z : ℂ, c 1 z = cauchyTransform ν' z)) := by
  classical
  classical
  -- ===== exponent data and constants =====
  obtain ⟨p, hp, hp', C, hCb, hcontr⟩ := exists_p_gt_two_beurling_contraction hκm hκb
  have hC0 : 0 ≤ C := hCb.1
  have hCbound := hCb.2
  have hκfin : eLpNormEssSup κ' volume ≠ ⊤ := (lt_trans hκb ENNReal.one_lt_top).ne
  set k' : ℝ := (eLpNormEssSup κ' volume).toReal with hk'def
  have hk'0 : 0 ≤ k' := ENNReal.toReal_nonneg
  have hk'1 : k' < 1 := by
    have h1 := (ENNReal.toReal_lt_toReal hκfin ENNReal.one_ne_top).mpr hκb
    simpa using h1
  have hcontr' : k' * C < 1 := hcontr
  have h1kC : (0 : ℝ) < 1 - k' * C := by
    have : 0 ≤ k' * C := mul_nonneg hk'0 hC0
    linarith
  have hνb' : eLpNormEssSup ν' volume ≤ ENNReal.ofReal M' :=
    eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hνM)
  have hνfin : eLpNormEssSup ν' volume ≠ ⊤ :=
    (lt_of_le_of_lt hνb' ENNReal.ofReal_lt_top).ne
  have hκLp : MemLp κ' p volume :=
    memLp_of_eLpNormEssSup_ne_top_of_support hp' hκm hκfin hκs
  have hνLp : MemLp ν' p volume :=
    memLp_of_eLpNormEssSup_ne_top_of_support hp' hνm hνfin hνs
  have hνLinf : MemLp ν' ⊤ volume := by
    refine ⟨hνm.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_exponent_top]
    exact lt_of_le_of_ne le_top hνfin
  have hκessOfReal : eLpNormEssSup κ' volume = ENNReal.ofReal k' := by
    rw [hk'def, ENNReal.ofReal_toReal hκfin]
  -- the parameter radius and the series ratio
  set ε : ℝ := min ((1 - k' * C) / (2 * M' * (C + 1))) ((1 - k') / (2 * M')) with hεdef
  have hε0 : 0 < ε := by
    refine lt_min (div_pos h1kC (by positivity)) (div_pos (by linarith) (by positivity))
  set ρ : ℝ := M' * C / (1 - k' * C) with hρdef
  have hρ0 : 0 ≤ ρ := div_nonneg (by positivity) h1kC.le
  have hερ : ε * ρ < 1 := by
    have h1 : ε ≤ (1 - k' * C) / (2 * M' * (C + 1)) := min_le_left _ _
    have h2 : ε * ρ ≤ (1 - k' * C) / (2 * M' * (C + 1)) * ρ :=
      mul_le_mul_of_nonneg_right h1 hρ0
    have h3 : (1 - k' * C) / (2 * M' * (C + 1)) * ρ = C / (2 * (C + 1)) := by
      rw [hρdef]
      field_simp
    have h4 : C / (2 * (C + 1)) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    calc ε * ρ ≤ (1 - k' * C) / (2 * M' * (C + 1)) * ρ := h2
      _ = C / (2 * (C + 1)) := h3
      _ < 1 := h4
  -- uniform smallness across the parameter ball
  have hsmallA : ∀ s : ℂ, ‖s‖ < ε → k' + ‖s‖ * M' ≤ (1 + k') / 2 := by
    intro s hs
    have h2 : ‖s‖ < (1 - k') / (2 * M') := lt_of_lt_of_le hs (min_le_right _ _)
    have h3 : ‖s‖ * M' ≤ (1 - k') / 2 := by
      have h4 : ‖s‖ * M' < (1 - k') / (2 * M') * M' :=
        mul_lt_mul_of_pos_right h2 hM0
      have h5 : (1 - k') / (2 * M') * M' = (1 - k') / 2 := by
        field_simp
      linarith
    linarith
  have hsmallB : ∀ s : ℂ, ‖s‖ < ε → (k' + ‖s‖ * M') * C ≤ (1 + k' * C) / 2 := by
    intro s hs
    have h2 : ‖s‖ < (1 - k' * C) / (2 * M' * (C + 1)) := lt_of_lt_of_le hs (min_le_left _ _)
    have h3 : ‖s‖ * (M' * C) ≤ (1 - k' * C) / 2 := by
      have h4 : ‖s‖ * (M' * C) ≤ (1 - k' * C) / (2 * M' * (C + 1)) * (M' * C) :=
        mul_le_mul_of_nonneg_right h2.le (by positivity)
      have h5 : (1 - k' * C) / (2 * M' * (C + 1)) * (M' * C)
          = (1 - k' * C) / 2 * (C / (C + 1)) := by
        field_simp
      have h6 : C / (C + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      have h7 : (1 - k' * C) / 2 * (C / (C + 1)) ≤ (1 - k' * C) / 2 * 1 :=
        mul_le_mul_of_nonneg_left h6 (by linarith)
      linarith
    have h8 : (k' + ‖s‖ * M') * C = k' * C + ‖s‖ * (M' * C) := by ring
    linarith
  have hmidA : (1 + k') / 2 < 1 := by linarith
  have hmidB : (1 + k' * C) / 2 < 1 := by linarith
  -- ===== the fixed-point solver with canonical representative =====
  have hL2 : ∀ u : ℂ → ℂ, MemLp u p volume → (∀ z : ℂ, R < ‖z‖ → u z = 0) →
      MemLp u 2 volume := fun u hu hs => memLp_mono_exponent_of_ball_support u p 2 R hp.le hu hs
  have hFP : ∀ g : ℂ → ℂ, MemLp g p volume → (∀ z : ℂ, R < ‖z‖ → g z = 0) →
      (∀ z : ℂ, z.im ≤ 0 → g z = 0) →
      ∃ u : ℂ → ℂ, MemLp u p volume ∧ (∀ z : ℂ, R < ‖z‖ → u z = 0) ∧
        (∀ z : ℂ, z.im ≤ 0 → u z = 0) ∧
        (u =ᵐ[volume] fun z => κ' z * beurling u z + g z) ∧
        eLpNorm u p volume ≤ ENNReal.ofReal ((1 - k' * C)⁻¹) * eLpNorm g p volume ∧
        ∃ h₀ : ℂ → ℂ, u = fun z => κ' z * beurling h₀ z + g z := by
    intro g hg hgs hgu
    obtain ⟨h, hLp, heq, hbnd⟩ :=
      exists_lp_fixedPoint_beltrami hp hp' hκm hκfin hCb hcontr' hg
    refine ⟨fun z => κ' z * beurling h z + g z, hLp.ae_eq heq, ?_, ?_, ?_, ?_, ⟨h, rfl⟩⟩
    · intro z hz
      change κ' z * beurling h z + g z = 0
      rw [hκs z hz, hgs z hz, zero_mul, zero_add]
    · intro z hz
      change κ' z * beurling h z + g z = 0
      rw [hκu z hz, hgu z hz, zero_mul, zero_add]
    · have huLp : MemLp (fun z => κ' z * beurling h z + g z) p volume := hLp.ae_eq heq
      have husupp : ∀ z : ℂ, R < ‖z‖ → (fun z => κ' z * beurling h z + g z) z = 0 := by
        intro z hz
        change κ' z * beurling h z + g z = 0
        rw [hκs z hz, hgs z hz, zero_mul, zero_add]
      have hL2u : MemLp (fun z => κ' z * beurling h z + g z) 2 volume :=
        hL2 _ huLp husupp
      have hL2h : MemLp h 2 volume := hL2u.ae_eq heq.symm
      have hSeq : beurling h =ᵐ[volume] beurling (fun z => κ' z * beurling h z + g z) :=
        beurling_congr_ae hL2h hL2u heq
      filter_upwards [hSeq] with z hz
      show κ' z * beurling h z + g z
          = κ' z * beurling (fun z => κ' z * beurling h z + g z) z + g z
      rw [hz]
    · calc eLpNorm (fun z => κ' z * beurling h z + g z) p volume
          = eLpNorm h p volume := eLpNorm_congr_ae heq.symm
        _ ≤ ENNReal.ofReal ((1 - (eLpNormEssSup κ' volume).toReal * C)⁻¹)
              * eLpNorm g p volume := hbnd
        _ = ENNReal.ofReal ((1 - k' * C)⁻¹) * eLpNorm g p volume := by rw [hk'def]
  choose! FP hFP1 hFP2 hFP3 hFP4 hFP5 hFP6 using hFP
  -- ===== the coefficient sequence =====
  set eterm : ℕ → ℂ → ℂ := fun m => if m = 0 then ν' else fun _ => 0 with hetermdef
  have het0 : eterm 0 = ν' := if_pos rfl
  have hetS : ∀ m : ℕ, eterm (m + 1) = fun _ => 0 := fun m => if_neg (Nat.succ_ne_zero m)
  have hetLp : ∀ m : ℕ, MemLp (eterm m) p volume := by
    intro m
    cases m with
    | zero => rw [het0]; exact hνLp
    | succ m => rw [hetS m]; exact MemLp.zero'
  have hetsupp : ∀ (m : ℕ) (z : ℂ), R < ‖z‖ → eterm m z = 0 := by
    intro m z hz
    cases m with
    | zero => rw [het0]; exact hνs z hz
    | succ m => rw [hetS m]
  have hetupp : ∀ (m : ℕ) (z : ℂ), z.im ≤ 0 → eterm m z = 0 := by
    intro m z hz
    cases m with
    | zero => rw [het0]; exact hνu z hz
    | succ m => rw [hetS m]
  have hetnorm : ∀ m : ℕ, eLpNorm (eterm m) p volume ≤ eLpNorm ν' p volume := by
    intro m
    cases m with
    | zero => rw [het0]
    | succ m =>
      rw [hetS m]
      have h0 : eLpNorm (fun _ : ℂ => (0 : ℂ)) p volume = 0 :=
        eLpNorm_zero (p := p) (μ := volume) (α := ℂ) (ε := ℂ)
      rw [h0]
      exact zero_le (eLpNorm ν' p volume)
  -- the recursion data and the sequence itself
  set datum : (ℂ → ℂ) → ℕ → ℂ → ℂ :=
    fun am m z => ν' z * beurling am z + eterm m z with hdatumdef
  set a : ℕ → ℂ → ℂ := fun n =>
    Nat.rec (motive := fun _ => ℂ → ℂ) (FP κ') (fun m am => FP (datum am m)) n with hadef
  have ha0 : a 0 = FP κ' := rfl
  have haS : ∀ m : ℕ, a (m + 1) = FP (datum (a m) m) := fun m => rfl
  -- the standing invariant
  have hdatum_ok : ∀ (u : ℂ → ℂ), MemLp u p volume → (∀ z : ℂ, R < ‖z‖ → u z = 0) →
      ∀ m : ℕ, MemLp (datum u m) p volume ∧
        (∀ z : ℂ, R < ‖z‖ → datum u m z = 0) ∧
        (∀ z : ℂ, z.im ≤ 0 → datum u m z = 0) := by
    intro u hu hus m
    refine ⟨?_, ?_, ?_⟩
    · exact ((memLp_beurling_of_memLp hp hp' hu).mul' hνLinf).add (hetLp m)
    · intro z hz
      change ν' z * beurling u z + eterm m z = 0
      rw [hνs z hz, hetsupp m z hz, zero_mul, zero_add]
    · intro z hz
      change ν' z * beurling u z + eterm m z = 0
      rw [hνu z hz, hetupp m z hz, zero_mul, zero_add]
  have hInv : ∀ n : ℕ, MemLp (a n) p volume ∧ (∀ z : ℂ, R < ‖z‖ → a n z = 0) ∧
      (∀ z : ℂ, z.im ≤ 0 → a n z = 0) := by
    intro n
    induction n with
    | zero =>
      rw [ha0]
      exact ⟨hFP1 κ' hκLp hκs hκu, hFP2 κ' hκLp hκs hκu, hFP3 κ' hκLp hκs hκu⟩
    | succ m ih =>
      rw [haS m]
      obtain ⟨hd1, hd2, hd3⟩ := hdatum_ok (a m) ih.1 ih.2.1 m
      exact ⟨hFP1 _ hd1 hd2 hd3, hFP2 _ hd1 hd2 hd3, hFP3 _ hd1 hd2 hd3⟩
  have haLp : ∀ n : ℕ, MemLp (a n) p volume := fun n => (hInv n).1
  have hasupp : ∀ (n : ℕ) (z : ℂ), R < ‖z‖ → a n z = 0 := fun n => (hInv n).2.1
  have haupp : ∀ (n : ℕ) (z : ℂ), z.im ≤ 0 → a n z = 0 := fun n => (hInv n).2.2
  have haL2 : ∀ n : ℕ, MemLp (a n) 2 volume := fun n => hL2 (a n) (haLp n) (hasupp n)
  -- the almost-everywhere recursions
  have hae0 : a 0 =ᵐ[volume] fun z => κ' z * beurling (a 0) z + κ' z := by
    rw [ha0]
    exact hFP4 κ' hκLp hκs hκu
  have haeS : ∀ m : ℕ, a (m + 1) =ᵐ[volume]
      fun z => κ' z * beurling (a (m + 1)) z + (ν' z * beurling (a m) z + eterm m z) := by
    intro m
    obtain ⟨hd1, hd2, hd3⟩ := hdatum_ok (a m) (haLp m) (hasupp m) m
    have h1 := hFP4 (datum (a m) m) hd1 hd2 hd3
    rw [← haS m] at h1
    exact h1
  -- ===== the geometric norm bounds =====
  have hAstep : ∀ m : ℕ, eLpNorm (a (m + 1)) p volume
      ≤ ENNReal.ofReal ((1 - k' * C)⁻¹) *
        (ENNReal.ofReal (M' * C) * eLpNorm (a m) p volume + eLpNorm (eterm m) p volume) := by
    intro m
    obtain ⟨hd1, hd2, hd3⟩ := hdatum_ok (a m) (haLp m) (hasupp m) m
    have h1 : eLpNorm (a (m + 1)) p volume
        ≤ ENNReal.ofReal ((1 - k' * C)⁻¹) * eLpNorm (datum (a m) m) p volume := by
      rw [haS m]
      exact hFP5 (datum (a m) m) hd1 hd2 hd3
    have h2 : eLpNorm (datum (a m) m) p volume
        ≤ ENNReal.ofReal (M' * C) * eLpNorm (a m) p volume + eLpNorm (eterm m) p volume := by
      have h3 : eLpNorm (fun z => ν' z * beurling (a m) z) p volume
          ≤ ENNReal.ofReal (M' * C) * eLpNorm (a m) p volume := by
        calc eLpNorm (fun z => ν' z * beurling (a m) z) p volume
            ≤ eLpNormEssSup ν' volume * eLpNorm (beurling (a m)) p volume :=
              eLpNorm_mul_le_essSup_mul hνm.aestronglyMeasurable
                (memLp_beurling_of_memLp hp hp' (haLp m))
          _ ≤ ENNReal.ofReal M' * (ENNReal.ofReal C * eLpNorm (a m) p volume) :=
              mul_le_mul' hνb' (hCbound (a m) (haLp m))
          _ = ENNReal.ofReal (M' * C) * eLpNorm (a m) p volume := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul hM0.le]
      calc eLpNorm (datum (a m) m) p volume
          ≤ eLpNorm (fun z => ν' z * beurling (a m) z) p volume
              + eLpNorm (eterm m) p volume := by
            have hν1 : MemLp (fun z => ν' z * beurling (a m) z) p volume :=
              (memLp_beurling_of_memLp hp hp' (haLp m)).mul' hνLinf
            refine eLpNorm_add_le ?_ ?_ (le_of_lt (lt_trans ENNReal.one_lt_two hp))
            · exact hν1.1
            · exact (hetLp m).1
        _ ≤ ENNReal.ofReal (M' * C) * eLpNorm (a m) p volume
              + eLpNorm (eterm m) p volume := by gcongr
    calc eLpNorm (a (m + 1)) p volume
        ≤ ENNReal.ofReal ((1 - k' * C)⁻¹) * eLpNorm (datum (a m) m) p volume := h1
      _ ≤ ENNReal.ofReal ((1 - k' * C)⁻¹) *
            (ENNReal.ofReal (M' * C) * eLpNorm (a m) p volume
              + eLpNorm (eterm m) p volume) := by gcongr
  have hAfin : ∀ n : ℕ, eLpNorm (a n) p volume ≠ ⊤ := fun n => (haLp n).2.ne
  -- pure-ratio step for `m ≥ 1`
  have hAstep' : ∀ m : ℕ, eLpNorm (a (m + 2)) p volume
      ≤ ENNReal.ofReal ρ * eLpNorm (a (m + 1)) p volume := by
    intro m
    have h1 := hAstep (m + 1)
    rw [hetS m] at h1
    have h2 : eLpNorm (fun _ : ℂ => (0 : ℂ)) p volume = 0 := by
      exact eLpNorm_zero (p := p) (μ := volume) (α := ℂ) (ε := ℂ)
    rw [h2, add_zero, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)] at h1
    have h3 : (1 - k' * C)⁻¹ * (M' * C) = ρ := by
      rw [hρdef]
      field_simp
    rwa [h3] at h1
  have hAgeo : ∀ n : ℕ, eLpNorm (a (n + 1)) p volume
      ≤ (ENNReal.ofReal ρ) ^ n * eLpNorm (a 1) p volume := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      calc eLpNorm (a (m + 2)) p volume
          ≤ ENNReal.ofReal ρ * eLpNorm (a (m + 1)) p volume := hAstep' m
        _ ≤ ENNReal.ofReal ρ * ((ENNReal.ofReal ρ) ^ m * eLpNorm (a 1) p volume) := by gcongr
        _ = (ENNReal.ofReal ρ) ^ (m + 1) * eLpNorm (a 1) p volume := by
            rw [← mul_assoc, ← pow_succ']
  -- real-valued geometric bounds
  set A0 : ℝ := (eLpNorm (a 0) p volume).toReal with hA0def
  set A1 : ℝ := (eLpNorm (a 1) p volume).toReal with hA1def
  have hA00 : 0 ≤ A0 := ENNReal.toReal_nonneg
  have hA10 : 0 ≤ A1 := ENNReal.toReal_nonneg
  have hAgeoR : ∀ n : ℕ, (eLpNorm (a (n + 1)) p volume).toReal ≤ ρ ^ n * A1 := by
    intro n
    have hne : (ENNReal.ofReal ρ) ^ n * eLpNorm (a 1) p volume ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (hAfin 1)
    have hmono := ENNReal.toReal_mono hne (hAgeo n)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ0] at hmono
  -- ===== the series coefficients =====
  obtain ⟨C₀, hC₀0, hC₀⟩ := norm_cauchyTransform_le_of_memLp_support (R := R) hp hp'
  set c : ℕ → ℂ → ℂ := fun n z => cauchyTransform (a n) z with hcdef
  set Mc : ℝ := C₀ * A0 + C₀ * A1 with hMcdef
  have hMc0 : 0 ≤ Mc := by positivity
  have hcb1 : ∀ (n : ℕ) (z : ℂ), ‖c (n + 1) z‖ ≤ Mc * ρ ^ n := by
    intro n z
    have h1 : ‖cauchyTransform (a (n + 1)) z‖
        ≤ C₀ * (eLpNorm (a (n + 1)) p volume).toReal :=
      hC₀ (a (n + 1)) (haLp (n + 1)) (hasupp (n + 1)) z
    have h2 : C₀ * (eLpNorm (a (n + 1)) p volume).toReal ≤ C₀ * (ρ ^ n * A1) :=
      mul_le_mul_of_nonneg_left (hAgeoR n) hC₀0
    have h3 : C₀ * (ρ ^ n * A1) ≤ Mc * ρ ^ n := by
      rw [hMcdef]
      have h4 : (0 : ℝ) ≤ C₀ * A0 * ρ ^ n := by positivity
      nlinarith only [pow_nonneg hρ0 n, h2, h4, hC₀0, hA10]
    calc ‖c (n + 1) z‖ = ‖cauchyTransform (a (n + 1)) z‖ := rfl
      _ ≤ C₀ * (eLpNorm (a (n + 1)) p volume).toReal := h1
      _ ≤ C₀ * (ρ ^ n * A1) := h2
      _ ≤ Mc * ρ ^ n := h3
  have hcb0 : ∀ z : ℂ, ‖c 0 z‖ ≤ Mc := by
    intro z
    have h1 : ‖cauchyTransform (a 0) z‖ ≤ C₀ * A0 := by
      rw [hA0def]
      exact hC₀ (a 0) (haLp 0) (hasupp 0) z
    calc ‖c 0 z‖ = ‖cauchyTransform (a 0) z‖ := rfl
      _ ≤ C₀ * A0 := h1
      _ ≤ Mc := by rw [hMcdef]; nlinarith only [h1, hC₀0, hA10]
  have hcdiff : ∀ n : ℕ, DifferentiableOn ℂ (c n) {z : ℂ | z.im < 0} := by
    intro n
    exact differentiableOn_cauchyTransform_lower (a n) p R hp (haLp n) (hasupp n) (haupp n)
  refine ⟨ε, c, Mc, ρ, hε0, hρ0, hMc0, hερ, hcb1, hcb0, hcdiff, ?_, ?_⟩
  · -- ===== the principal solutions along the parameter ball =====
    intro s hs
    have hsρ : ‖s‖ * ρ < 1 := by
      have h1 : ‖s‖ * ρ ≤ ε * ρ := mul_le_mul_of_nonneg_right hs.le hρ0
      exact lt_of_le_of_lt h1 hερ
    -- the affine coefficient and its bounds
    set μs : ℂ → ℂ := fun z => κ' z + s * ν' z with hμsdef
    have hμsm : Measurable μs := hκm.add (measurable_const.mul hνm)
    have hμsupp' : ∀ z : ℂ, R < ‖z‖ → μs z = 0 := by
      intro z hz
      change κ' z + s * ν' z = 0
      rw [hκs z hz, hνs z hz, mul_zero, add_zero]
    have hμsess : eLpNormEssSup μs volume ≤ ENNReal.ofReal (k' + ‖s‖ * M') := by
      have hrw : μs = κ' + fun z => s * ν' z := rfl
      have h1 : eLpNorm μs ⊤ volume
          ≤ eLpNorm κ' ⊤ volume + eLpNorm (fun z => s * ν' z) ⊤ volume := by
        rw [hrw]
        exact eLpNorm_add_le hκm.aestronglyMeasurable
          (measurable_const.mul hνm).aestronglyMeasurable le_top
      rw [eLpNorm_exponent_top, eLpNorm_exponent_top, eLpNorm_exponent_top] at h1
      have h2 : eLpNormEssSup (fun z => s * ν' z) volume
          = ‖s‖ₑ * eLpNormEssSup ν' volume := by
        have hsmul : (fun z => s * ν' z) = s • ν' := by
          funext z
          show s * ν' z = (s • ν') z
          rw [Pi.smul_apply, smul_eq_mul]
        rw [hsmul]
        exact MeasureTheory.eLpNormEssSup_const_smul s ν'
      calc eLpNormEssSup μs volume
          ≤ eLpNormEssSup κ' volume + eLpNormEssSup (fun z => s * ν' z) volume := h1
        _ = ENNReal.ofReal k' + ‖s‖ₑ * eLpNormEssSup ν' volume := by
            rw [hκessOfReal, h2]
        _ ≤ ENNReal.ofReal k' + ENNReal.ofReal ‖s‖ * ENNReal.ofReal M' :=
            add_le_add le_rfl
              (mul_le_mul' (le_of_eq (ofReal_norm_eq_enorm s).symm) hνb')
        _ = ENNReal.ofReal (k' + ‖s‖ * M') := by
            rw [← ENNReal.ofReal_mul (norm_nonneg s),
              ← ENNReal.ofReal_add hk'0 (mul_nonneg (norm_nonneg s) hM0.le)]
    have hμs1 : eLpNormEssSup μs volume < 1 := by
      refine lt_of_le_of_lt hμsess (ENNReal.ofReal_lt_one.mpr ?_)
      exact lt_of_le_of_lt (hsmallA s hs) hmidA
    have hμsfin : eLpNormEssSup μs volume ≠ ⊤ := (lt_trans hμs1 ENNReal.one_lt_top).ne
    have hμsLp : MemLp μs p volume :=
      memLp_of_eLpNormEssSup_ne_top_of_support hp' hμsm hμsfin hμsupp'
    have hμsRe : (eLpNormEssSup μs volume).toReal ≤ k' + ‖s‖ * M' := by
      have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hμsess
      rwa [ENNReal.toReal_ofReal
        (add_nonneg hk'0 (mul_nonneg (norm_nonneg s) hM0.le))] at h1
    have hμscontr : (eLpNormEssSup μs volume).toReal * C < 1 := by
      have h1 : (eLpNormEssSup μs volume).toReal * C ≤ (k' + ‖s‖ * M') * C :=
        mul_le_mul_of_nonneg_right hμsRe hC0
      exact lt_of_le_of_lt (le_trans h1 (hsmallB s hs)) hmidB
    -- the fixed point for the affine coefficient and its canonical representative
    obtain ⟨h, hhLp, hheq, _⟩ :=
      exists_lp_fixedPoint_beltrami hp hp' hμsm hμsfin hCb hμscontr hμsLp
    set h' : ℂ → ℂ := fun z => μs z * beurling h z + μs z with hh'def
    have hh'ae : h' =ᵐ[volume] h := hheq.symm
    have hh'Lp : MemLp h' p volume := hhLp.ae_eq hheq
    have hh'supp : ∀ z : ℂ, R < ‖z‖ → h' z = 0 := by
      intro z hz
      change μs z * beurling h z + μs z = 0
      rw [hμsupp' z hz, zero_mul, zero_add]
    have hh'L2 : MemLp h' 2 volume := hL2 h' hh'Lp hh'supp
    have hhL2 : MemLp h 2 volume := hh'L2.ae_eq hh'ae
    have hSeq : beurling h =ᵐ[volume] beurling h' := beurling_congr_ae hhL2 hh'L2 hheq
    have heq' : h' =ᵐ[volume] fun z => μs z * beurling h' z + μs z := by
      filter_upwards [hSeq] with z hz
      change μs z * beurling h z + μs z = μs z * beurling h' z + μs z
      rw [hz]
    have hprin : IsPrincipalSolution ⟨μs, hμsm, hμs1⟩ (fun z => z + cauchyTransform h' z) :=
      ⟨p, h', R, hp, hp', hh'Lp, hh'supp, heq', fun z => rfl⟩
    -- ===== the partial sums of the Neumann series =====
    set sP : ℕ → ℂ → ℂ := fun N z => ∑ n ∈ Finset.range N, s ^ n * a n z with hsPdef
    have hsP_zero : ∀ z : ℂ, sP 0 z = 0 := by
      intro z
      change ∑ n ∈ Finset.range 0, s ^ n * a n z = 0
      rw [Finset.sum_range_zero]
    have hsP_succ : ∀ (N : ℕ) (z : ℂ), sP (N + 1) z = sP N z + s ^ N * a N z := by
      intro N z
      change ∑ n ∈ Finset.range (N + 1), s ^ n * a n z
          = ∑ n ∈ Finset.range N, s ^ n * a n z + s ^ N * a N z
      rw [Finset.sum_range_succ]
    have hsPsupp : ∀ (N : ℕ) (z : ℂ), R < ‖z‖ → sP N z = 0 := by
      intro N z hz
      change ∑ n ∈ Finset.range N, s ^ n * a n z = 0
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [hasupp n z hz, mul_zero]
    have hsPLp : ∀ N : ℕ, MemLp (sP N) p volume := fun N =>
      memLp_finset_sum _ fun n _ => (haLp n).const_mul (s ^ n)
    have hsPL2 : ∀ N : ℕ, MemLp (sP N) 2 volume := fun N => hL2 _ (hsPLp N) (hsPsupp N)
    -- incremental linearity of the Beurling transform over the partial sums
    have hSstep : ∀ N : ℕ, beurling (sP (N + 1))
        =ᵐ[volume] fun z => beurling (sP N) z + s ^ N * beurling (a N) z := by
      intro N
      have hdecomp : sP (N + 1) = sP N + (s ^ N) • a N := by
        funext z
        rw [hsP_succ N z]
        rfl
      have hadd := beurling_add_ae_lp hp hp' (hsPLp N) ((haLp N).const_smul (s ^ N))
      have hsm := beurling_smul_ae (s ^ N) (Or.inl (haL2 N))
      rw [hdecomp]
      filter_upwards [hadd, hsm] with z hzadd hzsm
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hzadd hzsm
      rw [hzadd, hzsm]
    have hS0 : beurling (sP 0) =ᵐ[volume] fun _ : ℂ => (0 : ℂ) := by
      have h00 : sP 0 = (0 : ℂ) • a 0 := by
        funext z
        rw [hsP_zero z]
        show (0 : ℂ) = ((0 : ℂ) • a 0) z
        rw [Pi.smul_apply, zero_smul]
      have hb0 := beurling_smul_ae (0 : ℂ) (Or.inl (haL2 0))
      rw [← h00] at hb0
      filter_upwards [hb0] with z hz
      rw [hz, Pi.smul_apply, zero_smul]
    -- ===== the defect identity =====
    have hdefect : ∀ N : ℕ, (fun z => μs z * beurling (sP (N + 2)) z + μs z)
        =ᵐ[volume] fun z => sP (N + 2) z + s ^ (N + 2) * (ν' z * beurling (a (N + 1)) z) := by
      intro N
      induction N with
      | zero =>
        filter_upwards [hS0, hSstep 0, hSstep 1, hae0, haeS 0] with z h0 h1 h2 hA0 hA1
        change μs z * beurling (sP 2) z + μs z
            = sP 2 z + s ^ 2 * (ν' z * beurling (a 1) z)
        have h0' : beurling (sP 0) z = 0 := h0
        have h1' : beurling (sP 1) z = beurling (sP 0) z + s ^ 0 * beurling (a 0) z := h1
        have h2' : beurling (sP 2) z = beurling (sP 1) z + s ^ 1 * beurling (a 1) z := h2
        have hA0' : a 0 z = κ' z * beurling (a 0) z + κ' z := hA0
        have hA1' : a 1 z
            = κ' z * beurling (a 1) z + (ν' z * beurling (a 0) z + eterm 0 z) := hA1
        have he0z : eterm 0 z = ν' z := by rw [het0]
        rw [he0z] at hA1'
        have hsP2 : sP 2 z = a 0 z + s * a 1 z := by
          change ∑ n ∈ Finset.range 2, s ^ n * a n z = a 0 z + s * a 1 z
          rw [show (2 : ℕ) = 0 + 1 + 1 by rfl, Finset.sum_range_succ, Finset.sum_range_succ,
            Finset.sum_range_zero]
          ring
        have hB2 : beurling (sP 2) z = beurling (a 0) z + s * beurling (a 1) z := by
          rw [h2', h1', h0']
          ring
        rw [hB2, hsP2, hμsdef]
        change (κ' z + s * ν' z) * (beurling (a 0) z + s * beurling (a 1) z)
            + (κ' z + s * ν' z)
            = a 0 z + s * a 1 z + s ^ 2 * (ν' z * beurling (a 1) z)
        linear_combination -hA0' - s * hA1'
      | succ m ih =>
        filter_upwards [ih, hSstep (m + 2), haeS (m + 1)] with z hih hss ham2
        change μs z * beurling (sP (m + 3)) z + μs z
            = sP (m + 3) z + s ^ (m + 3) * (ν' z * beurling (a (m + 2)) z)
        have hss' : beurling (sP (m + 3)) z
            = beurling (sP (m + 2)) z + s ^ (m + 2) * beurling (a (m + 2)) z := hss
        have ham2' : a (m + 2) z = κ' z * beurling (a (m + 2)) z
            + (ν' z * beurling (a (m + 1)) z + eterm (m + 1) z) := ham2
        have hetz : eterm (m + 1) z = 0 := by rw [hetS m]
        rw [hetz, add_zero] at ham2'
        have hexp : sP (m + 3) z = sP (m + 2) z + s ^ (m + 2) * a (m + 2) z :=
          hsP_succ (m + 2) z
        rw [hss', hexp, hμsdef]
        change (κ' z + s * ν' z) * (beurling (sP (m + 2)) z + s ^ (m + 2) * beurling (a (m + 2))
            z)
            + (κ' z + s * ν' z)
            = sP (m + 2) z + s ^ (m + 2) * a (m + 2) z
              + s ^ (m + 3) * (ν' z * beurling (a (m + 2)) z)
        have hih' : (κ' z + s * ν' z) * beurling (sP (m + 2)) z + (κ' z + s * ν' z)
            = sP (m + 2) z + s ^ (m + 2) * (ν' z * beurling (a (m + 1)) z) := hih
        linear_combination hih' - s ^ (m + 2) * ham2'
    -- ===== the contraction estimate and geometric decay of the error =====
    have hbeurling_sub : ∀ u v : ℂ → ℂ, MemLp u p volume → MemLp v p volume →
        beurling (fun w => u w - v w)
          =ᵐ[volume] fun z => beurling u z - beurling v z := by
      intro u v hu hv
      have hadd := beurling_add_ae_lp hp hp' hv
        (show MemLp (fun w => u w - v w) p volume from hu.sub hv)
      have hvuv : (v + fun w => u w - v w) = u := by
        funext w
        simp
      rw [hvuv] at hadd
      filter_upwards [hadd] with z hz
      simp only [Pi.add_apply] at hz
      rw [hz]
      ring
    set Λ : ℝ := (1 + k' * C) / 2 with hΛdef
    have hΛ0 : 0 ≤ Λ := by
      rw [hΛdef]
      have : 0 ≤ k' * C := mul_nonneg hk'0 hC0
      linarith
    have hΛ1 : Λ < 1 := hmidB
    have hcontrΛ : ∀ u v : ℂ → ℂ, MemLp u p volume → MemLp v p volume →
        eLpNorm (fun z => μs z * beurling u z - μs z * beurling v z) p volume
          ≤ ENNReal.ofReal Λ * eLpNorm (fun z => u z - v z) p volume := by
      intro u v hu hv
      have h1 : (fun z => μs z * beurling u z - μs z * beurling v z)
          =ᵐ[volume] fun z => μs z * beurling (fun w => u w - v w) z := by
        filter_upwards [hbeurling_sub u v hu hv] with z hz
        rw [hz]
        ring
      calc eLpNorm (fun z => μs z * beurling u z - μs z * beurling v z) p volume
          = eLpNorm (fun z => μs z * beurling (fun w => u w - v w) z) p volume :=
            eLpNorm_congr_ae h1
        _ ≤ eLpNormEssSup μs volume
              * eLpNorm (beurling (fun w => u w - v w)) p volume :=
            eLpNorm_mul_le_essSup_mul hμsm.aestronglyMeasurable
              (memLp_beurling_of_memLp hp hp' (hu.sub hv))
        _ ≤ ENNReal.ofReal (k' + ‖s‖ * M')
              * (ENNReal.ofReal C * eLpNorm (fun w => u w - v w) p volume) :=
            mul_le_mul' hμsess (hCbound _ (hu.sub hv))
        _ = ENNReal.ofReal ((k' + ‖s‖ * M') * C) * eLpNorm (fun w => u w - v w) p volume := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul
              (add_nonneg hk'0 (mul_nonneg (norm_nonneg s) hM0.le))]
        _ ≤ ENNReal.ofReal Λ * eLpNorm (fun w => u w - v w) p volume := by
            gcongr
            exact hsmallB s hs
    -- the norm of the defect term
    have hnuS : ∀ n : ℕ, eLpNorm (fun z => ν' z * beurling (a n) z) p volume
        ≤ ENNReal.ofReal (M' * C) * eLpNorm (a n) p volume := by
      intro n
      calc eLpNorm (fun z => ν' z * beurling (a n) z) p volume
          ≤ eLpNormEssSup ν' volume * eLpNorm (beurling (a n)) p volume :=
            eLpNorm_mul_le_essSup_mul hνm.aestronglyMeasurable
              (memLp_beurling_of_memLp hp hp' (haLp n))
        _ ≤ ENNReal.ofReal M' * (ENNReal.ofReal C * eLpNorm (a n) p volume) :=
            mul_le_mul' hνb' (hCbound (a n) (haLp n))
        _ = ENNReal.ofReal (M' * C) * eLpNorm (a n) p volume := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hM0.le]
    -- the error sequence and its bound
    have hErrLp : ∀ N : ℕ, MemLp (fun z => h' z - sP (N + 2) z) p volume := fun N =>
      hh'Lp.sub (hsPLp (N + 2))
    have hEstep : ∀ N : ℕ, eLpNorm (fun z => h' z - sP (N + 2) z) p volume
        ≤ ENNReal.ofReal Λ * eLpNorm (fun z => h' z - sP (N + 2) z) p volume
          + ENNReal.ofReal (‖s‖ ^ (N + 2) * (M' * C * (ρ ^ N * A1))) := by
      intro N
      have hsplit : (fun z => h' z - sP (N + 2) z) =ᵐ[volume]
          fun z => (μs z * beurling h' z - μs z * beurling (sP (N + 2)) z)
            + s ^ (N + 2) * (ν' z * beurling (a (N + 1)) z) := by
        filter_upwards [heq', hdefect N] with z h1 h2
        have h2' : μs z * beurling (sP (N + 2)) z + μs z
            = sP (N + 2) z + s ^ (N + 2) * (ν' z * beurling (a (N + 1)) z) := h2
        have h1' : h' z = μs z * beurling h' z + μs z := h1
        change h' z - sP (N + 2) z
            = μs z * beurling h' z - μs z * beurling (sP (N + 2)) z
              + s ^ (N + 2) * (ν' z * beurling (a (N + 1)) z)
        linear_combination h1' + h2'
      have htri : eLpNorm (fun z => h' z - sP (N + 2) z) p volume
          ≤ eLpNorm (fun z => μs z * beurling h' z - μs z * beurling (sP (N + 2)) z) p volume
            + eLpNorm (fun z => s ^ (N + 2) * (ν' z * beurling (a (N + 1)) z)) p volume := by
        rw [eLpNorm_congr_ae hsplit]
        have hm1 : AEStronglyMeasurable
            (fun z => μs z * beurling h' z - μs z * beurling (sP (N + 2)) z) volume := by
          have hx : (fun z => μs z * beurling h' z - μs z * beurling (sP (N + 2)) z)
              =ᵐ[volume] fun z => μs z * beurling (fun w => h' w - sP (N + 2) w) z := by
            filter_upwards [hbeurling_sub h' (sP (N + 2)) hh'Lp (hsPLp (N + 2))] with z hz
            rw [hz]
            ring
          exact (hμsm.aestronglyMeasurable.mul
            (memLp_beurling_of_memLp hp hp' (hErrLp N)).1).congr hx.symm
        have hm2 : AEStronglyMeasurable
            (fun z => s ^ (N + 2) * (ν' z * beurling (a (N + 1)) z)) volume :=
          aestronglyMeasurable_const.mul (hνm.aestronglyMeasurable.mul
            (memLp_beurling_of_memLp hp hp' (haLp (N + 1))).1)
        have h3 := eLpNorm_add_le hm1 hm2 (le_of_lt (lt_trans ENNReal.one_lt_two hp))
        exact h3
      have hdterm : eLpNorm (fun z => s ^ (N + 2) * (ν' z * beurling (a (N + 1)) z)) p volume
          ≤ ENNReal.ofReal (‖s‖ ^ (N + 2) * (M' * C * (ρ ^ N * A1))) := by
        have hsm : (fun z => s ^ (N + 2) * (ν' z * beurling (a (N + 1)) z))
            = (s ^ (N + 2)) • fun z => ν' z * beurling (a (N + 1)) z := by
          funext z
          rw [Pi.smul_apply, smul_eq_mul]
        rw [hsm, eLpNorm_const_smul]
        have h4 : ‖s ^ (N + 2)‖ₑ = ENNReal.ofReal (‖s‖ ^ (N + 2)) := by
          rw [← ofReal_norm_eq_enorm, norm_pow]
        rw [h4]
        calc ENNReal.ofReal (‖s‖ ^ (N + 2))
              * eLpNorm (fun z => ν' z * beurling (a (N + 1)) z) p volume
            ≤ ENNReal.ofReal (‖s‖ ^ (N + 2))
                * (ENNReal.ofReal (M' * C) * eLpNorm (a (N + 1)) p volume) := by
              gcongr
              exact hnuS (N + 1)
          _ ≤ ENNReal.ofReal (‖s‖ ^ (N + 2))
                * (ENNReal.ofReal (M' * C) * ENNReal.ofReal (ρ ^ N * A1)) := by
              gcongr
              have h5 := hAgeoR N
              calc eLpNorm (a (N + 1)) p volume
                  = ENNReal.ofReal (eLpNorm (a (N + 1)) p volume).toReal :=
                    (ENNReal.ofReal_toReal (hAfin (N + 1))).symm
                _ ≤ ENNReal.ofReal (ρ ^ N * A1) := ENNReal.ofReal_le_ofReal h5
          _ = ENNReal.ofReal (‖s‖ ^ (N + 2) * (M' * C * (ρ ^ N * A1))) := by
              rw [← ENNReal.ofReal_mul (by positivity),
                ← ENNReal.ofReal_mul (by positivity)]
      calc eLpNorm (fun z => h' z - sP (N + 2) z) p volume
          ≤ eLpNorm (fun z => μs z * beurling h' z - μs z * beurling (sP (N + 2)) z) p volume
            + eLpNorm (fun z => s ^ (N + 2) * (ν' z * beurling (a (N + 1)) z)) p volume :=
            htri
        _ ≤ ENNReal.ofReal Λ * eLpNorm (fun z => h' z - sP (N + 2) z) p volume
            + ENNReal.ofReal (‖s‖ ^ (N + 2) * (M' * C * (ρ ^ N * A1))) :=
            add_le_add (hcontrΛ h' (sP (N + 2)) hh'Lp (hsPLp (N + 2))) hdterm
    -- pass to real numbers and solve the inequality
    have hEfin : ∀ N : ℕ, eLpNorm (fun z => h' z - sP (N + 2) z) p volume ≠ ⊤ := fun N =>
      (hErrLp N).2.ne
    have hEreal : ∀ N : ℕ, (eLpNorm (fun z => h' z - sP (N + 2) z) p volume).toReal
        ≤ (‖s‖ ^ (N + 2) * (M' * C * (ρ ^ N * A1))) / (1 - Λ) := by
      intro N
      set EN : ℝ := (eLpNorm (fun z => h' z - sP (N + 2) z) p volume).toReal with hENdef
      have hEN0 : 0 ≤ EN := ENNReal.toReal_nonneg
      have h1 := hEstep N
      have h2 : EN ≤ Λ * EN + ‖s‖ ^ (N + 2) * (M' * C * (ρ ^ N * A1)) := by
        have hne : ENNReal.ofReal Λ * eLpNorm (fun z => h' z - sP (N + 2) z) p volume
            + ENNReal.ofReal (‖s‖ ^ (N + 2) * (M' * C * (ρ ^ N * A1))) ≠ ⊤ :=
          ENNReal.add_ne_top.mpr
            ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hEfin N), ENNReal.ofReal_ne_top⟩
        have h3 := ENNReal.toReal_mono hne h1
        rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hEfin N))
          ENNReal.ofReal_ne_top, ENNReal.toReal_mul, ENNReal.toReal_ofReal hΛ0,
          ENNReal.toReal_ofReal (by positivity)] at h3
      have h4 : (1 - Λ) * EN ≤ ‖s‖ ^ (N + 2) * (M' * C * (ρ ^ N * A1)) := by nlinarith only [h2]
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - Λ)]
      nlinarith only [h4]
    have hEtend : Filter.Tendsto
        (fun N : ℕ => (eLpNorm (fun z => h' z - sP (N + 2) z) p volume).toReal)
        Filter.atTop (nhds 0) := by
      have hgeo : Filter.Tendsto
          (fun N : ℕ => ‖s‖ ^ 2 * (M' * C * A1) / (1 - Λ) * (‖s‖ * ρ) ^ N)
          Filter.atTop (nhds 0) := by
        have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one
          (mul_nonneg (norm_nonneg s) hρ0) hsρ
        have h2 := h1.const_mul (‖s‖ ^ 2 * (M' * C * A1) / (1 - Λ))
        simpa using h2
      refine squeeze_zero (fun N => ENNReal.toReal_nonneg) (fun N => ?_) hgeo
      refine le_trans (hEreal N) (le_of_eq ?_)
      rw [mul_pow]
      ring
    -- ===== pointwise convergence of the Cauchy transforms =====
    refine ⟨⟨μs, hμsm, hμs1⟩, fun z => rfl, ?_⟩
    have hser : ∀ z : ℂ, cauchyTransform h' z = ∑' n : ℕ, s ^ n * c n z := by
      intro z
      -- finite linearity of the Cauchy transform over the partial sums
      have hPsum : ∀ N : ℕ, cauchyTransform (sP N) z
          = ∑ n ∈ Finset.range N, s ^ n * c n z := by
        intro N
        have hint : ∀ n : ℕ, Integrable (fun ζ => a n ζ / (ζ - z)) volume := fun n =>
          integrable_div_sub_of_memLp_of_support hp hp' (haLp n) (hasupp n) z
        have hsdiv : (fun ζ => sP N ζ / (ζ - z))
            = fun ζ => ∑ n ∈ Finset.range N, s ^ n * (a n ζ / (ζ - z)) := by
          funext ζ
          change (∑ n ∈ Finset.range N, s ^ n * a n ζ) / (ζ - z) = _
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun n _ => mul_div_assoc _ _ _
        change -(1 / (Real.pi : ℂ)) * ∫ ζ, sP N ζ / (ζ - z)
            = ∑ n ∈ Finset.range N, s ^ n * c n z
        rw [hsdiv, integral_finset_sum _ (fun n _ => (hint n).const_mul (s ^ n)),
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        have hcm : ∫ ζ, s ^ n * (a n ζ / (ζ - z)) = s ^ n * ∫ ζ, a n ζ / (ζ - z) :=
          integral_const_mul _ _
        rw [hcm]
        change -(1 / (Real.pi : ℂ)) * (s ^ n * ∫ ζ, a n ζ / (ζ - z))
            = s ^ n * (-(1 / (Real.pi : ℂ)) * ∫ ζ, a n ζ / (ζ - z))
        ring
      -- the Cauchy transform of the error field
      have hPdiff : ∀ N : ℕ, cauchyTransform h' z - cauchyTransform (sP (N + 2)) z
          = cauchyTransform (fun w => h' w - sP (N + 2) w) z := by
        intro N
        have hinth : Integrable (fun ζ => h' ζ / (ζ - z)) volume :=
          integrable_div_sub_of_memLp_of_support hp hp' hh'Lp hh'supp z
        have hints : Integrable (fun ζ => sP (N + 2) ζ / (ζ - z)) volume :=
          integrable_div_sub_of_memLp_of_support hp hp' (hsPLp (N + 2)) (hsPsupp (N + 2)) z
        have hdiv : (fun ζ => (h' ζ - sP (N + 2) ζ) / (ζ - z))
            = fun ζ => h' ζ / (ζ - z) - sP (N + 2) ζ / (ζ - z) := by
          funext ζ
          rw [sub_div]
        change -(1 / (Real.pi : ℂ)) * (∫ ζ, h' ζ / (ζ - z))
              - -(1 / (Real.pi : ℂ)) * (∫ ζ, sP (N + 2) ζ / (ζ - z))
            = -(1 / (Real.pi : ℂ)) * ∫ ζ, (h' ζ - sP (N + 2) ζ) / (ζ - z)
        rw [hdiv, integral_sub hinth hints]
        ring
      have hErrsupp : ∀ N : ℕ, ∀ w : ℂ, R < ‖w‖ → h' w - sP (N + 2) w = 0 := by
        intro N w hw
        rw [hh'supp w hw, hsPsupp (N + 2) w hw, sub_zero]
      -- the summand bound and summability of the series
      have hsummand : ∀ n : ℕ, ‖s ^ n * c n z‖
          ≤ (if n = 0 then Mc else ‖s‖ * Mc * (‖s‖ * ρ) ^ (n - 1)) := by
        intro n
        cases n with
        | zero =>
          simp only [pow_zero, one_mul]
          exact hcb0 z
        | succ m =>
          simp only [if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel]
          calc ‖s ^ (m + 1) * c (m + 1) z‖ = ‖s‖ ^ (m + 1) * ‖c (m + 1) z‖ := by
                rw [norm_mul, norm_pow]
            _ ≤ ‖s‖ ^ (m + 1) * (Mc * ρ ^ m) :=
                mul_le_mul_of_nonneg_left (hcb1 m z) (pow_nonneg (norm_nonneg s) _)
            _ = ‖s‖ * Mc * (‖s‖ * ρ) ^ m := by
                rw [mul_pow, pow_succ]
                ring
      have hsummable : Summable (fun n : ℕ => s ^ n * c n z) := by
        refine Summable.of_norm_bounded
          (g := fun n => if n = 0 then Mc else ‖s‖ * Mc * (‖s‖ * ρ) ^ (n - 1)) ?_ hsummand
        have h1 : Summable (fun m : ℕ => ‖s‖ * Mc * (‖s‖ * ρ) ^ m) :=
          (summable_geometric_of_lt_one (mul_nonneg (norm_nonneg s) hρ0) hsρ).mul_left _
        refine (summable_nat_add_iff 1).mp ?_
        refine h1.congr fun m => ?_
        simp
      have htendP : Filter.Tendsto
          (fun N : ℕ => ∑ n ∈ Finset.range (N + 2), s ^ n * c n z)
          Filter.atTop (nhds (cauchyTransform h' z)) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        have hb : ∀ N : ℕ, ‖(∑ n ∈ Finset.range (N + 2), s ^ n * c n z)
            - cauchyTransform h' z‖
            ≤ C₀ * (eLpNorm (fun w => h' w - sP (N + 2) w) p volume).toReal := by
          intro N
          rw [norm_sub_rev, ← hPsum (N + 2), hPdiff N]
          exact hC₀ _ (hErrLp N) (hErrsupp N) z
        refine squeeze_zero (fun N => norm_nonneg _) hb ?_
        have h2 := hEtend.const_mul C₀
        simpa using h2
      have htendT : Filter.Tendsto
          (fun N : ℕ => ∑ n ∈ Finset.range (N + 2), s ^ n * c n z)
          Filter.atTop (nhds (∑' n : ℕ, s ^ n * c n z)) := by
        have h1 := hsummable.hasSum.tendsto_sum_nat
        exact h1.comp (Filter.tendsto_add_atTop_nat 2)
      exact tendsto_nhds_unique htendP htendT
    have hfun : (fun z => z + ∑' n : ℕ, s ^ n * c n z)
        = fun z => z + cauchyTransform h' z := by
      funext z
      rw [hser z]
    rw [hfun]
    exact hprin
  · -- ===== the collapse at a vanishing base coefficient =====
    intro hκ0
    obtain ⟨h₀, hstr⟩ := hFP6 κ' hκLp hκs hκu
    have ha0z : ∀ w : ℂ, a 0 w = 0 := by
      intro w
      have h1 : a 0 = fun z => κ' z * beurling h₀ z + κ' z := ha0.trans hstr
      rw [h1]
      change κ' w * beurling h₀ w + κ' w = 0
      rw [hκ0 w, zero_mul, zero_add]
    constructor
    · intro z
      change cauchyTransform (a 0) z = 0
      rw [cauchyTransform]
      have hzero : (fun ζ => a 0 ζ / (ζ - z)) = fun _ : ℂ => (0 : ℂ) := by
        funext ζ
        rw [ha0z ζ, zero_div]
      rw [hzero, integral_zero, mul_zero]
    · intro z
      have ha0fn : a 0 = (0 : ℂ) • a 0 := by
        funext w
        rw [Pi.smul_apply, zero_smul, ha0z w]
      have hb0 : beurling (a 0) =ᵐ[volume] fun _ : ℂ => (0 : ℂ) := by
        have h1 := beurling_smul_ae (0 : ℂ) (Or.inl (haL2 0))
        rw [← ha0fn] at h1
        filter_upwards [h1] with w hw
        rw [hw, Pi.smul_apply, zero_smul]
      have ha1 : a 1 =ᵐ[volume] ν' := by
        filter_upwards [haeS 0, hb0] with w h1 h2
        have h1' : a 1 w
            = κ' w * beurling (a 1) w + (ν' w * beurling (a 0) w + eterm 0 w) := h1
        have h2' : beurling (a 0) w = 0 := h2
        have he0 : eterm 0 w = ν' w := by rw [het0]
        change a 1 w = ν' w
        rw [h1', he0, hκ0 w, zero_mul, zero_add, h2', mul_zero, zero_add]
      change cauchyTransform (a 1) z = cauchyTransform ν' z
      rw [cauchyTransform, cauchyTransform]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [ha1] with ζ hζ
      show a 1 ζ / (ζ - z) = ν' ζ / (ζ - z)
      rw [hζ]

/-- Post-composition with a nonzero affine map preserves quasiconformal analyticity
for the same Beltrami coefficient. -/
theorem isQCAnalytic_affine_postcomp (F : ℂ → ℂ) (bF : BeltramiCoeff) (a c : ℂ)
    (ha : a ≠ 0) (hF : IsQCAnalytic F bF) :
    IsQCAnalytic (fun z => a * (F z - c)) bF := by
  classical
  have hLIofL2 : ∀ {w : ℂ → ℂ}, MemLpLocOn w 2 Set.univ →
      LocallyIntegrableOn w Set.univ := by
    intro w hw
    rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro Kc hKc
    haveI : IsFiniteMeasure (volume.restrict Kc) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp
      ((hw Kc (Set.subset_univ _) hKc).mono_exponent (by norm_num))
  obtain ⟨⟨hFhomeo, hFdet⟩, hFW12, hFbelt⟩ := hF
  have hFcont : Continuous F := hFhomeo.continuous
  have hFdiff : ∀ᵐ z : ℂ, DifferentiableAt ℝ F z := by
    filter_upwards [hFdet] with z hz
    by_contra hnd
    rw [det_fderiv_eq_wirtinger] at hz
    simp [dz, dzbar, fderiv_zero_of_not_differentiableAt hnd] at hz
  have hkey : ∀ᵐ z : ℂ, fderiv ℝ (fun w => a * (F w - c)) z = a • fderiv ℝ F z := by
    filter_upwards [hFdiff] with z hz
    have h1 : DifferentiableAt ℝ (fun w => F w - c) z := hz.sub_const c
    have hfun : (fun w => a * (F w - c)) = a • fun w => F w - c := by
      funext w
      simp [smul_eq_mul]
    rw [hfun, fderiv_const_smul h1 a, fderiv_sub_const]
  have hdzs : ∀ᵐ z : ℂ, dz (fun w => a * (F w - c)) z = a * dz F z
      ∧ dzbar (fun w => a * (F w - c)) z = a * dzbar F z := by
    filter_upwards [hkey] with z hk
    constructor
    · simp only [dz, hk, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    · simp only [dzbar, hk, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
  have hAhomeo : IsHomeomorph (fun z => a * (F z - c)) := by
    have h1 := ((Homeomorph.subRight c).trans (Homeomorph.mulLeft₀ a ha)).isHomeomorph
    have h2 : ⇑((Homeomorph.subRight c).trans (Homeomorph.mulLeft₀ a ha))
        = fun w : ℂ => a * (w - c) := by
      funext w
      simp [Homeomorph.trans_apply]
    rw [h2] at h1
    exact h1.comp hFhomeo
  have hAdet : ∀ᵐ z : ℂ, 0 < (fderiv ℝ (fun w => a * (F w - c)) z).det := by
    filter_upwards [hdzs, hFdet] with z hdw hd
    rw [det_fderiv_eq_wirtinger, hdw.1, hdw.2, norm_mul, norm_mul, mul_pow, mul_pow,
      ← mul_sub]
    rw [det_fderiv_eq_wirtinger] at hd
    exact mul_pos (pow_pos (norm_pos_iff.mpr ha) 2) hd
  have hAcont : Continuous fun z => a * (F z - c) :=
    continuous_const.mul (hFcont.sub continuous_const)
  have hAW12 : MemW12loc (fun z => a * (F z - c)) := by
    obtain ⟨hFloc, gx, gy, hFgrad, hgx, hgy⟩ := hFW12
    have hconst : ∀ v : ℂ, HasWeakDirDeriv v (fun _ : ℂ => (0 : ℂ)) (fun _ : ℂ => c)
        Set.univ := by
      intro v
      have h := HasWeakDirDeriv.of_contDiffOn (v := v) isOpen_univ
        (contDiffOn_const (c := c))
      have hzero : (fun z : ℂ => (fderiv ℝ (fun _ : ℂ => c) z) v) = fun _ => (0 : ℂ) := by
        funext z
        rw [(hasFDerivAt_const c z).fderiv]
        simp
      rwa [hzero] at h
    have hLIF : LocallyIntegrableOn F Set.univ :=
      hFcont.locallyIntegrable.locallyIntegrableOn _
    have hLIc : LocallyIntegrableOn (fun _ : ℂ => c) Set.univ :=
      continuous_const.locallyIntegrable.locallyIntegrableOn _
    have hLI0 : LocallyIntegrableOn (fun _ : ℂ => (0 : ℂ)) Set.univ :=
      continuous_const.locallyIntegrable.locallyIntegrableOn _
    have hgoalx : HasWeakDirDeriv 1 (fun z => a * gx z) (fun z => a * (F z - c))
        Set.univ := by
      have hsub := HasWeakDirDeriv.sub hFgrad.1 (hconst 1) hLIF hLIc (hLIofL2 hgx) hLI0
      have hsub' : HasWeakDirDeriv 1 gx (fun z => F z - c) Set.univ := by
        simpa using hsub
      simpa [smul_eq_mul] using HasWeakDirDeriv.const_smul a hsub'
    have hgoaly : HasWeakDirDeriv Complex.I (fun z => a * gy z) (fun z => a * (F z - c))
        Set.univ := by
      have hsub := HasWeakDirDeriv.sub hFgrad.2 (hconst Complex.I) hLIF hLIc
        (hLIofL2 hgy) hLI0
      have hsub' : HasWeakDirDeriv Complex.I gy (fun z => F z - c) Set.univ := by
        simpa using hsub
      simpa [smul_eq_mul] using HasWeakDirDeriv.const_smul a hsub'
    have hAloc : MemLpLocOn (fun z => a * (F z - c)) 2 Set.univ := by
      intro Kc _ hKc
      haveI : IsFiniteMeasure (volume.restrict Kc) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
      obtain ⟨Cb, hCb⟩ := hKc.exists_bound_of_continuousOn hAcont.continuousOn
      refine MemLp.of_bound hAcont.aestronglyMeasurable.restrict Cb ?_
      filter_upwards [ae_restrict_mem hKc.measurableSet] with z hz
      exact hCb z hz
    exact ⟨hAloc, fun z => a * gx z, fun z => a * gy z, ⟨hgoalx, hgoaly⟩,
      fun Kc hs hKc => (hgx Kc hs hKc).const_mul a,
      fun Kc hs hKc => (hgy Kc hs hKc).const_mul a⟩
  have hAbelt : ∀ᵐ z, dzbar (fun w => a * (F w - c)) z
      = bF.μ z * dz (fun w => a * (F w - c)) z := by
    filter_upwards [hdzs, hFbelt] with z hdw hb
    rw [hdw.1, hdw.2, hb]
    ring
  exact ⟨⟨hAhomeo, hAdet⟩, hAW12, hAbelt⟩

/-- **Uniform bound on balls**: normalized `K`-quasiconformal geometric maps admit one
bound on each ball, uniformly over the class. -/
theorem exists_uniform_bound_isQCGeometric (Kq ℓ : ℝ) :
    ∃ B : ℝ, ∀ f : ℂ → ℂ,
    IsQCGeometric f Kq → f 0 = 0 → f 1 = 1 → ∀ z : ℂ, ‖z‖ ≤ ℓ → ‖f z‖ ≤ B := by
  classical
  have hScpt : IsCompact (Metric.closedBall (0 : ℂ) (max ℓ 1)) := isCompact_closedBall _ _
  have h0S : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) (max ℓ 1) := by
    rw [Metric.mem_closedBall, dist_self]
    exact le_max_of_le_right zero_le_one
  have h1S : (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) (max ℓ 1) := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_one]
    exact le_max_right ℓ 1
  obtain ⟨B, hB⟩ := exists_uniform_image_bound
    (ι := {f : ℂ → ℂ // IsQCGeometric f Kq ∧ f 0 = 0 ∧ f 1 = 1})
    (f := fun i => i.1) (fun i => i.2.1) hScpt h0S h1S zero_ne_one (M := 1)
    (fun i => by
      change dist (i.1 0) (i.1 1) ≤ 1
      rw [i.2.2.1, i.2.2.2]
      simp)
  refine ⟨B, fun f hf h0 h1 z hz => ?_⟩
  have hzS : z ∈ Metric.closedBall (0 : ℂ) (max ℓ 1) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans hz (le_max_left ℓ 1)
  have h2 := hB ⟨f, hf, h0, h1⟩ z hzS 0 h0S
  simp only at h2
  rw [h0, dist_eq_norm, sub_zero] at h2
  exact h2

/-- **The Vitali upgrade**: a locally bounded sequence of holomorphic functions on an
open set that converges pointwise converges locally uniformly. -/
theorem tendstoLocallyUniformlyOn_of_bounded_of_tendsto (G : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (U : Set ℂ) (hU : IsOpen U) (hdiff : ∀ j : ℕ, DifferentiableOn ℂ (G j) U)
    (hbnd : ∀ K : Set ℂ, K ⊆ U → IsCompact K →
      ∃ B : ℝ, ∀ (j : ℕ), ∀ t ∈ K, ‖G j t‖ ≤ B)
    (hptw : ∀ t ∈ U, Filter.Tendsto (fun j => G j t) Filter.atTop (nhds (g t))) :
    TendstoLocallyUniformlyOn G g Filter.atTop U := by
  classical
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  rcases K.eq_empty_or_nonempty with hKe | ⟨t₀, ht₀⟩
  · rw [hKe]
    rw [Metric.tendstoUniformlyOn_iff]
    intro εr hεr
    filter_upwards with j x hx
    exact absurd hx (Set.notMem_empty x)
  rw [Metric.tendstoUniformlyOn_iff]
  intro εr hεr
  obtain ⟨δ, hδ0, hδsub⟩ := hK.exists_cthickening_subset_open hU hKU
  have hK'cpt : IsCompact (Metric.cthickening δ K) := hK.cthickening
  have hK'U : Metric.cthickening δ K ⊆ U := hδsub
  have hKK' : K ⊆ Metric.cthickening δ K := Metric.self_subset_cthickening K
  obtain ⟨B, hB⟩ := hbnd _ hK'U hK'cpt
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 t₀ (hKK' ht₀))
  have hδ40 : (0 : ℝ) < δ / 4 := by linarith
  -- the closed `δ/2`-ball around a point of `K` lies in the thickening
  have hball2 : ∀ x : ℂ, x ∈ K → Metric.closedBall x (δ / 2) ⊆ Metric.cthickening δ K := by
    intro x hx w hw
    rw [Metric.mem_closedBall] at hw
    refine Metric.mem_cthickening_of_dist_le w x δ K hx ?_
    linarith
  -- uniform Cauchy derivative bound
  have hderiv : ∀ (j : ℕ) (x : ℂ), x ∈ K → ∀ w ∈ Metric.closedBall x (δ / 4),
      ‖deriv (G j) w‖ ≤ B / (δ / 4) := by
    intro j x hx w hw
    have hsub : Metric.closedBall w (δ / 4) ⊆ Metric.cthickening δ K := by
      intro v hv
      refine hball2 x hx ?_
      rw [Metric.mem_closedBall] at hv hw ⊢
      calc dist v x ≤ dist v w + dist w x := dist_triangle v w x
        _ ≤ δ / 4 + δ / 4 := add_le_add hv hw
        _ ≤ δ / 2 := by linarith
    have hdc : DiffContOnCl ℂ (G j) (Metric.ball w (δ / 4)) := by
      refine ⟨(hdiff j).mono ?_, ((hdiff j).continuousOn).mono ?_⟩
      · exact le_trans (le_trans Metric.ball_subset_closedBall hsub) hK'U
      · refine le_trans ?_ (le_trans hsub hK'U)
        exact le_trans Metric.closure_ball_subset_closedBall le_rfl
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ40 hdc ?_
    intro v hv
    exact hB j v (hsub (Metric.sphere_subset_closedBall hv))
  have hball4 : ∀ x : ℂ, x ∈ K →
      Metric.closedBall x (δ / 4) ⊆ Metric.cthickening δ K := by
    intro x hx
    exact (Metric.closedBall_subset_closedBall (by linarith)).trans (hball2 x hx)
  -- Lipschitz bound with constant `L := B / (δ/4)` at scale `δ/4`
  have hL0 : 0 ≤ B / (δ / 4) := div_nonneg hB0 hδ40.le
  have hLip : ∀ (j : ℕ) (x : ℂ), x ∈ K → ∀ y ∈ Metric.closedBall x (δ / 4),
      ‖G j y - G j x‖ ≤ B / (δ / 4) * ‖y - x‖ := by
    intro j x hx y hy
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := G j) (f' := fun w => deriv (G j) w) (s := Metric.closedBall x (δ / 4))
      ?_ (fun w hw => hderiv j x hx w hw) (convex_closedBall x (δ / 4))
      (Metric.mem_closedBall_self hδ40.le) hy
    intro w hw
    have hwU : w ∈ U := hK'U (hball4 x hx hw)
    exact (((hdiff j).differentiableAt (hU.mem_nhds hwU)).hasDerivAt).hasDerivWithinAt
  -- the limit inherits the Lipschitz bound
  have hgLip : ∀ x : ℂ, x ∈ K → ∀ y ∈ Metric.closedBall x (δ / 4),
      ‖g y - g x‖ ≤ B / (δ / 4) * ‖y - x‖ := by
    intro x hx y hy
    have hxU : x ∈ U := hKU hx
    have hyU : y ∈ U := hK'U (hball4 x hx hy)
    have h1 : Filter.Tendsto (fun j => ‖G j y - G j x‖) Filter.atTop
        (nhds ‖g y - g x‖) := ((hptw y hyU).sub (hptw x hxU)).norm
    exact le_of_tendsto h1 (Filter.Eventually.of_forall fun j => hLip j x hx y hy)
  -- the finite net
  set r₀ : ℝ := min (δ / 4) (εr / (3 * (B / (δ / 4) + 1))) with hr₀def
  have hr₀0 : 0 < r₀ := lt_min hδ40 (by positivity)
  have hr₀L : B / (δ / 4) * r₀ < εr / 3 := by
    have h1 : r₀ ≤ εr / (3 * (B / (δ / 4) + 1)) := min_le_right _ _
    have h2 : B / (δ / 4) * r₀ ≤ B / (δ / 4) * (εr / (3 * (B / (δ / 4) + 1))) :=
      mul_le_mul_of_nonneg_left h1 hL0
    have h3 : B / (δ / 4) * (εr / (3 * (B / (δ / 4) + 1))) < εr / 3 := by
      have h4 : B / (δ / 4) * (εr / (3 * (B / (δ / 4) + 1)))
          = εr * (B / (δ / 4)) / (3 * (B / (δ / 4) + 1)) := by ring
      rw [h4, div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 3)]
      nlinarith only [hL0, hεr]
    linarith
  have hcover : K ⊆ ⋃ i : {x : ℂ // x ∈ K}, Metric.ball i.1 r₀ := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self hr₀0⟩
  obtain ⟨tf, htf⟩ := hK.elim_finite_subcover
    (fun i : {x : ℂ // x ∈ K} => Metric.ball i.1 r₀) (fun i => Metric.isOpen_ball) hcover
  have hev : ∀ᶠ j in Filter.atTop, ∀ i ∈ tf, dist (G j i.1) (g i.1) < εr / 3 := by
    rw [Filter.eventually_all_finset]
    intro i _
    have h1 := hptw i.1 (hKU i.2)
    exact (Metric.tendsto_nhds.mp h1) (εr / 3) (by linarith)
  filter_upwards [hev] with j hj
  intro x hx
  obtain ⟨i, hi, hxi⟩ : ∃ i ∈ tf, x ∈ Metric.ball i.1 r₀ := by
    have h1 := htf hx
    rw [Set.mem_iUnion₂] at h1
    obtain ⟨i, hi, hxi⟩ := h1
    exact ⟨i, hi, hxi⟩
  have hxball : x ∈ Metric.closedBall i.1 (δ / 4) := by
    rw [Metric.mem_ball] at hxi
    rw [Metric.mem_closedBall]
    exact le_trans hxi.le (min_le_left _ _)
  have hd1 : ‖g x - g i.1‖ ≤ B / (δ / 4) * ‖x - i.1‖ := hgLip i.1 i.2 x hxball
  have hd3 : ‖G j x - G j i.1‖ ≤ B / (δ / 4) * ‖x - i.1‖ := hLip j i.1 i.2 x hxball
  have hxr : ‖x - i.1‖ < r₀ := by
    rw [Metric.mem_ball, dist_eq_norm] at hxi
    exact hxi
  have hmul : B / (δ / 4) * ‖x - i.1‖ ≤ B / (δ / 4) * r₀ :=
    mul_le_mul_of_nonneg_left hxr.le hL0
  have hcen : dist (G j i.1) (g i.1) < εr / 3 := hj i hi
  rw [dist_eq_norm]
  calc ‖g x - G j x‖
      ≤ ‖g x - g i.1‖ + ‖g i.1 - G j i.1‖ + ‖G j i.1 - G j x‖ := by
        have := norm_add₃_le (a := g x - g i.1) (b := g i.1 - G j i.1)
          (c := G j i.1 - G j x)
        simpa using this
    _ < εr / 3 + εr / 3 + εr / 3 := by
        refine add_lt_add_of_lt_of_le (add_lt_add_of_le_of_lt ?_ ?_) ?_
        · exact le_trans hd1 (le_trans hmul hr₀L.le)
        · rw [← dist_eq_norm, dist_comm]
          exact hcen
        · rw [norm_sub_rev]
          exact le_trans hd3 (le_trans hmul hr₀L.le)
    _ = εr := by ring

end RiemannDynamics

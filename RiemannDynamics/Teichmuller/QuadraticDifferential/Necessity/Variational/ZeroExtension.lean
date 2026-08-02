/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Variational.Schwarzian
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Symmetrize

/-!
# Zero-extension solutions and their parameter dependence

A Beltrami coefficient supported in the closed upper half plane has its normalized
solution conformal on the open lower half plane, where the Schwarzian derivative reads
lower-half-plane points depend analytically on the parameter, as does the Schwarzian,
and at the origin of a linear ray the parameter derivative of the Schwarzian is the
pairing of the direction with the quartic kernel. A solution whose Schwarzian vanishes
on the lower half plane is the identity there, and therefore commutes with every real
Möbius map whose coefficient law it inherits.

* `differentiableOn_of_beltrami_ae_zero` — conformality where the coefficient vanishes.
* `exists_affine_solution_family` — the normalized solution family of an affine
  coefficient path, analytic in the parameter on the lower half plane.
* `eq_id_on_lower_of_schwarzian_eq_zero` — vanishing Schwarzian forces the identity.
* `moebiusMap_comm_of_eq_id_lower` — identity below plus invariance above forces
  commutation with the group.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-- **Conformality off the support**: a quasiconformal map whose coefficient vanishes
almost everywhere on an open set is holomorphic there. -/
theorem differentiableOn_of_beltrami_ae_zero {w : ℂ → ℂ} {b : BeltramiCoeff}
    (hw : IsQCAnalytic w b) {U : Set ℂ} (hU : IsOpen U)
    (hb : ∀ᵐ z ∂(volume.restrict U), b.μ z = 0) :
    DifferentiableOn ℂ w U := by
  have hwcont : Continuous w := hw.1.1.continuous
  have hwloc : LocallyIntegrable w := hwcont.locallyIntegrable
  have hdiff : ∀ᵐ z, DifferentiableAt ℝ w z := hw.ae_differentiableAt
  obtain ⟨_hLp, gx, gy, ⟨hwgx, hwgy⟩, hmgx, hmgy⟩ := hw.2.1
  have hLpgx : MemLpLocOn gx 2 Set.univ := hmgx
  have hLpgy : MemLpLocOn gy 2 Set.univ := hmgy
  -- `L²_loc ⟹ L¹_loc ⟹ LocallyIntegrable`.
  have memLpLoc_to_loc : ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 Set.univ →
      LocallyIntegrable g := by
    intro g hg
    rw [← locallyIntegrableOn_univ, locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro k hk
    haveI : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    have hmem1 : MemLp g 1 (volume.restrict k) :=
      (hg k (Set.subset_univ _) hk).mono_exponent (by norm_num)
    exact memLp_one_iff_integrable.mp hmem1
  have hgxLI : LocallyIntegrable gx := memLpLoc_to_loc hLpgx
  have hgyLI : LocallyIntegrable gy := memLpLoc_to_loc hLpgy
  -- a.e.: the pointwise partials agree with the weak partials.
  have haex : ∀ᵐ z, (fderiv ℝ w z) (1 : ℂ) = gx z :=
    fderiv_ae_eq_weakDirDeriv hwgx (locallyIntegrableOn_univ.mpr hgxLI) hdiff
      (Or.inl rfl) hwloc
  have haey : ∀ᵐ z, (fderiv ℝ w z) Complex.I = gy z :=
    fderiv_ae_eq_weakDirDeriv hwgy (locallyIntegrableOn_univ.mpr hgyLI) hdiff
      (Or.inr rfl) hwloc
  -- the coefficient vanishes a.e. on `U`, so the `∂̄`-combination vanishes a.e. on `U`.
  have hbU : ∀ᵐ z, z ∈ U → b.μ z = 0 := (ae_restrict_iff' hU.measurableSet).mp hb
  have hcomb : ∀ᵐ z, z ∈ U → gx z + Complex.I * gy z = 0 := by
    filter_upwards [hw.2.2, hbU, haex, haey] with z hbel hbz hx hy hzU
    have h0 : dzbar w z = 0 := by rw [hbel, hbz hzU, zero_mul]
    have hval : dzbar w z = (1 / 2 : ℂ) * (gx z + Complex.I * gy z) := by
      rw [dzbar, hx, hy]
    rw [hval] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (by norm_num)
    · exact h
  exact weyl_lemma_on hU hwcont.continuousOn
    ⟨hwgx.mono (Set.subset_univ U), hwgy.mono (Set.subset_univ U)⟩
    (hgxLI.locallyIntegrableOn U) (hgyLI.locallyIntegrableOn U) hcomb

set_option maxHeartbeats 400000 in
-- The single declaration runs the affine Neumann tier, the truncation limit, the
-- Vitali upgrade, and the kernel-derivative extraction; the default heartbeat
-- budget is exceeded in this one proof.
/-- **The affine solution family**: for a base coefficient and a direction, both bounded
measurable and supported in the closed upper half plane, the normalized solutions along
the affine path depend analytically on the parameter at every point of the lower half
plane, as does the Schwarzian derivative; along a linear ray the parameter derivative of
the Schwarzian at the origin is a fixed nonzero multiple of the quartic-kernel pairing
with the direction. The constant is universal. -/
theorem exists_affine_solution_family :
    ∃ c' : ℂ, c' ≠ 0 ∧
    ∀ (κ ν : ℂ → ℂ) (m M : ℝ), Measurable κ → Measurable ν →
      (∀ z, ‖κ z‖ ≤ m) → (∀ z, ‖ν z‖ ≤ M) →
      (∀ z : ℂ, z.im ≤ 0 → κ z = 0) → (∀ z : ℂ, z.im ≤ 0 → ν z = 0) →
      m < 1 → 0 < M →
      ∃ W : ℂ → ℂ → ℂ,
        (∀ t : ℂ, ‖t‖ < (1 - m) / M → ∃ b : BeltramiCoeff,
          (∀ z, b.μ z = κ z + t * ν z) ∧ IsQCAnalytic (W t) b ∧
          W t 0 = 0 ∧ W t 1 = 1) ∧
        (∀ z : ℂ, z.im < 0 →
          AnalyticOnNhd ℂ (fun t => W t z) {t : ℂ | ‖t‖ < (1 - m) / M}) ∧
        (∀ z : ℂ, z.im < 0 →
          AnalyticOnNhd ℂ (fun t => schwarzian (W t) z) {t : ℂ | ‖t‖ < (1 - m) / M}) ∧
        ((∀ z, κ z = 0) → ∀ z : ℂ, z.im < 0 →
          HasDerivAt (fun t => schwarzian (W t) z)
            (c' * ∫ ζ in {ζ : ℂ | 0 < ζ.im}, ν ζ / (ζ - z) ^ 4) 0) := by
  classical
  have w2_memLp_mono : ∀ (u : ℂ → ℂ) (p q : ℝ≥0∞) (R : ℝ), q ≤ p →
      MemLp u p volume → (∀ z : ℂ, R < ‖z‖ → u z = 0) → MemLp u q volume := by
    intro u p q R hqp hu husupp
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
  have w2_chunkB : ∀ (a : ℕ → ℂ) (M ρ : ℝ), 0 ≤ ρ →
      (∀ n : ℕ, ‖a n‖ ≤ M * ρ ^ n) →
      ∀ t₀ : ℂ, ‖t₀‖ * ρ < 1 →
        AnalyticAt ℂ (fun t : ℂ => ∑' n : ℕ, t ^ (n + 1) * a n) t₀ := by
    intro a M ρ hρ hbound t₀ ht₀
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
  have w2_an0 : ∀ (c : ℕ → ℂ) (M ρ : ℝ), 0 ≤ ρ →
      (∀ n : ℕ, ‖c (n + 1)‖ ≤ M * ρ ^ n) →
      ∀ t₀ : ℂ, ‖t₀‖ * ρ < 1 →
        AnalyticAt ℂ (fun t : ℂ => ∑' n : ℕ, t ^ n * c n) t₀ := by
    intro c M ρ hρ hb t₀ ht₀
    have hAn : AnalyticAt ℂ (fun t : ℂ => c 0 + ∑' n : ℕ, t ^ (n + 1) * c (n + 1)) t₀ :=
      analyticAt_const.add (w2_chunkB (fun n => c (n + 1)) M ρ hρ hb t₀ ht₀)
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
  have w2_der0 : ∀ (c : ℕ → ℂ) (M ρ : ℝ), 0 ≤ ρ →
      (∀ n : ℕ, ‖c (n + 1)‖ ≤ M * ρ ^ n) →
      HasDerivAt (fun t : ℂ => ∑' n : ℕ, t ^ n * c n) (c 1) 0 := by
    intro c M ρ hρ hb
    have hGb : ∀ n : ℕ, ‖c (n + 1 + 1)‖ ≤ M * ρ * ρ ^ n := by
      intro n
      calc ‖c (n + 1 + 1)‖ ≤ M * ρ ^ (n + 1) := hb (n + 1)
        _ = M * ρ * ρ ^ n := by rw [pow_succ]; ring
    have hG : AnalyticAt ℂ (fun t : ℂ => ∑' n : ℕ, t ^ n * c (n + 1)) 0 :=
      w2_an0 (fun n => c (n + 1)) (M * ρ) ρ hρ hGb 0 (by simp)
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
  have w2_ker4 : ∀ z : ℂ, z.im < 0 →
      Integrable (fun ζ : ℂ => (‖ζ - z‖ ^ (4 : ℕ))⁻¹)
        (volume.restrict {ζ : ℂ | 0 < ζ.im}) := by
    intro z hz
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
  have w2_ctDeriv : ∀ (u : ℂ → ℂ) (p : ℝ≥0∞) (R : ℝ), 2 < p → p ≠ ⊤ →
      MemLp u p volume → (∀ z : ℂ, R < ‖z‖ → u z = 0) → (∀ z : ℂ, z.im ≤ 0 → u z = 0) →
      ∀ (k : ℕ), 1 ≤ k → ∀ z : ℂ, z.im < 0 →
        HasDerivAt (fun w : ℂ => ∫ ζ : ℂ, u ζ / (ζ - w) ^ k)
          ((k : ℂ) * ∫ ζ : ℂ, u ζ / (ζ - z) ^ (k + 1)) z := by
    intro u p R hp hp' hu hsupp hupp k hk z hz
    have hd0 : (0 : ℝ) < -z.im / 2 := by
      have : 0 < -z.im := by linarith
      linarith
    have hu1 : MemLp u 1 volume :=
      w2_memLp_mono u p 1 R (le_of_lt (lt_trans ENNReal.one_lt_two hp)) hu hsupp
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
  have w2_ctDiff : ∀ (u : ℂ → ℂ) (p : ℝ≥0∞) (R : ℝ), 2 < p → p ≠ ⊤ →
      MemLp u p volume → (∀ z : ℂ, R < ‖z‖ → u z = 0) → (∀ z : ℂ, z.im ≤ 0 → u z = 0) →
      DifferentiableOn ℂ (cauchyTransform u) {z : ℂ | z.im < 0} := by
    intro u p R hp hp' hu hsupp hupp z hz
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
    exact (((w2_ctDeriv u p R hp hp' hu hsupp hupp 1 le_rfl z hz').const_mul
      (-(1 / (Real.pi : ℂ)))).differentiableAt).differentiableWithinAt
  have w2_ctD3 : ∀ (u : ℂ → ℂ) (p : ℝ≥0∞) (R : ℝ), 2 < p → p ≠ ⊤ →
      MemLp u p volume → (∀ z : ℂ, R < ‖z‖ → u z = 0) → (∀ z : ℂ, z.im ≤ 0 → u z = 0) →
      ∀ z : ℂ, z.im < 0 →
        iteratedDeriv 3 (cauchyTransform u) z
          = -(6 / (Real.pi : ℂ)) * ∫ ζ : ℂ, u ζ / (ζ - z) ^ 4 := by
    intro u p R hp hp' hu hsupp hupp z hz
    have hLopen : IsOpen {w : ℂ | w.im < 0} :=
      isOpen_lt Complex.continuous_im continuous_const
    have hI : ∀ (m : ℕ), 1 ≤ m → ∀ w : ℂ, w.im < 0 →
        HasDerivAt (fun w' : ℂ => ∫ ζ : ℂ, u ζ / (ζ - w') ^ m)
          ((m : ℂ) * ∫ ζ : ℂ, u ζ / (ζ - w) ^ (m + 1)) w :=
      fun m hm w hw => w2_ctDeriv u p R hp hp' hu hsupp hupp m hm w hw
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
  have w2_main_local : ∀ (κ' ν' : ℂ → ℂ) (R M' : ℝ), Measurable κ' → Measurable ν' →
      (∀ z : ℂ, R < ‖z‖ → κ' z = 0) → (∀ z : ℂ, R < ‖z‖ → ν' z = 0) →
      (∀ z : ℂ, z.im ≤ 0 → κ' z = 0) → (∀ z : ℂ, z.im ≤ 0 → ν' z = 0) →
      eLpNormEssSup κ' volume < 1 → (∀ z : ℂ, ‖ν' z‖ ≤ M') → 0 < M' →
      ∃ (ε : ℝ) (c : ℕ → ℂ → ℂ) (Mc ρc : ℝ), 0 < ε ∧ 0 ≤ ρc ∧ 0 ≤ Mc ∧ ε * ρc < 1 ∧
        (∀ (n : ℕ) (z : ℂ), ‖c (n + 1) z‖ ≤ Mc * ρc ^ n) ∧
        (∀ z : ℂ, ‖c 0 z‖ ≤ Mc) ∧
        (∀ n : ℕ, DifferentiableOn ℂ (c n) {z : ℂ | z.im < 0}) ∧
        (∀ s : ℂ, ‖s‖ < ε → ∃ bs : BeltramiCoeff, (∀ z : ℂ, bs.μ z = κ' z + s * ν' z) ∧
          IsPrincipalSolution bs (fun z => z + ∑' n : ℕ, s ^ n * c n z)) ∧
        ((∀ z : ℂ, κ' z = 0) → (∀ z : ℂ, c 0 z = 0) ∧
          (∀ z : ℂ, c 1 z = cauchyTransform ν' z)) := by
    intro κ' ν' R M' hκm hνm hκs hνs hκu hνu hκb hνM hM0
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
        MemLp u 2 volume := fun u hu hs => w2_memLp_mono u p 2 R hp.le hu hs
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
      exact w2_ctDiff (a n) p R hp hp' (haLp n) (hasupp n) (haupp n)
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
  have w2_affine : ∀ (F : ℂ → ℂ) (bF : BeltramiCoeff) (aa cc : ℂ), aa ≠ 0 →
      IsQCAnalytic F bF → IsQCAnalytic (fun z => aa * (F z - cc)) bF := by
    have hLIofL2 : ∀ {w : ℂ → ℂ}, MemLpLocOn w 2 Set.univ →
        LocallyIntegrableOn w Set.univ := by
      intro w hw
      rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
      intro Kc hKc
      haveI : IsFiniteMeasure (volume.restrict Kc) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
      exact memLp_one_iff_integrable.mp
        ((hw Kc (Set.subset_univ _) hKc).mono_exponent (by norm_num))
    intro F bF a c ha hF
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
  have w2_ubnd : ∀ (Kq ℓ : ℝ), 0 ≤ ℓ → ∃ B : ℝ, ∀ f : ℂ → ℂ,
      IsQCGeometric f Kq → f 0 = 0 → f 1 = 1 → ∀ z : ℂ, ‖z‖ ≤ ℓ → ‖f z‖ ≤ B := by
    intro Kq ℓ hℓ
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
  have w2_vitali : ∀ (G : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (U : Set ℂ), IsOpen U →
      (∀ j : ℕ, DifferentiableOn ℂ (G j) U) →
      (∀ K : Set ℂ, K ⊆ U → IsCompact K → ∃ B : ℝ, ∀ (j : ℕ), ∀ t ∈ K, ‖G j t‖ ≤ B) →
      (∀ t ∈ U, Filter.Tendsto (fun j => G j t) Filter.atTop (nhds (g t))) →
      TendstoLocallyUniformlyOn G g Filter.atTop U := by
    intro G g U hU hdiff hbnd hptw
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
  have w2_trunc_conv : ∀ (b : BeltramiCoeff) (bs : ℕ → BeltramiCoeff) (ws : ℕ → ℂ → ℂ)
      (g : ℂ → ℂ),
      (∀ n : ℕ, IsQCAnalytic (ws n) (bs n)) → (∀ n : ℕ, ws n 0 = 0) → (∀ n : ℕ, ws n 1 = 1) →
      (∀ (n : ℕ) (z : ℂ), ‖z‖ ≤ (n : ℝ) + 1 → (bs n).μ z = b.μ z) →
      (∀ n : ℕ, (bs n).normInf ≤ b.normInf) →
      IsQCAnalytic g b → g 0 = 0 → g 1 = 1 →
      TendstoLocallyUniformly ws g Filter.atTop := by
    intro b bs ws g hQC hw0 hw1 hagree hnormb hg hg0 hg1
    classical
    -- ===== constants =====
    have hk0 : 0 ≤ b.normInf := b.normInf_nonneg
    have hk1 : b.normInf < 1 := b.normInf_lt_one
    have h1k : (0 : ℝ) < 1 - b.normInf := by linarith
    set K : ℝ := (1 + b.normInf) / (1 - b.normInf) with hK_def
    have hK1 : (1 : ℝ) ≤ K := by
      rw [hK_def, le_div_iff₀ h1k]
      linarith
    have hKk : (K - 1) / (K + 1) = b.normInf := by
      have hKp : (0 : ℝ) < K + 1 := by
        have : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK1
        linarith
      rw [div_eq_iff hKp.ne', hK_def]
      field_simp
      ring
    have hws_geo : ∀ n : ℕ, IsQCGeometric (ws n) K := by
      intro n
      refine isQCGeometric_of_isQCAnalytic hK1 ?_ (hQC n)
      rw [hKk]
      exact hnormb n
    have hLIofL2 : ∀ {w : ℂ → ℂ}, MemLpLocOn w 2 Set.univ →
        LocallyIntegrableOn w Set.univ := by
      intro w hw
      rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
      intro Kc hKc
      haveI : IsFiniteMeasure (volume.restrict Kc) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
      exact memLp_one_iff_integrable.mp
        ((hw Kc (Set.subset_univ _) hKc).mono_exponent (by norm_num))
    have hbμ_ae : ∀ᵐ z : ℂ, ‖b.μ z‖ ≤ 1 := by
      filter_upwards [enorm_ae_le_eLpNormEssSup b.μ volume] with z hz
      have h1 : ‖b.μ z‖ₑ ≤ 1 := hz.trans b.bound.le
      rwa [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_one,
        ENNReal.ofReal_le_ofReal_iff zero_le_one] at h1
    have hmul_int : ∀ (X ψt : ℂ → ℂ), AEStronglyMeasurable X volume →
        MemLpLocOn X 2 Set.univ → MemLp ψt 2 volume → HasCompactSupport ψt →
        Integrable (fun z => X z * ψt z) volume := by
      intro X ψt hXmeas hX2 hψ2 hψcs
      have hon : IntegrableOn (fun z => X z * ψt z) (tsupport ψt) volume :=
        (hX2 _ (Set.subset_univ _) hψcs).integrable_mul (hψ2.restrict _)
      have hsupp : Function.support (fun z => X z * ψt z) ⊆ tsupport ψt := by
        intro z hz
        apply subset_tsupport ψt
        simp only [Function.mem_support] at hz ⊢
        intro h0
        apply hz
        rw [h0, mul_zero]
      exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
    -- ===== the subsequence-identification core =====
    have key : ∀ ψ : ℕ → ℕ, StrictMono ψ →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          TendstoLocallyUniformly (fun k => ws (ψ (φ k))) g Filter.atTop := by
      intro ψ hψ
      obtain ⟨φ₁, g', hφ₁, hg'K, hconv⟩ :=
        exists_subseq_tendstoLocallyUniformly_isQCGeometric
          (fun k => hws_geo (ψ k)) zero_ne_one zero_ne_one
          (fun k => hw0 (ψ k)) (fun k => hw1 (ψ k))
      obtain ⟨b', _hb'norm, hb'⟩ := isQCAnalytic_of_isQCGeometric hK1 hg'K
      obtain ⟨⟨hghomeo, hgdet⟩, hgW12, _hb'belt⟩ := hb'
      have hgcont : Continuous g' := hghomeo.continuous
      obtain ⟨φ₂, u, v, hφ₂, hWG, humeas, hvmeas, hu2, hv2, hwx, hwy, _hE⟩ :=
        exists_subseq_weakGradient_package (fun k => hws_geo (ψ (φ₁ k))) hconv hgcont
      have hwx' : TendstoWeaklyL2Loc (fun k => partialX (ws (ψ (φ₁ (φ₂ k))))) u := hwx
      have hwy' : TendstoWeaklyL2Loc (fun k => partialY (ws (ψ (φ₁ (φ₂ k))))) v := hwy
      -- the limit Beltrami equation with the original coefficient
      set W : ℂ → ℂ := fun z => (1 - b.μ z) * u z + Complex.I * ((1 + b.μ z) * v z)
        with hW_def
      have hWmeas : AEStronglyMeasurable W volume := by
        rw [hW_def]
        exact ((measurable_const.sub b.measurable).aestronglyMeasurable.mul humeas).add
          (aestronglyMeasurable_const.mul
            ((measurable_const.add b.measurable).aestronglyMeasurable.mul hvmeas))
      have hWloc : LocallyIntegrableOn W Set.univ := by
        rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
        intro Kc hKc
        haveI : IsFiniteMeasure (volume.restrict Kc) :=
          ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
        have hu1 : Integrable u (volume.restrict Kc) := memLp_one_iff_integrable.mp
          ((hu2 Kc (Set.subset_univ _) hKc).mono_exponent (by norm_num))
        have hv1 : Integrable v (volume.restrict Kc) := memLp_one_iff_integrable.mp
          ((hv2 Kc (Set.subset_univ _) hKc).mono_exponent (by norm_num))
        refine Integrable.mono' ((hu1.norm.const_mul 2).add (hv1.norm.const_mul 2))
          hWmeas.restrict ?_
        filter_upwards [ae_restrict_of_ae hbμ_ae] with z hz
        simp only [hW_def]
        calc ‖(1 - b.μ z) * u z + Complex.I * ((1 + b.μ z) * v z)‖
            ≤ ‖(1 - b.μ z) * u z‖ + ‖Complex.I * ((1 + b.μ z) * v z)‖ := norm_add_le _ _
          _ = ‖1 - b.μ z‖ * ‖u z‖ + ‖1 + b.μ z‖ * ‖v z‖ := by
              rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul]
          _ ≤ 2 * ‖u z‖ + 2 * ‖v z‖ := by
              have h1 : ‖(1 : ℂ) - b.μ z‖ ≤ 2 :=
                le_trans (norm_sub_le _ _) (by rw [norm_one]; linarith)
              have h2 : ‖(1 : ℂ) + b.μ z‖ ≤ 2 :=
                le_trans (norm_add_le _ _) (by rw [norm_one]; linarith)
              have hu0 := norm_nonneg (u z)
              have hv0 := norm_nonneg (v z)
              nlinarith only [h1, h2, hu0, hv0, hz]
      have hWzero : ∀ᵐ z : ℂ, z ∈ Set.univ → W z = 0 := by
        refine isOpen_univ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hWloc ?_
        intro φt hφt hφcs _hts
        set ψ₁ : ℂ → ℂ := fun z => (1 - b.μ z) * (φt z : ℂ) with hψ₁_def
        set ψ₂ : ℂ → ℂ := fun z => Complex.I * ((1 + b.μ z) * (φt z : ℂ)) with hψ₂_def
        have hφcoe_cont : Continuous fun z : ℂ => (φt z : ℂ) :=
          Complex.continuous_ofReal.comp hφt.continuous
        have hφcoe_cs : HasCompactSupport fun z : ℂ => (φt z : ℂ) :=
          hφcs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
        have h2φ_L2 : MemLp (fun z : ℂ => (2 : ℂ) * (φt z : ℂ)) 2 volume :=
          (hφcoe_cont.memLp_of_hasCompactSupport hφcoe_cs).const_mul 2
        have hψ₁_meas : AEStronglyMeasurable ψ₁ volume := by
          rw [hψ₁_def]
          exact (measurable_const.sub b.measurable).aestronglyMeasurable.mul
            hφcoe_cont.aestronglyMeasurable
        have hψ₂_meas : AEStronglyMeasurable ψ₂ volume := by
          rw [hψ₂_def]
          exact aestronglyMeasurable_const.mul
            ((measurable_const.add b.measurable).aestronglyMeasurable.mul
              hφcoe_cont.aestronglyMeasurable)
        have hψ₁_L2 : MemLp ψ₁ 2 volume := by
          refine h2φ_L2.of_le hψ₁_meas ?_
          filter_upwards [hbμ_ae] with z hz
          simp only [hψ₁_def]
          rw [norm_mul, norm_mul]
          have h1 : ‖(1 : ℂ) - b.μ z‖ ≤ ‖(2 : ℂ)‖ := by
            rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
            exact le_trans (norm_sub_le _ _) (by rw [norm_one]; linarith)
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        have hψ₂_L2 : MemLp ψ₂ 2 volume := by
          refine h2φ_L2.of_le hψ₂_meas ?_
          filter_upwards [hbμ_ae] with z hz
          simp only [hψ₂_def]
          rw [norm_mul, Complex.norm_I, one_mul, norm_mul, norm_mul]
          have h1 : ‖(1 : ℂ) + b.μ z‖ ≤ ‖(2 : ℂ)‖ := by
            rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
            exact le_trans (norm_add_le _ _) (by rw [norm_one]; linarith)
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        have hψ₁_cs : HasCompactSupport ψ₁ := hφcoe_cs.mul_left
        have hψ₂_cs : HasCompactSupport ψ₂ := by
          have h := (hφcoe_cs.mul_left
            (f := fun z : ℂ => (1 : ℂ) + b.μ z)).mul_left (f := fun _ : ℂ => Complex.I)
          simpa [mul_assoc] using h
        have hlim : Filter.Tendsto
            (fun k => (∫ z, partialX (ws (ψ (φ₁ (φ₂ k)))) z * ψ₁ z)
              + ∫ z, partialY (ws (ψ (φ₁ (φ₂ k)))) z * ψ₂ z) Filter.atTop
            (nhds ((∫ z, u z * ψ₁ z) + ∫ z, v z * ψ₂ z)) :=
          (hwx' ψ₁ hψ₁_L2 hψ₁_cs).add (hwy' ψ₂ hψ₂_L2 hψ₂_cs)
        have hev0 : ∀ᶠ k in Filter.atTop,
            (∫ z, partialX (ws (ψ (φ₁ (φ₂ k)))) z * ψ₁ z)
              + ∫ z, partialY (ws (ψ (φ₁ (φ₂ k)))) z * ψ₂ z = 0 := by
          obtain ⟨Rb, hRb⟩ := hφcs.isBounded.subset_closedBall (0 : ℂ)
          obtain ⟨N, hN⟩ := exists_nat_ge Rb
          rw [Filter.eventually_atTop]
          refine ⟨N, fun k hk => ?_⟩
          set m : ℕ := ψ (φ₁ (φ₂ k)) with hm_def
          have hmk : (N : ℝ) ≤ (m : ℝ) := by
            have h1 : N ≤ m := le_trans hk (le_trans (le_trans hφ₂.le_apply
              hφ₁.le_apply) hψ.le_apply)
            exact_mod_cast h1
          have hXfun : partialX (ws m) = fun w => (fderiv ℝ (ws m) w) 1 :=
            funext fun w => partialX_def _ w
          have hYfun : partialY (ws m) = fun w => (fderiv ℝ (ws m) w) Complex.I :=
            funext fun w => partialY_def _ w
          have hX2 : MemLpLocOn (partialX (ws m)) 2 Set.univ := by
            rw [hXfun]
            exact (hws_geo m).forwardW12Data.2.2.1
          have hY2 : MemLpLocOn (partialY (ws m)) 2 Set.univ := by
            rw [hYfun]
            exact (hws_geo m).forwardW12Data.2.2.2.1
          have hXmeas : AEStronglyMeasurable (partialX (ws m)) volume := by
            rw [hXfun]
            exact (measurable_fderiv_apply_const ℝ (ws m) 1).aestronglyMeasurable
          have hYmeas : AEStronglyMeasurable (partialY (ws m)) volume := by
            rw [hYfun]
            exact (measurable_fderiv_apply_const ℝ (ws m) Complex.I).aestronglyMeasurable
          have hint1 : Integrable (fun z => partialX (ws m) z * ψ₁ z) volume :=
            hmul_int _ _ hXmeas hX2 hψ₁_L2 hψ₁_cs
          have hint2 : Integrable (fun z => partialY (ws m) z * ψ₂ z) volume :=
            hmul_int _ _ hYmeas hY2 hψ₂_L2 hψ₂_cs
          rw [← integral_add hint1 hint2]
          apply integral_eq_zero_of_ae
          filter_upwards [(hQC m).2.2] with z hbz
          by_cases hz : z ∈ tsupport φt
          · have hzR : ‖z‖ ≤ (m : ℝ) + 1 := by
              have h1 : z ∈ Metric.closedBall (0 : ℂ) Rb := hRb hz
              rw [Metric.mem_closedBall, dist_zero_right] at h1
              calc ‖z‖ ≤ Rb := h1
                _ ≤ (N : ℝ) := hN
                _ ≤ (m : ℝ) := hmk
                _ ≤ (m : ℝ) + 1 := by linarith
            have hbtz : (bs m).μ z = b.μ z := hagree m z hzR
            have hXY0 : (1 - b.μ z) * partialX (ws m) z
                + Complex.I * ((1 + b.μ z) * partialY (ws m) z) = 0 := by
              rw [hbtz] at hbz
              rw [partialX_def, partialY_def]
              simp only [dzbar, dz] at hbz
              linear_combination (2 : ℂ) * hbz
            change partialX (ws m) z * ψ₁ z + partialY (ws m) z * ψ₂ z = 0
            simp only [hψ₁_def, hψ₂_def]
            linear_combination ((φt z : ℂ)) * hXY0
          · have hz0 : φt z = 0 := image_eq_zero_of_notMem_tsupport hz
            change partialX (ws m) z * ψ₁ z + partialY (ws m) z * ψ₂ z = 0
            simp [hψ₁_def, hψ₂_def, hz0]
        have h0 : (∫ z, u z * ψ₁ z) + ∫ z, v z * ψ₂ z = 0 :=
          tendsto_nhds_unique hlim
            (Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev0) tendsto_const_nhds)
        have hint_u : Integrable (fun z => u z * ψ₁ z) volume :=
          hmul_int _ _ humeas hu2 hψ₁_L2 hψ₁_cs
        have hint_v : Integrable (fun z => v z * ψ₂ z) volume :=
          hmul_int _ _ hvmeas hv2 hψ₂_L2 hψ₂_cs
        calc ∫ z, φt z • W z
            = ∫ z, (u z * ψ₁ z + v z * ψ₂ z) := by
              apply integral_congr_ae
              filter_upwards with z
              simp only [hW_def, hψ₁_def, hψ₂_def, Complex.real_smul]
              ring
          _ = (∫ z, u z * ψ₁ z) + ∫ z, v z * ψ₂ z := integral_add hint_u hint_v
          _ = 0 := h0
      -- weak-to-pointwise Wirtinger equation for the limit
      have hgdiff : ∀ᵐ z, DifferentiableAt ℝ g' z :=
        GehringLehto.ae_differentiableAt_of_W12loc_homeomorph hghomeo hWG hu2 hv2
      have hgfloc : LocallyIntegrable g' := hgcont.locallyIntegrable
      have haex : ∀ᵐ z, (fderiv ℝ g' z) (1 : ℂ) = u z :=
        fderiv_ae_eq_weakDirDeriv hWG.1 (hLIofL2 hu2) hgdiff (Or.inl rfl) hgfloc
      have haey : ∀ᵐ z, (fderiv ℝ g' z) Complex.I = v z :=
        fderiv_ae_eq_weakDirDeriv hWG.2 (hLIofL2 hv2) hgdiff (Or.inr rfl) hgfloc
      have hgbelt : ∀ᵐ z, dzbar g' z = b.μ z * dz g' z := by
        filter_upwards [hWzero, haex, haey] with z hw hx hy
        have hw' : (1 - b.μ z) * u z + Complex.I * ((1 + b.μ z) * v z) = 0 := hw trivial
        simp only [dzbar, dz, hx, hy]
        linear_combination (1 / 2 : ℂ) * hw'
      have hQC' : IsQCAnalytic g' b := ⟨⟨hghomeo, hgdet⟩, hgW12, hgbelt⟩
      -- normalization passes to the limit
      have hptw : ∀ x : ℂ, Filter.Tendsto (fun k => ws (ψ (φ₁ k)) x) Filter.atTop
          (nhds (g' x)) := by
        intro x
        exact (tendstoLocallyUniformlyOn_univ.mpr hconv).tendsto_at (Set.mem_univ x)
      have hg'0 : g' 0 = 0 := by
        have h1 := hptw 0
        have h2 : (fun k => ws (ψ (φ₁ k)) 0) = fun _ => (0 : ℂ) := by
          funext k
          exact hw0 (ψ (φ₁ k))
        rw [h2] at h1
        exact tendsto_nhds_unique h1 tendsto_const_nhds
      have hg'1 : g' 1 = 1 := by
        have h1 := hptw 1
        have h2 : (fun k => ws (ψ (φ₁ k)) 1) = fun _ => (1 : ℂ) := by
          funext k
          exact hw1 (ψ (φ₁ k))
        rw [h2] at h1
        exact tendsto_nhds_unique h1 tendsto_const_nhds
      obtain ⟨f₀, _hf₀, huniq⟩ := mrmt_unique_normalized b
      have he1 : g' = f₀ := huniq g' ⟨hQC', hg'0, hg'1⟩
      have he2 : g = f₀ := huniq g ⟨hg, hg0, hg1⟩
      refine ⟨φ₁, hφ₁, ?_⟩
      rw [he2, ← he1]
      exact hconv
    -- ===== upgrade to full convergence by contradiction =====
    by_contra hcon
    rw [tendstoLocallyUniformly_iff_forall_isCompact] at hcon
    push Not at hcon
    obtain ⟨Kc, hKc, hnc⟩ := hcon
    rw [Metric.tendstoUniformlyOn_iff] at hnc
    push Not at hnc
    obtain ⟨εr, hεr, hne⟩ := hnc
    have hfreq : ∃ᶠ n in Filter.atTop, ∃ x ∈ Kc, εr ≤ dist (g x) (ws n x) := hne
    obtain ⟨ψ, hψmono, hψ⟩ := Filter.extraction_of_frequently_atTop hfreq
    obtain ⟨φ, _hφ, hconv⟩ := key ψ hψmono
    have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.mp hconv) Kc hKc
    rw [Metric.tendstoUniformlyOn_iff] at hunif
    obtain ⟨k, hk⟩ := (hunif εr hεr).exists
    obtain ⟨x, hxK, hxd⟩ := hψ (φ k)
    exact absurd (hk x hxK) (not_lt.mpr hxd)
  have w2_cau : ∀ (u : ℂ → ℂ) (Bu : ℝ), DifferentiableOn ℂ u {z : ℂ | z.im < 0} →
      ∀ z₀ : ℂ, z₀.im < 0 → (∀ z ∈ Metric.closedBall z₀ (-z₀.im / 2), ‖u z‖ ≤ Bu) →
      ∀ k : ℕ, ‖iteratedDeriv k u z₀‖ ≤ (k.factorial : ℝ) * Bu / (-z₀.im / 2) ^ k := by
    intro u Bu hdiff z₀ hz₀ hBu k
    have hr2 : (0 : ℝ) < -z₀.im / 2 := by linarith
    have hsub : Metric.closedBall z₀ (-z₀.im / 2) ⊆ {z : ℂ | z.im < 0} := by
      intro w hw
      rw [Metric.mem_closedBall] at hw
      have h1 : w.im - z₀.im ≤ ‖w - z₀‖ := by
        calc w.im - z₀.im ≤ |w.im - z₀.im| := le_abs_self _
          _ = |(w - z₀).im| := by rw [Complex.sub_im]
          _ ≤ ‖w - z₀‖ := Complex.abs_im_le_norm _
      have h2 : ‖w - z₀‖ ≤ -z₀.im / 2 := by rwa [← dist_eq_norm]
      change w.im < 0
      linarith
    have hdc : DiffContOnCl ℂ u (Metric.ball z₀ (-z₀.im / 2)) := by
      refine ⟨hdiff.mono (le_trans Metric.ball_subset_closedBall hsub), ?_⟩
      exact (hdiff.continuousOn).mono
        (le_trans Metric.closure_ball_subset_closedBall hsub)
    exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr2 hdc
      (fun v hv => hBu v (Metric.sphere_subset_closedBall hv))
  have w2_glue : ∀ (f : ℂ → ℂ) (t₀ : ℂ) (ε : ℝ) (ψf : ℂ → ℂ), 0 < ε →
      AnalyticAt ℂ ψf 0 → (∀ s : ℂ, ‖s‖ < ε → f (t₀ + s) = ψf s) →
      AnalyticAt ℂ f t₀ := by
    intro f t₀ ε ψf hε hψ heq
    have h0 : AnalyticAt ℂ (fun t : ℂ => t - t₀) t₀ := analyticAt_id.sub analyticAt_const
    have h1 : AnalyticAt ℂ (fun t : ℂ => ψf (t - t₀)) t₀ := by
      have h2 := AnalyticAt.comp (g := ψf) (f := fun t : ℂ => t - t₀) (x := t₀) ?_ h0
      · exact h2
      · change AnalyticAt ℂ ψf (t₀ - t₀)
        rw [sub_self]
        exact hψ
    refine h1.congr ?_
    filter_upwards [Metric.ball_mem_nhds t₀ hε] with t ht
    have h2 : ‖t - t₀‖ < ε := by
      rw [Metric.mem_ball, dist_eq_norm] at ht
      exact ht
    have h3 := heq (t - t₀) h2
    rw [add_sub_cancel] at h3
    exact h3.symm
  have w2_zwei : ∀ (cs : ℕ → ℂ → ℂ) (Mc ρc : ℝ) (s : ℂ), 0 ≤ ρc → 0 ≤ Mc →
      ‖s‖ * ρc < 1 →
      (∀ (n : ℕ) (z : ℂ), ‖cs (n + 1) z‖ ≤ Mc * ρc ^ n) → (∀ z : ℂ, ‖cs 0 z‖ ≤ Mc) →
      (∀ n : ℕ, DifferentiableOn ℂ (cs n) {z : ℂ | z.im < 0}) →
      ∀ z₀ : ℂ, z₀.im < 0 →
        deriv (fun z => z + ∑' n : ℕ, s ^ n * cs n z) z₀
            = 1 + ∑' n : ℕ, s ^ n * deriv (cs n) z₀
        ∧ deriv (deriv (fun z => z + ∑' n : ℕ, s ^ n * cs n z)) z₀
            = ∑' n : ℕ, s ^ n * deriv (deriv (cs n)) z₀
        ∧ deriv (deriv (deriv (fun z => z + ∑' n : ℕ, s ^ n * cs n z))) z₀
            = ∑' n : ℕ, s ^ n * deriv (deriv (deriv (cs n))) z₀ := by
    intro cs Mc ρc s hρ0 hMc0 hsρ hcb1 hcb0 hcdiff z₀ hz₀
    have hLower : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
    have hz₀m : z₀ ∈ {z : ℂ | z.im < 0} := hz₀
    -- the summable uniform bound
    set v : ℕ → ℝ := fun n => if n = 0 then Mc else ‖s‖ * Mc * (‖s‖ * ρc) ^ (n - 1) with hvdef
    have hvsum : Summable v := by
      have h1 : Summable (fun m : ℕ => ‖s‖ * Mc * (‖s‖ * ρc) ^ m) :=
        (summable_geometric_of_lt_one (mul_nonneg (norm_nonneg s) hρ0) hsρ).mul_left _
      refine (summable_nat_add_iff 1).mp ?_
      refine h1.congr fun m => ?_
      simp [hvdef]
    have hvb : ∀ (n : ℕ) (z : ℂ), ‖s ^ n * cs n z‖ ≤ v n := by
      intro n z
      cases n with
      | zero =>
        simp only [hvdef, if_pos rfl, pow_zero, one_mul]
        exact hcb0 z
      | succ m =>
        simp only [hvdef, if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel]
        calc ‖s ^ (m + 1) * cs (m + 1) z‖ = ‖s‖ ^ (m + 1) * ‖cs (m + 1) z‖ := by
              rw [norm_mul, norm_pow]
          _ ≤ ‖s‖ ^ (m + 1) * (Mc * ρc ^ m) :=
              mul_le_mul_of_nonneg_left (hcb1 m z) (pow_nonneg (norm_nonneg s) _)
          _ = ‖s‖ * Mc * (‖s‖ * ρc) ^ m := by
              rw [mul_pow, pow_succ]
              ring
    -- uniform convergence of the partial sums including the identity part
    have hUnifS : TendstoUniformlyOn
        (fun N : ℕ => fun z : ℂ => ∑ n ∈ Finset.range N, s ^ n * cs n z)
        (fun z : ℂ => ∑' n : ℕ, s ^ n * cs n z) Filter.atTop {z : ℂ | z.im < 0} :=
      tendstoUniformlyOn_tsum_nat hvsum fun n z _ => hvb n z
    have hUnif : TendstoUniformlyOn
        (fun N : ℕ => fun z : ℂ => z + ∑ n ∈ Finset.range N, s ^ n * cs n z)
        (fun z : ℂ => z + ∑' n : ℕ, s ^ n * cs n z) Filter.atTop {z : ℂ | z.im < 0} := by
      rw [Metric.tendstoUniformlyOn_iff] at hUnifS ⊢
      intro εr hεr
      filter_upwards [hUnifS εr hεr] with N hN z hz
      have h1 := hN z hz
      rw [dist_eq_norm] at h1 ⊢
      have h2 : z + ∑' n : ℕ, s ^ n * cs n z
          - (z + ∑ n ∈ Finset.range N, s ^ n * cs n z)
          = (∑' n : ℕ, s ^ n * cs n z) - ∑ n ∈ Finset.range N, s ^ n * cs n z := by
        ring
      rw [h2]
      exact h1
    have hTL : TendstoLocallyUniformlyOn
        (fun N : ℕ => fun z : ℂ => z + ∑ n ∈ Finset.range N, s ^ n * cs n z)
        (fun z : ℂ => z + ∑' n : ℕ, s ^ n * cs n z) Filter.atTop {z : ℂ | z.im < 0} :=
      hUnif.tendstoLocallyUniformlyOn
    -- differentiability of the partial sums and their derivative towers
    have hPdiff : ∀ N : ℕ, DifferentiableOn ℂ
        (fun z : ℂ => z + ∑ n ∈ Finset.range N, s ^ n * cs n z) {z : ℂ | z.im < 0} := by
      intro N
      refine DifferentiableOn.add differentiableOn_id ?_
      refine DifferentiableOn.fun_sum fun n _ => ?_
      exact (hcdiff n).const_mul (s ^ n)
    have hPan : ∀ N : ℕ, AnalyticOnNhd ℂ
        (fun z : ℂ => z + ∑ n ∈ Finset.range N, s ^ n * cs n z) {z : ℂ | z.im < 0} :=
      fun N => (hPdiff N).analyticOnNhd hLower
    have hcsan : ∀ n : ℕ, AnalyticOnNhd ℂ (cs n) {z : ℂ | z.im < 0} :=
      fun n => (hcdiff n).analyticOnNhd hLower
    -- first-derivative identification on the lower half plane
    have hd1P : ∀ (N : ℕ) (w : ℂ), w.im < 0 →
        deriv (fun z : ℂ => z + ∑ n ∈ Finset.range N, s ^ n * cs n z) w
          = 1 + ∑ n ∈ Finset.range N, s ^ n * deriv (cs n) w := by
      intro N w hw
      have h1 : HasDerivAt (fun z : ℂ => z + ∑ n ∈ Finset.range N, s ^ n * cs n z)
          (1 + ∑ n ∈ Finset.range N, s ^ n * deriv (cs n) w) w := by
        refine (hasDerivAt_id w).add (HasDerivAt.fun_sum fun n _ => ?_)
        exact (((hcdiff n).differentiableAt (hLower.mem_nhds hw)).hasDerivAt).const_mul (s ^ n)
      exact h1.deriv
    have hd2P : ∀ (N : ℕ) (w : ℂ), w.im < 0 →
        deriv (deriv (fun z : ℂ => z + ∑ n ∈ Finset.range N, s ^ n * cs n z)) w
          = ∑ n ∈ Finset.range N, s ^ n * deriv (deriv (cs n)) w := by
      intro N w hw
      have hev : deriv (fun z : ℂ => z + ∑ n ∈ Finset.range N, s ^ n * cs n z)
          =ᶠ[nhds w] fun w' : ℂ => 1 + ∑ n ∈ Finset.range N, s ^ n * deriv (cs n) w' := by
        filter_upwards [hLower.mem_nhds hw] with x hx
        exact hd1P N x hx
      rw [hev.deriv_eq]
      have h1 : HasDerivAt (fun w' : ℂ => 1 + ∑ n ∈ Finset.range N, s ^ n * deriv (cs n) w')
          (∑ n ∈ Finset.range N, s ^ n * deriv (deriv (cs n)) w) w := by
        have h2 : HasDerivAt (fun w' : ℂ => ∑ n ∈ Finset.range N, s ^ n * deriv (cs n) w')
            (∑ n ∈ Finset.range N, s ^ n * deriv (deriv (cs n)) w) w := by
          refine HasDerivAt.fun_sum fun n _ => ?_
          exact ((((hcsan n).deriv w hw).differentiableAt).hasDerivAt).const_mul (s ^ n)
        simpa using h2.const_add (1 : ℂ)
      exact h1.deriv
    have hd3P : ∀ (N : ℕ) (w : ℂ), w.im < 0 →
        deriv (deriv (deriv (fun z : ℂ => z + ∑ n ∈ Finset.range N, s ^ n * cs n z))) w
          = ∑ n ∈ Finset.range N, s ^ n * deriv (deriv (deriv (cs n))) w := by
      intro N w hw
      have hev : deriv (deriv (fun z : ℂ => z + ∑ n ∈ Finset.range N, s ^ n * cs n z))
          =ᶠ[nhds w] fun w' : ℂ => ∑ n ∈ Finset.range N, s ^ n * deriv (deriv (cs n)) w' := by
        filter_upwards [hLower.mem_nhds hw] with x hx
        exact hd2P N x hx
      rw [hev.deriv_eq]
      refine HasDerivAt.deriv ?_
      refine HasDerivAt.fun_sum fun n _ => ?_
      exact (((((hcsan n).deriv).deriv w hw).differentiableAt).hasDerivAt).const_mul (s ^ n)
    -- Weierstrass chains
    have hW1 : TendstoLocallyUniformlyOn
        (deriv ∘ fun N : ℕ => fun z : ℂ => z + ∑ n ∈ Finset.range N, s ^ n * cs n z)
        (deriv fun z : ℂ => z + ∑' n : ℕ, s ^ n * cs n z) Filter.atTop {z : ℂ | z.im < 0} :=
      hTL.deriv (Filter.Eventually.of_forall hPdiff) hLower
    have hW1diff : ∀ N : ℕ, DifferentiableOn ℂ
        (deriv (fun z : ℂ => z + ∑ n ∈ Finset.range N, s ^ n * cs n z))
        {z : ℂ | z.im < 0} := fun N => ((hPan N).deriv).differentiableOn
    have hW2 : TendstoLocallyUniformlyOn
        (deriv ∘ deriv ∘ fun N : ℕ => fun z : ℂ => z + ∑ n ∈ Finset.range N, s ^ n * cs n z)
        (deriv (deriv fun z : ℂ => z + ∑' n : ℕ, s ^ n * cs n z))
        Filter.atTop {z : ℂ | z.im < 0} :=
      hW1.deriv (Filter.Eventually.of_forall hW1diff) hLower
    have hW2diff : ∀ N : ℕ, DifferentiableOn ℂ
        (deriv (deriv (fun z : ℂ => z + ∑ n ∈ Finset.range N, s ^ n * cs n z)))
        {z : ℂ | z.im < 0} := fun N => (((hPan N).deriv).deriv).differentiableOn
    have hW3 : TendstoLocallyUniformlyOn
        (deriv ∘ deriv ∘ deriv ∘
          fun N : ℕ => fun z : ℂ => z + ∑ n ∈ Finset.range N, s ^ n * cs n z)
        (deriv (deriv (deriv fun z : ℂ => z + ∑' n : ℕ, s ^ n * cs n z)))
        Filter.atTop {z : ℂ | z.im < 0} :=
      hW2.deriv (Filter.Eventually.of_forall hW2diff) hLower
    -- summability of the derivative-tower series
    have hcau : ∀ (k : ℕ) (n : ℕ), ‖iteratedDeriv k (cs n) z₀‖
        ≤ (k.factorial : ℝ) * (if n = 0 then Mc else Mc * ρc ^ (n - 1)) / (-z₀.im / 2) ^ k := by
      intro k n
      cases n with
      | zero =>
        rw [if_pos rfl]
        exact w2_cau (cs 0) Mc (hcdiff 0) z₀ hz₀ (fun z _ => hcb0 z) k
      | succ m =>
        simp only [if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel]
        exact w2_cau (cs (m + 1)) (Mc * ρc ^ m) (hcdiff (m + 1)) z₀ hz₀
          (fun z _ => hcb1 m z) k
    have hsumtow : ∀ dtow : ℕ → ℂ, (∀ n : ℕ, ∃ k : ℕ, dtow n = iteratedDeriv k (cs n) z₀
          ∧ ∀ n' : ℕ, dtow n' = iteratedDeriv k (cs n') z₀) →
        Summable (fun n : ℕ => s ^ n * dtow n) := by
      intro dtow hd
      obtain ⟨k, _, hk⟩ := hd 0
      have hb : ∀ n : ℕ, ‖s ^ n * dtow n‖
          ≤ if n = 0 then (k.factorial : ℝ) * Mc / (-z₀.im / 2) ^ k
            else ‖s‖ * ((k.factorial : ℝ) * Mc / (-z₀.im / 2) ^ k) * (‖s‖ * ρc) ^ (n - 1) := by
        intro n
        cases n with
        | zero =>
          simp only [pow_zero, one_mul]
          rw [hk 0]
          have h1 := hcau k 0
          simpa using h1
        | succ m =>
          simp only [if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel]
          rw [norm_mul, norm_pow, hk (m + 1)]
          have h1 := hcau k (m + 1)
          simp only [if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel] at h1
          calc ‖s‖ ^ (m + 1) * ‖iteratedDeriv k (cs (m + 1)) z₀‖
              ≤ ‖s‖ ^ (m + 1) * ((k.factorial : ℝ) * (Mc * ρc ^ m) / (-z₀.im / 2) ^ k) :=
                mul_le_mul_of_nonneg_left h1 (pow_nonneg (norm_nonneg s) _)
            _ = ‖s‖ * ((k.factorial : ℝ) * Mc / (-z₀.im / 2) ^ k) * (‖s‖ * ρc) ^ m := by
                rw [mul_pow, pow_succ]
                ring
      refine Summable.of_norm_bounded ?_ hb
      have h1 : Summable (fun m : ℕ =>
          ‖s‖ * ((k.factorial : ℝ) * Mc / (-z₀.im / 2) ^ k) * (‖s‖ * ρc) ^ m) :=
        (summable_geometric_of_lt_one (mul_nonneg (norm_nonneg s) hρ0) hsρ).mul_left _
      refine (summable_nat_add_iff 1).mp ?_
      refine h1.congr fun m => ?_
      simp
    -- identify the three towers
    have hID1 : ∀ u : ℂ → ℂ, iteratedDeriv 1 u = deriv u := fun u => iteratedDeriv_one
    have hID2 : ∀ u : ℂ → ℂ, iteratedDeriv 2 u = deriv (deriv u) := by
      intro u
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have hID3 : ∀ u : ℂ → ℂ, iteratedDeriv 3 u = deriv (deriv (deriv u)) := by
      intro u
      rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, show (2 : ℕ) = 1 + 1 from rfl,
        iteratedDeriv_succ, iteratedDeriv_one]
    have hsum1 : Summable (fun n : ℕ => s ^ n * deriv (cs n) z₀) := by
      refine hsumtow (fun n => deriv (cs n) z₀) fun n => ⟨1, ?_, fun n' => ?_⟩
      · rw [hID1]
      · rw [hID1]
    have hsum2 : Summable (fun n : ℕ => s ^ n * deriv (deriv (cs n)) z₀) := by
      refine hsumtow (fun n => deriv (deriv (cs n)) z₀) fun n => ⟨2, ?_, fun n' => ?_⟩
      · rw [hID2]
      · rw [hID2]
    have hsum3 : Summable (fun n : ℕ => s ^ n * deriv (deriv (deriv (cs n))) z₀) := by
      refine hsumtow (fun n => deriv (deriv (deriv (cs n))) z₀) fun n => ⟨3, ?_, fun n' => ?_⟩
      · rw [hID3]
      · rw [hID3]
    refine ⟨?_, ?_, ?_⟩
    · -- first derivative
      have hT1 := hW1.tendsto_at hz₀m
      have hT1' : Filter.Tendsto
          (fun N : ℕ => 1 + ∑ n ∈ Finset.range N, s ^ n * deriv (cs n) z₀) Filter.atTop
          (nhds (deriv (fun z : ℂ => z + ∑' n : ℕ, s ^ n * cs n z) z₀)) := by
        refine hT1.congr fun N => ?_
        change deriv (fun z : ℂ => z + ∑ n ∈ Finset.range N, s ^ n * cs n z) z₀ = _
        exact hd1P N z₀ hz₀
      have hT2 : Filter.Tendsto
          (fun N : ℕ => 1 + ∑ n ∈ Finset.range N, s ^ n * deriv (cs n) z₀) Filter.atTop
          (nhds (1 + ∑' n : ℕ, s ^ n * deriv (cs n) z₀)) :=
        (hsum1.hasSum.tendsto_sum_nat).const_add 1
      exact tendsto_nhds_unique hT1' hT2
    · -- second derivative
      have hT1 := hW2.tendsto_at hz₀m
      have hT1' : Filter.Tendsto
          (fun N : ℕ => ∑ n ∈ Finset.range N, s ^ n * deriv (deriv (cs n)) z₀) Filter.atTop
          (nhds (deriv (deriv (fun z : ℂ => z + ∑' n : ℕ, s ^ n * cs n z)) z₀)) := by
        refine hT1.congr fun N => ?_
        change deriv (deriv (fun z : ℂ => z + ∑ n ∈ Finset.range N, s ^ n * cs n z)) z₀ = _
        exact hd2P N z₀ hz₀
      exact tendsto_nhds_unique hT1' hsum2.hasSum.tendsto_sum_nat
    · -- third derivative
      have hT1 := hW3.tendsto_at hz₀m
      have hT1' : Filter.Tendsto
          (fun N : ℕ => ∑ n ∈ Finset.range N, s ^ n * deriv (deriv (deriv (cs n))) z₀)
          Filter.atTop
          (nhds (deriv (deriv (deriv (fun z : ℂ => z + ∑' n : ℕ, s ^ n * cs n z))) z₀)) := by
        refine hT1.congr fun N => ?_
        change deriv (deriv (deriv
          (fun z : ℂ => z + ∑ n ∈ Finset.range N, s ^ n * cs n z))) z₀ = _
        exact hd3P N z₀ hz₀
      exact tendsto_nhds_unique hT1' hsum3.hasSum.tendsto_sum_nat
  refine ⟨-(6 / (Real.pi : ℂ)), ?_, ?_⟩
  · rw [neg_ne_zero]
    refine div_ne_zero (by norm_num) ?_
    exact_mod_cast Real.pi_ne_zero
  intro κ ν m M hκmeas hνmeas hκbnd hνbnd hκupp hνupp hm1 hM0
  have hLower : IsOpen {z : ℂ | z.im < 0} :=
    isOpen_lt Complex.continuous_im continuous_const
  have hopenD : IsOpen {t : ℂ | ‖t‖ < (1 - m) / M} :=
    isOpen_lt continuous_norm continuous_const
  have hm0 : 0 ≤ m := le_trans (norm_nonneg (κ 0)) (hκbnd 0)
  have hD0 : 0 < (1 - m) / M := div_pos (by linarith) hM0
  have hDball : ∀ t : ℂ, ‖t‖ < (1 - m) / M → m + ‖t‖ * M < 1 := by
    intro t ht
    have h1 : ‖t‖ * M < (1 - m) / M * M := mul_lt_mul_of_pos_right ht hM0
    have h2 : (1 - m) / M * M = 1 - m := by field_simp
    linarith
  -- ===== the full coefficients and the normalized solution family =====
  have hbtex : ∀ t : ℂ, ‖t‖ < (1 - m) / M →
      ∃ bb : BeltramiCoeff, ∀ z : ℂ, bb.μ z = κ z + t * ν z := by
    intro t ht
    refine ⟨⟨fun z => κ z + t * ν z, hκmeas.add (measurable_const.mul hνmeas), ?_⟩,
      fun z => rfl⟩
    have hb : ∀ z : ℂ, ‖κ z + t * ν z‖ ≤ m + ‖t‖ * M := by
      intro z
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul]
      exact add_le_add (hκbnd z)
        (mul_le_mul_of_nonneg_left (hνbnd z) (norm_nonneg t))
    refine lt_of_le_of_lt (eLpNormEssSup_le_of_ae_bound
      (Filter.Eventually.of_forall hb)) ?_
    exact ENNReal.ofReal_lt_one.mpr (hDball t ht)
  choose bt hbt using hbtex
  have hWex : ∀ (t : ℂ) (ht : ‖t‖ < (1 - m) / M),
      ∃ w : ℂ → ℂ, IsQCAnalytic w (bt t ht) ∧ w 0 = 0 ∧ w 1 = 1 :=
    fun t ht => (mrmt_unique_normalized (bt t ht)).exists
  choose W0 hW0 using hWex
  obtain ⟨W, hWt⟩ : ∃ W : ℂ → ℂ → ℂ,
      ∀ (t : ℂ) (ht : ‖t‖ < (1 - m) / M), W t = W0 t ht :=
    ⟨fun t => if ht : ‖t‖ < (1 - m) / M then W0 t ht else id, fun t ht => dif_pos ht⟩
  -- ===== the truncations =====
  set κt : ℕ → ℂ → ℂ := fun j z => if ‖z‖ ≤ (j : ℝ) + 1 then κ z else 0 with hκtdef
  set νt : ℕ → ℂ → ℂ := fun j z => if ‖z‖ ≤ (j : ℝ) + 1 then ν z else 0 with hνtdef
  have hκtm : ∀ j : ℕ, Measurable (κt j) := fun j =>
    Measurable.ite (measurableSet_le measurable_norm measurable_const) hκmeas
      measurable_const
  have hνtm : ∀ j : ℕ, Measurable (νt j) := fun j =>
    Measurable.ite (measurableSet_le measurable_norm measurable_const) hνmeas
      measurable_const
  have hκtb : ∀ (j : ℕ) (z : ℂ), ‖κt j z‖ ≤ m := by
    intro j z
    change ‖if ‖z‖ ≤ (j : ℝ) + 1 then κ z else 0‖ ≤ m
    by_cases hz : ‖z‖ ≤ (j : ℝ) + 1
    · rw [if_pos hz]
      exact hκbnd z
    · rw [if_neg hz, norm_zero]
      exact hm0
  have hνtb : ∀ (j : ℕ) (z : ℂ), ‖νt j z‖ ≤ M := by
    intro j z
    change ‖if ‖z‖ ≤ (j : ℝ) + 1 then ν z else 0‖ ≤ M
    by_cases hz : ‖z‖ ≤ (j : ℝ) + 1
    · rw [if_pos hz]
      exact hνbnd z
    · rw [if_neg hz, norm_zero]
      exact hM0.le
  have hκts : ∀ (j : ℕ) (z : ℂ), (j : ℝ) + 1 < ‖z‖ → κt j z = 0 := by
    intro j z hz
    exact if_neg (not_le.mpr hz)
  have hνts : ∀ (j : ℕ) (z : ℂ), (j : ℝ) + 1 < ‖z‖ → νt j z = 0 := by
    intro j z hz
    exact if_neg (not_le.mpr hz)
  have hκtu : ∀ (j : ℕ) (z : ℂ), z.im ≤ 0 → κt j z = 0 := by
    intro j z hz
    change (if ‖z‖ ≤ (j : ℝ) + 1 then κ z else 0) = 0
    by_cases hzb : ‖z‖ ≤ (j : ℝ) + 1
    · rw [if_pos hzb]
      exact hκupp z hz
    · rw [if_neg hzb]
  have hνtu : ∀ (j : ℕ) (z : ℂ), z.im ≤ 0 → νt j z = 0 := by
    intro j z hz
    change (if ‖z‖ ≤ (j : ℝ) + 1 then ν z else 0) = 0
    by_cases hzb : ‖z‖ ≤ (j : ℝ) + 1
    · rw [if_pos hzb]
      exact hνupp z hz
    · rw [if_neg hzb]
  have hκta : ∀ (j : ℕ) (z : ℂ), ‖z‖ ≤ (j : ℝ) + 1 → κt j z = κ z := by
    intro j z hz
    exact if_pos hz
  have hνta : ∀ (j : ℕ) (z : ℂ), ‖z‖ ≤ (j : ℝ) + 1 → νt j z = ν z := by
    intro j z hz
    exact if_pos hz
  -- ===== the truncated coefficients and principal solutions =====
  have hbtrex : ∀ (j : ℕ) (t : ℂ), ‖t‖ < (1 - m) / M →
      ∃ bb : BeltramiCoeff, ∀ z : ℂ, bb.μ z = κt j z + t * νt j z := by
    intro j t ht
    refine ⟨⟨fun z => κt j z + t * νt j z,
      (hκtm j).add (measurable_const.mul (hνtm j)), ?_⟩, fun z => rfl⟩
    have hb : ∀ z : ℂ, ‖κt j z + t * νt j z‖ ≤ m + ‖t‖ * M := by
      intro z
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul]
      exact add_le_add (hκtb j z)
        (mul_le_mul_of_nonneg_left (hνtb j z) (norm_nonneg t))
    refine lt_of_le_of_lt (eLpNormEssSup_le_of_ae_bound
      (Filter.Eventually.of_forall hb)) ?_
    exact ENNReal.ofReal_lt_one.mpr (hDball t ht)
  choose btr hbtr using hbtrex
  have hFex : ∀ (j : ℕ) (t : ℂ) (ht : ‖t‖ < (1 - m) / M),
      ∃ f : ℂ → ℂ, IsPrincipalSolution (btr j t ht) f := by
    intro j t ht
    refine exists_isPrincipalSolution (btr j t ht) (R := (j : ℝ) + 1) ?_
    intro z hz
    rw [hbtr j t ht z, hκts j z hz, hνts j z hz, mul_zero, add_zero]
  choose F0 hF0 using hFex
  obtain ⟨Fj, hFjt⟩ : ∃ Fj : ℕ → ℂ → ℂ → ℂ,
      ∀ (j : ℕ) (t : ℂ) (ht : ‖t‖ < (1 - m) / M), Fj j t = F0 j t ht :=
    ⟨fun j t => if ht : ‖t‖ < (1 - m) / M then F0 j t ht else id,
      fun j t ht => dif_pos ht⟩
  have hFj : ∀ (j : ℕ) (t : ℂ) (ht : ‖t‖ < (1 - m) / M),
      IsPrincipalSolution (btr j t ht) (Fj j t) := by
    intro j t ht
    rw [hFjt j t ht]
    exact hF0 j t ht
  have hFden : ∀ (j : ℕ) (t : ℂ), ‖t‖ < (1 - m) / M → Fj j t 1 - Fj j t 0 ≠ 0 := by
    intro j t ht hcon
    exact one_ne_zero ((hFj j t ht).injective (sub_eq_zero.mp hcon))
  obtain ⟨Wj, hWjeq⟩ : ∃ Wj : ℕ → ℂ → ℂ → ℂ, ∀ (j : ℕ) (t : ℂ),
      Wj j t = fun z => (Fj j t 1 - Fj j t 0)⁻¹ * (Fj j t z - Fj j t 0) :=
    ⟨fun j t z => (Fj j t 1 - Fj j t 0)⁻¹ * (Fj j t z - Fj j t 0), fun j t => rfl⟩
  have hWj0 : ∀ (j : ℕ) (t : ℂ), Wj j t 0 = 0 := by
    intro j t
    rw [hWjeq j t]
    change (Fj j t 1 - Fj j t 0)⁻¹ * (Fj j t 0 - Fj j t 0) = 0
    rw [sub_self, mul_zero]
  have hWj1 : ∀ (j : ℕ) (t : ℂ), ‖t‖ < (1 - m) / M → Wj j t 1 = 1 := by
    intro j t ht
    rw [hWjeq j t]
    change (Fj j t 1 - Fj j t 0)⁻¹ * (Fj j t 1 - Fj j t 0) = 1
    exact inv_mul_cancel₀ (hFden j t ht)
  have hWjQC : ∀ (j : ℕ) (t : ℂ) (ht : ‖t‖ < (1 - m) / M),
      IsQCAnalytic (Wj j t) (btr j t ht) := by
    intro j t ht
    rw [hWjeq j t]
    exact w2_affine (Fj j t) (btr j t ht) (Fj j t 1 - Fj j t 0)⁻¹ (Fj j t 0)
      (inv_ne_zero (hFden j t ht)) (hFj j t ht).isQCAnalytic
  -- transport of principal solutions along equal coefficients
  have htrans : ∀ (b₁ b₂ : BeltramiCoeff) (f : ℂ → ℂ), b₁.μ = b₂.μ →
      IsPrincipalSolution b₁ f → IsPrincipalSolution b₂ f := by
    intro b₁ b₂ f hμ h
    obtain ⟨p, hh, R, h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨p, hh, R, h1, h2, h3, h4, ?_, h6⟩
    rw [← hμ]
    exact h5
  -- ===== the local series data =====
  have hFloc : ∀ (j : ℕ) (t₀ : ℂ), ‖t₀‖ < (1 - m) / M →
      ∃ (ε : ℝ) (cs : ℕ → ℂ → ℂ) (Mc ρc : ℝ), 0 < ε ∧ 0 ≤ ρc ∧ 0 ≤ Mc ∧ ε * ρc < 1 ∧
        (∀ (n : ℕ) (z : ℂ), ‖cs (n + 1) z‖ ≤ Mc * ρc ^ n) ∧
        (∀ z : ℂ, ‖cs 0 z‖ ≤ Mc) ∧
        (∀ n : ℕ, DifferentiableOn ℂ (cs n) {z : ℂ | z.im < 0}) ∧
        (∀ s : ℂ, ‖s‖ < ε → Fj j (t₀ + s) = fun z => z + ∑' n : ℕ, s ^ n * cs n z) ∧
        ((∀ z : ℂ, κ z = 0) → t₀ = 0 → (∀ z : ℂ, cs 0 z = 0) ∧
          (∀ z : ℂ, cs 1 z = cauchyTransform (νt j) z)) := by
    intro j t₀ ht₀
    have hb' : ∀ z : ℂ, ‖κt j z + t₀ * νt j z‖ ≤ m + ‖t₀‖ * M := by
      intro z
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul]
      exact add_le_add (hκtb j z)
        (mul_le_mul_of_nonneg_left (hνtb j z) (norm_nonneg t₀))
    obtain ⟨ε₁, cs, Mc, ρc, hε₁0, hρc0, hMc0, hε₁ρ, hcb1, hcb0, hcdiff, hprin, hkz⟩ :=
      w2_main_local (fun z => κt j z + t₀ * νt j z) (νt j) ((j : ℝ) + 1) M
        ((hκtm j).add (measurable_const.mul (hνtm j))) (hνtm j)
        (fun z hz => by
          change κt j z + t₀ * νt j z = 0
          rw [hκts j z hz, hνts j z hz, mul_zero, add_zero])
        (hνts j)
        (fun z hz => by
          change κt j z + t₀ * νt j z = 0
          rw [hκtu j z hz, hνtu j z hz, mul_zero, add_zero])
        (hνtu j)
        (lt_of_le_of_lt (eLpNormEssSup_le_of_ae_bound
          (Filter.Eventually.of_forall hb'))
          (ENNReal.ofReal_lt_one.mpr (hDball t₀ ht₀)))
        (hνtb j) hM0
    refine ⟨min ε₁ ((1 - m) / M - ‖t₀‖), cs, Mc, ρc,
      lt_min hε₁0 (by linarith), hρc0, hMc0, ?_, hcb1, hcb0, hcdiff, ?_, ?_⟩
    · refine lt_of_le_of_lt ?_ hε₁ρ
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) hρc0
    · intro s hs
      have hs1 : ‖s‖ < ε₁ := lt_of_lt_of_le hs (min_le_left _ _)
      have hsD : ‖t₀ + s‖ < (1 - m) / M := by
        have h1 : ‖s‖ < (1 - m) / M - ‖t₀‖ := lt_of_lt_of_le hs (min_le_right _ _)
        refine lt_of_le_of_lt (norm_add_le _ _) ?_
        linarith
      obtain ⟨bs, hbsμ, hbsP⟩ := hprin s hs1
      have hμeq : bs.μ = (btr j (t₀ + s) hsD).μ := by
        funext z
        rw [hbsμ z, hbtr j (t₀ + s) hsD z]
        ring
      exact (isPrincipalSolution_unique (htrans bs (btr j (t₀ + s) hsD) _ hμeq hbsP)
        (hFj j (t₀ + s) hsD)).symm
    · intro hκ0 ht₀0
      refine hkz ?_
      intro z
      rw [ht₀0, zero_mul, add_zero]
      change (if ‖z‖ ≤ (j : ℝ) + 1 then κ z else 0) = 0
      by_cases hz : ‖z‖ ≤ (j : ℝ) + 1
      · rw [if_pos hz]
        exact hκ0 z
      · rw [if_neg hz]
  -- ===== convergence of the truncated normalized solutions =====
  have hWconv : ∀ (t : ℂ) (ht : ‖t‖ < (1 - m) / M),
      TendstoLocallyUniformly (fun j => Wj j t) (W t) Filter.atTop := by
    intro t ht
    refine w2_trunc_conv (bt t ht) (fun j => btr j t ht) (fun j => Wj j t) (W t)
      (fun j => hWjQC j t ht) (fun j => hWj0 j t) (fun j => hWj1 j t ht) ?_ ?_ ?_ ?_ ?_
    · intro j z hz
      rw [hbtr j t ht z, hbt t ht z, hκta j z hz, hνta j z hz]
    · intro j
      have hle : eLpNormEssSup (btr j t ht).μ volume
          ≤ eLpNormEssSup (bt t ht).μ volume := by
        rw [← eLpNorm_exponent_top, ← eLpNorm_exponent_top]
        refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun z => ?_)
        rw [hbtr j t ht z, hbt t ht z]
        by_cases hz : ‖z‖ ≤ (j : ℝ) + 1
        · rw [hκta j z hz, hνta j z hz]
        · rw [hκts j z (not_le.mp hz), hνts j z (not_le.mp hz), mul_zero, add_zero,
            norm_zero]
          exact norm_nonneg _
      exact ENNReal.toReal_mono (ne_top_of_lt (bt t ht).bound) hle
    · rw [hWt t ht]
      exact (hW0 t ht).1
    · rw [hWt t ht]
      exact (hW0 t ht).2.1
    · rw [hWt t ht]
      exact (hW0 t ht).2.2
  -- ===== holomorphy on the lower half plane =====
  have hFjeq0 : ∀ (j : ℕ) (t : ℂ), ‖t‖ < (1 - m) / M →
      ∃ c0 : ℂ → ℂ, DifferentiableOn ℂ c0 {z : ℂ | z.im < 0} ∧
        Fj j t = fun z => z + c0 z := by
    intro j t ht
    obtain ⟨ε, cs, Mc, ρc, hε0, _, _, _, _, _, hcdiff, hser, _⟩ := hFloc j t ht
    have h0 : Fj j (t + 0) = fun z => z + ∑' n : ℕ, (0 : ℂ) ^ n * cs n z :=
      hser 0 (by simpa using hε0)
    rw [add_zero] at h0
    refine ⟨cs 0, hcdiff 0, ?_⟩
    rw [h0]
    funext z
    congr 1
    rw [tsum_eq_single 0 (fun n hn => by rw [zero_pow hn, zero_mul])]
    rw [pow_zero, one_mul]
  have hFjdiff : ∀ (j : ℕ) (t : ℂ), ‖t‖ < (1 - m) / M →
      DifferentiableOn ℂ (Fj j t) {z : ℂ | z.im < 0} := by
    intro j t ht
    obtain ⟨c0, hc0, heq⟩ := hFjeq0 j t ht
    rw [heq]
    exact differentiableOn_id.add hc0
  have hWjdiff : ∀ (j : ℕ) (t : ℂ), ‖t‖ < (1 - m) / M →
      DifferentiableOn ℂ (Wj j t) {z : ℂ | z.im < 0} := by
    intro j t ht
    rw [hWjeq j t]
    exact ((hFjdiff j t ht).sub_const (Fj j t 0)).const_mul (Fj j t 1 - Fj j t 0)⁻¹
  have hWdiff : ∀ (t : ℂ), ‖t‖ < (1 - m) / M →
      DifferentiableOn ℂ (W t) {z : ℂ | z.im < 0} := by
    intro t ht
    refine TendstoLocallyUniformlyOn.differentiableOn
      (((tendstoLocallyUniformlyOn_univ.mpr (hWconv t ht)).mono (Set.subset_univ _)))
      (Filter.Eventually.of_forall fun j => hWjdiff j t ht) hLower
  -- ===== derivative-tower scaling identities =====
  have hWjD : ∀ (j : ℕ) (t : ℂ), ‖t‖ < (1 - m) / M → ∀ w : ℂ, w.im < 0 →
      deriv (Wj j t) w = (Fj j t 1 - Fj j t 0)⁻¹ * deriv (Fj j t) w
      ∧ deriv (deriv (Wj j t)) w
          = (Fj j t 1 - Fj j t 0)⁻¹ * deriv (deriv (Fj j t)) w
      ∧ deriv (deriv (deriv (Wj j t))) w
          = (Fj j t 1 - Fj j t 0)⁻¹ * deriv (deriv (deriv (Fj j t))) w := by
    intro j t ht w hw
    have hFan : AnalyticOnNhd ℂ (Fj j t) {z : ℂ | z.im < 0} :=
      (hFjdiff j t ht).analyticOnNhd hLower
    have hT1 : ∀ w' : ℂ, w'.im < 0 → deriv (Wj j t) w'
        = (Fj j t 1 - Fj j t 0)⁻¹ * deriv (Fj j t) w' := by
      intro w' hw'
      have hF : HasDerivAt (Fj j t) (deriv (Fj j t) w') w' :=
        ((hFjdiff j t ht).differentiableAt (hLower.mem_nhds hw')).hasDerivAt
      rw [hWjeq j t]
      exact ((hF.sub_const (Fj j t 0)).const_mul (Fj j t 1 - Fj j t 0)⁻¹).deriv
    have hT2 : ∀ w' : ℂ, w'.im < 0 → deriv (deriv (Wj j t)) w'
        = (Fj j t 1 - Fj j t 0)⁻¹ * deriv (deriv (Fj j t)) w' := by
      intro w' hw'
      have hev : deriv (Wj j t) =ᶠ[nhds w']
          fun x => (Fj j t 1 - Fj j t 0)⁻¹ * deriv (Fj j t) x := by
        filter_upwards [hLower.mem_nhds hw'] with x hx
        exact hT1 x hx
      rw [hev.deriv_eq]
      have hF2 : HasDerivAt (deriv (Fj j t)) (deriv (deriv (Fj j t)) w') w' :=
        ((hFan.deriv w' hw').differentiableAt).hasDerivAt
      exact (hF2.const_mul (Fj j t 1 - Fj j t 0)⁻¹).deriv
    have hT3 : deriv (deriv (deriv (Wj j t))) w
        = (Fj j t 1 - Fj j t 0)⁻¹ * deriv (deriv (deriv (Fj j t))) w := by
      have hev : deriv (deriv (Wj j t)) =ᶠ[nhds w]
          fun x => (Fj j t 1 - Fj j t 0)⁻¹ * deriv (deriv (Fj j t)) x := by
        filter_upwards [hLower.mem_nhds hw] with x hx
        exact hT2 x hx
      rw [hev.deriv_eq]
      have hF3 : HasDerivAt (deriv (deriv (Fj j t)))
          (deriv (deriv (deriv (Fj j t))) w) w :=
        (((hFan.deriv).deriv w hw).differentiableAt).hasDerivAt
      exact (hF3.const_mul (Fj j t 1 - Fj j t 0)⁻¹).deriv
    exact ⟨hT1 w hw, hT2 w hw, hT3⟩
  -- ===== the per-point analytic core =====
  have hMain : ∀ z₀ : ℂ, z₀.im < 0 →
      (∀ t₁ : ℂ, ‖t₁‖ < (1 - m) / M → AnalyticAt ℂ (fun t => W t z₀) t₁)
      ∧ (∀ t₁ : ℂ, ‖t₁‖ < (1 - m) / M →
          AnalyticAt ℂ (fun t => schwarzian (W t) z₀) t₁)
      ∧ ((∀ z : ℂ, κ z = 0) → HasDerivAt (fun t => schwarzian (W t) z₀)
          (-(6 / (Real.pi : ℂ)) * ∫ ζ in {ζ : ℂ | 0 < ζ.im}, ν ζ / (ζ - z₀) ^ 4) 0) := by
    intro z₀ hz₀
    have hz₀m : z₀ ∈ {z : ℂ | z.im < 0} := hz₀
    have hr2 : (0 : ℝ) < -z₀.im / 2 := by
      have : z₀.im < 0 := hz₀
      linarith
    have hID2 : ∀ u : ℂ → ℂ, iteratedDeriv 2 u = deriv (deriv u) := by
      intro u
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have hID3 : ∀ u : ℂ → ℂ, iteratedDeriv 3 u = deriv (deriv (deriv u)) := by
      intro u
      rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, show (2 : ℕ) = 1 + 1 from rfl,
        iteratedDeriv_succ, iteratedDeriv_one]
    -- ===== A: per-(j, t₁) parameter-analyticity of the Fⱼ towers =====
    have hFjAn : ∀ (j : ℕ) (t₁ : ℂ), ‖t₁‖ < (1 - m) / M →
        (∀ z : ℂ, AnalyticAt ℂ (fun t => Fj j t z) t₁)
        ∧ AnalyticAt ℂ (fun t => deriv (Fj j t) z₀) t₁
        ∧ AnalyticAt ℂ (fun t => deriv (deriv (Fj j t)) z₀) t₁
        ∧ AnalyticAt ℂ (fun t => deriv (deriv (deriv (Fj j t))) z₀) t₁ := by
      intro j t₁ ht₁
      obtain ⟨ε, cs, Mc, ρc, hε0, hρc0, hMc0, hερ, hcb1, hcb0, hcdiff, hser, _⟩ :=
        hFloc j t₁ ht₁
      have hsρ : ∀ s : ℂ, ‖s‖ < ε → ‖s‖ * ρc < 1 := fun s hs =>
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right hs.le hρc0) hερ
      have hzwei : ∀ s : ℂ, ‖s‖ < ε →
          deriv (fun z => z + ∑' n : ℕ, s ^ n * cs n z) z₀
              = 1 + ∑' n : ℕ, s ^ n * deriv (cs n) z₀
          ∧ deriv (deriv (fun z => z + ∑' n : ℕ, s ^ n * cs n z)) z₀
              = ∑' n : ℕ, s ^ n * deriv (deriv (cs n)) z₀
          ∧ deriv (deriv (deriv (fun z => z + ∑' n : ℕ, s ^ n * cs n z))) z₀
              = ∑' n : ℕ, s ^ n * deriv (deriv (deriv (cs n))) z₀ :=
        fun s hs => w2_zwei cs Mc ρc s hρc0 hMc0 (hsρ s hs) hcb1 hcb0 hcdiff z₀ hz₀
      have hb1 : ∀ n : ℕ, ‖deriv (cs (n + 1)) z₀‖
          ≤ ((1 : ℕ).factorial * Mc / (-z₀.im / 2) ^ 1) * ρc ^ n := by
        intro n
        have h1 := w2_cau (cs (n + 1)) (Mc * ρc ^ n) (hcdiff (n + 1)) z₀ hz₀
          (fun z _ => hcb1 n z) 1
        rw [iteratedDeriv_one] at h1
        calc ‖deriv (cs (n + 1)) z₀‖
            ≤ ((1 : ℕ).factorial : ℝ) * (Mc * ρc ^ n) / (-z₀.im / 2) ^ 1 := h1
          _ = ((1 : ℕ).factorial * Mc / (-z₀.im / 2) ^ 1) * ρc ^ n := by ring
      have hb2 : ∀ n : ℕ, ‖deriv (deriv (cs (n + 1))) z₀‖
          ≤ ((2 : ℕ).factorial * Mc / (-z₀.im / 2) ^ 2) * ρc ^ n := by
        intro n
        have h1 := w2_cau (cs (n + 1)) (Mc * ρc ^ n) (hcdiff (n + 1)) z₀ hz₀
          (fun z _ => hcb1 n z) 2
        rw [hID2 (cs (n + 1))] at h1
        calc ‖deriv (deriv (cs (n + 1))) z₀‖
            ≤ ((2 : ℕ).factorial : ℝ) * (Mc * ρc ^ n) / (-z₀.im / 2) ^ 2 := h1
          _ = ((2 : ℕ).factorial * Mc / (-z₀.im / 2) ^ 2) * ρc ^ n := by ring
      have hb3 : ∀ n : ℕ, ‖deriv (deriv (deriv (cs (n + 1)))) z₀‖
          ≤ ((3 : ℕ).factorial * Mc / (-z₀.im / 2) ^ 3) * ρc ^ n := by
        intro n
        have h1 := w2_cau (cs (n + 1)) (Mc * ρc ^ n) (hcdiff (n + 1)) z₀ hz₀
          (fun z _ => hcb1 n z) 3
        rw [hID3 (cs (n + 1))] at h1
        calc ‖deriv (deriv (deriv (cs (n + 1)))) z₀‖
            ≤ ((3 : ℕ).factorial : ℝ) * (Mc * ρc ^ n) / (-z₀.im / 2) ^ 3 := h1
          _ = ((3 : ℕ).factorial * Mc / (-z₀.im / 2) ^ 3) * ρc ^ n := by ring
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro z
        refine w2_glue _ t₁ ε (fun s => z + ∑' n : ℕ, s ^ n * cs n z) hε0
          (analyticAt_const.add
            (w2_an0 (fun n => cs n z) Mc ρc hρc0 (fun n => hcb1 n z) 0 (by simp))) ?_
        intro s hs
        change Fj j (t₁ + s) z = z + ∑' n : ℕ, s ^ n * cs n z
        rw [hser s hs]
      · refine w2_glue _ t₁ ε (fun s => 1 + ∑' n : ℕ, s ^ n * deriv (cs n) z₀) hε0
          (analyticAt_const.add
            (w2_an0 (fun n => deriv (cs n) z₀) _ ρc hρc0 hb1 0 (by simp))) ?_
        intro s hs
        change deriv (Fj j (t₁ + s)) z₀ = 1 + ∑' n : ℕ, s ^ n * deriv (cs n) z₀
        rw [hser s hs]
        exact (hzwei s hs).1
      · refine w2_glue _ t₁ ε (fun s => ∑' n : ℕ, s ^ n * deriv (deriv (cs n)) z₀) hε0
          (w2_an0 (fun n => deriv (deriv (cs n)) z₀) _ ρc hρc0 hb2 0 (by simp)) ?_
        intro s hs
        change deriv (deriv (Fj j (t₁ + s))) z₀
            = ∑' n : ℕ, s ^ n * deriv (deriv (cs n)) z₀
        rw [hser s hs]
        exact (hzwei s hs).2.1
      · refine w2_glue _ t₁ ε
          (fun s => ∑' n : ℕ, s ^ n * deriv (deriv (deriv (cs n))) z₀) hε0
          (w2_an0 (fun n => deriv (deriv (deriv (cs n))) z₀) _ ρc hρc0 hb3 0 (by simp)) ?_
        intro s hs
        change deriv (deriv (deriv (Fj j (t₁ + s)))) z₀
            = ∑' n : ℕ, s ^ n * deriv (deriv (deriv (cs n))) z₀
        rw [hser s hs]
        exact (hzwei s hs).2.2
    -- ===== B: parameter-analyticity of the Wⱼ towers =====
    have hXan : ∀ (j : ℕ) (t₁ : ℂ), ‖t₁‖ < (1 - m) / M →
        AnalyticAt ℂ (fun t => Wj j t z₀) t₁
        ∧ AnalyticAt ℂ (fun t => deriv (Wj j t) z₀) t₁
        ∧ AnalyticAt ℂ (fun t => deriv (deriv (Wj j t)) z₀) t₁
        ∧ AnalyticAt ℂ (fun t => deriv (deriv (deriv (Wj j t))) z₀) t₁ := by
      intro j t₁ ht₁
      obtain ⟨hF0an, hF1an, hF2an, hF3an⟩ := hFjAn j t₁ ht₁
      have hdenan : AnalyticAt ℂ (fun t => Fj j t 1 - Fj j t 0) t₁ :=
        (hF0an 1).sub (hF0an 0)
      have hinvan : AnalyticAt ℂ (fun t => (Fj j t 1 - Fj j t 0)⁻¹) t₁ :=
        hdenan.inv (hFden j t₁ ht₁)
      have hWfun : (fun t => Wj j t z₀)
          = fun t => (Fj j t 1 - Fj j t 0)⁻¹ * (Fj j t z₀ - Fj j t 0) := by
        funext t
        rw [hWjeq j t]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hWfun]
        exact hinvan.mul ((hF0an z₀).sub (hF0an 0))
      · refine (hinvan.mul hF1an).congr ?_
        filter_upwards [hopenD.mem_nhds ht₁] with t ht
        exact ((hWjD j t ht z₀ hz₀).1).symm
      · refine (hinvan.mul hF2an).congr ?_
        filter_upwards [hopenD.mem_nhds ht₁] with t ht
        exact ((hWjD j t ht z₀ hz₀).2.1).symm
      · refine (hinvan.mul hF3an).congr ?_
        filter_upwards [hopenD.mem_nhds ht₁] with t ht
        exact ((hWjD j t ht z₀ hz₀).2.2).symm
    -- ===== C: pointwise convergence of the towers in the parameter =====
    have hXconv : ∀ t : ℂ, ‖t‖ < (1 - m) / M →
        Filter.Tendsto (fun j => Wj j t z₀) Filter.atTop (nhds (W t z₀))
        ∧ Filter.Tendsto (fun j => deriv (Wj j t) z₀) Filter.atTop
            (nhds (deriv (W t) z₀))
        ∧ Filter.Tendsto (fun j => deriv (deriv (Wj j t)) z₀) Filter.atTop
            (nhds (deriv (deriv (W t)) z₀))
        ∧ Filter.Tendsto (fun j => deriv (deriv (deriv (Wj j t))) z₀) Filter.atTop
            (nhds (deriv (deriv (deriv (W t))) z₀)) := by
      intro t ht
      have hTLU : TendstoLocallyUniformlyOn (fun j => Wj j t) (W t) Filter.atTop
          {z : ℂ | z.im < 0} :=
        (tendstoLocallyUniformlyOn_univ.mpr (hWconv t ht)).mono (Set.subset_univ _)
      have hWjan : ∀ j : ℕ, AnalyticOnNhd ℂ (Wj j t) {z : ℂ | z.im < 0} := fun j =>
        (hWjdiff j t ht).analyticOnNhd hLower
      have hd1 := hTLU.deriv (Filter.Eventually.of_forall fun j => hWjdiff j t ht) hLower
      have hd2 := hd1.deriv
        (Filter.Eventually.of_forall fun j => ((hWjan j).deriv).differentiableOn) hLower
      have hd3 := hd2.deriv
        (Filter.Eventually.of_forall fun j => (((hWjan j).deriv).deriv).differentiableOn)
        hLower
      exact ⟨hTLU.tendsto_at hz₀m, hd1.tendsto_at hz₀m, hd2.tendsto_at hz₀m,
        hd3.tendsto_at hz₀m⟩
    -- ===== D: uniform bounds on parameter compacts =====
    have hXbnd : ∀ Kc : Set ℂ, Kc ⊆ {t : ℂ | ‖t‖ < (1 - m) / M} → IsCompact Kc →
        ∃ B : ℝ, ∀ (j : ℕ), ∀ t ∈ Kc, ‖Wj j t z₀‖ ≤ B ∧ ‖deriv (Wj j t) z₀‖ ≤ B
          ∧ ‖deriv (deriv (Wj j t)) z₀‖ ≤ B
          ∧ ‖deriv (deriv (deriv (Wj j t))) z₀‖ ≤ B := by
      intro Kc hKcD hKc
      rcases Kc.eq_empty_or_nonempty with hKe | hKne
      · refine ⟨0, fun j t htK => absurd htK ?_⟩
        rw [hKe]
        exact Set.notMem_empty t
      obtain ⟨t₂, ht₂K, ht₂max⟩ := hKc.exists_isMaxOn hKne continuous_norm.continuousOn
      have ht₂b : ∀ x ∈ Kc, ‖x‖ ≤ ‖t₂‖ := fun x hx => ht₂max hx
      clear ht₂max
      have ht₂D : ‖t₂‖ < (1 - m) / M := hKcD ht₂K
      have hk₀1 : m + ‖t₂‖ * M < 1 := hDball t₂ ht₂D
      have hk₀0 : 0 ≤ m + ‖t₂‖ * M :=
        add_nonneg hm0 (mul_nonneg (norm_nonneg t₂) hM0.le)
      have h1k₀ : (0 : ℝ) < 1 - (m + ‖t₂‖ * M) := by linarith
      obtain ⟨Kq, hKqdef⟩ : ∃ q : ℝ,
          q = (1 + (m + ‖t₂‖ * M)) / (1 - (m + ‖t₂‖ * M)) := ⟨_, rfl⟩
      have hKq1 : (1 : ℝ) ≤ Kq := by
        rw [hKqdef, le_div_iff₀ h1k₀]
        linarith only [hk₀0]
      have hKqmul : Kq * (1 - (m + ‖t₂‖ * M)) = 1 + (m + ‖t₂‖ * M) := by
        rw [hKqdef]
        exact div_mul_cancel₀ _ h1k₀.ne'
      have hKqk : (Kq - 1) / (Kq + 1) = m + ‖t₂‖ * M := by
        have hKqp : (0 : ℝ) < Kq + 1 := by
          have h1 : (0 : ℝ) < Kq := lt_of_lt_of_le one_pos hKq1
          linarith only [h1]
        rw [div_eq_iff hKqp.ne']
        linear_combination hKqmul
      have hgeo : ∀ (j : ℕ), ∀ t ∈ Kc, IsQCGeometric (Wj j t) Kq := by
        intro j t htK
        have htD := hKcD htK
        refine isQCGeometric_of_isQCAnalytic hKq1 ?_ (hWjQC j t htD)
        rw [hKqk]
        have hb : ∀ z : ℂ, ‖(btr j t htD).μ z‖ ≤ m + ‖t₂‖ * M := by
          intro z
          rw [hbtr j t htD z]
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_mul]
          refine add_le_add (hκtb j z) ?_
          refine mul_le_mul (ht₂b t htK) (hνtb j z) (norm_nonneg _) (norm_nonneg _)
        have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top
          (eLpNormEssSup_le_of_ae_bound (μ := volume)
            (Filter.Eventually.of_forall hb))
        rwa [ENNReal.toReal_ofReal hk₀0] at h2
      obtain ⟨B₀, hB₀⟩ := w2_ubnd Kq (‖z₀‖ + -z₀.im / 2)
        (add_nonneg (norm_nonneg z₀) hr2.le)
      have hdisk : ∀ (j : ℕ), ∀ t ∈ Kc, ∀ ζ ∈ Metric.closedBall z₀ (-z₀.im / 2),
          ‖Wj j t ζ‖ ≤ B₀ := by
        intro j t htK ζ hζ
        refine hB₀ (Wj j t) (hgeo j t htK) (hWj0 j t) (hWj1 j t (hKcD htK)) ζ ?_
        rw [Metric.mem_closedBall, dist_eq_norm] at hζ
        calc ‖ζ‖ = ‖z₀ + (ζ - z₀)‖ := by ring_nf
          _ ≤ ‖z₀‖ + ‖ζ - z₀‖ := norm_add_le _ _
          _ ≤ ‖z₀‖ + -z₀.im / 2 := add_le_add le_rfl hζ
      have hB₀0 : 0 ≤ B₀ :=
        le_trans (norm_nonneg _)
          (hdisk 0 t₂ ht₂K z₀ (Metric.mem_closedBall_self hr2.le))
      have hrp1 : (0 : ℝ) < (-z₀.im / 2) ^ 1 := by
        rw [pow_one]
        exact hr2
      have hrp2 : (0 : ℝ) < (-z₀.im / 2) ^ 2 := pow_pos hr2 2
      have hrp3 : (0 : ℝ) < (-z₀.im / 2) ^ 3 := pow_pos hr2 3
      have ht1 : (0 : ℝ) ≤ 1 * B₀ / (-z₀.im / 2) ^ 1 :=
        div_nonneg (by linarith only [hB₀0]) hrp1.le
      have ht2 : (0 : ℝ) ≤ 2 * B₀ / (-z₀.im / 2) ^ 2 :=
        div_nonneg (by linarith only [hB₀0]) hrp2.le
      have ht3 : (0 : ℝ) ≤ 6 * B₀ / (-z₀.im / 2) ^ 3 :=
        div_nonneg (by linarith only [hB₀0]) hrp3.le
      refine ⟨B₀ + (1 * B₀ / (-z₀.im / 2) ^ 1 + 2 * B₀ / (-z₀.im / 2) ^ 2
        + 6 * B₀ / (-z₀.im / 2) ^ 3), fun j t htK => ?_⟩
      have htD := hKcD htK
      have hc1 := w2_cau (Wj j t) B₀ (hWjdiff j t htD) z₀ hz₀ (hdisk j t htK) 1
      have hc2 := w2_cau (Wj j t) B₀ (hWjdiff j t htD) z₀ hz₀ (hdisk j t htK) 2
      have hc3 := w2_cau (Wj j t) B₀ (hWjdiff j t htD) z₀ hz₀ (hdisk j t htK) 3
      rw [iteratedDeriv_one] at hc1
      rw [hID2 (Wj j t)] at hc2
      rw [hID3 (Wj j t)] at hc3
      refine ⟨?_, ?_, ?_, ?_⟩
      · have h1 := hdisk j t htK z₀ (Metric.mem_closedBall_self hr2.le)
        linarith only [h1, ht1, ht2, ht3]
      · have h1 : ((1 : ℕ).factorial : ℝ) * B₀ / (-z₀.im / 2) ^ 1
            = 1 * B₀ / (-z₀.im / 2) ^ 1 := by
          rw [Nat.factorial_one, Nat.cast_one]
        rw [h1] at hc1
        linarith only [hc1, hB₀0, ht2, ht3]
      · have h1 : ((2 : ℕ).factorial : ℝ) * B₀ / (-z₀.im / 2) ^ 2
            = 2 * B₀ / (-z₀.im / 2) ^ 2 := by
          rw [show (2 : ℕ).factorial = 2 from rfl]
          norm_num
        rw [h1] at hc2
        linarith only [hc2, hB₀0, ht1, ht3]
      · have h1 : ((3 : ℕ).factorial : ℝ) * B₀ / (-z₀.im / 2) ^ 3
            = 6 * B₀ / (-z₀.im / 2) ^ 3 := by
          rw [show (3 : ℕ).factorial = 6 from rfl]
          norm_num
        rw [h1] at hc3
        linarith only [hc3, hB₀0, ht1, ht2]
    -- ===== E: Vitali upgrades =====
    have hVit0 : TendstoLocallyUniformlyOn (fun j => fun t => Wj j t z₀)
        (fun t => W t z₀) Filter.atTop {t : ℂ | ‖t‖ < (1 - m) / M} := by
      refine w2_vitali _ _ _ hopenD ?_ ?_ ?_
      · intro j t₁ ht₁
        exact ((hXan j t₁ ht₁).1).differentiableAt.differentiableWithinAt
      · intro Kc hKcD hKc
        obtain ⟨B, hB⟩ := hXbnd Kc hKcD hKc
        exact ⟨B, fun j t htK => (hB j t htK).1⟩
      · intro t ht
        exact (hXconv t ht).1
    have hVit1 : TendstoLocallyUniformlyOn (fun j => fun t => deriv (Wj j t) z₀)
        (fun t => deriv (W t) z₀) Filter.atTop {t : ℂ | ‖t‖ < (1 - m) / M} := by
      refine w2_vitali _ _ _ hopenD ?_ ?_ ?_
      · intro j t₁ ht₁
        exact ((hXan j t₁ ht₁).2.1).differentiableAt.differentiableWithinAt
      · intro Kc hKcD hKc
        obtain ⟨B, hB⟩ := hXbnd Kc hKcD hKc
        exact ⟨B, fun j t htK => (hB j t htK).2.1⟩
      · intro t ht
        exact (hXconv t ht).2.1
    have hVit2 : TendstoLocallyUniformlyOn (fun j => fun t => deriv (deriv (Wj j t)) z₀)
        (fun t => deriv (deriv (W t)) z₀) Filter.atTop {t : ℂ | ‖t‖ < (1 - m) / M} := by
      refine w2_vitali _ _ _ hopenD ?_ ?_ ?_
      · intro j t₁ ht₁
        exact ((hXan j t₁ ht₁).2.2.1).differentiableAt.differentiableWithinAt
      · intro Kc hKcD hKc
        obtain ⟨B, hB⟩ := hXbnd Kc hKcD hKc
        exact ⟨B, fun j t htK => (hB j t htK).2.2.1⟩
      · intro t ht
        exact (hXconv t ht).2.2.1
    have hVit3 : TendstoLocallyUniformlyOn
        (fun j => fun t => deriv (deriv (deriv (Wj j t))) z₀)
        (fun t => deriv (deriv (deriv (W t))) z₀) Filter.atTop
        {t : ℂ | ‖t‖ < (1 - m) / M} := by
      refine w2_vitali _ _ _ hopenD ?_ ?_ ?_
      · intro j t₁ ht₁
        exact ((hXan j t₁ ht₁).2.2.2).differentiableAt.differentiableWithinAt
      · intro Kc hKcD hKc
        obtain ⟨B, hB⟩ := hXbnd Kc hKcD hKc
        exact ⟨B, fun j t htK => (hB j t htK).2.2.2⟩
      · intro t ht
        exact (hXconv t ht).2.2.2
    -- ===== F: analyticity of the limit towers =====
    have hdiffOfVit : ∀ (G : ℕ → ℂ → ℂ) (g' : ℂ → ℂ),
        TendstoLocallyUniformlyOn G g' Filter.atTop {t : ℂ | ‖t‖ < (1 - m) / M} →
        (∀ (j : ℕ) (t₁ : ℂ), ‖t₁‖ < (1 - m) / M → AnalyticAt ℂ (G j) t₁) →
        AnalyticOnNhd ℂ g' {t : ℂ | ‖t‖ < (1 - m) / M} := by
      intro G g' hG hGan
      refine DifferentiableOn.analyticOnNhd ?_ hopenD
      refine hG.differentiableOn (Filter.Eventually.of_forall fun j => ?_) hopenD
      intro t₁ ht₁
      exact (hGan j t₁ ht₁).differentiableAt.differentiableWithinAt
    have hψ0an : AnalyticOnNhd ℂ (fun t => W t z₀) {t : ℂ | ‖t‖ < (1 - m) / M} :=
      hdiffOfVit _ _ hVit0 fun j t₁ ht₁ => (hXan j t₁ ht₁).1
    have hψ1an : AnalyticOnNhd ℂ (fun t => deriv (W t) z₀)
        {t : ℂ | ‖t‖ < (1 - m) / M} :=
      hdiffOfVit _ _ hVit1 fun j t₁ ht₁ => (hXan j t₁ ht₁).2.1
    have hψ2an : AnalyticOnNhd ℂ (fun t => deriv (deriv (W t)) z₀)
        {t : ℂ | ‖t‖ < (1 - m) / M} :=
      hdiffOfVit _ _ hVit2 fun j t₁ ht₁ => (hXan j t₁ ht₁).2.2.1
    have hψ3an : AnalyticOnNhd ℂ (fun t => deriv (deriv (deriv (W t))) z₀)
        {t : ℂ | ‖t‖ < (1 - m) / M} :=
      hdiffOfVit _ _ hVit3 fun j t₁ ht₁ => (hXan j t₁ ht₁).2.2.2
    -- ===== G: nonvanishing of the first derivative =====
    have hψ1ne : ∀ t : ℂ, ‖t‖ < (1 - m) / M → deriv (W t) z₀ ≠ 0 := by
      intro t ht
      have hinj : Function.Injective (W t) := by
        rw [hWt t ht]
        exact (hW0 t ht).1.1.1.injective
      exact deriv_ne_zero_of_injOn hLower (hWdiff t ht)
        (Function.Injective.injOn hinj) hz₀m
    -- ===== H: the Schwarzian as a rational tower expression =====
    have hSchw : (fun t => schwarzian (W t) z₀)
        = fun t => deriv (deriv (deriv (W t))) z₀ / deriv (W t) z₀
          - 3 / 2 * (deriv (deriv (W t)) z₀ / deriv (W t) z₀) ^ 2 := by
      funext t
      show schwarzian (W t) z₀ = _
      rw [schwarzian, hID3 (W t), hID2 (W t)]
    refine ⟨?_, ?_, ?_⟩
    · intro t₁ ht₁
      exact hψ0an t₁ ht₁
    · intro t₁ ht₁
      rw [hSchw]
      exact ((hψ3an t₁ ht₁).div (hψ1an t₁ ht₁) (hψ1ne t₁ ht₁)).sub
        (analyticAt_const.mul
          (((hψ2an t₁ ht₁).div (hψ1an t₁ ht₁) (hψ1ne t₁ ht₁)).pow 2))
    · -- ===== I: the kernel derivative at the origin =====
      intro hκ0
      have h0D : ‖(0 : ℂ)‖ < (1 - m) / M := by simpa using hD0
      -- per-j kernel derivative of the third tower
      have hderXj : ∀ j : ℕ, HasDerivAt (fun t => deriv (deriv (deriv (Wj j t))) z₀)
          (-(6 / (Real.pi : ℂ)) * ∫ ζ : ℂ, νt j ζ / (ζ - z₀) ^ 4) 0 := by
        intro j
        obtain ⟨ε, cs, Mc, ρc, hε0, hρc0, hMc0, hερ, hcb1, hcb0, hcdiff, hser, hkz⟩ :=
          hFloc j 0 h0D
        obtain ⟨hcs0, hcs1⟩ := hkz hκ0 rfl
        have hsρ : ∀ s : ℂ, ‖s‖ < ε → ‖s‖ * ρc < 1 := fun s hs =>
          lt_of_le_of_lt (mul_le_mul_of_nonneg_right hs.le hρc0) hερ
        -- the base solution is the identity
        have hFj0 : Fj j 0 = fun z : ℂ => z := by
          have h0 := hser 0 (by simpa using hε0)
          rw [add_zero] at h0
          rw [h0]
          funext z
          rw [tsum_eq_single 0 (fun n hn => by rw [zero_pow hn, zero_mul]), pow_zero,
            one_mul, hcs0 z, add_zero]
        have hden0 : Fj j 0 1 - Fj j 0 0 = 1 := by
          rw [hFj0]
          simp
        -- the third-tower series at the origin
        have hN3eq : ∀ s : ℂ, ‖s‖ < ε → deriv (deriv (deriv (Fj j s))) z₀
            = ∑' n : ℕ, s ^ n * deriv (deriv (deriv (cs n))) z₀ := by
          intro s hs
          have h1 := hser s hs
          rw [zero_add] at h1
          rw [h1]
          exact (w2_zwei cs Mc ρc s hρc0 hMc0 (hsρ s hs) hcb1 hcb0 hcdiff z₀ hz₀).2.2
        have hb3 : ∀ n : ℕ, ‖deriv (deriv (deriv (cs (n + 1)))) z₀‖
            ≤ ((3 : ℕ).factorial * Mc / (-z₀.im / 2) ^ 3) * ρc ^ n := by
          intro n
          have h1 := w2_cau (cs (n + 1)) (Mc * ρc ^ n) (hcdiff (n + 1)) z₀ hz₀
            (fun z _ => hcb1 n z) 3
          rw [hID3 (cs (n + 1))] at h1
          calc ‖deriv (deriv (deriv (cs (n + 1)))) z₀‖
              ≤ ((3 : ℕ).factorial : ℝ) * (Mc * ρc ^ n) / (-z₀.im / 2) ^ 3 := h1
            _ = ((3 : ℕ).factorial * Mc / (-z₀.im / 2) ^ 3) * ρc ^ n := by ring
        -- values of the tower coefficients
        have hcs0' : cs 0 = fun _ : ℂ => (0 : ℂ) := funext hcs0
        have hd30 : deriv (deriv (deriv (cs 0))) z₀ = 0 := by
          rw [hcs0', deriv_const', deriv_const', deriv_const']
        have hd31 : deriv (deriv (deriv (cs 1))) z₀
            = -(6 / (Real.pi : ℂ)) * ∫ ζ : ℂ, νt j ζ / (ζ - z₀) ^ 4 := by
          have h1 : cs 1 = cauchyTransform (νt j) := funext hcs1
          rw [h1, ← hID3 (cauchyTransform (νt j))]
          refine w2_ctD3 (νt j) 3 ((j : ℝ) + 1) (by norm_num) (by norm_num) ?_
            (hνts j) (hνtu j) z₀ hz₀
          refine memLp_of_eLpNormEssSup_ne_top_of_support (by norm_num) (hνtm j) ?_
            (hνts j)
          exact (lt_of_le_of_lt (eLpNormEssSup_le_of_ae_bound
            (Filter.Eventually.of_forall (hνtb j))) ENNReal.ofReal_lt_top).ne
        -- derivative of the numerator at the origin
        have hN3der : HasDerivAt (fun s : ℂ => deriv (deriv (deriv (Fj j s))) z₀)
            (deriv (deriv (deriv (cs 1))) z₀) 0 := by
          have h1 := w2_der0 (fun n => deriv (deriv (deriv (cs n))) z₀)
            ((3 : ℕ).factorial * Mc / (-z₀.im / 2) ^ 3) ρc hρc0 hb3
          refine h1.congr_of_eventuallyEq ?_
          filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε0] with s hs
          have hs' : ‖s‖ < ε := by
            rw [Metric.mem_ball, dist_zero_right] at hs
            exact hs
          change deriv (deriv (deriv (Fj j s))) z₀
              = ∑' n : ℕ, s ^ n * deriv (deriv (deriv (cs n))) z₀
          exact hN3eq s hs'
        -- the numerator vanishes at the origin
        have hN30 : deriv (deriv (deriv (Fj j 0))) z₀ = 0 := by
          rw [hFj0, deriv_id'', deriv_const', deriv_const']
        -- the denominator has value one at the origin
        have hdenan : AnalyticAt ℂ (fun t => Fj j t 1 - Fj j t 0) 0 :=
          (((hFjAn j 0 h0D).1 1)).sub (((hFjAn j 0 h0D).1 0))
        have hdender : HasDerivAt (fun t => Fj j t 1 - Fj j t 0)
            (deriv (fun t => Fj j t 1 - Fj j t 0) 0) 0 :=
          hdenan.differentiableAt.hasDerivAt
        have hdenne0 : Fj j 0 1 - Fj j 0 0 ≠ 0 := by
          rw [hden0]
          exact one_ne_zero
        -- the inverse-denominator times numerator has the kernel derivative
        have hinv : HasDerivAt (fun t => (Fj j t 1 - Fj j t 0)⁻¹)
            (-(deriv (fun t => Fj j t 1 - Fj j t 0) 0) / (Fj j 0 1 - Fj j 0 0) ^ 2) 0 :=
          hdender.inv hdenne0
        have hprod := hinv.mul hN3der
        have hprod' : HasDerivAt
            (fun t => (Fj j t 1 - Fj j t 0)⁻¹ * deriv (deriv (deriv (Fj j t))) z₀)
            (deriv (deriv (deriv (cs 1))) z₀) 0 := by
          convert hprod using 1
          beta_reduce
          rw [hN30, hden0, mul_zero, zero_add, inv_one, one_mul]
        have hXev : (fun t => deriv (deriv (deriv (Wj j t))) z₀) =ᶠ[nhds 0]
            fun t => (Fj j t 1 - Fj j t 0)⁻¹ * deriv (deriv (deriv (Fj j t))) z₀ := by
          filter_upwards [hopenD.mem_nhds h0D] with t ht
          exact (hWjD j t ht z₀ hz₀).2.2
        have h3 := hprod'.congr_of_eventuallyEq hXev
        rwa [hd31] at h3
      -- identity of the truncated solutions at the origin
      have hFj0all : ∀ j : ℕ, Fj j 0 = fun z : ℂ => z := by
        intro j
        obtain ⟨ε, cs, Mc, ρc, hε0, _, _, _, _, _, _, hser, hkz⟩ := hFloc j 0 h0D
        obtain ⟨hcs0, _⟩ := hkz hκ0 rfl
        have h0 := hser 0 (by simpa using hε0)
        rw [add_zero] at h0
        rw [h0]
        funext z
        rw [tsum_eq_single 0 (fun n hn => by rw [zero_pow hn, zero_mul]), pow_zero,
          one_mul, hcs0 z, add_zero]
      have hWjid : ∀ j : ℕ, Wj j 0 = fun z : ℂ => z := by
        intro j
        rw [hWjeq j 0, hFj0all j]
        funext z
        simp
      -- the tower values of the limit at the origin
      have hψ10 : deriv (W 0) z₀ = 1 := by
        have h1 := (hXconv 0 h0D).2.1
        have h2 : (fun j => deriv (Wj j 0) z₀) = fun _ : ℕ => (1 : ℂ) := by
          funext j
          rw [hWjid j]
          exact deriv_id z₀
        rw [h2] at h1
        exact tendsto_nhds_unique h1 tendsto_const_nhds
      have hψ20 : deriv (deriv (W 0)) z₀ = 0 := by
        have h1 := (hXconv 0 h0D).2.2.1
        have h2 : (fun j => deriv (deriv (Wj j 0)) z₀) = fun _ : ℕ => (0 : ℂ) := by
          funext j
          rw [hWjid j, deriv_id'', deriv_const']
        rw [h2] at h1
        exact tendsto_nhds_unique h1 tendsto_const_nhds
      have hψ30 : deriv (deriv (deriv (W 0))) z₀ = 0 := by
        have h1 := (hXconv 0 h0D).2.2.2
        have h2 : (fun j => deriv (deriv (deriv (Wj j 0))) z₀) = fun _ : ℕ => (0 : ℂ) := by
          funext j
          rw [hWjid j, deriv_id'', deriv_const', deriv_const']
        rw [h2] at h1
        exact tendsto_nhds_unique h1 tendsto_const_nhds
      have hq0 : schwarzian (W 0) z₀ = 0 := by
        have h1 := congrFun hSchw 0
        simp only at h1
        rw [h1, hψ30, hψ20, hψ10]
        norm_num
      -- Weierstrass in the parameter: the limit tower derivative at the origin
      have hX3diff : ∀ j : ℕ, DifferentiableOn ℂ
          (fun t => deriv (deriv (deriv (Wj j t))) z₀) {t : ℂ | ‖t‖ < (1 - m) / M} := by
        intro j t₁ ht₁
        exact ((hXan j t₁ ht₁).2.2.2).differentiableAt.differentiableWithinAt
      have hVd := hVit3.deriv (Filter.Eventually.of_forall hX3diff) hopenD
      have hlim1 : Filter.Tendsto
          (fun j => deriv (fun t => deriv (deriv (deriv (Wj j t))) z₀) 0) Filter.atTop
          (nhds (deriv (fun t => deriv (deriv (deriv (W t))) z₀) 0)) :=
        hVd.tendsto_at h0D
      -- identify the per-j derivative values and pass to the limit integral
      have hsetint : ∀ j : ℕ, (∫ ζ : ℂ, νt j ζ / (ζ - z₀) ^ 4)
          = ∫ ζ in {ζ : ℂ | 0 < ζ.im}, νt j ζ / (ζ - z₀) ^ 4 := by
        intro j
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
        intro ζ hζ
        have hζ' : ζ.im ≤ 0 := le_of_not_gt hζ
        rw [hνtu j ζ hζ', zero_div]
      have hdom : Filter.Tendsto
          (fun j => ∫ ζ in {ζ : ℂ | 0 < ζ.im}, νt j ζ / (ζ - z₀) ^ 4) Filter.atTop
          (nhds (∫ ζ in {ζ : ℂ | 0 < ζ.im}, ν ζ / (ζ - z₀) ^ 4)) := by
        refine tendsto_integral_of_dominated_convergence
          (fun ζ => M * (‖ζ - z₀‖ ^ (4 : ℕ))⁻¹) ?_ ?_ ?_ ?_
        · intro j
          have h1 : (fun ζ : ℂ => νt j ζ / (ζ - z₀) ^ 4)
              = fun ζ : ℂ => νt j ζ * ((ζ - z₀) ^ 4)⁻¹ := by
            funext ζ
            rw [div_eq_mul_inv]
          rw [h1]
          exact ((hνtm j).mul
            (((measurable_id.sub_const z₀).pow_const 4).inv)).aestronglyMeasurable.restrict
        · exact (w2_ker4 z₀ hz₀).const_mul M
        · intro j
          refine Filter.Eventually.of_forall fun ζ => ?_
          rw [norm_div, norm_pow, div_eq_mul_inv]
          refine mul_le_mul (hνtb j ζ) le_rfl
            (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) 4)) hM0.le
        · refine Filter.Eventually.of_forall fun ζ => ?_
          obtain ⟨N, hN⟩ := exists_nat_ge ‖ζ‖
          refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
          rw [Filter.EventuallyEq, Filter.eventually_atTop]
          refine ⟨N, fun j hj => ?_⟩
          have h1 : ‖ζ‖ ≤ (j : ℝ) + 1 := by
            have h2 : (N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
            linarith only [hN, h2]
          rw [hνta j ζ h1]
      have hcomb : Filter.Tendsto
          (fun j => deriv (fun t => deriv (deriv (deriv (Wj j t))) z₀) 0) Filter.atTop
          (nhds (-(6 / (Real.pi : ℂ))
            * ∫ ζ in {ζ : ℂ | 0 < ζ.im}, ν ζ / (ζ - z₀) ^ 4)) := by
        refine Filter.Tendsto.congr ?_ (hdom.const_mul (-(6 / (Real.pi : ℂ))))
        intro j
        rw [← hsetint j, ← (hderXj j).deriv]
      have hψ3der0 : deriv (fun t => deriv (deriv (deriv (W t))) z₀) 0
          = -(6 / (Real.pi : ℂ)) * ∫ ζ in {ζ : ℂ | 0 < ζ.im}, ν ζ / (ζ - z₀) ^ 4 :=
        tendsto_nhds_unique hlim1 hcomb
      -- the product-rule identity at the origin
      have hqan : AnalyticAt ℂ (fun t => schwarzian (W t) z₀) 0 := by
        rw [hSchw]
        exact ((hψ3an 0 h0D).div (hψ1an 0 h0D) (hψ1ne 0 h0D)).sub
          (analyticAt_const.mul
            (((hψ2an 0 h0D).div (hψ1an 0 h0D) (hψ1ne 0 h0D)).pow 2))
      have hq' : HasDerivAt (fun t => schwarzian (W t) z₀)
          (deriv (fun t => schwarzian (W t) z₀) 0) 0 :=
        hqan.differentiableAt.hasDerivAt
      have hψ1der : HasDerivAt (fun t => deriv (W t) z₀)
          (deriv (fun t => deriv (W t) z₀) 0) 0 :=
        (hψ1an 0 h0D).differentiableAt.hasDerivAt
      have hψ2der : HasDerivAt (fun t => deriv (deriv (W t)) z₀)
          (deriv (fun t => deriv (deriv (W t)) z₀) 0) 0 :=
        (hψ2an 0 h0D).differentiableAt.hasDerivAt
      have hψ3der : HasDerivAt (fun t => deriv (deriv (deriv (W t))) z₀)
          (deriv (fun t => deriv (deriv (deriv (W t))) z₀) 0) 0 :=
        (hψ3an 0 h0D).differentiableAt.hasDerivAt
      have hident : ∀ t : ℂ, ‖t‖ < (1 - m) / M →
          schwarzian (W t) z₀ * (deriv (W t) z₀) ^ 2
            = deriv (deriv (deriv (W t))) z₀ * deriv (W t) z₀
              - 3 / 2 * (deriv (deriv (W t)) z₀) ^ 2 := by
        intro t ht
        have h1 := congrFun hSchw t
        simp only at h1
        rw [h1]
        have hne := hψ1ne t ht
        have e1 : deriv (deriv (deriv (W t))) z₀ / deriv (W t) z₀ * deriv (W t) z₀
            = deriv (deriv (deriv (W t))) z₀ := div_mul_cancel₀ _ hne
        have e2 : deriv (deriv (W t)) z₀ / deriv (W t) z₀ * deriv (W t) z₀
            = deriv (deriv (W t)) z₀ := div_mul_cancel₀ _ hne
        calc (deriv (deriv (deriv (W t))) z₀ / deriv (W t) z₀
              - 3 / 2 * (deriv (deriv (W t)) z₀ / deriv (W t) z₀) ^ 2)
                * (deriv (W t) z₀) ^ 2
            = (deriv (deriv (deriv (W t))) z₀ / deriv (W t) z₀ * deriv (W t) z₀)
                * deriv (W t) z₀
              - 3 / 2 * (deriv (deriv (W t)) z₀ / deriv (W t) z₀ * deriv (W t) z₀) ^ 2 := by
              ring
          _ = deriv (deriv (deriv (W t))) z₀ * deriv (W t) z₀
              - 3 / 2 * (deriv (deriv (W t)) z₀) ^ 2 := by
              rw [e1, e2]
      have hψ1sq : HasDerivAt (fun t => (deriv (W t) z₀) ^ 2)
          (2 * deriv (W 0) z₀ * deriv (fun t => deriv (W t) z₀) 0) 0 := by
        have h1 := hψ1der.pow 2
        convert h1 using 1
        push_cast
        ring
      have hψ2sq : HasDerivAt (fun t => (deriv (deriv (W t)) z₀) ^ 2)
          (2 * deriv (deriv (W 0)) z₀ * deriv (fun t => deriv (deriv (W t)) z₀) 0) 0 := by
        have h1 := hψ2der.pow 2
        convert h1 using 1
        push_cast
        ring
      have hL : HasDerivAt (fun t => schwarzian (W t) z₀ * (deriv (W t) z₀) ^ 2)
          (deriv (fun t => schwarzian (W t) z₀) 0 * (deriv (W 0) z₀) ^ 2
            + schwarzian (W 0) z₀
              * (2 * deriv (W 0) z₀ * deriv (fun t => deriv (W t) z₀) 0)) 0 :=
        hq'.mul hψ1sq
      have hR : HasDerivAt (fun t => deriv (deriv (deriv (W t))) z₀ * deriv (W t) z₀
            - 3 / 2 * (deriv (deriv (W t)) z₀) ^ 2)
          (deriv (fun t => deriv (deriv (deriv (W t))) z₀) 0 * deriv (W 0) z₀
            + deriv (deriv (deriv (W 0))) z₀ * deriv (fun t => deriv (W t) z₀) 0
            - 3 / 2 * (2 * deriv (deriv (W 0)) z₀
                * deriv (fun t => deriv (deriv (W t)) z₀) 0)) 0 := by
        have h1 := (hψ3der.mul hψ1der).sub (hψ2sq.const_mul (3 / 2 : ℂ))
        convert h1 using 1
      have hEv : (fun t => deriv (deriv (deriv (W t))) z₀ * deriv (W t) z₀
            - 3 / 2 * (deriv (deriv (W t)) z₀) ^ 2) =ᶠ[nhds 0]
          fun t => schwarzian (W t) z₀ * (deriv (W t) z₀) ^ 2 := by
        filter_upwards [hopenD.mem_nhds h0D] with t ht
        exact (hident t ht).symm
      have hL2 := hL.congr_of_eventuallyEq hEv
      have huniq := hL2.unique hR
      rw [hψ10, hq0, hψ20, hψ30] at huniq
      have hq3 : deriv (fun t => schwarzian (W t) z₀) 0
          = deriv (fun t => deriv (deriv (deriv (W t))) z₀) 0 := by
        linear_combination huniq
      rw [hq3, hψ3der0] at hq'
      exact hq'
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · intro t ht
    refine ⟨bt t ht, hbt t ht, ?_, ?_, ?_⟩
    · rw [hWt t ht]
      exact (hW0 t ht).1
    · rw [hWt t ht]
      exact (hW0 t ht).2.1
    · rw [hWt t ht]
      exact (hW0 t ht).2.2
  · intro z hz t₁ ht₁
    exact (hMain z hz).1 t₁ ht₁
  · intro z hz t₁ ht₁
    exact (hMain z hz).2.1 t₁ ht₁
  · intro hκ0 z hz
    exact (hMain z hz).2.2 hκ0

/-- **Identity from vanishing Schwarzian**: a normalized solution of an upper-supported
coefficient whose Schwarzian vanishes on the lower half plane is the identity on the
closed lower half plane. -/
theorem eq_id_on_lower_of_schwarzian_eq_zero {w : ℂ → ℂ} {b : BeltramiCoeff}
    (hw : IsQCAnalytic w b) (hb : ∀ z : ℂ, z.im ≤ 0 → b.μ z = 0)
    (h0 : w 0 = 0) (h1 : w 1 = 1)
    (hS : ∀ z : ℂ, z.im < 0 → schwarzian w z = 0) :
    ∀ z : ℂ, z.im ≤ 0 → w z = z := by
  have hLopen : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  -- the coefficient vanishes a.e. on the open lower half plane, so `w` is holomorphic there
  have hbae : ∀ᵐ z ∂(volume.restrict {z : ℂ | z.im < 0}), b.μ z = 0 :=
    (ae_restrict_iff' hLopen.measurableSet).mpr
      (Filter.Eventually.of_forall fun z hz => hb z (le_of_lt hz))
  have hol : DifferentiableOn ℂ w {z : ℂ | z.im < 0} :=
    differentiableOn_of_beltrami_ae_zero hw hLopen hbae
  have hinj : Set.InjOn w {z : ℂ | z.im < 0} := fun x _ y _ h => hw.injective h
  -- rigidity of the vanishing Schwarzian: `w` is a single ratio on the lower half plane
  obtain ⟨a, p, c, d, hdet, hratio⟩ :=
    exists_ratio_of_schwarzian_eq_zero hLopen ((convex_halfSpace_im_lt 0).isPreconnected)
      ⟨-Complex.I, by simp⟩ hol
      (fun z hz => deriv_ne_zero_of_injOn hLopen hol hinj hz) (fun z hz => hS z hz)
  -- the vertical test ray
  have humem : ∀ n : ℕ, -((n : ℂ) + 1) * Complex.I ∈ {z : ℂ | z.im < 0} := by
    intro n
    have him : (-((n : ℂ) + 1) * Complex.I).im = -((n : ℝ) + 1) := by
      simp [Complex.mul_im]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simp only [Set.mem_setOf_eq, him]
    linarith
  have hnorm_u : ∀ n : ℕ, ‖-((n : ℂ) + 1) * Complex.I‖ = (n : ℝ) + 1 := by
    intro n
    rw [norm_mul, Complex.norm_I, mul_one, norm_neg]
    have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_natCast]
    push_cast
    ring
  -- properness of the plane homeomorphism `w` forces `c = 0`
  have hc0 : c = 0 := by
    by_contra hc
    set u : ℕ → ℂ := fun n => -((n : ℂ) + 1) * Complex.I with hu
    -- the ratio value along the ray, in pole-free form
    have hdecomp : ∀ n : ℕ, w (u n) = a / c + (p - a * d / c) * (c * u n + d)⁻¹ := by
      intro n
      rw [(hratio (u n) (humem n)).2]
      have hden := (hratio (u n) (humem n)).1
      rw [div_eq_iff hden, add_mul, mul_assoc, inv_mul_cancel₀ hden, mul_one]
      field_simp [hc]
      ring
    -- the denominator norm tends to infinity along the ray
    have hnormden : Filter.Tendsto (fun n : ℕ => ‖c * u n + d‖) Filter.atTop Filter.atTop := by
      have hlow : ∀ n : ℕ, ‖c‖ * ((n : ℝ) + 1) - ‖d‖ ≤ ‖c * u n + d‖ := by
        intro n
        have h1 : ‖c * u n‖ ≤ ‖c * u n + d‖ + ‖d‖ := by
          calc ‖c * u n‖ = ‖c * u n + d - d‖ := by ring_nf
            _ ≤ ‖c * u n + d‖ + ‖d‖ := norm_sub_le _ _
        have h2 : ‖c * u n‖ = ‖c‖ * ((n : ℝ) + 1) := by rw [norm_mul, hnorm_u n]
        linarith
      have hbase : Filter.Tendsto (fun n : ℕ => ‖c‖ * ((n : ℝ) + 1) - ‖d‖)
          Filter.atTop Filter.atTop := by
        have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1) Filter.atTop Filter.atTop :=
          Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
        have h2 := h1.const_mul_atTop (norm_pos_iff.mpr hc)
        simpa [sub_eq_add_neg] using Filter.tendsto_atTop_add_const_right _ (-‖d‖) h2
      exact Filter.tendsto_atTop_mono hlow hbase
    -- hence the inverses tend to zero and the ratio values converge
    have hinvzero : Filter.Tendsto (fun n : ℕ => (c * u n + d)⁻¹) Filter.atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa [norm_inv] using hnormden.inv_tendsto_atTop
    have hlim : Filter.Tendsto (fun n : ℕ => w (u n)) Filter.atTop (nhds (a / c)) := by
      have h1 : Filter.Tendsto (fun n : ℕ => a / c + (p - a * d / c) * (c * u n + d)⁻¹)
          Filter.atTop (nhds (a / c + (p - a * d / c) * 0)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.mul hinvzero)
      rw [mul_zero, add_zero] at h1
      exact h1.congr fun n => (hdecomp n).symm
    -- but the preimage of a compact ball under the homeomorphism is bounded
    have hK : IsCompact ((IsHomeomorph.homeomorph w hw.1.1).symm ''
        Metric.closedBall (a / c) 1) :=
      (isCompact_closedBall _ _).image (IsHomeomorph.homeomorph w hw.1.1).symm.continuous
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    have hev : ∀ᶠ n : ℕ in Filter.atTop, w (u n) ∈ Metric.closedBall (a / c) 1 :=
      hlim.eventually_mem (Metric.closedBall_mem_nhds _ one_pos)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    have hmem := hN (max N (Nat.ceil R)) (le_max_left _ _)
    have humem2 : u (max N (Nat.ceil R)) ∈ (IsHomeomorph.homeomorph w hw.1.1).symm ''
        Metric.closedBall (a / c) 1 := by
      refine ⟨w (u (max N (Nat.ceil R))), hmem, ?_⟩
      rw [← IsHomeomorph.homeomorph_apply w hw.1.1, Homeomorph.symm_apply_apply]
    have hle := hR humem2
    rw [Metric.mem_closedBall, dist_zero_right, hnorm_u] at hle
    have hceil : R ≤ ((max N (Nat.ceil R) : ℕ) : ℝ) :=
      le_trans (Nat.le_ceil R) (by exact_mod_cast le_max_right N (Nat.ceil R))
    linarith
  -- with `c = 0` the ratio is affine and extends by continuity to the closed half plane
  have hdne : d ≠ 0 := fun h => hdet (by rw [hc0, h]; ring)
  have hEq : Set.EqOn w (fun z => (a * z + p) / d) {z : ℂ | z.im < 0} := by
    intro z hz
    have h := (hratio z hz).2
    rwa [hc0, zero_mul, zero_add] at h
  have hcontg : Continuous fun z : ℂ => (a * z + p) / d :=
    ((continuous_const.mul continuous_id).add continuous_const).div_const d
  have hclose : Set.EqOn w (fun z => (a * z + p) / d) {z : ℂ | z.im ≤ 0} := by
    have h := hEq.closure hw.1.1.continuous hcontg
    rwa [Complex.closure_setOf_im_lt] at h
  -- normalization pins the affine map to the identity
  have hp0 : p = 0 := by
    have h := hclose (show (0 : ℂ) ∈ {z : ℂ | z.im ≤ 0} by simp)
    rw [h0] at h
    have h' : p / d = 0 := by simpa using h.symm
    rcases div_eq_zero_iff.mp h' with h'' | h''
    · exact h''
    · exact absurd h'' hdne
  have had : a = d := by
    have h := hclose (show (1 : ℂ) ∈ {z : ℂ | z.im ≤ 0} by simp)
    rw [h1] at h
    have h' : (a + p) / d = 1 := by simpa using h.symm
    rw [hp0, add_zero] at h'
    exact (div_eq_one_iff_eq hdne).mp h'
  intro z hz
  have h := hclose hz
  simp only [hp0, had, add_zero] at h
  rw [h, mul_comm d z, mul_div_assoc, div_self hdne, mul_one]

/-- **Group commutation from boundary triviality**: a normalized solution of an
upper-supported coefficient obeying the invariance law of `Γ` on the upper half plane
and equal to the identity on the closed lower half plane commutes with every Möbius map
of `Γ` off its pole. -/
theorem moebiusMap_comm_of_eq_id_lower {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {w : ℂ → ℂ} {b : BeltramiCoeff} (hw : IsQCAnalytic w b)
    (hb : ∀ z : ℂ, z.im ≤ 0 → b.μ z = 0)
    (hinv : ∀ W ∈ Γ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      b.μ (moebiusMap W z) * (moebiusDenom W z) ^ 2
        = b.μ z * (starRingEnd ℂ (moebiusDenom W z)) ^ 2)
    (hid : ∀ z : ℂ, z.im ≤ 0 → w z = z) :
    ∀ γ ∈ Γ, ∀ z : ℂ, moebiusDenom γ z ≠ 0 →
      w (moebiusMap γ z) = moebiusMap γ (w z) := by
  -- the support hypothesis is subsumed: the identity below already forces the
  -- coefficient to vanish there, and the reflection glue does not consult it
  have _ := hb
  -- `w` fixes the real line pointwise and preserves the open upper half plane
  have hreal : ∀ t : ℝ, (w (t : ℂ)).im = 0 := by
    intro t
    rw [hid (t : ℂ) (le_of_eq (Complex.ofReal_im t))]
    exact Complex.ofReal_im t
  have hupper : ∀ z : ℂ, 0 < z.im → 0 < (w z).im := by
    intro z hz
    by_contra hle
    push Not at hle
    have h2 : w z = z := hw.injective (hid (w z) hle)
    rw [h2] at hle
    linarith
  -- the conjugate-reflection glue: a symmetric solution agreeing with `w` above
  obtain ⟨F, bF, hFqc, hagree, hsym, hbF⟩ := exists_reflectGlue hw hreal hupper
  have hF0 : F 0 = 0 := by
    rw [hagree 0 (le_of_eq Complex.zero_im.symm)]
    exact hid 0 (le_of_eq Complex.zero_im)
  have hF1 : F 1 = 1 := by
    rw [hagree 1 (le_of_eq Complex.one_im.symm)]
    exact hid 1 (le_of_eq Complex.one_im)
  intro γ hγ
  -- the glued coefficient obeys the invariance law globally
  have hlaw : ∀ᵐ z : ℂ, bF.μ (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
      = bF.μ z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 := by
    rw [hbF]
    exact symmExtension_invariant Γ hinv γ hγ
  obtain ⟨W, hWeq⟩ := exists_sl2_equivariant hFqc hF0 hF1 hsym γ hlaw
  -- a real Möbius map has at most one real pole
  have huniq : ∀ (V : Matrix.SpecialLinearGroup (Fin 2) ℝ) (s t : ℝ),
      moebiusDenom V (s : ℂ) = 0 → moebiusDenom V (t : ℂ) = 0 → s = t := by
    intro V s t hs ht
    have hs' : (V 1 0 : ℂ) * (s : ℂ) + (V 1 1 : ℂ) = 0 := hs
    have ht' : (V 1 0 : ℂ) * (t : ℂ) + (V 1 1 : ℂ) = 0 := ht
    have hfac : (V 1 0 : ℂ) * ((s : ℂ) - (t : ℂ)) = 0 := by linear_combination hs' - ht'
    rcases mul_eq_zero.mp hfac with h | h
    · exfalso
      have hc0 : V 1 0 = 0 := by exact_mod_cast h
      have h11 : (V 1 1 : ℂ) = 0 := by rw [h, zero_mul, zero_add] at hs'; exact hs'
      have h11' : V 1 1 = 0 := by exact_mod_cast h11
      have hdet : V 0 0 * V 1 1 - V 0 1 * V 1 0 = 1 := by
        have hD := Matrix.SpecialLinearGroup.det_coe V
        rwa [Matrix.det_fin_two] at hD
      rw [hc0, h11'] at hdet
      norm_num at hdet
    · have hst : (s : ℂ) = (t : ℂ) := sub_eq_zero.mp h
      exact_mod_cast hst
  -- each of the two matrices has at most one real pole
  have hpoles : ∀ V : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∃ q : ℝ,
      ∀ t : ℝ, moebiusDenom V (t : ℂ) = 0 → t = q := by
    intro V
    by_cases hex : ∃ t : ℝ, moebiusDenom V (t : ℂ) = 0
    · obtain ⟨q, hq⟩ := hex
      exact ⟨q, fun t ht => huniq V t q ht hq⟩
    · exact ⟨0, fun t ht => absurd ⟨t, ht⟩ hex⟩
  obtain ⟨qγ, hqγ⟩ := hpoles γ
  obtain ⟨qW, hqW⟩ := hpoles W
  set T : ℝ := |qγ| + |qW| + 1 with hT
  -- large real points avoid both poles
  have hgood : ∀ s : ℝ, T ≤ s →
      moebiusDenom γ (s : ℂ) ≠ 0 ∧ moebiusDenom W (s : ℂ) ≠ 0 := by
    intro s hs
    rw [hT] at hs
    have h1 : qγ ≤ |qγ| := le_abs_self qγ
    have h2 : qW ≤ |qW| := le_abs_self qW
    have h3 : (0 : ℝ) ≤ |qγ| := abs_nonneg qγ
    have h4 : (0 : ℝ) ≤ |qW| := abs_nonneg qW
    constructor
    · intro h
      have he := hqγ s h
      rw [he] at hs
      linarith
    · intro h
      have he := hqW s h
      rw [he] at hs
      linarith
  -- at large real points the equivariance identity reads `γ = W` on values
  have hpin : ∀ s : ℝ, T ≤ s → moebiusMap γ (s : ℂ) = moebiusMap W (s : ℂ) := by
    intro s hs
    obtain ⟨hdγ, _⟩ := hgood s hs
    have h1 := hWeq (s : ℂ) hdγ
    have hims : ((s : ℝ) : ℂ).im = 0 := Complex.ofReal_im s
    have h2 : F (s : ℂ) = (s : ℂ) := by
      rw [hagree _ (le_of_eq hims.symm)]
      exact hid _ (le_of_eq hims)
    have him2 : (moebiusMap γ (s : ℂ)).im = 0 := moebiusMap_im_eq_zero γ hims hdγ
    have h3 : F (moebiusMap γ (s : ℂ)) = moebiusMap γ (s : ℂ) := by
      rw [hagree _ (le_of_eq him2.symm)]
      exact hid _ (le_of_eq him2)
    rw [h3, h2] at h1
    exact h1
  -- three distinct such points pin the matrix up to sign, hence the map exactly
  have hne12 : ((T : ℝ) : ℂ) ≠ ((T + 1 : ℝ) : ℂ) := by
    rw [Ne, Complex.ofReal_inj]
    intro h
    linarith
  have hne13 : ((T : ℝ) : ℂ) ≠ ((T + 2 : ℝ) : ℂ) := by
    rw [Ne, Complex.ofReal_inj]
    intro h
    linarith
  have hne23 : ((T + 1 : ℝ) : ℂ) ≠ ((T + 2 : ℝ) : ℂ) := by
    rw [Ne, Complex.ofReal_inj]
    intro h
    linarith
  have hVden : ∀ ζ ∈ ({((T : ℝ) : ℂ), ((T + 1 : ℝ) : ℂ), ((T + 2 : ℝ) : ℂ)} : Set ℂ),
      moebiusDenom γ ζ ≠ 0 := by
    intro ζ hζ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hζ
    rcases hζ with rfl | rfl | rfl
    · exact (hgood T le_rfl).1
    · exact (hgood (T + 1) (by linarith)).1
    · exact (hgood (T + 2) (by linarith)).1
  have hWden : ∀ ζ ∈ ({((T : ℝ) : ℂ), ((T + 1 : ℝ) : ℂ), ((T + 2 : ℝ) : ℂ)} : Set ℂ),
      moebiusDenom W ζ ≠ 0 := by
    intro ζ hζ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hζ
    rcases hζ with rfl | rfl | rfl
    · exact (hgood T le_rfl).2
    · exact (hgood (T + 1) (by linarith)).2
    · exact (hgood (T + 2) (by linarith)).2
  have hpts : ∀ ζ ∈ ({((T : ℝ) : ℂ), ((T + 1 : ℝ) : ℂ), ((T + 2 : ℝ) : ℂ)} : Set ℂ),
      moebiusMap γ ζ = moebiusMap W ζ := by
    intro ζ hζ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hζ
    rcases hζ with rfl | rfl | rfl
    · exact hpin T le_rfl
    · exact hpin (T + 1) (by linarith)
    · exact hpin (T + 2) (by linarith)
  have hMW : ∀ ζ : ℂ, moebiusMap W ζ = moebiusMap γ ζ := by
    rcases moebius_ext_three hne12 hne13 hne23 hVden hWden hpts with h | h
    · intro ζ
      rw [Subtype.coe_injective h]
    · intro ζ
      exact (moebiusMap_neg_matrix h ζ).symm
  -- assemble: above the axis through the glue, below it directly
  intro z hden
  rcases le_or_gt z.im 0 with hz | hz
  swap
  · have h1 := hWeq z hden
    rw [hagree z hz.le, hagree (moebiusMap γ z) (moebiusMap_im_pos γ hz).le, hMW] at h1
    exact h1
  · have hγz : (moebiusMap γ z).im ≤ 0 := by
      rcases lt_or_eq_of_le hz with h | h
      · exact (moebiusMap_im_neg γ h).le
      · exact le_of_eq (moebiusMap_im_eq_zero γ h hden)
    rw [hid z hz, hid (moebiusMap γ z) hγz]

end RiemannDynamics

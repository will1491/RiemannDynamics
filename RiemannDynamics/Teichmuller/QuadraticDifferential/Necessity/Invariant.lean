/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Extremal

/-!
# Invariance of the candidate coefficient

The Beltrami coefficient of a marked candidate satisfies the Beltrami invariance law for
the marked group of the domain representative: the candidate intertwines each `W` in the
domain group with a Möbius map of the target group, both Möbius maps are holomorphic off
their real poles, and the almost-everywhere Wirtinger chain rule turns the intertwining
identity into the transformation law of the coefficient on the upper half plane. This is
the law that lets the coefficient pair `Γ`-invariantly with automorphic quadratic
differentials in the Hamilton–Krushkal argument.

* `beltrami_invariant_of_isMarkedCandidate` — the invariance law of the coefficient of a
  marked candidate under the domain group.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **Invariance of the candidate coefficient**: the Beltrami coefficient of a marked
candidate for the pair `(x, y)` satisfies the Beltrami invariance law for the marked
group of `y` almost everywhere on the upper half plane. -/
theorem beltrami_invariant_of_isMarkedCandidate {x y : TeichRep Γ₀} {F : ℂ → ℂ}
    {b : BeltramiCoeff} (hmc : IsMarkedCandidate x y F) (hqa : IsQCAnalytic F b) :
    ∀ W ∈ y.group, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      b.μ (moebiusMap W z) * (moebiusDenom W z) ^ 2
        = b.μ z * (starRingEnd ℂ (moebiusDenom W z)) ^ 2 := by
  intro W hW
  obtain ⟨W', hW'm, hconj⟩ := hmc.2.1 W hW
  have hFup : ∀ z : ℂ, 0 < z.im → 0 < (F z).im :=
    isMarkedCandidate_mapsTo_upper hqa.isQCGeometric_K hmc.1
  -- transport the a.e. Jacobian and Beltrami data through the Möbius map
  have haeMoeb : ∀ P : ℂ → Prop,
      (∀ᵐ w : ℂ, P w) → ∀ᵐ z : ℂ, moebiusDenom W z ≠ 0 → P (moebiusMap W z) := by
    intro P hP
    have hopen : IsOpen {w : ℂ | moebiusDenom W⁻¹ w ≠ 0} := by
      have hc : Continuous (moebiusDenom W⁻¹) := by
        unfold moebiusDenom
        fun_prop
      exact isOpen_compl_singleton.preimage hc
    rw [ae_iff] at hP ⊢
    have himg : volume (moebiusMap W⁻¹ ''
        (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom W⁻¹ w ≠ 0})) = 0 := by
      have hSmeas : MeasurableSet
          (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom W⁻¹ w ≠ 0}) :=
        (measurableSet_toMeasurable _ _).inter hopen.measurableSet
      have hSnull : volume
          (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom W⁻¹ w ≠ 0}) = 0 := by
        refine le_antisymm (le_trans (measure_mono Set.inter_subset_left) ?_) (zero_le _)
        rw [measure_toMeasurable]
        exact hP.le
      have hfd : ∀ w ∈ toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom W⁻¹ w ≠ 0},
          HasFDerivWithinAt (moebiusMap W⁻¹) (fderiv ℝ (moebiusMap W⁻¹) w)
            (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom W⁻¹ w ≠ 0}) w := by
        intro w hw
        have hder := hasDerivAt_moebiusMap W⁻¹ hw.2
        exact ((hder.complexToReal_fderiv).differentiableAt.hasFDerivAt).hasFDerivWithinAt
      have hinjOn : Set.InjOn (moebiusMap W⁻¹)
          (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom W⁻¹ w ≠ 0}) := by
        intro u hu v hv huv
        have hu1 : moebiusMap W (moebiusMap W⁻¹ u) = u := by
          rw [moebiusMap_mul W W⁻¹ u hu.2, mul_inv_cancel, moebiusMap_one]
        have hv1 : moebiusMap W (moebiusMap W⁻¹ v) = v := by
          rw [moebiusMap_mul W W⁻¹ v hv.2, mul_inv_cancel, moebiusMap_one]
        rw [← hu1, ← hv1, huv]
      have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hfd hinjOn
        (fun _ => (1 : ℝ≥0∞))
      rw [setLIntegral_one, setLIntegral_measure_zero _ _ hSnull] at hcov
      exact hcov
    refine measure_mono_null ?_ himg
    intro z hz
    simp only [Set.mem_setOf_eq, Classical.not_imp] at hz
    obtain ⟨hden, hbad⟩ := hz
    have hd1 : moebiusDenom W⁻¹ (moebiusMap W z) * moebiusDenom W z = 1 := by
      rw [moebiusDenom_mul W⁻¹ W z hden, inv_mul_cancel, moebiusDenom_one]
    have hdinv : moebiusDenom W⁻¹ (moebiusMap W z) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hd1
      exact zero_ne_one hd1
    refine ⟨moebiusMap W z, ⟨subset_toMeasurable _ _ hbad, hdinv⟩, ?_⟩
    rw [moebiusMap_mul W⁻¹ W z hden, inv_mul_cancel, moebiusMap_one]
  have hgood : ∀ᵐ w : ℂ, 0 < (fderiv ℝ F w).det ∧ dzbar F w = b.μ w * dz F w :=
    hqa.1.2.and hqa.2.2
  have hgoodT :=
    haeMoeb (fun w => 0 < (fderiv ℝ F w).det ∧ dzbar F w = b.μ w * dz F w) hgood
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  rw [ae_restrict_iff' hU]
  filter_upwards [hgood, hgoodT] with z hgz hgTz hzmem
  have hzup : 0 < z.im := hzmem
  have hz : moebiusDenom W z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero W hzup.ne'
  obtain ⟨hdet_z, hbel_z⟩ := hgz
  obtain ⟨hdet_p, hbel_p⟩ := hgTz hz
  have hWd : moebiusDenom W' (F z) ≠ 0 :=
    moebiusDenom_ne_zero_of_im_ne_zero W' (hFup z hzup).ne'
  have hDz : DifferentiableAt ℝ F z := by
    by_contra hnd
    rw [fderiv_zero_of_not_differentiableAt hnd] at hdet_z
    simp [ContinuousLinearMap.det] at hdet_z
  have hDp : DifferentiableAt ℝ F (moebiusMap W z) := by
    by_contra hnd
    rw [fderiv_zero_of_not_differentiableAt hnd] at hdet_p
    simp [ContinuousLinearMap.det] at hdet_p
  have hγd := hasDerivAt_moebiusMap W hz
  have hWdd := hasDerivAt_moebiusMap W' hWd
  have hopenU : IsOpen {w : ℂ | 0 < w.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hev : (fun w => F (moebiusMap W w)) =ᶠ[nhds z] fun w => moebiusMap W' (F w) := by
    filter_upwards [hopenU.mem_nhds hzup] with w hw
    exact hconj w hw
  have hfd : fderiv ℝ (fun w => F (moebiusMap W w)) z
      = fderiv ℝ (fun w => moebiusMap W' (F w)) z := hev.fderiv_eq
  have hdzEq : dz (fun w => F (moebiusMap W w)) z
      = dz (fun w => moebiusMap W' (F w)) z := by
    unfold dz
    rw [hfd]
  have hdzbEq : dzbar (fun w => F (moebiusMap W w)) z
      = dzbar (fun w => moebiusMap W' (F w)) z := by
    unfold dzbar
    rw [hfd]
  have hLdz : dz (fun w => F (moebiusMap W w)) z
      = dz F (moebiusMap W z) * ((moebiusDenom W z) ^ 2)⁻¹ := by
    have hcr := dz_comp_of_holomorphicAt hγd.differentiableAt hDp
    rw [hγd.deriv] at hcr
    simpa [Function.comp_def] using hcr
  have hLdzb : dzbar (fun w => F (moebiusMap W w)) z
      = dzbar F (moebiusMap W z) * starRingEnd ℂ (((moebiusDenom W z) ^ 2)⁻¹) := by
    have hcr := dzbar_comp_of_holomorphicAt hγd.differentiableAt hDp
    rw [hγd.deriv] at hcr
    simpa [Function.comp_def] using hcr
  have hWreal : DifferentiableAt ℝ (moebiusMap W') (F z) :=
    (differentiableAt_complex_iff_differentiableAt_real.mp hWdd.differentiableAt).1
  have hdzW : dz (moebiusMap W') (F z) = ((moebiusDenom W' (F z)) ^ 2)⁻¹ := by
    rw [dz_eq_deriv_of_differentiableAt hWdd.differentiableAt, hWdd.deriv]
  have hdzbW : dzbar (moebiusMap W') (F z) = 0 :=
    dzbar_eq_zero_of_differentiableAt hWdd.differentiableAt
  have hRdz : dz (fun w => moebiusMap W' (F w)) z
      = ((moebiusDenom W' (F z)) ^ 2)⁻¹ * dz F z := by
    have hcr := dz_comp hDz hWreal
    rw [hdzW, hdzbW, zero_mul, add_zero] at hcr
    exact hcr
  have hRdzb : dzbar (fun w => moebiusMap W' (F w)) z
      = ((moebiusDenom W' (F z)) ^ 2)⁻¹ * dzbar F z := by
    have hcr := dzbar_comp hDz hWreal
    rw [hdzW, hdzbW, zero_mul, add_zero] at hcr
    exact hcr
  have hEq1 : dz F (moebiusMap W z) * ((moebiusDenom W z) ^ 2)⁻¹
      = ((moebiusDenom W' (F z)) ^ 2)⁻¹ * dz F z := by
    rw [← hLdz, ← hRdz]
    exact hdzEq
  have hEq2 : dzbar F (moebiusMap W z) * starRingEnd ℂ (((moebiusDenom W z) ^ 2)⁻¹)
      = ((moebiusDenom W' (F z)) ^ 2)⁻¹ * dzbar F z := by
    rw [← hLdzb, ← hRdzb]
    exact hdzbEq
  rw [hbel_p, hbel_z, map_inv₀, map_pow] at hEq2
  have hdzne : dz F z ≠ 0 := by
    intro h0
    rw [det_fderiv_eq_wirtinger, h0] at hdet_z
    simp only [norm_zero] at hdet_z
    nlinarith [norm_nonneg (dzbar F z), sq_nonneg ‖dzbar F z‖]
  have hD2 : (moebiusDenom W z) ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have hE2 : (moebiusDenom W' (F z)) ^ 2 ≠ 0 := pow_ne_zero 2 hWd
  have hcD : starRingEnd ℂ (moebiusDenom W z) ≠ 0 := by simpa using hz
  have hcD2 : (starRingEnd ℂ (moebiusDenom W z)) ^ 2 ≠ 0 := pow_ne_zero 2 hcD
  field_simp [hD2, hE2, hcD2] at hEq1 hEq2
  have hgoal2 : b.μ (moebiusMap W z) * (moebiusDenom W z) ^ 2 * dz F z
      = b.μ z * (starRingEnd ℂ (moebiusDenom W z)) ^ 2 * dz F z := by
    linear_combination hEq2 - b.μ (moebiusMap W z) * hEq1
  exact mul_right_cancel₀ hdzne hgoal2

end RiemannDynamics

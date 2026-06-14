/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Sobolev.Wirtinger
import RiemannDynamics.Analysis.SingularIntegral.Cauchy
import RiemannDynamics.Analysis.SingularIntegral.CalderonZygmund
import Carleson.TwoSidedCarleson.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The Beurling transform

The **Beurling transform** of `μ : ℂ → ℂ` is the principal-value singular
integral

`Tμ(z) = -(1/π) p.v.∫ μ(ζ)/(z - ζ)² dA(ζ)`,

realized here as the `r → 0⁺` limit of the truncated singular integral
`czOperator` (the Carleson-project Calderón–Zygmund operator) with the Beurling
kernel `K(z, ζ) = (z - ζ)⁻²`. It is the holomorphic Wirtinger derivative of the
Cauchy transform, `T = ∂ ∘ P` (`beurling_eq_dz_cauchyTransform`), so it carries
`∂̄f` to `∂f` and inverts the Beltrami equation.

Its analytic content is the engine input to the measurable Riemann mapping
theorem:

* `beurling_l2_isometry` — `T` is an `L²` isometry (Fourier multiplier `ξ̄/ξ`,
  modulus one), so `‖T‖₂ = 1`;
* `beurling_lp_bound` — `T` is bounded `Lᵖ(ℂ) → Lᵖ(ℂ)` for `1 < p < ∞`
  (Calderón–Zygmund: the Beurling kernel satisfies the kernel hypotheses, giving
  weak-(1,1) via `czOperator_weak_1_1`, then `Lᵖ` by real interpolation against
  the `L²` isometry);
* `beurling_opNorm_continuous` — the `Lᵖ` constant tends to `1` as `p → 2`, the
  qualitative input the MRMT Neumann series consumes.
-/

open MeasureTheory Complex Filter Topology
open scoped Real ENNReal

namespace RiemannDynamics

variable {μ : ℂ → ℂ} {z : ℂ} {p : ℝ≥0∞}

/-- The **Beurling transform** `Tμ(z) = -(1/π) p.v.∫ μ(ζ)/(z - ζ)² dA(ζ)`, the
principal value taken as the `r → 0⁺` limit of the truncated Calderón–Zygmund
operator with the Beurling kernel `K(z, ζ) = (z - ζ)⁻²`. -/
noncomputable def beurling (μ : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(1 / (π : ℂ)) * limUnder (𝓝[>] (0 : ℝ))
    (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r μ z)

/-- **`T = ∂ ∘ P`.** The Beurling transform is the holomorphic Wirtinger
derivative of the Cauchy transform. -/
theorem beurling_eq_dz_cauchyTransform (hμ : ContDiff ℝ 1 μ) (hμc : HasCompactSupport μ)
    (z : ℂ) : dz (cauchyTransform μ) z = beurling μ z := by
  -- Part A: `∂(Pμ) = P(∂μ)`, the `dz` analog of `dzbar_cauchyTransform_eq`.
  have hA : dz (cauchyTransform μ) z = cauchyTransform (fun ζ => dz μ ζ) z := by
    set L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ with hL
    set k : ℂ → ℂ := fun u => -u⁻¹ with hk
    have hk_loc : LocallyIntegrable k volume := by
      rw [hk]
      apply LocallyIntegrable.neg
      rw [MeasureTheory.locallyIntegrable_iff]
      intro K hK
      obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
      apply MeasureTheory.IntegrableOn.mono_set _ hR
      rw [IntegrableOn]
      refine ⟨measurable_inv.aestronglyMeasurable.restrict, ?_⟩
      rw [hasFiniteIntegral_iff_enorm, ← lintegral_indicator measurableSet_closedBall,
        ← Complex.lintegral_comp_polarCoord_symm]
      set lhs : ℝ × ℝ → ENNReal := fun p =>
        ENNReal.ofReal p.1 •
          (Metric.closedBall (0 : ℂ) R).indicator (fun u : ℂ => ‖u⁻¹‖ₑ) (Complex.polarCoord.symm p)
        with hlhs
      set box : ℝ × ℝ → ENNReal :=
        (Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-π) π).indicator (fun _ => (1 : ENNReal)) with hbox
      have hbound : ∀ p ∈ polarCoord.target, lhs p ≤ box p := by
        intro p hp
        simp only [hlhs, hbox]
        rw [polarCoord_target, Set.mem_prod] at hp
        obtain ⟨hp1, hp2⟩ := hp
        simp only [Set.mem_Ioi] at hp1
        by_cases hmem : Complex.polarCoord.symm p ∈ Metric.closedBall (0 : ℂ) R
        · rw [Set.indicator_of_mem hmem]
          have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
            rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
          have hsymm_ne : Complex.polarCoord.symm p ≠ 0 := by
            rw [← norm_ne_zero_iff, hnorm]; exact ne_of_gt hp1
          rw [enorm_inv hsymm_ne]
          have henorm : ‖Complex.polarCoord.symm p‖ₑ = ENNReal.ofReal p.1 := by
            rw [← ofReal_norm_eq_enorm, hnorm]
          rw [henorm, smul_eq_mul,
            ENNReal.mul_inv_cancel (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp1)
              ENNReal.ofReal_lt_top.ne]
          have hpR : p.1 ≤ R := by
            rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hmem
            exact hmem
          have hmem2 : p ∈ Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-π) π :=
            Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨hp1, hpR⟩, hp2⟩
          rw [Set.indicator_of_mem hmem2]
        · rw [Set.indicator_of_notMem hmem]
          simp
      have hmeas : Measurable box :=
        measurable_const.indicator (measurableSet_Ioc.prod measurableSet_Ioo)
      have hbox_meas : MeasurableSet (Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-π) π) :=
        measurableSet_Ioc.prod measurableSet_Ioo
      calc
        ∫⁻ p in polarCoord.target, lhs p
            ≤ ∫⁻ p in polarCoord.target, box p := setLIntegral_mono hmeas hbound
        _ ≤ ∫⁻ p, box p := setLIntegral_le_lintegral _ _
        _ = volume (Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-π) π) := by
              rw [hbox, lintegral_indicator hbox_meas]; simp
        _ < ⊤ := by
              have hvol : (volume : Measure (ℝ × ℝ)) = volume.prod volume :=
                Measure.volume_eq_prod ℝ ℝ
              rw [hvol, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioo]
              exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    have hCT : cauchyTransform μ
        = fun w => (-(1 / (π : ℂ))) • (MeasureTheory.convolution μ k L volume) w := by
      funext w
      rw [cauchyTransform, MeasureTheory.convolution_def, smul_eq_mul]
      congr 1
      apply integral_congr_ae (ae_of_all _ fun ζ => ?_)
      rw [hL, ContinuousLinearMap.mul_apply']
      change μ ζ / (ζ - w) = μ ζ * -(w - ζ)⁻¹
      have hflip : -(w - ζ)⁻¹ = (ζ - w)⁻¹ := by rw [← neg_sub ζ w, inv_neg, neg_neg]
      rw [hflip, div_eq_mul_inv]
    have hfd0 : HasFDerivAt (MeasureTheory.convolution μ k L volume)
        (MeasureTheory.convolution (fderiv ℝ μ) k (ContinuousLinearMap.precompL ℂ L) volume z) z :=
      hμc.hasFDerivAt_convolution_left L hμ hk_loc z
    set D₀ := MeasureTheory.convolution (fderiv ℝ μ) k (ContinuousLinearMap.precompL ℂ L) volume z
      with hD₀
    have hfderiv : fderiv ℝ (cauchyTransform μ) z = (-(1 / (π : ℂ))) • D₀ := by
      have hfd : HasFDerivAt (cauchyTransform μ) ((-(1 / (π : ℂ))) • D₀) z := by
        rw [hCT]; exact hfd0.const_smul (-(1 / (π : ℂ)))
      exact hfd.fderiv
    have hex : ConvolutionExistsAt (fderiv ℝ μ) k z (ContinuousLinearMap.precompL ℂ L) volume :=
      ((hμc.fderiv ℝ).convolutionExists_left (ContinuousLinearMap.precompL ℂ L)
        (hμ.continuous_fderiv one_ne_zero) hk_loc) z
    have hex_int : Integrable
        (fun t => (ContinuousLinearMap.precompL ℂ L) (fderiv ℝ μ t) (k (z - t))) volume :=
      hex
    set A : ℂ → ℂ := fun t => (fderiv ℝ μ t) 1 * k (z - t) with hA_def
    set B : ℂ → ℂ := fun t => (fderiv ℝ μ t) Complex.I * k (z - t) with hB_def
    have hA_int : Integrable A volume := by
      have h := hex_int.apply_continuousLinearMap (1 : ℂ)
      apply h.congr; apply ae_of_all _ fun t => ?_
      change (ContinuousLinearMap.precompL ℂ L) (fderiv ℝ μ t) (k (z - t)) 1 = A t
      rw [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.mul_apply']
    have hB_int : Integrable B volume := by
      have h := hex_int.apply_continuousLinearMap Complex.I
      apply h.congr; apply ae_of_all _ fun t => ?_
      change (ContinuousLinearMap.precompL ℂ L) (fderiv ℝ μ t) (k (z - t)) Complex.I = B t
      rw [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.mul_apply']
    have hD₀_eval : ∀ v : ℂ, D₀ v = ∫ t, ((fderiv ℝ μ t) v) * (k (z - t)) ∂volume := by
      intro v
      rw [hD₀, MeasureTheory.convolution_def, ContinuousLinearMap.integral_apply hex_int]
      apply integral_congr_ae (ae_of_all _ fun t => ?_)
      rw [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.mul_apply']
    have hD₀1 : D₀ 1 = ∫ t, A t := hD₀_eval 1
    have hD₀I : D₀ Complex.I = ∫ t, B t := hD₀_eval Complex.I
    have hRHS : cauchyTransform (fun ζ => dz μ ζ) z
        = (-(1 / (π : ℂ))) * ((1 / 2) * ((∫ t, A t) - Complex.I * (∫ t, B t))) := by
      rw [cauchyTransform]
      congr 1
      have hker : ∀ t : ℂ, (dz μ t) / (t - z) = (1 / 2 : ℂ) * (A t - Complex.I * B t) := by
        intro t
        rw [dz]
        have hk_eq : (t - z)⁻¹ = k (z - t) := by
          rw [hk]; change (t - z)⁻¹ = -(z - t)⁻¹
          rw [← neg_sub t z, inv_neg, neg_neg]
        rw [div_eq_mul_inv, hk_eq, hA_def, hB_def]; ring
      rw [integral_congr_ae (ae_of_all _ hker)]
      have h1 : ∫ (a : ℂ), (1 : ℂ) / 2 * (A a - Complex.I * B a)
          = (1 : ℂ) / 2 * ∫ a, (A a - Complex.I * B a) :=
        MeasureTheory.integral_const_mul ((1 : ℂ) / 2) _
      rw [h1]; congr 1
      have h2 : ∫ a, (A a - Complex.I * B a) = (∫ a, A a) - ∫ a, Complex.I * B a :=
        integral_sub hA_int (hB_int.const_mul Complex.I)
      rw [h2]; congr 1
      exact MeasureTheory.integral_const_mul Complex.I B
    rw [hRHS, dz, hfderiv]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [hD₀1, hD₀I]
    ring
  rw [hA]
  -- Part B: `P(∂μ) = beurling μ`.
  classical
  -- Basic data about `μ` and the unit-circle parametrization `e`.
  set e : ℝ → ℂ := fun t => (Real.cos t : ℂ) + (Real.sin t : ℂ) * I with he_def
  have hgdiff : ∀ ζ : ℂ, DifferentiableAt ℝ μ ζ := fun ζ => hμ.differentiable one_ne_zero ζ
  have he_cont : Continuous e := by rw [he_def]; fun_prop
  have he_mul_conj : ∀ θ : ℝ, e θ * (starRingEnd ℂ) (e θ) = 1 := by
    intro θ
    simp only [he_def, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring_nf
    rw [Complex.I_sq]
    ring_nf
    have h1 : (Real.cos θ) ^ 2 + (Real.sin θ) ^ 2 = 1 := by
      rw [add_comm]; exact Real.sin_sq_add_cos_sq θ
    have h2 : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by exact_mod_cast h1
    linear_combination h2
  have he_ne : ∀ θ : ℝ, e θ ≠ 0 := by
    intro θ h; have := he_mul_conj θ; rw [h] at this; simp at this
  have he_inv : ∀ θ : ℝ, (e θ)⁻¹ = (starRingEnd ℂ) (e θ) := fun θ =>
    inv_eq_of_mul_eq_one_right (he_mul_conj θ)
  have he_norm : ∀ θ : ℝ, ‖e θ‖ = 1 := by
    intro θ
    have h := he_mul_conj θ
    have : ‖e θ * (starRingEnd ℂ) (e θ)‖ = ‖e θ‖ ^ 2 := by
      rw [norm_mul, Complex.norm_conj]; ring
    rw [h, norm_one] at this
    nlinarith [norm_nonneg (e θ), this]
  have he_deriv : ∀ θ : ℝ, HasDerivAt e (I * e θ) θ := by
    intro θ
    have hcos : HasDerivAt (fun s : ℝ => (Real.cos s : ℂ)) ((-Real.sin θ : ℝ) : ℂ) θ :=
      (Real.hasDerivAt_cos θ).ofReal_comp
    have hsin : HasDerivAt (fun s : ℝ => (Real.sin s : ℂ)) ((Real.cos θ : ℝ) : ℂ) θ :=
      (Real.hasDerivAt_sin θ).ofReal_comp
    have hd : HasDerivAt (fun s : ℝ => (Real.cos s : ℂ) + (Real.sin s : ℂ) * I)
        ((((-Real.sin θ : ℝ)) : ℂ) + (((Real.cos θ : ℝ)) : ℂ) * I) θ :=
      hcos.add (hsin.mul_const I)
    have hev : (((-Real.sin θ : ℝ)) : ℂ) + (((Real.cos θ : ℝ)) : ℂ) * I = I * e θ := by
      rw [he_def, Complex.ofReal_neg]
      linear_combination (-(Real.sin θ : ℂ)) * Complex.I_mul_I
    rw [he_def, ← hev]; exact hd
  have he_diff : ∀ t : ℝ, DifferentiableAt ℝ e t := by
    intro t; rw [he_def]
    apply DifferentiableAt.add
    · exact Complex.ofRealCLM.differentiableAt.comp t Real.differentiable_cos.differentiableAt
    · exact (Complex.ofRealCLM.differentiableAt.comp t
        Real.differentiable_sin.differentiableAt).mul_const _
  -- Continuity and compact support of `dz μ`.
  have hdzμ_cont : Continuous (fun ζ => dz μ ζ) := by unfold dz; fun_prop
  have hdzμ_cs : HasCompactSupport (fun ζ => dz μ ζ) := by
    have hfderiv_cs : HasCompactSupport (fun ζ => fderiv ℝ μ ζ) := hμc.fderiv (𝕜 := ℝ)
    have hcomp : (fun ζ => dz μ ζ)
        = (fun D : ℂ →L[ℝ] ℂ => (1/2 : ℂ) * (D 1 - I * D I)) ∘ (fun ζ => fderiv ℝ μ ζ) := by
      funext ζ; rfl
    rw [hcomp]; exact hfderiv_cs.comp_left (by simp)
  -- Local integrability of the kernel `ζ ↦ (z - ζ)⁻¹`.
  have hloc0 : LocallyIntegrable (fun u : ℂ => u⁻¹) volume := by
    rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    apply MeasureTheory.IntegrableOn.mono_set _ hR
    rw [IntegrableOn]
    refine ⟨measurable_inv.aestronglyMeasurable.restrict, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, ← lintegral_indicator measurableSet_closedBall,
      ← Complex.lintegral_comp_polarCoord_symm]
    set lhs : ℝ × ℝ → ENNReal := fun p =>
      ENNReal.ofReal p.1 •
        (Metric.closedBall (0 : ℂ) R).indicator (fun u : ℂ => ‖u⁻¹‖ₑ) (Complex.polarCoord.symm p)
      with hlhs
    set box : ℝ × ℝ → ENNReal :=
      (Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-π) π).indicator (fun _ => (1 : ENNReal)) with hbox
    have hbound : ∀ p ∈ polarCoord.target, lhs p ≤ box p := by
      intro p hp
      simp only [hlhs, hbox]
      rw [polarCoord_target, Set.mem_prod] at hp
      obtain ⟨hp1, hp2⟩ := hp
      simp only [Set.mem_Ioi] at hp1
      by_cases hmem : Complex.polarCoord.symm p ∈ Metric.closedBall (0 : ℂ) R
      · rw [Set.indicator_of_mem hmem]
        have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
        have hsymm_ne : Complex.polarCoord.symm p ≠ 0 := by
          rw [← norm_ne_zero_iff, hnorm]; exact ne_of_gt hp1
        rw [enorm_inv hsymm_ne]
        have henorm : ‖Complex.polarCoord.symm p‖ₑ = ENNReal.ofReal p.1 := by
          rw [← ofReal_norm_eq_enorm, hnorm]
        rw [henorm, smul_eq_mul,
          ENNReal.mul_inv_cancel (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp1)
            ENNReal.ofReal_lt_top.ne]
        have hpR : p.1 ≤ R := by
          rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hmem; exact hmem
        rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨hp1, hpR⟩, hp2⟩)]
      · rw [Set.indicator_of_notMem hmem]; simp
    calc
      ∫⁻ p in polarCoord.target, lhs p
          ≤ ∫⁻ p in polarCoord.target, box p :=
            setLIntegral_mono (measurable_const.indicator
              (measurableSet_Ioc.prod measurableSet_Ioo)) hbound
      _ ≤ ∫⁻ p, box p := setLIntegral_le_lintegral _ _
      _ = volume (Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-π) π) := by
            rw [hbox, lintegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]; simp
      _ < ⊤ := by
            rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioo]
            exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hloc : LocallyIntegrable (fun ζ : ℂ => (z - ζ)⁻¹) volume := by
    set hh : ℂ ≃ₜ ℂ := (Homeomorph.neg ℂ).trans (Homeomorph.addLeft z) with hh_def
    have hmap : Measure.map hh (volume : Measure ℂ) = volume := by
      have hmp : MeasurePreserving (fun ζ : ℂ => z - ζ) volume volume := by
        have h1 : MeasurePreserving (fun ζ : ℂ => z + ζ) volume volume :=
          measurePreserving_add_left volume z
        have h2 : MeasurePreserving (fun ζ : ℂ => -ζ) volume volume :=
          Measure.measurePreserving_neg volume
        have := h1.comp h2
        simpa [Function.comp, sub_eq_add_neg] using this
      have hh_eq : (hh : ℂ → ℂ) = fun ζ : ℂ => z - ζ := by
        funext ζ; simp [hh_def, Homeomorph.trans, Homeomorph.neg, Homeomorph.addLeft,
          sub_eq_add_neg]
      rw [show (Measure.map hh (volume : Measure ℂ))
          = Measure.map (fun ζ : ℂ => z - ζ) volume by rw [hh_eq]]
      exact hmp.map_eq
    have hiff := locallyIntegrable_map_homeomorph hh (f := fun u : ℂ => u⁻¹) (μ := volume)
    rw [hmap] at hiff
    have hcomp : (fun u : ℂ => u⁻¹) ∘ hh = fun ζ : ℂ => (z - ζ)⁻¹ := by
      funext ζ; simp [hh_def, Homeomorph.trans, Homeomorph.neg, Homeomorph.addLeft,
        sub_eq_add_neg]
    rw [hcomp] at hiff
    exact hiff.mp hloc0
  -- Integrability of the kernel integrand `g`.
  have hg_int : Integrable (fun ζ => (dz μ ζ) * (z - ζ)⁻¹) volume := by
    have := hloc.integrable_smul_left_of_hasCompactSupport hdzμ_cont hdzμ_cs
    simpa [smul_eq_mul] using this
  -- A radius `R` enclosing the support of `μ`, off which `μ` and `dz μ` vanish.
  obtain ⟨R, hR⟩ : ∃ R : ℝ, tsupport μ ⊆ Metric.closedBall z R :=
    (hμc.isCompact.isBounded).subset_closedBall z
  have hμ_van : ∀ ζ : ℂ, R < ‖ζ - z‖ → μ ζ = 0 := by
    intro ζ hζ
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hR hmem
    rw [Metric.mem_closedBall, dist_eq] at this
    linarith
  -- Reduce to the `Tendsto` statement.
  rw [cauchyTransform, beurling]
  congr 1
  refine (Filter.Tendsto.limUnder_eq ?_).symm
  -- The kernel-integral limit (Step B.1).
  have hB1 : Tendsto (fun r : ℝ => ∫ y in (Metric.ball z r)ᶜ, (dz μ y) * (z - y)⁻¹)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ ζ, (dz μ ζ) * (z - ζ)⁻¹)) := by
    have hballvol : Tendsto (fun r : ℝ => (volume ∘ (fun r => Metric.ball z r)) r)
        (𝓝[>] 0) (𝓝 0) := by
      simp only [Function.comp]
      have heqv : (fun r : ℝ => volume (Metric.ball z r))
          = fun r : ℝ => ENNReal.ofReal r ^ 2 * ↑NNReal.pi := by
        funext r; rw [Complex.volume_ball]
      rw [heqv, show (0 : ENNReal) = ENNReal.ofReal 0 ^ 2 * ↑NNReal.pi by simp]
      have htof : Tendsto (fun r : ℝ => ENNReal.ofReal r) (𝓝[>] 0) (𝓝 (ENNReal.ofReal 0)) :=
        (ENNReal.continuous_ofReal.tendsto 0).comp nhdsWithin_le_nhds
      exact ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow htof) (Or.inr (by simp))
    have hzero : Tendsto (fun r : ℝ => ∫ y in Metric.ball z r, (dz μ y) * (z - y)⁻¹)
        (𝓝[>] 0) (𝓝 0) := hg_int.tendsto_setIntegral_nhds_zero hballvol
    have heq : ∀ r : ℝ, (∫ y in (Metric.ball z r)ᶜ, (dz μ y) * (z - y)⁻¹)
        = (∫ ζ, (dz μ ζ) * (z - ζ)⁻¹) - ∫ y in Metric.ball z r, (dz μ y) * (z - y)⁻¹ := by
      intro r; rw [setIntegral_compl measurableSet_ball hg_int]
    rw [funext heq]
    simpa using tendsto_const_nhds.sub hzero
  -- The angular integral of `conj(e θ)^2` over a full turn vanishes.
  have hconjint : (∫ θ in Set.Ioo (-π : ℝ) π, ((starRingEnd ℂ) (e θ))^2) = 0 := by
    have hper : ∀ s : ℝ, HasDerivAt (fun t : ℝ => (I/2) * ((starRingEnd ℂ) (e t))^2)
        (((starRingEnd ℂ) (e s))^2) s := by
      intro s
      have hconj_d : HasDerivAt (fun t : ℝ => (starRingEnd ℂ) (e t))
          (-I * (starRingEnd ℂ) (e s)) s := by
        have hconj_eq : (fun t : ℝ => (starRingEnd ℂ) (e t))
            = fun t : ℝ => (Real.cos t : ℂ) - (Real.sin t : ℂ) * I := by
          funext t; rw [he_def]
          simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
        rw [hconj_eq]
        have hcos : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ)) ((-Real.sin s : ℝ) : ℂ) s :=
          (Real.hasDerivAt_cos s).ofReal_comp
        have hsin : HasDerivAt (fun t : ℝ => (Real.sin t : ℂ)) ((Real.cos s : ℝ) : ℂ) s :=
          (Real.hasDerivAt_sin s).ofReal_comp
        have hd := hcos.sub (hsin.mul_const I)
        convert hd using 1
        rw [he_def]
        simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
        linear_combination (Real.sin s : ℂ) * Complex.I_mul_I
      have h2 := (hconj_d.pow 2).const_mul (I/2)
      convert h2 using 1
      have hps : (2:ℕ) - 1 = 1 := rfl
      rw [hps, pow_one]
      have hI2 : (I:ℂ)^2 = -1 := by rw [pow_two]; exact Complex.I_mul_I
      field_simp
      rw [hI2]; ring
    have hπle : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hπle]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hper θ)]
    · have hπ : e π = (-1 : ℂ) := by rw [he_def]; simp [Real.cos_pi, Real.sin_pi]
      have hmπ : e (-π) = (-1 : ℂ) := by rw [he_def]; simp [Real.cos_pi, Real.sin_pi]
      rw [hπ, hmπ]; simp
    · apply Continuous.intervalIntegrable
      rw [he_def]; fun_prop
  -- The boundary-term limit (Step B.2 endpoint).
  have hB2 : Tendsto (fun r : ℝ => (1/2 : ℂ) * ∫ θ in Set.Ioo (-π) π,
        ((starRingEnd ℂ) (e θ))^2 * μ (z + (r : ℂ) * e θ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    obtain ⟨M, hM⟩ : ∃ M, ∀ ζ, ‖μ ζ‖ ≤ M := hμc.exists_bound_of_continuous hμ.continuous
    set F : ℝ → ℝ → ℂ := fun r θ => ((starRingEnd ℂ) (e θ))^2 * μ (z + (r : ℂ) * e θ) with hF
    have hFcont : ∀ r : ℝ, Continuous (fun θ : ℝ => F r θ) := by
      intro r
      rw [hF]
      have h1 : Continuous (fun θ : ℝ => ((starRingEnd ℂ) (e θ))^2) :=
        ((Complex.continuous_conj.comp he_cont)).pow 2
      have h2 : Continuous (fun θ : ℝ => μ (z + (r : ℂ) * e θ)) :=
        hμ.continuous.comp (continuous_const.add (continuous_const.mul he_cont))
      exact h1.mul h2
    have hcontAt : ContinuousAt (fun r : ℝ => ∫ θ in Set.Ioo (-π) π, F r θ) 0 := by
      apply continuousAt_of_dominated (bound := fun _ => M)
      · filter_upwards with r
        exact (hFcont r).aestronglyMeasurable
      · filter_upwards with r
        filter_upwards with θ
        rw [hF, norm_mul]
        have hc : ‖((starRingEnd ℂ) (e θ))^2‖ = 1 := by
          rw [norm_pow, Complex.norm_conj, he_norm]; ring
        rw [hc, one_mul]; exact hM _
      · exact integrableOn_const measure_Ioo_lt_top.ne (by finiteness)
      · filter_upwards with θ
        apply Continuous.continuousAt
        rw [hF]
        exact continuous_const.mul (hμ.continuous.comp
          (continuous_const.add ((Complex.continuous_ofReal).mul continuous_const)))
    have hAt0 : (∫ θ in Set.Ioo (-π) π, F 0 θ) = 0 := by
      have hsimp : (fun θ : ℝ => F 0 θ) = fun θ => ((starRingEnd ℂ) (e θ))^2 * μ z := by
        funext θ; rw [hF]; simp
      rw [hsimp]
      rw [show (∫ θ in Set.Ioo (-π : ℝ) π, ((starRingEnd ℂ) (e θ))^2 * μ z)
          = (∫ θ in Set.Ioo (-π : ℝ) π, ((starRingEnd ℂ) (e θ))^2) * μ z from
        integral_mul_const (μ z) (fun θ => ((starRingEnd ℂ) (e θ))^2)]
      rw [hconjint, zero_mul]
    have htend : Tendsto (fun r : ℝ => ∫ θ in Set.Ioo (-π) π, F r θ) (𝓝[>] 0)
        (𝓝 (∫ θ in Set.Ioo (-π) π, F 0 θ)) :=
      (hcontAt.tendsto).comp nhdsWithin_le_nhds
    rw [hAt0] at htend
    have hfin : Tendsto (fun r : ℝ => (1/2 : ℂ) * ∫ θ in Set.Ioo (-π) π, F r θ) (𝓝[>] 0)
        (𝓝 ((1/2 : ℂ) * 0)) := htend.const_mul _
    simpa using hfin
  -- Prerequisites for the polar identity.
  obtain ⟨Mμ, hMμ⟩ : ∃ M, ∀ ζ, ‖μ ζ‖ ≤ M := hμc.exists_bound_of_continuous hμ.continuous
  have hfderiv_cont : Continuous (fun ζ => fderiv ℝ μ ζ) := hμ.continuous_fderiv one_ne_zero
  have hfderiv_van : ∀ ζ : ℂ, R < ‖ζ - z‖ → fderiv ℝ μ ζ = 0 := by
    intro ζ hζ
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := (tsupport_fderiv_subset ℝ (f := μ)) hmem
    have h2 := hR h1
    rw [Metric.mem_closedBall, dist_eq] at h2
    linarith
  obtain ⟨Mf, hMf⟩ : ∃ M, ∀ ζ : ℂ, ‖fderiv ℝ μ ζ‖ ≤ M :=
    (hμc.fderiv ℝ).exists_bound_of_continuous hfderiv_cont
  -- The polar change-of-variables on the exterior of a disc.
  have hpolar : ∀ (r' : ℝ), 0 < r' → ∀ (φ : ℂ → ℂ),
      (∫ ζ in (Metric.ball z r')ᶜ, φ ζ)
        = ∫ p in (Set.Ioi r' ×ˢ Set.Ioo (-π) π), p.1 • φ (z + Complex.polarCoord.symm p) := by
    intro r' hr' φ
    have hshift : (∫ ζ in (Metric.ball z r')ᶜ, φ ζ)
        = ∫ ξ in (Metric.ball (0:ℂ) r')ᶜ, φ (z + ξ) := by
      have hmp : MeasurePreserving (fun ξ : ℂ => z + ξ) volume volume :=
        measurePreserving_add_left volume z
      have hemb : MeasurableEmbedding (fun ξ : ℂ => z + ξ) :=
        (Homeomorph.addLeft z).measurableEmbedding
      have hpre : (fun ξ : ℂ => z + ξ) ⁻¹' (Metric.ball z r')ᶜ = (Metric.ball (0:ℂ) r')ᶜ := by
        ext ξ; simp [Metric.mem_ball]
      have := hmp.setIntegral_preimage_emb hemb φ (Metric.ball z r')ᶜ
      rw [hpre] at this; rw [← this]
    rw [hshift]
    set ψ : ℂ → ℂ := fun ξ => φ (z + ξ) with hψ
    rw [← integral_indicator measurableSet_ball.compl,
      ← Complex.integral_comp_polarCoord_symm ((Metric.ball (0:ℂ) r')ᶜ.indicator ψ),
      polarCoord_target]
    have hae : ∀ᵐ p : ℝ × ℝ ∂volume,
        p ∈ (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π) \ (Set.Ioi r' ×ˢ Set.Ioo (-π) π) →
          p.1 • (Metric.ball (0:ℂ) r')ᶜ.indicator ψ (Complex.polarCoord.symm p) = 0 := by
      have hnull : (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | p.1 = r'} = 0 := by
        have heq : {p : ℝ × ℝ | p.1 = r'} = Prod.fst ⁻¹' {r'} := rfl
        rw [heq, Measure.volume_eq_prod, ← Set.prod_univ, Measure.prod_prod]; simp
      have haene : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ r' := by rw [ae_iff]; simpa using hnull
      filter_upwards [haene] with p hpne hpdiff
      obtain ⟨hpt, hps⟩ := hpdiff
      obtain ⟨hp1, hp2⟩ := hpt
      simp only [Set.mem_Ioi] at hp1
      simp only [Set.mem_prod, Set.mem_Ioi, not_and] at hps
      have hpr : p.1 ≤ r' := not_lt.mp (fun h => hps h hp2)
      have hplt : p.1 < r' := lt_of_le_of_ne hpr hpne
      have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
      have hnotmem : Complex.polarCoord.symm p ∉ (Metric.ball (0:ℂ) r')ᶜ := by
        simp only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, hnorm, not_not]
        exact hplt
      change p.1 • (Metric.ball (0:ℂ) r')ᶜ.indicator ψ (Complex.polarCoord.symm p) = 0
      rw [Set.indicator_of_notMem hnotmem]; simp
    refine (setIntegral_eq_of_subset_of_ae_diff_eq_zero
        (measurableSet_Ioi.prod measurableSet_Ioo).nullMeasurableSet
        (Set.prod_mono (Set.Ioi_subset_Ioi (le_of_lt hr')) (le_refl _)) hae).trans ?_
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    obtain ⟨hpr, hp2⟩ := hp
    simp only [Set.mem_Ioi] at hpr
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos (lt_trans hr' hpr)]
    have hmem : Complex.polarCoord.symm p ∈ (Metric.ball (0:ℂ) r')ᶜ := by
      simp only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, hnorm, not_lt]
      exact le_of_lt hpr
    change p.1 • (Metric.ball (0:ℂ) r')ᶜ.indicator ψ (Complex.polarCoord.symm p)
      = p.1 • φ (z + Complex.polarCoord.symm p)
    rw [Set.indicator_of_mem hmem]
  -- Integrability of the singular kernel integrand on the exterior of a disc.
  have hext_int : ∀ r' : ℝ, 0 < r' →
      IntegrableOn (fun y => (z - y) ^ (-2 : ℤ) * μ y) (Metric.ball z r')ᶜ volume := by
    intro r' hr'
    set f : ℂ → ℂ := fun y => (z - y) ^ (-2 : ℤ) * μ y with hf
    set t : Set ℂ := (Metric.ball z r')ᶜ ∩ Metric.closedBall z R with ht
    have htmeas : MeasurableSet t := measurableSet_ball.compl.inter measurableSet_closedBall
    have htfin : volume t ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right) measure_closedBall_lt_top)
    have hfmeas : AEStronglyMeasurable f volume := by
      apply Measurable.aestronglyMeasurable
      apply Measurable.mul _ hμ.continuous.measurable
      fun_prop
    have hbound : ∀ᵐ y ∂volume.restrict t, ‖f y‖ ≤ Mμ * r'⁻¹^2 := by
      rw [ae_restrict_iff' htmeas]
      filter_upwards with y hy
      obtain ⟨hy1, _⟩ := hy
      simp only [Set.mem_compl_iff, Metric.mem_ball, not_lt, dist_eq] at hy1
      rw [hf, norm_mul, norm_zpow]
      have hzy : r' ≤ ‖z - y‖ := by rw [← norm_neg, neg_sub]; exact hy1
      have hpos : (0:ℝ) < ‖z - y‖ := lt_of_lt_of_le hr' hzy
      have hk : ‖z - y‖ ^ (-2 : ℤ) ≤ r'⁻¹^2 := by
        rw [zpow_neg, zpow_two, show r'⁻¹^2 = (r'*r')⁻¹ by rw [mul_inv]; ring]
        apply inv_anti₀ (by positivity)
        exact mul_le_mul hzy hzy (le_of_lt hr') (le_of_lt hpos)
      calc ‖z - y‖ ^ (-2:ℤ) * ‖μ y‖ ≤ r'⁻¹^2 * Mμ :=
              mul_le_mul hk (hMμ y) (norm_nonneg _) (by positivity)
        _ = Mμ * r'⁻¹^2 := by ring
    have hint_t : IntegrableOn f t volume :=
      Measure.integrableOn_of_bounded htfin hfmeas hbound
    refine hint_t.of_forall_diff_eq_zero measurableSet_ball.compl ?_
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [ht, Set.mem_inter_iff, not_and] at hy2
    have hyR := hy2 hy1
    simp only [Metric.mem_closedBall, not_le, dist_eq] at hyR
    change (z - y) ^ (-2 : ℤ) * μ y = 0
    rw [hμ_van y hyR, mul_zero]
  -- The per-`r` polar identity (Step B.2 core / the integration-by-parts).
  have hPolar : ∀ r : ℝ, 0 < r →
      (∫ y in (Metric.ball z r)ᶜ, (z - y) ^ (-2 : ℤ) * μ y)
        = (1/2 : ℂ) * (∫ θ in Set.Ioo (-π) π, ((starRingEnd ℂ) (e θ))^2 * μ (z + (r : ℂ) * e θ))
          - ∫ y in (Metric.ball z r)ᶜ, (dz μ y) * (z - y)⁻¹ := by
    intro r hr
    rw [eq_sub_iff_add_eq, ← integral_add (hext_int r hr) (hg_int.integrableOn)]
    have hIBP : ∀ y ∈ (Metric.ball z r)ᶜ,
        (z - y) ^ (-2 : ℤ) * μ y + (dz μ y) * (z - y)⁻¹ = dz (fun w => μ w * (z - w)⁻¹) y := by
      intro y hy
      have hyz : y ≠ z := by
        intro h; rw [h] at hy
        simp only [Set.mem_compl_iff, Metric.mem_ball, dist_self] at hy
        exact hy hr
      have hsub : z - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyz)
      have hμd : DifferentiableAt ℝ μ y := hgdiff y
      have hkerℂ : DifferentiableAt ℂ (fun w => (z - w)⁻¹) y :=
        DifferentiableAt.inv ((differentiableAt_const z).sub differentiableAt_id) hsub
      have hkerℝ : DifferentiableAt ℝ (fun w => (z - w)⁻¹) y :=
        (differentiableAt_complex_iff_differentiableAt_real.mp hkerℂ).1
      rw [dz_mul hμd hkerℝ]
      have hdzker : dz (fun w => (z - w)⁻¹) y = (z - y) ^ (-2 : ℤ) := by
        rw [dz_eq_deriv_of_differentiableAt hkerℂ]
        have hderiv : HasDerivAt (fun w => (z - w)⁻¹) ((z - y) ^ (-2 : ℤ)) y := by
          have h1 : HasDerivAt (fun w : ℂ => z - w) (-1) y := by
            simpa using (hasDerivAt_id y).const_sub z
          have h2 := (h1.inv hsub)
          convert h2 using 1
          rw [zpow_neg, zpow_two]; field_simp
        exact hderiv.deriv
      rw [hdzker]; ring
    rw [setIntegral_congr_fun measurableSet_ball.compl hIBP,
      hpolar r hr (fun w => dz (fun w => μ w * (z - w)⁻¹) w)]
    set RIfn : ℝ × ℝ → ℂ := fun p => (1/2 : ℂ) * (starRingEnd ℂ) (e p.2)
        * (deriv (fun s : ℝ => -((starRingEnd ℂ) (e p.2)) * μ (z + (s : ℂ) * e p.2)) p.1) with hRIfn
    set AIfn : ℝ × ℝ → ℂ := fun p => (I/2 : ℂ)
        * (deriv (fun t : ℝ => -((p.1:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2
            * μ (z + (p.1:ℂ) * e t)) p.2)
        with hAIfn
    have hsplit : ∀ p ∈ Set.Ioi r ×ˢ Set.Ioo (-π : ℝ) π,
        p.1 • (dz (fun w => μ w * (z - w)⁻¹) (z + Complex.polarCoord.symm p))
          = RIfn p - AIfn p := by
      intro p hp
      obtain ⟨hpr, hp2⟩ := hp
      simp only [Set.mem_Ioi] at hpr
      have hp1 : 0 < p.1 := lt_trans hr hpr
      have hPp : Complex.polarCoord.symm p = (p.1 : ℂ) * e p.2 := by
        rw [Complex.polarCoord_symm_apply, he_def]
      set Rrad : ℂ :=
        deriv (fun s : ℝ => -((starRingEnd ℂ) (e p.2)) * μ (z + (s : ℂ) * e p.2)) p.1 with hRrad_def
      set Aang : ℂ :=
        deriv (fun t : ℝ => -((p.1:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2 * μ (z + (p.1:ℂ) * e t)) p.2
        with hAang_def
      have hRrad : HasDerivAt
          (fun s : ℝ => -((starRingEnd ℂ) (e p.2)) * μ (z + (s : ℂ) * e p.2)) Rrad p.1 := by
        apply DifferentiableAt.hasDerivAt
        apply DifferentiableAt.const_mul
        apply (hgdiff _).comp
        exact (differentiableAt_const _).add (Complex.ofRealCLM.differentiableAt.mul_const _)
      have hAang : HasDerivAt
          (fun t : ℝ => -((p.1:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2 * μ (z + (p.1:ℂ) * e t))
          Aang p.2 := by
        apply DifferentiableAt.hasDerivAt
        apply DifferentiableAt.mul
        · apply (differentiableAt_const _).mul
          apply DifferentiableAt.pow
          exact (Complex.conjCLE.differentiableAt).comp p.2 (he_diff p.2)
        · apply (hgdiff _).comp
          exact (differentiableAt_const _).add ((differentiableAt_const _).mul (he_diff p.2))
      rw [hPp]
      change p.1 • (dz (fun w => μ w * (z - w)⁻¹) (z + (p.1 : ℂ) * e p.2))
          = (1/2 : ℂ) * (starRingEnd ℂ) (e p.2) * Rrad - (I/2) * Aang
      set ρ := p.1
      set θ := p.2
      set D := fderiv ℝ μ (z + (ρ:ℂ) * e θ) with hD
      -- dz F value via IBP identity
      have hyz : z + (ρ:ℂ) * e θ ≠ z := by
        intro h
        exact (mul_ne_zero (by exact_mod_cast ne_of_gt hp1) (he_ne θ)) (add_eq_left.mp h)
      have hsub : z - (z + (ρ:ℂ)*e θ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hyz)
      have hμd : DifferentiableAt ℝ μ (z + (ρ:ℂ)*e θ) := hgdiff _
      have hkerℂ : DifferentiableAt ℂ (fun w => (z - w)⁻¹) (z + (ρ:ℂ)*e θ) :=
        DifferentiableAt.inv ((differentiableAt_const z).sub differentiableAt_id) hsub
      have hkerℝ : DifferentiableAt ℝ (fun w => (z - w)⁻¹) (z + (ρ:ℂ)*e θ) :=
        (differentiableAt_complex_iff_differentiableAt_real.mp hkerℂ).1
      have hdzF : dz (fun w => μ w * (z - w)⁻¹) (z + (ρ:ℂ)*e θ)
          = μ (z + (ρ:ℂ)*e θ) * (z - (z + (ρ:ℂ)*e θ)) ^ (-2 : ℤ)
            + (dz μ (z + (ρ:ℂ)*e θ)) * (z - (z + (ρ:ℂ)*e θ))⁻¹ := by
        rw [dz_mul hμd hkerℝ]
        have hdzker : dz (fun w => (z - w)⁻¹) (z + (ρ:ℂ)*e θ)
            = (z - (z + (ρ:ℂ)*e θ)) ^ (-2 : ℤ) := by
          rw [dz_eq_deriv_of_differentiableAt hkerℂ]
          have hderiv : HasDerivAt (fun w => (z - w)⁻¹)
              ((z - (z + (ρ:ℂ)*e θ)) ^ (-2 : ℤ)) (z + (ρ:ℂ)*e θ) := by
            have h1 : HasDerivAt (fun w : ℂ => z - w) (-1) (z + (ρ:ℂ)*e θ) := by
              simpa using (hasDerivAt_id _).const_sub z
            have h2 := (h1.inv hsub)
            convert h2 using 1
            rw [zpow_neg, zpow_two]; field_simp
          exact hderiv.deriv
        rw [hdzker]; ring
      rw [hdzF]
      -- bridge dz μ
      have hdzμ_eq : dz μ (z + (ρ:ℂ)*e θ)
          = (1/2 : ℂ) * (starRingEnd ℂ) (e θ) * (D (e θ) - I * D (I * e θ)) := by
        rw [dz, ← hD]
        have hDe : D (e θ) = (Real.cos θ : ℂ) * D 1 + (Real.sin θ : ℂ) * D I := by
          have hee : e θ = (Real.cos θ : ℝ) • (1 : ℂ) + (Real.sin θ : ℝ) • I := by
            rw [he_def]; simp [Complex.real_smul]
          rw [hee, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
        have hDIe : D (I * e θ) = -(Real.sin θ : ℂ) * D 1 + (Real.cos θ : ℂ) * D I := by
          have hIe : I * e θ = (-(Real.sin θ) : ℝ) • (1 : ℂ) + (Real.cos θ : ℝ) • I := by
            rw [he_def, Complex.real_smul, Complex.real_smul, Complex.ofReal_neg]
            linear_combination ((Real.sin θ : ℂ)) * Complex.I_mul_I
          rw [hIe, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul,
            Complex.ofReal_neg]
        have hconj : (starRingEnd ℂ) (e θ) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I := by
          rw [he_def]; simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
        rw [hDe, hDIe, hconj]
        have hI2 : (I:ℂ)^2 = -1 := by rw [pow_two]; exact Complex.I_mul_I
        have hcs : (Real.cos θ : ℂ)^2 + (Real.sin θ : ℂ)^2 = 1 := by
          have : (Real.cos θ)^2 + (Real.sin θ)^2 = 1 := Real.cos_sq_add_sin_sq θ
          exact_mod_cast this
        ring_nf
        rw [hI2]
        linear_combination (-(1/2 : ℂ) * (D 1 - I * D I)) * hcs
      -- radial deriv value
      have hRrad_eq : Rrad = -(starRingEnd ℂ) (e θ) * D (e θ) := by
        have hd : HasDerivAt (fun s : ℝ => -((starRingEnd ℂ) (e θ)) * μ (z + (s : ℂ) * e θ))
            (-((starRingEnd ℂ) (e θ)) * D (e θ)) p.1 := by
          have hinner : HasDerivAt (fun s : ℝ => z + (s : ℂ) * e θ) (e θ) p.1 := by
            have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * e θ) (e θ) p.1 := by
              have := (Complex.ofRealCLM.hasDerivAt (x := p.1)).mul_const (e θ); simpa using this
            exact h1.const_add z
          have hcomp := (hgdiff _).hasFDerivAt.comp_hasDerivAt p.1 hinner
          exact hcomp.const_mul (-(starRingEnd ℂ) (e θ))
        exact hRrad.unique hd
      -- angular deriv value
      have hAang_eq : Aang
          = -((ρ:ℂ)⁻¹) * ((-2 * I * ((starRingEnd ℂ) (e θ))^2) * μ (z + (ρ:ℂ) * e θ)
            + ((starRingEnd ℂ) (e θ))^2 * ((ρ:ℂ) * D (I * e θ))) := by
        have hd : HasDerivAt
            (fun t : ℝ => -((ρ:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2 * μ (z + (ρ:ℂ) * e t))
            (-((ρ:ℂ)⁻¹) * ((-2 * I * ((starRingEnd ℂ) (e θ))^2) * μ (z + (ρ:ℂ) * e θ)
              + ((starRingEnd ℂ) (e θ))^2 * ((ρ:ℂ) * D (I * e θ)))) θ := by
          have hconj_d : HasDerivAt (fun s : ℝ => (starRingEnd ℂ) (e s))
              (-I * (starRingEnd ℂ) (e θ)) θ := by
            have hconj_eq : (fun s : ℝ => (starRingEnd ℂ) (e s))
                = fun s : ℝ => (Real.cos s : ℂ) - (Real.sin s : ℂ) * I := by
              funext s; rw [he_def]
              simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
            rw [hconj_eq]
            have hcos : HasDerivAt (fun s : ℝ => (Real.cos s : ℂ)) ((-Real.sin θ : ℝ) : ℂ) θ :=
              (Real.hasDerivAt_cos θ).ofReal_comp
            have hsin : HasDerivAt (fun s : ℝ => (Real.sin s : ℂ)) ((Real.cos θ : ℝ) : ℂ) θ :=
              (Real.hasDerivAt_sin θ).ofReal_comp
            have hdd := hcos.sub (hsin.mul_const I)
            convert hdd using 1
            rw [he_def]
            simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
            linear_combination (Real.sin θ : ℂ) * Complex.I_mul_I
          have hconj2_d : HasDerivAt (fun s : ℝ => ((starRingEnd ℂ) (e s))^2)
              (-2 * I * ((starRingEnd ℂ) (e θ))^2) θ := by
            have h := hconj_d.pow 2
            convert h using 1
            have hps : (2:ℕ) - 1 = 1 := rfl
            rw [hps, pow_one]; push_cast; ring
          have hμ_d : HasDerivAt (fun t : ℝ => μ (z + (ρ:ℂ) * e t))
              ((ρ:ℂ) * D (I * e θ)) θ := by
            have hinner : HasDerivAt (fun t : ℝ => z + (ρ:ℂ) * e t) ((ρ:ℂ) * (I * e θ)) θ :=
              ((he_deriv θ).const_mul (ρ:ℂ)).const_add z
            have hcomp := (hgdiff _).hasFDerivAt.comp_hasDerivAt θ hinner
            have hsm : (fderiv ℝ μ (z + (ρ:ℂ) * e θ)) ((ρ:ℂ) * (I * e θ))
                = (ρ:ℂ) * D (I * e θ) := by
              rw [show ((ρ:ℂ) * (I * e θ)) = (ρ:ℝ) • (I * e θ) by rw [Complex.real_smul], map_smul,
                Complex.real_smul, ← hD]
            rwa [hsm] at hcomp
          have hprod := hconj2_d.mul hμ_d
          have hfull := hprod.const_mul (-((ρ:ℂ)⁻¹))
          have hfun : (fun t : ℝ => -((ρ:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2 * μ (z + (ρ:ℂ) * e t))
              = (fun t : ℝ => -((ρ:ℂ)⁻¹) * (((starRingEnd ℂ) (e t))^2 * μ (z + (ρ:ℂ) * e t))) := by
            funext t; ring
          rw [hfun]; exact hfull
        exact hAang.unique hd
      rw [hRrad_eq, hAang_eq, hdzμ_eq]
      -- now the algebraic split (ptsplit3 core)
      have hρne : (ρ:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp1
      have hinv1 : (z - (z + (ρ:ℂ)*e θ))⁻¹ = -((ρ:ℂ)⁻¹) * (starRingEnd ℂ) (e θ) := by
        have hzz : z - (z + (ρ:ℂ)*e θ) = -((ρ:ℂ)*e θ) := by ring
        rw [hzz, mul_comm (ρ:ℂ) (e θ), show -(e θ * (ρ:ℂ)) = (e θ) * (-(ρ:ℂ)) by ring,
          mul_inv, he_inv]; field_simp
      have hinv2 : (z - (z + (ρ:ℂ)*e θ)) ^ (-2 : ℤ) = ((ρ:ℂ)⁻¹)^2 * (starRingEnd ℂ) (e θ)^2 := by
        have hzz : z - (z + (ρ:ℂ)*e θ) = -((ρ:ℂ)*e θ) := by ring
        rw [hzz, zpow_neg, zpow_two, neg_mul_neg, mul_inv, mul_inv, he_inv]; ring
      rw [hinv1, hinv2, Complex.real_smul]
      have hI2 : (I:ℂ)^2 = -1 := by rw [pow_two]; exact Complex.I_mul_I
      field_simp
      linear_combination ((starRingEnd ℂ) (e θ)^2 * μ (z + (ρ:ℂ)*e θ) * 2) * hI2
    rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hsplit]
    -- Integrability of RIfn on the product domain.
    have hRval : ∀ p : ℝ × ℝ,
        deriv (fun s : ℝ => -((starRingEnd ℂ) (e p.2)) * μ (z + (s : ℂ) * e p.2)) p.1
          = -((starRingEnd ℂ) (e p.2)) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (e p.2) := by
      intro p
      apply HasDerivAt.deriv
      have hinner : HasDerivAt (fun s : ℝ => z + (s : ℂ) * e p.2) (e p.2) p.1 := by
        have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * e p.2) (e p.2) p.1 := by
          have := (Complex.ofRealCLM.hasDerivAt (x := p.1)).mul_const (e p.2); simpa using this
        exact h1.const_add z
      have hcomp := (hgdiff _).hasFDerivAt.comp_hasDerivAt p.1 hinner
      exact hcomp.const_mul (-(starRingEnd ℂ) (e p.2))
    set RI : ℝ × ℝ → ℂ := fun p => (1/2 : ℂ) * (starRingEnd ℂ) (e p.2)
        * (-((starRingEnd ℂ) (e p.2)) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (e p.2)) with hRI
    have hRIfn_eq : ∀ p, RIfn p = RI p := by
      intro p
      change (1/2 : ℂ) * (starRingEnd ℂ) (e p.2)
          * (deriv (fun s : ℝ => -((starRingEnd ℂ) (e p.2)) * μ (z + (s : ℂ) * e p.2)) p.1)
        = (1/2 : ℂ) * (starRingEnd ℂ) (e p.2)
          * (-((starRingEnd ℂ) (e p.2)) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (e p.2))
      rw [hRval]
    have hP_cont : Continuous (fun p : ℝ × ℝ => z + (p.1:ℂ) * e p.2) :=
      continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul
        (he_cont.comp continuous_snd))
    have hconj_c : Continuous (fun p : ℝ × ℝ => (starRingEnd ℂ) (e p.2)) :=
      Complex.continuous_conj.comp (he_cont.comp continuous_snd)
    have hRI_cont : Continuous RI := by
      rw [hRI]
      exact (continuous_const.mul hconj_c).mul (hconj_c.neg.mul
        ((hfderiv_cont.comp hP_cont).clm_apply (he_cont.comp continuous_snd)))
    have hRI_bound : ∀ p, ‖RI p‖ ≤ (1/2) * Mf := by
      intro p
      rw [hRI]
      have h1 : ‖(1/2 : ℂ)‖ = 1/2 := by norm_num
      rw [norm_mul, norm_mul, norm_mul, h1, Complex.norm_conj, he_norm, norm_neg, Complex.norm_conj,
        he_norm]
      have h2 : ‖(fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (e p.2)‖ ≤ Mf := by
        calc ‖(fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (e p.2)‖
            ≤ ‖fderiv ℝ μ (z + (p.1:ℂ) * e p.2)‖ * ‖e p.2‖ := ContinuousLinearMap.le_opNorm _ _
          _ = ‖fderiv ℝ μ (z + (p.1:ℂ) * e p.2)‖ := by rw [he_norm, mul_one]
          _ ≤ Mf := hMf _
      nlinarith [norm_nonneg ((fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (e p.2))]
    have hRI_supp : ∀ p : ℝ × ℝ, R < p.1 → RI p = 0 := by
      intro p hp
      have hv : fderiv ℝ μ (z + (p.1:ℂ) * e p.2) = 0 := by
        apply hfderiv_van
        rw [add_sub_cancel_left, norm_mul, he_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
        exact lt_of_lt_of_le hp (le_abs_self _)
      change (1/2 : ℂ) * (starRingEnd ℂ) (e p.2)
          * (-((starRingEnd ℂ) (e p.2)) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (e p.2)) = 0
      rw [hv]; simp
    have hRI_base : IntegrableOn RI (Set.Ioi r ×ˢ Set.Ioo (-π) π) volume := by
      set S : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) (R + 1) ×ˢ Set.Ioo (-π) π with hS
      have hSfin : volume S ≠ ⊤ := by
        rw [hS, Measure.volume_eq_prod, Measure.prod_prod]
        exact (ENNReal.mul_lt_top measure_Ioo_lt_top measure_Ioo_lt_top).ne
      have hintS : IntegrableOn RI S volume :=
        Measure.integrableOn_of_bounded hSfin hRI_cont.aestronglyMeasurable
          (ae_of_all _ (fun p => hRI_bound p))
      apply hintS.of_forall_diff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      obtain ⟨hpT, hpnS⟩ := hp
      obtain ⟨hr', hθ⟩ := hpT
      simp only [Set.mem_Ioi] at hr'
      apply hRI_supp
      by_contra hle
      rw [not_lt] at hle
      apply hpnS
      exact ⟨Set.mem_Ioo.mpr ⟨lt_trans hr hr', by linarith⟩, hθ⟩
    have hRI_int : IntegrableOn RIfn (Set.Ioi r ×ˢ Set.Ioo (-π) π) volume :=
      hRI_base.congr_fun (fun p _ => (hRIfn_eq p).symm) (measurableSet_Ioi.prod measurableSet_Ioo)
    -- The value of the radial integral S1.
    have hS1 : (∫ p in (Set.Ioi r ×ˢ Set.Ioo (-π) π), RIfn p)
        = (1/2 : ℂ)
          * (∫ θ in Set.Ioo (-π) π, ((starRingEnd ℂ) (e θ))^2 * μ (z + (r : ℂ) * e θ)) := by
      rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) (fun p _ => hRIfn_eq p)]
      have hRI_int' : IntegrableOn RI (Set.Ioi r ×ˢ Set.Ioo (-π) π) (volume.prod volume) := by
        rw [← Measure.volume_eq_prod ℝ ℝ]; exact hRI_base
      have hswapint : IntegrableOn (fun q : ℝ × ℝ => RI q.swap)
          (Set.Ioo (-π) π ×ˢ Set.Ioi r) (volume.prod volume) := by
        have h1 : Integrable RI
            ((volume.restrict (Set.Ioi r)).prod (volume.restrict (Set.Ioo (-π) π))) := by
          rw [Measure.prod_restrict]; exact hRI_int'
        have h2 := h1.swap
        rw [IntegrableOn, ← Measure.prod_restrict]
        exact h2
      rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
      rw [← setIntegral_prod_swap (Set.Ioi r) (Set.Ioo (-π) π) RI, setIntegral_prod _ hswapint]
      -- Inner radial integral evaluation.
      have hinner : ∀ θ : ℝ, θ ∈ Set.Ioo (-π : ℝ) π →
          (∫ ρ in Set.Ioi r, RI (ρ, θ))
            = (1/2 : ℂ) * (((starRingEnd ℂ) (e θ))^2 * μ (z + (r : ℂ) * e θ)) := by
        intro θ _
        have hconst : ∀ ρ : ℝ, RI (ρ, θ) = ((1/2 : ℂ) * (starRingEnd ℂ) (e θ))
            • (deriv (fun s : ℝ => -((starRingEnd ℂ) (e θ)) * μ (z + (s : ℂ) * e θ)) ρ) := by
          intro ρ
          have hv := hRval (ρ, θ)
          simp only at hv
          change (1/2 : ℂ) * (starRingEnd ℂ) (e θ)
              * (-((starRingEnd ℂ) (e θ)) * (fderiv ℝ μ (z + (ρ:ℂ) * e θ)) (e θ))
            = ((1/2 : ℂ) * (starRingEnd ℂ) (e θ))
              • (deriv (fun s : ℝ => -((starRingEnd ℂ) (e θ)) * μ (z + (s : ℂ) * e θ)) ρ)
          rw [hv, smul_eq_mul]
        rw [setIntegral_congr_fun measurableSet_Ioi (fun ρ _ => hconst ρ), integral_smul]
        -- radial FTC
        have hFCD : ContDiff ℝ 1
            (fun s : ℝ => -((starRingEnd ℂ) (e θ)) * μ (z + (s : ℂ) * e θ)) := by
          have h1 : ContDiff ℝ 1 (fun s : ℝ => z + (s : ℂ) * e θ) :=
            contDiff_const.add ((Complex.ofRealCLM.contDiff).mul contDiff_const)
          exact contDiff_const.mul (hμ.comp h1)
        have hFCS : HasCompactSupport
            (fun s : ℝ => -((starRingEnd ℂ) (e θ)) * μ (z + (s : ℂ) * e θ)) := by
          apply HasCompactSupport.intro (K := Set.Icc (-(|R| + 1)) (|R| + 1)) isCompact_Icc
          intro s hs
          rw [Set.mem_Icc, not_and_or] at hs
          have hvan : μ (z + (s:ℂ) * e θ) = 0 := by
            apply hμ_van
            rw [add_sub_cancel_left, norm_mul, he_norm, mul_one, Complex.norm_real,
              Real.norm_eq_abs]
            rcases hs with h | h
            · rw [abs_of_neg (by nlinarith [abs_nonneg R] : s < 0)]
              nlinarith [abs_nonneg R, le_abs_self R]
            · rw [abs_of_pos (by nlinarith [abs_nonneg R] : (0:ℝ) < s)]
              nlinarith [abs_nonneg R, le_abs_self R]
          change -((starRingEnd ℂ) (e θ)) * μ (z + (s:ℂ) * e θ) = 0
          rw [hvan, mul_zero]
        rw [HasCompactSupport.integral_Ioi_deriv_eq hFCD hFCS r, smul_eq_mul]
        change (1/2 : ℂ) * (starRingEnd ℂ) (e θ)
            * (-(-((starRingEnd ℂ) (e θ)) * μ (z + (r : ℂ) * e θ)))
            = (1/2 : ℂ) * (((starRingEnd ℂ) (e θ))^2 * μ (z + (r : ℂ) * e θ))
        ring
      have hswap_eq : ∀ x : ℝ, (∫ y in Set.Ioi r, RI (x, y).swap)
          = ∫ ρ in Set.Ioi r, RI (ρ, x) := by
        intro x; rfl
      rw [setIntegral_congr_fun measurableSet_Ioo (fun x hx => (hswap_eq x).trans (hinner x hx))]
      rw [show (∫ x in Set.Ioo (-π : ℝ) π,
            (1/2 : ℂ) * (((starRingEnd ℂ) (e x))^2 * μ (z + (r : ℂ) * e x)))
          = (1/2 : ℂ) * ∫ x in Set.Ioo (-π : ℝ) π,
            ((starRingEnd ℂ) (e x))^2 * μ (z + (r : ℂ) * e x) from
        integral_const_mul (1/2 : ℂ) (fun x => ((starRingEnd ℂ) (e x))^2 * μ (z + (r : ℂ) * e x))]
    -- The angular deriv value (uniqueness).
    have hAval : ∀ p : ℝ × ℝ, 0 < p.1 →
        deriv (fun t : ℝ => -((p.1:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2 * μ (z + (p.1:ℂ) * e t)) p.2
          = -((p.1:ℂ)⁻¹) * ((-2 * I * ((starRingEnd ℂ) (e p.2))^2) * μ (z + (p.1:ℂ) * e p.2)
              + ((starRingEnd ℂ) (e p.2))^2
                * ((p.1:ℂ) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (I * e p.2))) := by
      intro p hp1
      apply HasDerivAt.deriv
      have hconj_d : HasDerivAt (fun s : ℝ => (starRingEnd ℂ) (e s))
          (-I * (starRingEnd ℂ) (e p.2)) p.2 := by
        have hconj_eq : (fun s : ℝ => (starRingEnd ℂ) (e s))
            = fun s : ℝ => (Real.cos s : ℂ) - (Real.sin s : ℂ) * I := by
          funext s; rw [he_def]
          simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
        rw [hconj_eq]
        have hcos : HasDerivAt (fun s : ℝ => (Real.cos s : ℂ)) ((-Real.sin p.2 : ℝ) : ℂ) p.2 :=
          (Real.hasDerivAt_cos p.2).ofReal_comp
        have hsin : HasDerivAt (fun s : ℝ => (Real.sin s : ℂ)) ((Real.cos p.2 : ℝ) : ℂ) p.2 :=
          (Real.hasDerivAt_sin p.2).ofReal_comp
        have hdd := hcos.sub (hsin.mul_const I)
        convert hdd using 1
        rw [he_def]
        simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
        linear_combination (Real.sin p.2 : ℂ) * Complex.I_mul_I
      have hconj2_d : HasDerivAt (fun s : ℝ => ((starRingEnd ℂ) (e s))^2)
          (-2 * I * ((starRingEnd ℂ) (e p.2))^2) p.2 := by
        have h := hconj_d.pow 2
        convert h using 1
        have hps : (2:ℕ) - 1 = 1 := rfl
        rw [hps, pow_one]; push_cast; ring
      have hμ_d : HasDerivAt (fun t : ℝ => μ (z + (p.1:ℂ) * e t))
          ((p.1:ℂ) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (I * e p.2)) p.2 := by
        have hinner : HasDerivAt (fun t : ℝ => z + (p.1:ℂ) * e t) ((p.1:ℂ) * (I * e p.2)) p.2 :=
          ((he_deriv p.2).const_mul (p.1:ℂ)).const_add z
        have hcomp := (hgdiff _).hasFDerivAt.comp_hasDerivAt p.2 hinner
        have hsm : (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) ((p.1:ℂ) * (I * e p.2))
            = (p.1:ℂ) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (I * e p.2) := by
          rw [show ((p.1:ℂ) * (I * e p.2)) = (p.1:ℝ) • (I * e p.2) by rw [Complex.real_smul],
            map_smul,
            Complex.real_smul]
        rwa [hsm] at hcomp
      have hprod := hconj2_d.mul hμ_d
      have hfull := hprod.const_mul (-((p.1:ℂ)⁻¹))
      have hfun : (fun t : ℝ => -((p.1:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2 * μ (z + (p.1:ℂ) * e t))
          = (fun t : ℝ => -((p.1:ℂ)⁻¹) * (((starRingEnd ℂ) (e t))^2 * μ (z + (p.1:ℂ) * e t))) := by
        funext t; ring
      rw [hfun]; exact hfull
    -- The angular integrand (continuous, bounded, supported in {ρ ≤ R}).
    set AI : ℝ × ℝ → ℂ := fun p => (I/2 : ℂ)
        * (-((p.1:ℂ)⁻¹) * ((-2 * I * ((starRingEnd ℂ) (e p.2))^2) * μ (z + (p.1:ℂ) * e p.2)
            + ((starRingEnd ℂ) (e p.2))^2
              * ((p.1:ℂ) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (I * e p.2)))) with hAI
    have hAI_contOn : ContinuousOn AI (Set.Ioi r ×ˢ Set.Ioo (-π) π) := by
      rw [hAI]
      have hP : Continuous (fun p : ℝ × ℝ => z + (p.1:ℂ) * e p.2) :=
        continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul
          (he_cont.comp continuous_snd))
      have hconj : Continuous (fun p : ℝ × ℝ => (starRingEnd ℂ) (e p.2)) :=
        Complex.continuous_conj.comp (he_cont.comp continuous_snd)
      have hp1inv : ContinuousOn (fun p : ℝ × ℝ => (p.1:ℂ)⁻¹) (Set.Ioi r ×ˢ Set.Ioo (-π) π) := by
        apply ContinuousOn.inv₀ (Complex.continuous_ofReal.comp continuous_fst).continuousOn
        intro p hp
        obtain ⟨hp1, _⟩ := hp
        simp only [Set.mem_Ioi] at hp1
        simp only [Function.comp_apply, ne_eq, Complex.ofReal_eq_zero]
        exact ne_of_gt (lt_trans hr hp1)
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.mul (hp1inv.neg)
      apply ContinuousOn.add
      · apply ContinuousOn.mul (continuousOn_const.mul (hconj.pow 2).continuousOn)
        exact (hμ.continuous.comp hP).continuousOn
      · apply ContinuousOn.mul (hconj.pow 2).continuousOn
        apply ContinuousOn.mul (Complex.continuous_ofReal.comp continuous_fst).continuousOn
        exact ((hfderiv_cont.comp hP).clm_apply
          (continuous_const.mul (he_cont.comp continuous_snd))).continuousOn
    have hAI_int : IntegrableOn AI (Set.Ioi r ×ˢ Set.Ioo (-π) π) volume := by
      set S : Set (ℝ × ℝ) := Set.Ioo r (R + 1) ×ˢ Set.Ioo (-π) π with hS
      have hSmeas : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
      have hSfin : volume S ≠ ⊤ := by
        rw [hS, Measure.volume_eq_prod, Measure.prod_prod]
        exact (ENNReal.mul_lt_top measure_Ioo_lt_top measure_Ioo_lt_top).ne
      have hSsub : S ⊆ Set.Ioi r ×ˢ Set.Ioo (-π) π :=
        Set.prod_mono Set.Ioo_subset_Ioi_self (le_refl _)
      have haem : AEStronglyMeasurable AI (volume.restrict S) :=
        (hAI_contOn.mono hSsub).aestronglyMeasurable hSmeas
      have hbnd : ∀ᵐ p ∂volume.restrict S,
          ‖AI p‖ ≤ (1/2) * (r⁻¹ * (2 * Mμ + (R + 1) * Mf)) := by
        rw [ae_restrict_iff' hSmeas]
        filter_upwards with p hp
        obtain ⟨hp1, _⟩ := hp
        simp only [Set.mem_Ioo] at hp1
        obtain ⟨hpr, hpR⟩ := hp1
        have hp1pos : 0 < p.1 := lt_trans hr hpr
        rw [hAI]
        have hnorm12 : ‖(I/2 : ℂ)‖ = 1/2 := by
          rw [show (I/2 : ℂ) = (1/2 : ℂ) * I by ring, norm_mul, Complex.norm_I, mul_one]; norm_num
        rw [norm_mul, hnorm12, norm_mul, norm_neg, norm_inv, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hp1pos]
        have hT1 : ‖(-2 * I * ((starRingEnd ℂ) (e p.2))^2) * μ (z + (p.1:ℂ) * e p.2)‖ ≤ 2 * Mμ := by
          have hcc : ‖((starRingEnd ℂ) (e p.2))^2‖ = 1 := by
            rw [norm_pow, Complex.norm_conj, he_norm]; ring
          have hco : ‖(-2 * I * ((starRingEnd ℂ) (e p.2))^2)‖ = 2 := by
            rw [norm_mul, norm_mul, hcc, mul_one, Complex.norm_I, mul_one,
              show ‖(-2 : ℂ)‖ = 2 by norm_num]
          rw [norm_mul, hco]
          nlinarith [hMμ (z + (p.1:ℂ) * e p.2), norm_nonneg (μ (z + (p.1:ℂ) * e p.2))]
        have hT2 : ‖((starRingEnd ℂ) (e p.2))^2
            * ((p.1:ℂ) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (I * e p.2))‖
            ≤ (R + 1) * Mf := by
          rw [norm_mul, norm_mul]
          have hc1 : ‖((starRingEnd ℂ) (e p.2))^2‖ = 1 := by
            rw [norm_pow, Complex.norm_conj, he_norm]; ring
          rw [hc1, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp1pos]
          have hfb : ‖(fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (I * e p.2)‖ ≤ Mf := by
            calc ‖(fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (I * e p.2)‖
                ≤ ‖fderiv ℝ μ (z + (p.1:ℂ) * e p.2)‖ * ‖I * e p.2‖ :=
                  ContinuousLinearMap.le_opNorm _ _
              _ = ‖fderiv ℝ μ (z + (p.1:ℂ) * e p.2)‖ := by
                    rw [norm_mul, Complex.norm_I, he_norm, mul_one, mul_one]
              _ ≤ Mf := hMf _
          have hp1le : p.1 ≤ R + 1 := le_of_lt hpR
          nlinarith [norm_nonneg (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)
            (I * e p.2)), hMf (z + (p.1:ℂ) * e p.2), norm_nonneg (μ (z + (p.1:ℂ) * e p.2))]
        have hsum : ‖(-2 * I * ((starRingEnd ℂ) (e p.2))^2) * μ (z + (p.1:ℂ) * e p.2)
            + ((starRingEnd ℂ) (e p.2))^2
              * ((p.1:ℂ) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (I * e p.2))‖
            ≤ 2 * Mμ + (R + 1) * Mf := le_trans (norm_add_le _ _) (add_le_add hT1 hT2)
        have hrinv : p.1⁻¹ ≤ r⁻¹ := by
          rw [inv_le_inv₀ hp1pos hr]; exact le_of_lt hpr
        have hMμnn : 0 ≤ Mμ := le_trans (norm_nonneg _) (hMμ z)
        have hsum_nn : 0 ≤ 2 * Mμ + (R + 1) * Mf := le_trans (norm_nonneg _) hsum
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/2)
        apply mul_le_mul hrinv hsum (norm_nonneg _) (by positivity)
      have hIFM : IsFiniteMeasure (volume.restrict S) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hSfin.lt_top⟩
      have hintS : IntegrableOn AI S volume := ⟨haem, HasFiniteIntegral.of_bounded hbnd⟩
      apply hintS.of_forall_diff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      obtain ⟨hpT, hpnS⟩ := hp
      obtain ⟨hr', hθ⟩ := hpT
      simp only [Set.mem_Ioi] at hr'
      have hpR : R + 1 ≤ p.1 := by
        by_contra hlt
        rw [not_le] at hlt
        exact hpnS ⟨Set.mem_Ioo.mpr ⟨hr', hlt⟩, hθ⟩
      change (I/2 : ℂ) * (-((p.1:ℂ)⁻¹) * ((-2 * I * ((starRingEnd ℂ) (e p.2))^2)
            * μ (z + (p.1:ℂ) * e p.2)
          + ((starRingEnd ℂ) (e p.2))^2
            * ((p.1:ℂ) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (I * e p.2)))) = 0
      have hvμ : μ (z + (p.1:ℂ) * e p.2) = 0 := by
        apply hμ_van
        rw [add_sub_cancel_left, norm_mul, he_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        linarith
      have hv : fderiv ℝ μ (z + (p.1:ℂ) * e p.2) = 0 := by
        apply hfderiv_van
        rw [add_sub_cancel_left, norm_mul, he_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        linarith
      rw [hvμ, hv]; simp
    have hAIfn_eq : ∀ p ∈ Set.Ioi r ×ˢ Set.Ioo (-π : ℝ) π, AIfn p = AI p := by
      intro p hp
      obtain ⟨hp1, _⟩ := hp
      simp only [Set.mem_Ioi] at hp1
      change (I/2 : ℂ) * (deriv (fun t : ℝ => -((p.1:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2
          * μ (z + (p.1:ℂ) * e t)) p.2) = AI p
      rw [hAI, hAval p (lt_trans hr hp1)]
    have hAI_int_fn : IntegrableOn AIfn (Set.Ioi r ×ˢ Set.Ioo (-π) π) volume :=
      hAI_int.congr_fun (fun p hp => (hAIfn_eq p hp).symm)
        (measurableSet_Ioi.prod measurableSet_Ioo)
    have hS2 : (∫ p in (Set.Ioi r ×ˢ Set.Ioo (-π) π), AIfn p) = 0 := by
      rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hAIfn_eq]
      -- Fubini: ρ outer, θ inner, with the inner integral vanishing.
      have hAI_int' : IntegrableOn AI (Set.Ioi r ×ˢ Set.Ioo (-π) π) (volume.prod volume) := by
        rw [← Measure.volume_eq_prod ℝ ℝ]; exact hAI_int
      rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
      rw [setIntegral_prod _ hAI_int']
      -- inner angular integral vanishes for each ρ > r.
      have hinner : ∀ ρ : ℝ, ρ ∈ Set.Ioi r → (∫ θ in Set.Ioo (-π) π, AI (ρ, θ)) = 0 := by
        intro ρ hρ
        simp only [Set.mem_Ioi] at hρ
        have hρpos : 0 < ρ := lt_trans hr hρ
        set g : ℝ → ℂ := fun t : ℝ => -((ρ:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2 * μ (z + (ρ:ℂ) * e t)
          with hg
        -- explicit derivative value V θ, continuous in θ, with HasDerivAt g (V θ) θ
        set V : ℝ → ℂ := fun θ => -((ρ:ℂ)⁻¹) * ((-2 * I * ((starRingEnd ℂ) (e θ))^2)
              * μ (z + (ρ:ℂ) * e θ)
            + ((starRingEnd ℂ) (e θ))^2
              * ((ρ:ℂ) * (fderiv ℝ μ (z + (ρ:ℂ) * e θ)) (I * e θ))) with hV
        have hg_deriv : ∀ θ : ℝ, HasDerivAt g (V θ) θ := by
          intro θ
          have hconj_d : HasDerivAt (fun s : ℝ => (starRingEnd ℂ) (e s))
              (-I * (starRingEnd ℂ) (e θ)) θ := by
            have hconj_eq : (fun s : ℝ => (starRingEnd ℂ) (e s))
                = fun s : ℝ => (Real.cos s : ℂ) - (Real.sin s : ℂ) * I := by
              funext s; rw [he_def]
              simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
            rw [hconj_eq]
            have hcos : HasDerivAt (fun s : ℝ => (Real.cos s : ℂ)) ((-Real.sin θ : ℝ) : ℂ) θ :=
              (Real.hasDerivAt_cos θ).ofReal_comp
            have hsin : HasDerivAt (fun s : ℝ => (Real.sin s : ℂ)) ((Real.cos θ : ℝ) : ℂ) θ :=
              (Real.hasDerivAt_sin θ).ofReal_comp
            have hdd := hcos.sub (hsin.mul_const I)
            convert hdd using 1
            rw [he_def]
            simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
            linear_combination (Real.sin θ : ℂ) * Complex.I_mul_I
          have hconj2_d : HasDerivAt (fun s : ℝ => ((starRingEnd ℂ) (e s))^2)
              (-2 * I * ((starRingEnd ℂ) (e θ))^2) θ := by
            have h := hconj_d.pow 2
            convert h using 1
            have hps : (2:ℕ) - 1 = 1 := rfl
            rw [hps, pow_one]; push_cast; ring
          have hμ_d : HasDerivAt (fun t : ℝ => μ (z + (ρ:ℂ) * e t))
              ((ρ:ℂ) * (fderiv ℝ μ (z + (ρ:ℂ) * e θ)) (I * e θ)) θ := by
            have hinner2 : HasDerivAt (fun t : ℝ => z + (ρ:ℂ) * e t) ((ρ:ℂ) * (I * e θ)) θ :=
              ((he_deriv θ).const_mul (ρ:ℂ)).const_add z
            have hcomp := (hgdiff _).hasFDerivAt.comp_hasDerivAt θ hinner2
            have hsm : (fderiv ℝ μ (z + (ρ:ℂ) * e θ)) ((ρ:ℂ) * (I * e θ))
                = (ρ:ℂ) * (fderiv ℝ μ (z + (ρ:ℂ) * e θ)) (I * e θ) := by
              rw [show ((ρ:ℂ) * (I * e θ)) = (ρ:ℝ) • (I * e θ) by rw [Complex.real_smul], map_smul,
                Complex.real_smul]
            rwa [hsm] at hcomp
          have hprod := hconj2_d.mul hμ_d
          have hfull := hprod.const_mul (-((ρ:ℂ)⁻¹))
          have hfun : (fun t : ℝ => -((ρ:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2 * μ (z + (ρ:ℂ) * e t))
              = (fun t : ℝ => -((ρ:ℂ)⁻¹) * (((starRingEnd ℂ) (e t))^2 * μ (z + (ρ:ℂ) * e t))) := by
            funext t; ring
          rw [hg, hfun]
          exact hfull
        have hV_cont : Continuous V := by
          rw [hV]
          have hP : Continuous (fun θ : ℝ => z + (ρ:ℂ) * e θ) :=
            continuous_const.add (continuous_const.mul he_cont)
          have hconj : Continuous (fun θ : ℝ => (starRingEnd ℂ) (e θ)) :=
            Complex.continuous_conj.comp he_cont
          apply Continuous.mul continuous_const
          apply Continuous.add
          · exact ((continuous_const.mul (hconj.pow 2))).mul (hμ.continuous.comp hP)
          · apply Continuous.mul (hconj.pow 2)
            apply Continuous.mul continuous_const
            exact (hfderiv_cont.comp hP).clm_apply (continuous_const.mul he_cont)
        have hAIeq : ∀ θ : ℝ, AI (ρ, θ) = (I/2 : ℂ) * V θ := by
          intro θ; rw [hAI, hV]
        rw [setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hAIeq θ)]
        rw [show (∫ θ in Set.Ioo (-π : ℝ) π, (I/2 : ℂ) * V θ)
            = (I/2 : ℂ) * ∫ θ in Set.Ioo (-π : ℝ) π, V θ from integral_const_mul (I/2 : ℂ) V]
        have hπle : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hπle,
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hg_deriv θ)
          (hV_cont.intervalIntegrable _ _)]
        have hπ : e π = (-1 : ℂ) := by rw [he_def]; simp [Real.cos_pi, Real.sin_pi]
        have hmπ : e (-π) = (-1 : ℂ) := by rw [he_def]; simp [Real.cos_pi, Real.sin_pi]
        have hper : g π = g (-π) := by
          change -((ρ:ℂ)⁻¹) * ((starRingEnd ℂ) (e π))^2 * μ (z + (ρ:ℂ) * e π)
            = -((ρ:ℂ)⁻¹) * ((starRingEnd ℂ) (e (-π)))^2 * μ (z + (ρ:ℂ) * e (-π))
          rw [hπ, hmπ]
        rw [hper, sub_self, mul_zero]
      rw [setIntegral_congr_fun measurableSet_Ioi hinner]
      simp
    rw [integral_sub hRI_int hAI_int_fn, hS1, hS2, sub_zero]
  -- Assemble: `czOp r = boundary r - kernel r`, take `r → 0`.
  have hmain : Tendsto (fun r : ℝ => ∫ y in (Metric.ball z r)ᶜ, (z - y) ^ (-2 : ℤ) * μ y)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ ζ, (dz μ ζ) / (ζ - z))) := by
    have hcongr : ∀ᶠ r in 𝓝[>] (0:ℝ),
        (∫ y in (Metric.ball z r)ᶜ, (z - y) ^ (-2 : ℤ) * μ y)
          = ((1/2 : ℂ) * ∫ θ in Set.Ioo (-π) π,
                ((starRingEnd ℂ) (e θ))^2 * μ (z + (r : ℂ) * e θ))
            - ∫ y in (Metric.ball z r)ᶜ, (dz μ y) * (z - y)⁻¹ := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact hPolar r hr
    have htarget : (∫ ζ, (dz μ ζ) / (ζ - z)) = 0 - ∫ ζ, (dz μ ζ) * (z - ζ)⁻¹ := by
      rw [zero_sub, ← integral_neg]
      apply integral_congr_ae (ae_of_all _ fun ζ => ?_)
      rw [div_eq_mul_inv, ← neg_sub z ζ, inv_neg, mul_neg]
    rw [htarget]
    refine (hB2.sub hB1).congr' ?_
    filter_upwards [hcongr] with r hr
    exact hr.symm
  -- Express the `czOperator` truncation via the explicit integral (`rfl`).
  have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r μ z
      = ∫ y in (Metric.ball z r)ᶜ, (z - y) ^ (-2 : ℤ) * μ y := fun r => rfl
  simpa [hcz] using hmain

/-- **`L²` isometry.** `‖Tμ‖₂ = ‖μ‖₂`: the Beurling transform is an `L²`
isometry, its Fourier multiplier `ξ̄/ξ` having modulus one. -/
theorem beurling_l2_isometry (hμ : MemLp μ 2 volume) :
    eLpNorm (beurling μ) 2 volume = eLpNorm μ 2 volume := by
  sorry

/-- **`Lᵖ` boundedness.** For `1 < p < ∞` the Beurling transform is bounded
`Lᵖ(ℂ) → Lᵖ(ℂ)` (Calderón–Zygmund). -/
theorem beurling_lp_bound (hp : 1 < p) (hp' : p ≠ ⊤) :
    ∃ C : ℝ, IsCalderonZygmundBound beurling p C := by
  sorry

/-- **Operator-norm continuity at `p = 2`.** The `Lᵖ` bound constant can be taken
arbitrarily close to `1` for `p` near `2` — the qualitative input the Neumann
series of the measurable Riemann mapping theorem consumes. -/
theorem beurling_opNorm_continuous (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℝ≥0∞, 2 < p ∧ p ≠ ⊤ ∧ ∃ C : ℝ, C < 1 + ε ∧ IsCalderonZygmundBound beurling p C := by
  sorry

end RiemannDynamics

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Variational.AffineNeumann

/-!
# The affine solution family

Along an affine family of Beltrami coefficients supported in the closed upper half
plane the normalized solution values at lower-half-plane points depend analytically on
the parameter, as does the Schwarzian, and at the origin of a linear ray the parameter
derivative of the Schwarzian is the pairing of the direction with the quartic kernel.
The truncation-convergence stage, the Cauchy estimates on the lower half plane, and
the termwise differentiation of the solution series are proved on the way.

* `exists_affine_solution_family` — the normalized solution family of an affine
  coefficient path, analytic in the parameter on the lower half plane.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-- **Truncation convergence**: normalized solutions for ball-truncations of a
coefficient converge locally uniformly to the normalized solution of the
coefficient. -/
theorem tendstoLocallyUniformly_of_beltrami_truncation (b : BeltramiCoeff)
    (bs : ℕ → BeltramiCoeff) (ws : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (hQC : ∀ n : ℕ, IsQCAnalytic (ws n) (bs n))
    (hw0 : ∀ n : ℕ, ws n 0 = 0) (hw1 : ∀ n : ℕ, ws n 1 = 1)
    (hagree : ∀ (n : ℕ) (z : ℂ), ‖z‖ ≤ (n : ℝ) + 1 → (bs n).μ z = b.μ z)
    (hnormb : ∀ n : ℕ, (bs n).normInf ≤ b.normInf)
    (hg : IsQCAnalytic g b) (hg0 : g 0 = 0) (hg1 : g 1 = 1) :
    TendstoLocallyUniformly ws g Filter.atTop := by
  classical
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

/-- **Cauchy estimates in the lower half plane**: a function holomorphic below the
real axis and bounded by `Bu` on the disk of radius `-im z₀ / 2` about `z₀` has its
`k`-th derivative at `z₀` bounded by `k! * Bu / (-im z₀ / 2)^k`. -/
theorem norm_iteratedDeriv_le_of_im_neg (u : ℂ → ℂ) (Bu : ℝ)
    (hdiff : DifferentiableOn ℂ u {z : ℂ | z.im < 0}) (z₀ : ℂ) (hz₀ : z₀.im < 0)
    (hBu : ∀ z ∈ Metric.closedBall z₀ (-z₀.im / 2), ‖u z‖ ≤ Bu) (k : ℕ) :
    ‖iteratedDeriv k u z₀‖ ≤ (k.factorial : ℝ) * Bu / (-z₀.im / 2) ^ k := by
  classical
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

/-- A function that agrees near `t₀` with an analytic germ at the origin, shifted to
`t₀`, is analytic at `t₀`. -/
theorem analyticAt_of_shift_eq (f : ℂ → ℂ) (t₀ : ℂ) (ε : ℝ) (ψf : ℂ → ℂ) (hε : 0 < ε)
    (hψ : AnalyticAt ℂ ψf 0) (heq : ∀ s : ℂ, ‖s‖ < ε → f (t₀ + s) = ψf s) :
    AnalyticAt ℂ f t₀ := by
  classical
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

/-- **Termwise differentiation of the solution series**: in the lower half plane the
first three `z`-derivatives of `z ↦ z + ∑ sⁿ cₙ(z)` are computed term by term. -/
theorem deriv_add_tsum_pow_mul_of_im_neg (cs : ℕ → ℂ → ℂ) (Mc ρc : ℝ) (s : ℂ)
    (hρ0 : 0 ≤ ρc) (hsρ : ‖s‖ * ρc < 1)
    (hcb1 : ∀ (n : ℕ) (z : ℂ), ‖cs (n + 1) z‖ ≤ Mc * ρc ^ n)
    (hcb0 : ∀ z : ℂ, ‖cs 0 z‖ ≤ Mc)
    (hcdiff : ∀ n : ℕ, DifferentiableOn ℂ (cs n) {z : ℂ | z.im < 0})
    (z₀ : ℂ) (hz₀ : z₀.im < 0) :
      deriv (fun z => z + ∑' n : ℕ, s ^ n * cs n z) z₀
          = 1 + ∑' n : ℕ, s ^ n * deriv (cs n) z₀
      ∧ deriv (deriv (fun z => z + ∑' n : ℕ, s ^ n * cs n z)) z₀
          = ∑' n : ℕ, s ^ n * deriv (deriv (cs n)) z₀
      ∧ deriv (deriv (deriv (fun z => z + ∑' n : ℕ, s ^ n * cs n z))) z₀
          = ∑' n : ℕ, s ^ n * deriv (deriv (deriv (cs n))) z₀ := by
  classical
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
      exact norm_iteratedDeriv_le_of_im_neg (cs 0) Mc (hcdiff 0) z₀ hz₀ (fun z _ => hcb0 z) k
    | succ m =>
      simp only [if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel]
      exact norm_iteratedDeriv_le_of_im_neg (cs (m + 1)) (Mc * ρc ^ m) (hcdiff (m + 1)) z₀ hz₀
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
    exact isQCAnalytic_affine_postcomp (Fj j t) (btr j t ht) (Fj j t 1 - Fj j t 0)⁻¹ (Fj j t 0)
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
      exists_principal_solution_power_series (fun z => κt j z + t₀ * νt j z) (νt j) ((j : ℝ) + 1) M
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
    refine tendstoLocallyUniformly_of_beltrami_truncation (bt t ht) (fun j => btr j t ht)
      (fun j => Wj j t) (W t)
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
      obtain ⟨ε, cs, Mc, ρc, hε0, hρc0, _, hερ, hcb1, hcb0, hcdiff, hser, _⟩ :=
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
        fun s hs =>
          deriv_add_tsum_pow_mul_of_im_neg cs Mc ρc s hρc0 (hsρ s hs) hcb1 hcb0 hcdiff z₀ hz₀
      have hb1 : ∀ n : ℕ, ‖deriv (cs (n + 1)) z₀‖
          ≤ ((1 : ℕ).factorial * Mc / (-z₀.im / 2) ^ 1) * ρc ^ n := by
        intro n
        have h1 := norm_iteratedDeriv_le_of_im_neg (cs (n + 1)) (Mc * ρc ^ n)
          (hcdiff (n + 1)) z₀ hz₀
          (fun z _ => hcb1 n z) 1
        rw [iteratedDeriv_one] at h1
        calc ‖deriv (cs (n + 1)) z₀‖
            ≤ ((1 : ℕ).factorial : ℝ) * (Mc * ρc ^ n) / (-z₀.im / 2) ^ 1 := h1
          _ = ((1 : ℕ).factorial * Mc / (-z₀.im / 2) ^ 1) * ρc ^ n := by ring
      have hb2 : ∀ n : ℕ, ‖deriv (deriv (cs (n + 1))) z₀‖
          ≤ ((2 : ℕ).factorial * Mc / (-z₀.im / 2) ^ 2) * ρc ^ n := by
        intro n
        have h1 := norm_iteratedDeriv_le_of_im_neg (cs (n + 1)) (Mc * ρc ^ n)
          (hcdiff (n + 1)) z₀ hz₀
          (fun z _ => hcb1 n z) 2
        rw [hID2 (cs (n + 1))] at h1
        calc ‖deriv (deriv (cs (n + 1))) z₀‖
            ≤ ((2 : ℕ).factorial : ℝ) * (Mc * ρc ^ n) / (-z₀.im / 2) ^ 2 := h1
          _ = ((2 : ℕ).factorial * Mc / (-z₀.im / 2) ^ 2) * ρc ^ n := by ring
      have hb3 : ∀ n : ℕ, ‖deriv (deriv (deriv (cs (n + 1)))) z₀‖
          ≤ ((3 : ℕ).factorial * Mc / (-z₀.im / 2) ^ 3) * ρc ^ n := by
        intro n
        have h1 := norm_iteratedDeriv_le_of_im_neg (cs (n + 1)) (Mc * ρc ^ n)
          (hcdiff (n + 1)) z₀ hz₀
          (fun z _ => hcb1 n z) 3
        rw [hID3 (cs (n + 1))] at h1
        calc ‖deriv (deriv (deriv (cs (n + 1)))) z₀‖
            ≤ ((3 : ℕ).factorial : ℝ) * (Mc * ρc ^ n) / (-z₀.im / 2) ^ 3 := h1
          _ = ((3 : ℕ).factorial * Mc / (-z₀.im / 2) ^ 3) * ρc ^ n := by ring
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro z
        refine analyticAt_of_shift_eq _ t₁ ε (fun s => z + ∑' n : ℕ, s ^ n * cs n z) hε0
          (analyticAt_const.add
            (analyticAt_tsum_pow_mul_of_le_geometric (fun n => cs n z) Mc ρc hρc0
              (fun n => hcb1 n z) 0 (by simp))) ?_
        intro s hs
        change Fj j (t₁ + s) z = z + ∑' n : ℕ, s ^ n * cs n z
        rw [hser s hs]
      · refine analyticAt_of_shift_eq _ t₁ ε (fun s => 1 + ∑' n : ℕ, s ^ n * deriv (cs n) z₀) hε0
          (analyticAt_const.add
            (analyticAt_tsum_pow_mul_of_le_geometric (fun n => deriv (cs n) z₀) _ ρc hρc0
              hb1 0 (by simp))) ?_
        intro s hs
        change deriv (Fj j (t₁ + s)) z₀ = 1 + ∑' n : ℕ, s ^ n * deriv (cs n) z₀
        rw [hser s hs]
        exact (hzwei s hs).1
      · refine analyticAt_of_shift_eq _ t₁ ε
          (fun s => ∑' n : ℕ, s ^ n * deriv (deriv (cs n)) z₀) hε0
          (analyticAt_tsum_pow_mul_of_le_geometric (fun n => deriv (deriv (cs n)) z₀) _ ρc
            hρc0 hb2 0 (by simp)) ?_
        intro s hs
        change deriv (deriv (Fj j (t₁ + s))) z₀
            = ∑' n : ℕ, s ^ n * deriv (deriv (cs n)) z₀
        rw [hser s hs]
        exact (hzwei s hs).2.1
      · refine analyticAt_of_shift_eq _ t₁ ε
          (fun s => ∑' n : ℕ, s ^ n * deriv (deriv (deriv (cs n))) z₀) hε0
          (analyticAt_tsum_pow_mul_of_le_geometric (fun n => deriv (deriv (deriv (cs n))) z₀)
            _ ρc hρc0 hb3 0 (by simp)) ?_
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
      obtain ⟨B₀, hB₀⟩ := exists_uniform_bound_isQCGeometric Kq (‖z₀‖ + -z₀.im / 2)
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
      have hc1 := norm_iteratedDeriv_le_of_im_neg (Wj j t) B₀ (hWjdiff j t htD) z₀ hz₀
        (hdisk j t htK) 1
      have hc2 := norm_iteratedDeriv_le_of_im_neg (Wj j t) B₀ (hWjdiff j t htD) z₀ hz₀
        (hdisk j t htK) 2
      have hc3 := norm_iteratedDeriv_le_of_im_neg (Wj j t) B₀ (hWjdiff j t htD) z₀ hz₀
        (hdisk j t htK) 3
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
      refine tendstoLocallyUniformlyOn_of_bounded_of_tendsto _ _ _ hopenD ?_ ?_ ?_
      · intro j t₁ ht₁
        exact ((hXan j t₁ ht₁).1).differentiableAt.differentiableWithinAt
      · intro Kc hKcD hKc
        obtain ⟨B, hB⟩ := hXbnd Kc hKcD hKc
        exact ⟨B, fun j t htK => (hB j t htK).1⟩
      · intro t ht
        exact (hXconv t ht).1
    have hVit1 : TendstoLocallyUniformlyOn (fun j => fun t => deriv (Wj j t) z₀)
        (fun t => deriv (W t) z₀) Filter.atTop {t : ℂ | ‖t‖ < (1 - m) / M} := by
      refine tendstoLocallyUniformlyOn_of_bounded_of_tendsto _ _ _ hopenD ?_ ?_ ?_
      · intro j t₁ ht₁
        exact ((hXan j t₁ ht₁).2.1).differentiableAt.differentiableWithinAt
      · intro Kc hKcD hKc
        obtain ⟨B, hB⟩ := hXbnd Kc hKcD hKc
        exact ⟨B, fun j t htK => (hB j t htK).2.1⟩
      · intro t ht
        exact (hXconv t ht).2.1
    have hVit2 : TendstoLocallyUniformlyOn (fun j => fun t => deriv (deriv (Wj j t)) z₀)
        (fun t => deriv (deriv (W t)) z₀) Filter.atTop {t : ℂ | ‖t‖ < (1 - m) / M} := by
      refine tendstoLocallyUniformlyOn_of_bounded_of_tendsto _ _ _ hopenD ?_ ?_ ?_
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
      refine tendstoLocallyUniformlyOn_of_bounded_of_tendsto _ _ _ hopenD ?_ ?_ ?_
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
        obtain ⟨ε, cs, Mc, ρc, hε0, hρc0, _, hερ, hcb1, hcb0, hcdiff, hser, hkz⟩ :=
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
          exact (deriv_add_tsum_pow_mul_of_im_neg cs Mc ρc s hρc0 (hsρ s hs) hcb1
            hcb0 hcdiff z₀ hz₀).2.2
        have hb3 : ∀ n : ℕ, ‖deriv (deriv (deriv (cs (n + 1)))) z₀‖
            ≤ ((3 : ℕ).factorial * Mc / (-z₀.im / 2) ^ 3) * ρc ^ n := by
          intro n
          have h1 := norm_iteratedDeriv_le_of_im_neg (cs (n + 1)) (Mc * ρc ^ n)
            (hcdiff (n + 1)) z₀ hz₀
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
          refine iteratedDeriv_three_cauchyTransform (νt j) 3 ((j : ℝ) + 1) (by norm_num)
            ?_ (hνts j) (hνtu j) z₀ hz₀
          refine memLp_of_eLpNormEssSup_ne_top_of_support (by norm_num) (hνtm j) ?_
            (hνts j)
          exact (lt_of_le_of_lt (eLpNormEssSup_le_of_ae_bound
            (Filter.Eventually.of_forall (hνtb j))) ENNReal.ofReal_lt_top).ne
        -- derivative of the numerator at the origin
        have hN3der : HasDerivAt (fun s : ℂ => deriv (deriv (deriv (Fj j s))) z₀)
            (deriv (deriv (deriv (cs 1))) z₀) 0 := by
          have h1 := hasDerivAt_tsum_pow_mul_of_le_geometric
            (fun n => deriv (deriv (deriv (cs n))) z₀)
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
        · exact (integrable_inv_norm_sub_pow_four_of_im_neg z₀ hz₀).const_mul M
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

end RiemannDynamics

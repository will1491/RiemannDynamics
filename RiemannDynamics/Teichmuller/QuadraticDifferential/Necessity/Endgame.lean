/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Bergman

/-!
# The equality case of the Hamilton pairing

When the Hamilton pairing of a coefficient bounded by `k` attains the value `k` on the
unit ball, the Hölder chain `k = Re ∫ μ q₀ ≤ ∫ |μ| |q₀| ≤ k ∫ |q₀| ≤ k` collapses: the
maximizer has unit mass, and almost everywhere on the Dirichlet domain the coefficient is
`k` times the normalized conjugate of the maximizer — the Teichmüller form `k q̄₀/|q₀|`.
The identification then spreads from the domain to the whole upper half plane: both sides
obey the same Beltrami invariance law, Möbius maps preserve null sets, and the closed
tiles cover the upper half plane.

* `volume_moebiusMap_image_eq_zero` — plane Möbius maps preserve null subsets of the
  upper half plane.
* `ae_eq_upper_of_ae_eq_dirichlet` — spreading an almost-everywhere identity from the
  Dirichlet domain to the upper half plane along the invariance law.
* `eq_teichmullerCoeffFun_ae_of_maximal` — the equality case on the Dirichlet domain.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **Möbius maps preserve null sets off the real axis**: the plane Möbius image of a
Lebesgue-null subset of the upper half plane is Lebesgue-null. -/
theorem volume_moebiusMap_image_eq_zero (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {S : Set ℂ} (hSsub : S ⊆ {z : ℂ | 0 < z.im}) (hSmeas : MeasurableSet S)
    (hS0 : volume S = 0) : volume (moebiusMap γ '' S) = 0 := by
  have hfd : ∀ z ∈ S, HasFDerivWithinAt (moebiusMap γ) (fderiv ℝ (moebiusMap γ) z) S z := by
    intro z hzS
    have hd : moebiusDenom γ z ≠ 0 :=
      moebiusDenom_ne_zero_of_im_ne_zero γ (hSsub hzS).ne'
    exact (((hasDerivAt_moebiusMap γ hd).complexToReal_fderiv).differentiableAt.hasFDerivAt
      ).hasFDerivWithinAt
  have hinj : Set.InjOn (moebiusMap γ) S := by
    intro x hx y hy hxy
    have hdx : moebiusDenom γ x ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ (hSsub hx).ne'
    have hdy : moebiusDenom γ y ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ (hSsub hy).ne'
    have h1 : moebiusMap γ⁻¹ (moebiusMap γ x) = x := by
      rw [moebiusMap_mul γ⁻¹ γ x hdx, inv_mul_cancel, moebiusMap_one]
    have h2 : moebiusMap γ⁻¹ (moebiusMap γ y) = y := by
      rw [moebiusMap_mul γ⁻¹ γ y hdy, inv_mul_cancel, moebiusMap_one]
    rw [← h1, ← h2, hxy]
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hfd hinj
    (fun _ => (1 : ℝ≥0∞))
  have h1 : volume (moebiusMap γ '' S) = ∫⁻ _ in moebiusMap γ '' S, (1 : ℝ≥0∞) ∂volume :=
    (setLIntegral_one _).symm
  refine h1.trans (hcov.trans ?_)
  rw [Measure.restrict_eq_zero.mpr hS0, lintegral_zero_measure]

/-- **Spreading along the invariance law**: two functions on the upper half plane obeying
the same `Γ`-Beltrami invariance law and agreeing almost everywhere on the canonical
Dirichlet domain agree almost everywhere on the upper half plane. -/
theorem ae_eq_upper_of_ae_eq_dirichlet (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    {f g : ℂ → ℂ}
    (hlawf : ∀ W ∈ Γ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      f (moebiusMap W z) * (moebiusDenom W z) ^ 2
        = f z * (starRingEnd ℂ (moebiusDenom W z)) ^ 2)
    (hlawg : ∀ W ∈ Γ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      g (moebiusMap W z) * (moebiusDenom W z) ^ 2
        = g z * (starRingEnd ℂ (moebiusDenom W z)) ^ 2)
    (heq : ∀ᵐ z ∂(volume.restrict
      (UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I)), f z = g z) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), f z = g z := by
  classical
  have : Countable ↥Γ := IsFuchsianGroup.countable hΓ
  obtain ⟨ε, hε, hgap⟩ := exists_trace_gap hΓ hfree hcc
  obtain ⟨R, hR, hdense⟩ := exists_orbit_density_bound hΓ hε hgap hcc UpperHalfPlane.I
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  set D : Set ℂ := UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I with hDdef
  have hDc : IsCompact D :=
    (isCompact_dirichletDomain hdense).image UpperHalfPlane.continuous_coe
  have hDsub : D ⊆ {z : ℂ | 0 < z.im} := by
    rintro w ⟨τ, -, rfl⟩
    simpa using τ.im_pos
  have hDmeas : MeasurableSet D := hDc.measurableSet
  have hNf : ∀ δ : ↥Γ, ∃ N : Set ℂ, MeasurableSet N ∧ volume N = 0 ∧
      ∀ z : ℂ, 0 < z.im → z ∉ N →
        f (moebiusMap (↑δ) z) * (moebiusDenom (↑δ) z) ^ 2
          = f z * (starRingEnd ℂ (moebiusDenom (↑δ) z)) ^ 2 := by
    intro δ
    have h := hlawf (↑δ) δ.2
    rw [ae_iff, Measure.restrict_apply' hU] at h
    obtain ⟨N, hsubN, hNmeas, hN0⟩ := exists_measurable_superset_of_null h
    refine ⟨N, hNmeas, hN0, fun z hz hzN => ?_⟩
    by_contra hne
    exact hzN (hsubN ⟨hne, hz⟩)
  have hNg : ∀ δ : ↥Γ, ∃ N : Set ℂ, MeasurableSet N ∧ volume N = 0 ∧
      ∀ z : ℂ, 0 < z.im → z ∉ N →
        g (moebiusMap (↑δ) z) * (moebiusDenom (↑δ) z) ^ 2
          = g z * (starRingEnd ℂ (moebiusDenom (↑δ) z)) ^ 2 := by
    intro δ
    have h := hlawg (↑δ) δ.2
    rw [ae_iff, Measure.restrict_apply' hU] at h
    obtain ⟨N, hsubN, hNmeas, hN0⟩ := exists_measurable_superset_of_null h
    refine ⟨N, hNmeas, hN0, fun z hz hzN => ?_⟩
    by_contra hne
    exact hzN (hsubN ⟨hne, hz⟩)
  choose Nf hNfmeas hNf0 hNfP using hNf
  choose Ng hNgmeas hNg0 hNgP using hNg
  have hE := heq
  rw [ae_iff, Measure.restrict_apply' hDmeas] at hE
  obtain ⟨NE, hsubNE, hNEmeas, hNE0⟩ := exists_measurable_superset_of_null hE
  set M : ↥Γ → Set ℂ := fun δ => D ∩ (Nf δ ∪ Ng δ ∪ NE) with hMdef
  have hMnull : ∀ δ : ↥Γ, volume (moebiusMap (↑δ) '' M δ) = 0 := by
    intro δ
    refine volume_moebiusMap_image_eq_zero (↑δ) (fun z hz => hDsub hz.1)
      (hDmeas.inter (((hNfmeas δ).union (hNgmeas δ)).union hNEmeas)) ?_
    exact measure_mono_null Set.inter_subset_right
      (measure_union_null (measure_union_null (hNf0 δ) (hNg0 δ)) hNE0)
  have hnull : volume (⋃ δ : ↥Γ, moebiusMap (↑δ) '' M δ) = 0 :=
    measure_iUnion_null hMnull
  have hcover : ∀ z : ℂ, 0 < z.im → f z ≠ g z →
      z ∈ ⋃ δ : ↥Γ, moebiusMap (↑δ) '' M δ := by
    intro z hz hzne
    obtain ⟨γ, hγ⟩ := exists_smul_mem_dirichletDomain hΓ UpperHalfPlane.I ⟨z, hz⟩
    set ζ : ℂ := ((γ • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) with hζdef
    have hζD : ζ ∈ D := ⟨γ • (⟨z, hz⟩ : UpperHalfPlane), hγ, rfl⟩
    have hζim : 0 < ζ.im := hDsub hζD
    have hzζ : moebiusMap (↑(γ⁻¹ : ↥Γ)) ζ = z := by
      have h1 : ((γ⁻¹ • (γ • (⟨z, hz⟩ : UpperHalfPlane)) : UpperHalfPlane) : ℂ)
          = moebiusMap (↑(γ⁻¹ : ↥Γ)) ζ :=
        coe_smul_eq_moebiusMap (↑(γ⁻¹ : ↥Γ)) (γ • (⟨z, hz⟩ : UpperHalfPlane))
      rw [inv_smul_smul] at h1
      exact h1.symm
    refine Set.mem_iUnion.mpr ⟨γ⁻¹, ζ, ⟨hζD, ?_⟩, hzζ⟩
    by_contra hnot
    have hnf : ζ ∉ Nf γ⁻¹ := fun h => hnot (Set.mem_union_left _ (Set.mem_union_left _ h))
    have hng : ζ ∉ Ng γ⁻¹ := fun h => hnot (Set.mem_union_left _ (Set.mem_union_right _ h))
    have hnE : ζ ∉ NE := fun h => hnot (Set.mem_union_right _ h)
    have hfl := hNfP γ⁻¹ ζ hζim hnf
    have hgl := hNgP γ⁻¹ ζ hζim hng
    have hfg : f ζ = g ζ := by
      by_contra hne
      exact hnE (hsubNE ⟨hne, hζD⟩)
    have hd2 : (moebiusDenom (↑(γ⁻¹ : ↥Γ)) ζ) ^ 2 ≠ 0 :=
      pow_ne_zero _ (moebiusDenom_ne_zero_of_im_ne_zero _ hζim.ne')
    refine hzne (mul_right_cancel₀ hd2 ?_)
    rw [← hzζ, hfl, hgl, hfg]
  rw [ae_restrict_iff' hU, ae_iff]
  refine measure_mono_null (fun z hz => ?_) hnull
  rw [Set.mem_ofPred_eq] at hz
  push Not at hz
  exact hcover z hz.1 hz.2

/-- **The equality case of the Hamilton pairing**: a coefficient bounded by `k > 0` on
the Dirichlet domain whose pairing with a unit-ball differential attains `k` equals the
Teichmüller form `k q̄₀/|q₀|` almost everywhere on the domain. -/
theorem eq_teichmullerCoeffFun_ae_of_maximal (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    {μ : ℂ → ℂ} (hmeas : Measurable μ) {k : ℝ} (hk : 0 < k)
    (hμ : ∀ᵐ z ∂(volume.restrict
      (UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I)), ‖μ z‖ ≤ k)
    {q₀ : QuadraticDifferential Γ} (hq1 : q₀.l1Norm ≤ 1)
    (hmax : (qdPairing μ q₀).re = k) :
    ∀ᵐ z ∂(volume.restrict
      (UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I)),
      μ z = teichmullerCoeffFun q₀ k z := by
  classical
  obtain ⟨ε, hε, hgap⟩ := exists_trace_gap hΓ hfree hcc
  obtain ⟨R, hR, hdense⟩ := exists_orbit_density_bound hΓ hε hgap hcc UpperHalfPlane.I
  set D : Set ℂ := UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I with hDdef
  have hDc : IsCompact D :=
    (isCompact_dirichletDomain hdense).image UpperHalfPlane.continuous_coe
  have hDsub : D ⊆ {z : ℂ | 0 < z.im} := by
    rintro w ⟨τ, -, rfl⟩
    simpa using τ.im_pos
  have hDmeas : MeasurableSet D := hDc.measurableSet
  have h_int_q : Integrable (fun z => q₀ z) (volume.restrict D) := by
    refine ⟨q₀.measurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    exact lt_of_le_of_lt hq1 ENNReal.one_lt_top
  have h_int_mq : Integrable (fun z => μ z * q₀ z) (volume.restrict D) :=
    Integrable.bdd_mul h_int_q hmeas.aestronglyMeasurable hμ
  have h_int_re : Integrable (fun z => (μ z * q₀ z).re) (volume.restrict D) := by
    have h := h_int_mq.re
    simpa only [RCLike.re_to_complex] using h
  have h_re : ∫ z in D, (μ z * q₀ z).re = k := by
    have h := integral_re h_int_mq
    simp only [RCLike.re_to_complex] at h
    rw [h]
    exact hmax
  have h_norm_int : ∫ z in D, ‖q₀ z‖ ≤ 1 := by
    rw [integral_norm_eq_lintegral_enorm q₀.measurable.aestronglyMeasurable]
    have h1 : (∫⁻ z in D, ‖q₀ z‖ₑ) ≤ 1 := hq1
    calc (∫⁻ z in D, ‖q₀ z‖ₑ).toReal ≤ (1 : ℝ≥0∞).toReal :=
          ENNReal.toReal_mono ENNReal.one_ne_top h1
      _ = 1 := by simp
  have h_ptwise : ∀ᵐ z ∂(volume.restrict D),
      (μ z * q₀ z).re ≤ k * ‖q₀ z‖ ∧ ‖μ z * q₀ z‖ ≤ k * ‖q₀ z‖ := by
    filter_upwards [hμ] with z hz
    have hn : ‖μ z * q₀ z‖ ≤ k * ‖q₀ z‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
    exact ⟨le_trans (Complex.re_le_norm _) hn, hn⟩
  have h_int_diff : Integrable (fun z => k * ‖q₀ z‖ - (μ z * q₀ z).re)
      (volume.restrict D) := (h_int_q.norm.const_mul k).sub h_int_re
  have h_int_val : ∫ z in D, (k * ‖q₀ z‖ - (μ z * q₀ z).re)
      = k * (∫ z in D, ‖q₀ z‖) - k := by
    rw [integral_sub (h_int_q.norm.const_mul k) h_int_re, integral_const_mul, h_re]
  have h_nonneg : 0 ≤ᶠ[ae (volume.restrict D)]
      fun z => k * ‖q₀ z‖ - (μ z * q₀ z).re := by
    filter_upwards [h_ptwise] with z hz
    simpa using sub_nonneg.mpr hz.1
  have h_ge : 0 ≤ ∫ z in D, (k * ‖q₀ z‖ - (μ z * q₀ z).re) :=
    integral_nonneg_of_ae h_nonneg
  have h_zero : ∫ z in D, (k * ‖q₀ z‖ - (μ z * q₀ z).re) = 0 := by
    have hle : k * (∫ z in D, ‖q₀ z‖) - k ≤ 0 := by
      have h2 := mul_le_mul_of_nonneg_left h_norm_int (le_of_lt hk)
      linarith
    rw [h_int_val] at h_ge ⊢
    linarith
  have h_ae0 : ∀ᵐ z ∂(volume.restrict D), k * ‖q₀ z‖ - (μ z * q₀ z).re = 0 := by
    have h := (integral_eq_zero_iff_of_nonneg_ae h_nonneg h_int_diff).mp h_zero
    filter_upwards [h] with z hz
    simpa using hz
  have hq0 : ∃ z : ℂ, 0 < z.im ∧ q₀ z ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ᵐ z ∂(volume.restrict D), μ z * q₀ z = 0 := by
      refine (ae_restrict_iff' hDmeas).mpr (Filter.Eventually.of_forall fun z hz => ?_)
      rw [hnone z (hDsub hz), mul_zero]
    have h0 : qdPairing μ q₀ = 0 := integral_eq_zero_of_ae hzero
    rw [h0] at hmax
    simp at hmax
    exact absurd hmax.symm hk.ne'
  have h_ne : ∀ᵐ z ∂(volume.restrict D), q₀ z ≠ 0 :=
    ae_restrict_of_ae_restrict_of_subset hDsub (q₀.ae_ne_zero hq0)
  filter_upwards [h_ae0, hμ, h_ne] with z h1 h2 h3
  have hre : (μ z * q₀ z).re = k * ‖q₀ z‖ := by linarith
  have hnle : ‖μ z * q₀ z‖ ≤ k * ‖q₀ z‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  have hnorm : ‖μ z * q₀ z‖ = k * ‖q₀ z‖ :=
    le_antisymm hnle (hre ▸ Complex.re_le_norm (μ z * q₀ z))
  have him : (μ z * q₀ z).im = 0 := by
    have hsq : Complex.normSq (μ z * q₀ z) = ‖μ z * q₀ z‖ ^ 2 :=
      Complex.normSq_eq_norm_sq _
    rw [Complex.normSq_apply, hre, hnorm] at hsq
    have h4 : (μ z * q₀ z).im * (μ z * q₀ z).im = 0 := by nlinarith [hsq]
    exact mul_self_eq_zero.mp h4
  have hw : μ z * q₀ z = ((k * ‖q₀ z‖ : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [hre, Complex.ofReal_re]
    · rw [him, Complex.ofReal_im]
  have hq0n : ‖q₀ z‖ ≠ 0 := norm_ne_zero_iff.mpr h3
  have hgoal : μ z = ((k * ‖q₀ z‖ : ℝ) : ℂ) / q₀ z := by
    rw [eq_div_iff h3]
    exact hw
  rw [hgoal]
  change ((k * ‖q₀ z‖ : ℝ) : ℂ) / q₀ z
      = (k : ℂ) * starRingEnd ℂ (q₀ z) * ((‖q₀ z‖⁻¹ : ℝ) : ℂ)
  have hcc2 : starRingEnd ℂ (q₀ z) * q₀ z = ((‖q₀ z‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq _
  have hn : ((‖q₀ z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq0n
  rw [div_eq_iff h3]
  push_cast
  rw [mul_assoc ((k : ℂ) * starRingEnd ℂ (q₀ z)), mul_comm (((‖q₀ z‖ : ℝ) : ℂ)⁻¹) (q₀ z),
    ← mul_assoc, mul_assoc (k : ℂ), mul_comm (starRingEnd ℂ (q₀ z)) (q₀ z), mul_comm (q₀ z)]
  rw [hcc2]
  field_simp

end RiemannDynamics

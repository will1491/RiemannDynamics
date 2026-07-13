/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Sobolev.WeakDeriv
import RiemannDynamics.Analysis.Sobolev.GehringLehto.Differentiability
import RiemannDynamics.Analysis.SingularIntegral.GehringHigherIntegrability.Sobolev

/-!
# Conformal change of variables for weak derivatives

This file states the two Sobolev bricks transporting the `W^{1,2}_loc` theory across a
conformal conjugation `z ↦ ψ (w (φ z))` and across a puncture.

* `hasWeakDirDeriv_comp_conformal` — the chain rule for weak directional derivatives under a
  holomorphic change of variables on both sides. Let `φ` be holomorphic, injective, with
  nonvanishing derivative `φ'` on an open set `U`, and let `ψ` be holomorphic with derivative
  `ψ'` on an open set `V` receiving `w ∘ φ`. If `w` is continuous on `φ '' U` and carries a
  weak gradient `(gx, gy)` there with locally square-integrable components, then any function
  agreeing with `ψ ∘ w ∘ φ` on `U` has, in each real direction `v`, the weak directional
  derivative `z ↦ ψ'(w(φ z)) · ((v·φ'(z)).re · gx(φ z) + (v·φ'(z)).im · gy(φ z))` on `U`
  (the real differential of `w` at `φ z` evaluated at `v · φ'(z)`, then rotated and scaled by
  `ψ'`), and this derivative is again locally square-integrable on `U`: the Dirichlet class
  is conformally invariant in the plane. Taking `ψ = id` (resp. `φ = id`) specializes to the
  one-sided pre-composition (resp. post-composition) chain rules.

* `HasWeakDirDeriv.removable_singleton` — a single point has zero `W^{1,2}`-capacity: a weak
  directional derivative identity holding on `Ω \ {p}`, for a function continuous on the open
  set `Ω` with locally square-integrable derivative on `Ω`, holds on all of `Ω`.
-/

open MeasureTheory
open scoped ENNReal ContDiff

namespace RiemannDynamics

/-- **Weak chain rule under conformal change of variables.** For `φ` holomorphic, injective,
with nonvanishing derivative `φ'` on the open set `U`, and `ψ` holomorphic with derivative
`ψ'` on the open set `V` containing `w '' (φ '' U)`: if `w` is continuous on `φ '' U` with a
weak gradient `(gx, gy)` there whose components are locally square-integrable, then every
function agreeing with `ψ ∘ w ∘ φ` on `U` has, in each real direction `v`, the weak
directional derivative `z ↦ ψ'(w(φ z)) · ((v·φ' z).re · gx(φ z) + (v·φ' z).im · gy(φ z))`
on `U`, and this derivative is locally square-integrable on `U`. -/
theorem hasWeakDirDeriv_comp_conformal {w gx gy φ φ' ψ ψ' f : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hφ : ∀ z ∈ U, HasDerivAt φ (φ' z) z) (hφ0 : ∀ z ∈ U, φ' z ≠ 0)
    (hφinj : Set.InjOn φ U)
    (hψ : ∀ u ∈ V, HasDerivAt ψ (ψ' u) u)
    (hmaps : Set.MapsTo w (φ '' U) V)
    (hwc : ContinuousOn w (φ '' U))
    (hw : HasWeakGradient gx gy w (φ '' U))
    (hgx : MemLpLocOn gx 2 (φ '' U)) (hgy : MemLpLocOn gy 2 (φ '' U))
    (hfeq : Set.EqOn f (fun z => ψ (w (φ z))) U) (v : ℂ) :
    HasWeakDirDeriv v (fun z =>
        ψ' (w (φ z)) * (((v * φ' z).re : ℂ) * gx (φ z) + ((v * φ' z).im : ℂ) * gy (φ z)))
      f U ∧
    MemLpLocOn (fun z =>
        ψ' (w (φ z)) * (((v * φ' z).re : ℂ) * gx (φ z) + ((v * φ' z).im : ℂ) * gy (φ z)))
      2 U := by
  classical
  haveI : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  haveI : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  haveI : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  -- ================= (S0) analyticity and continuity of the data =================
  have hφdiff : DifferentiableOn ℂ φ U :=
    fun z hz => ((hφ z hz).differentiableAt).differentiableWithinAt
  have hφa : AnalyticOnNhd ℂ φ U := hφdiff.analyticOnNhd hU
  have hφcont : ContinuousOn φ U := hφdiff.continuousOn
  have hφ'cont : ContinuousOn φ' U := by
    apply (hφa.deriv.continuousOn).congr
    intro z hz
    exact ((hφ z hz).deriv).symm
  have hψdiff : DifferentiableOn ℂ ψ V :=
    fun u hu => ((hψ u hu).differentiableAt).differentiableWithinAt
  have hψa : AnalyticOnNhd ℂ ψ V := hψdiff.analyticOnNhd hV
  have hψcont : ContinuousOn ψ V := hψdiff.continuousOn
  have hψ'cont : ContinuousOn ψ' V := by
    apply (hψa.deriv.continuousOn).congr
    intro u hu
    exact ((hψ u hu).deriv).symm
  -- ================= (S1) the image is open =================
  have hU'open : IsOpen (φ '' U) := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨z, hz, rfl⟩
    have hsd : HasStrictDerivAt φ (deriv φ z) z := (hφa z hz).hasStrictDerivAt
    have hne : deriv φ z ≠ 0 := by
      rw [(hφ z hz).deriv]
      exact hφ0 z hz
    rw [← hsd.map_nhds_eq hne]
    exact Filter.image_mem_map (hU.mem_nhds hz)
  -- ================= (S2) real Fréchet derivative of `φ` =================
  have hφR : ∀ z ∈ U, HasFDerivAt φ (ContinuousLinearMap.mul ℝ ℂ (φ' z)) z := by
    intro z hz
    have h2 := ((hφ z hz).hasFDerivAt).restrictScalars ℝ
    have h3 : (ContinuousLinearMap.toSpanSingleton ℂ (φ' z)).restrictScalars ℝ
        = ContinuousLinearMap.mul ℝ ℂ (φ' z) := by
      apply ContinuousLinearMap.ext
      intro a
      simp only [ContinuousLinearMap.coe_restrictScalars',
        ContinuousLinearMap.toSpanSingleton_apply,
        ContinuousLinearMap.mul_apply', smul_eq_mul]
      ring
    rwa [h3] at h2
  have hψR : ∀ u ∈ V, HasFDerivAt ψ (ContinuousLinearMap.mul ℝ ℂ (ψ' u)) u := by
    intro u hu
    have h2 := ((hψ u hu).hasFDerivAt).restrictScalars ℝ
    have h3 : (ContinuousLinearMap.toSpanSingleton ℂ (ψ' u)).restrictScalars ℝ
        = ContinuousLinearMap.mul ℝ ℂ (ψ' u) := by
      apply ContinuousLinearMap.ext
      intro a
      simp only [ContinuousLinearMap.coe_restrictScalars',
        ContinuousLinearMap.toSpanSingleton_apply,
        ContinuousLinearMap.mul_apply', smul_eq_mul]
      ring
    rwa [h3] at h2
  -- ================= (S3) determinant of the multiplication map =================
  have hdet : ∀ (cc : ℂ), (ContinuousLinearMap.mul ℝ ℂ cc).det = Complex.normSq cc := by
    intro cc
    have h := LinearMap.det_toMatrix Complex.basisOneI
      ((ContinuousLinearMap.mul ℝ ℂ cc : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)
    have hgoal : (ContinuousLinearMap.mul ℝ ℂ cc).det
        = ((LinearMap.toMatrix Complex.basisOneI Complex.basisOneI)
            ((ContinuousLinearMap.mul ℝ ℂ cc : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)).det := h.symm
    rw [hgoal, Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply]
    rw [show Complex.basisOneI 0 = 1 by simp [Complex.coe_basisOneI],
      show Complex.basisOneI 1 = Complex.I by simp [Complex.coe_basisOneI]]
    simp only [Complex.coe_basisOneI_repr]
    change (cc * 1).re * (cc * Complex.I).im - (cc * Complex.I).re * (cc * 1).im
        = Complex.normSq cc
    simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  -- ================= (S4) change of variables =================
  have hCoV : ∀ (s : Set ℂ), MeasurableSet s → s ⊆ U → ∀ (q : ℂ → ℝ≥0∞),
      (∫⁻ ζ in φ '' s, q ζ ∂volume) = ∫⁻ z in s, ‖φ' z‖ₑ ^ (2 : ℕ) * q (φ z) ∂volume := by
    intro s hsmeas hsub q
    have hfd : ∀ z ∈ s, HasFDerivWithinAt φ (ContinuousLinearMap.mul ℝ ℂ (φ' z)) s z :=
      fun z hz => (hφR z (hsub hz)).hasFDerivWithinAt
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hsmeas hfd (hφinj.mono hsub) q]
    apply setLIntegral_congr_fun hsmeas
    intro z _
    dsimp only
    rw [hdet, abs_of_nonneg (Complex.normSq_nonneg _),
      show Complex.normSq (φ' z) = ‖φ' z‖ ^ 2 from Complex.normSq_eq_norm_sq _,
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  -- ================= (S5) null sets pull back to null sets =================
  have hnullpre : ∀ (E : Set ℂ), volume E = 0 → ∀ (K : Set ℂ), IsCompact K → K ⊆ U →
      volume {z | z ∈ K ∧ φ z ∈ E} = 0 := by
    intro E hE K hKc hKU
    obtain ⟨E', hEE', hE'meas, hE'null⟩ := exists_measurable_superset_of_null hE
    -- measurability of the preimage within `K`
    have hres : Continuous (K.restrict φ) := ContinuousOn.restrict (hφcont.mono hKU)
    have hs_meas : MeasurableSet (K ∩ φ ⁻¹' E') := by
      have h1 : MeasurableSet ((K.restrict φ) ⁻¹' E') := hres.measurable hE'meas
      have h2 : MeasurableSet (Subtype.val '' ((K.restrict φ) ⁻¹' E')) :=
        MeasurableSet.subtype_image hKc.measurableSet h1
      have h3 : Subtype.val '' ((K.restrict φ) ⁻¹' E') = K ∩ φ ⁻¹' E' := by
        ext z
        constructor
        · rintro ⟨⟨y, hy⟩, hmem, rfl⟩
          exact ⟨hy, hmem⟩
        · rintro ⟨hzK, hzE⟩
          exact ⟨⟨z, hzK⟩, hzE, rfl⟩
      rwa [h3] at h2
    set s : Set ℂ := K ∩ φ ⁻¹' E' with hsdef
    -- the area-formula lower bound forces `s` to be null
    have hfd : ∀ z ∈ s, HasFDerivWithinAt φ (ContinuousLinearMap.mul ℝ ℂ (φ' z)) s z :=
      fun z hz => (hφR z (hKU hz.1)).hasFDerivWithinAt
    have hle := lintegral_abs_det_fderiv_le_addHaar_image volume hs_meas hfd
      (hφinj.mono (fun z hz => hKU hz.1))
    have himg : φ '' s ⊆ E' := by
      rintro ζ ⟨z, hz, rfl⟩
      exact hz.2
    have hzero : (∫⁻ z in s, ENNReal.ofReal |(ContinuousLinearMap.mul ℝ ℂ (φ' z)).det| ∂volume)
        = 0 := by
      refine le_antisymm (le_trans hle ?_) (zero_le _)
      rw [← hE'null]
      exact measure_mono himg
    -- the integrand is a.e.-measurable and pointwise positive on `s`
    have haem : AEMeasurable (fun z => ENNReal.ofReal
        |(ContinuousLinearMap.mul ℝ ℂ (φ' z)).det|) (volume.restrict s) := by
      have h1 : AEMeasurable φ' (volume.restrict s) := by
        apply AEMeasurable.mono_measure ((hφ'cont.mono hKU).aemeasurable hKc.measurableSet)
        exact Measure.restrict_mono Set.inter_subset_left le_rfl
      have h2 : AEMeasurable (fun z => Complex.normSq (φ' z)) (volume.restrict s) :=
        Complex.continuous_normSq.measurable.comp_aemeasurable h1
      have h3 : AEMeasurable (fun z => ENNReal.ofReal (Complex.normSq (φ' z)))
          (volume.restrict s) := ENNReal.measurable_ofReal.comp_aemeasurable h2
      apply h3.congr
      filter_upwards with z
      rw [hdet, abs_of_nonneg (Complex.normSq_nonneg _)]
    have hae0 := (lintegral_eq_zero_iff' haem).mp hzero
    have hfalse : ∀ᵐ z ∂(volume.restrict s), False := by
      filter_upwards [hae0, ae_restrict_mem hs_meas] with z hz hzs
      have hpos : 0 < Complex.normSq (φ' z) :=
        Complex.normSq_pos.mpr (hφ0 z (hKU hzs.1))
      rw [Pi.zero_apply, hdet, abs_of_nonneg (Complex.normSq_nonneg _)] at hz
      rw [ENNReal.ofReal_eq_zero] at hz
      linarith
    have hs0 : volume s = 0 := by
      have hbot : (volume.restrict s) = 0 :=
        MeasureTheory.ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hfalse)
      have h4 : (volume : Measure ℂ).restrict s Set.univ = volume s :=
        Measure.restrict_apply_univ s
      rw [hbot] at h4
      simpa using h4.symm
    refine measure_mono_null ?_ hs0
    intro z hz
    exact ⟨hz.1, hEE' hz.2⟩
  -- ================= (S6) transport of a.e.-strong-measurability =================
  have hASMcomp : ∀ (K : Set ℂ), IsCompact K → K ⊆ U → ∀ (q : ℂ → ℂ),
      AEStronglyMeasurable q (volume.restrict (φ '' K)) →
      AEStronglyMeasurable (fun z => q (φ z)) (volume.restrict K) := by
    intro K hKc hKU q hq
    have hKmeas : MeasurableSet K := hKc.measurableSet
    have hKimg_meas : MeasurableSet (φ '' K) :=
      MeasurableSet.image_of_continuousOn_injOn hKmeas (hφcont.mono hKU) (hφinj.mono hKU)
    have hφae : AEMeasurable φ (volume.restrict K) :=
      (hφcont.mono hKU).aemeasurable hKmeas
    have hqm : StronglyMeasurable (hq.mk q) := hq.stronglyMeasurable_mk
    have hqeq : q =ᵐ[volume.restrict (φ '' K)] hq.mk q := hq.ae_eq_mk
    -- the bad set upstairs is null
    have hqnull : volume ({ζ | q ζ ≠ hq.mk q ζ} ∩ φ '' K) = 0 := by
      have h1 : ∀ᵐ ζ ∂volume, ζ ∈ φ '' K → q ζ = hq.mk q ζ :=
        (ae_restrict_iff' hKimg_meas).mp hqeq
      rw [MeasureTheory.ae_iff] at h1
      refine measure_mono_null ?_ h1
      intro ζ hζ
      simp only [Set.mem_setOf_eq, Classical.not_imp]
      exact ⟨hζ.2, hζ.1⟩
    obtain ⟨E, hEsub, hEmeas, hEnull⟩ := exists_measurable_superset_of_null hqnull
    have hpre : volume {z | z ∈ K ∧ φ z ∈ E} = 0 := hnullpre E hEnull K hKc hKU
    -- a.e. identification of the composite with a measurable composite
    have hae_comp : (fun z => hq.mk q (hφae.mk φ z)) =ᵐ[volume.restrict K]
        (fun z => q (φ z)) := by
      have h2 : ∀ᵐ z ∂(volume.restrict K), ¬(z ∈ K ∧ φ z ∈ E) := by
        rw [MeasureTheory.ae_iff]
        refine le_antisymm (le_trans (Measure.restrict_le_self _) ?_) (zero_le _)
        rw [← hpre]
        apply le_of_eq
        congr 1
        ext z
        simp
      filter_upwards [hφae.ae_eq_mk, ae_restrict_mem hKmeas, h2] with z hzeq hzK hzE
      have hqz : q (φ z) = hq.mk q (φ z) := by
        by_contra hne
        exact hzE ⟨hzK, hEsub ⟨hne, Set.mem_image_of_mem φ hzK⟩⟩
      rw [← hzeq, hqz]
    exact ((hqm.comp_measurable hφae.measurable_mk).aestronglyMeasurable).congr hae_comp
  -- ================= (S7) the Cauchy–Schwarz + change-of-variables engine =================
  have p_conv2 : ∀ (h : ℂ → ℂ) (μ : Measure ℂ),
      eLpNorm h 2 μ = (∫⁻ z, ‖h z‖ₑ ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) := by
    intro h μ
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    have h2 : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
    rw [h2]
    congr 1
    apply lintegral_congr
    intro z
    rw [← ENNReal.rpow_natCast]
    norm_num
  have p_fin : ∀ {h : ℂ → ℂ} {μ : Measure ℂ}, MemLp h 2 μ →
      (∫⁻ z, ‖h z‖ₑ ^ (2 : ℕ) ∂μ) < ⊤ := by
    intro h μ hh
    have h1 := hh.2
    rw [p_conv2] at h1
    by_contra hX
    have hXtop : (∫⁻ z, ‖h z‖ₑ ^ (2 : ℕ) ∂μ) = ⊤ := eq_top_iff.mpr (not_lt.mp hX)
    rw [hXtop, ENNReal.top_rpow_of_pos (by norm_num)] at h1
    exact (lt_irrefl _ h1).elim
  have hCS : ∀ (K : Set ℂ), IsCompact K → K ⊆ U → ∀ (q : ℂ → ℂ),
      AEStronglyMeasurable (fun z => q (φ z)) (volume.restrict K) →
      (∫⁻ z in K, ‖q (φ z)‖ₑ * ‖φ' z‖ₑ ∂volume)
        ≤ ((∫⁻ ζ in φ '' K, ‖q ζ‖ₑ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ))
          * (volume K) ^ (1 / 2 : ℝ) := by
    intro K hKc hKU q hqφ
    have hφ'ae : AEMeasurable φ' (volume.restrict K) :=
      (hφ'cont.mono hKU).aemeasurable hKc.measurableSet
    have hfae : AEMeasurable (fun z => ‖q (φ z)‖ₑ * ‖φ' z‖ₑ) (volume.restrict K) :=
      hqφ.aemeasurable.enorm.mul hφ'ae.enorm
    have hHolder : (2 : ℝ).HolderConjugate 2 := by
      rw [Real.holderConjugate_iff]
      norm_num
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict K)
      hHolder hfae (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_one,
      Measure.restrict_apply_univ] at h
    refine h.trans (le_of_eq ?_)
    have hsq : (∫⁻ z in K, (‖q (φ z)‖ₑ * ‖φ' z‖ₑ) ^ (2 : ℝ) ∂volume)
        = ∫⁻ ζ in φ '' K, ‖q ζ‖ₑ ^ (2 : ℕ) ∂volume := by
      rw [hCoV K hKc.measurableSet hKU (fun ζ => ‖q ζ‖ₑ ^ (2 : ℕ))]
      apply lintegral_congr
      intro z
      conv_lhs => rw [show ((2 : ℝ)) = (((2 : ℕ) : ℝ)) by norm_num, ENNReal.rpow_natCast]
      rw [mul_pow]
      ring
    rw [hsq]
  -- ================= (S8) smooth compact-in-open cutoffs =================
  have hcut : ∀ (C O : Set ℂ), IsCompact C → IsOpen O → C ⊆ O →
      ∃ (χ : ℂ → ℝ) (O₁ : Set ℂ), ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ O ∧ IsOpen O₁ ∧ C ⊆ O₁ ∧ (∀ ζ ∈ O₁, χ ζ = 1) ∧
        (∀ ζ, 0 ≤ χ ζ) ∧ (∀ ζ, χ ζ ≤ 1) := by
    intro C O hCc hOo hCO
    obtain ⟨r, hrpos, hrsub⟩ := hCc.exists_cthickening_subset_open hOo hCO
    set b : ContDiffBump (0 : ℂ) := ⟨r / 8, r / 4, by positivity, by linarith⟩ with hbdef
    set ρ : ℂ → ℝ := b.normed volume with hρdef
    have hρnn : ∀ t, 0 ≤ ρ t := fun t => b.nonneg_normed t
    have hρint : Integrable ρ volume := b.integrable_normed
    have hρ1 : (∫ t, ρ t ∂volume) = 1 := b.integral_normed
    set A : Set ℂ := Metric.thickening (r / 2) C with hAdef
    have hAmeas : MeasurableSet A := Metric.isOpen_thickening.measurableSet
    set ind : ℂ → ℝ := A.indicator (fun _ => (1 : ℝ)) with hinddef
    have hind_meas : Measurable ind := measurable_const.indicator hAmeas
    have hind_nonneg : ∀ x, 0 ≤ ind x := by
      intro x
      rw [hinddef]
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx]
        norm_num
      · rw [Set.indicator_of_notMem hx]
    have hind_le1 : ∀ x, ind x ≤ 1 := by
      intro x
      rw [hinddef]
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        norm_num
    -- global integrability of the indicator
    have hAsub : A ⊆ Metric.cthickening r C := by
      refine (Metric.thickening_subset_cthickening _ _).trans (Metric.cthickening_mono ?_ _)
      linarith
    have hAvol : volume A < ⊤ :=
      lt_of_le_of_lt (measure_mono hAsub) hCc.cthickening.measure_lt_top
    have hind_int : Integrable ind volume := by
      constructor
      · exact hind_meas.aestronglyMeasurable
      · rw [hasFiniteIntegral_iff_enorm]
        calc (∫⁻ x, ‖ind x‖ₑ ∂volume) ≤ ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) x ∂volume := by
              apply lintegral_mono
              intro x
              dsimp only
              rw [hinddef]
              by_cases hx : x ∈ A
              · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
                simp
              · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
                simp
          _ = volume A := by
              rw [lintegral_indicator hAmeas]
              simp
          _ < ⊤ := hAvol
    have hind_li : MeasureTheory.LocallyIntegrable ind volume := hind_int.locallyIntegrable
    set χ : ℂ → ℝ :=
      MeasureTheory.convolution ρ ind (ContinuousLinearMap.lsmul ℝ ℝ) volume with hχdef
    have hχsm : ContDiff ℝ ∞ χ :=
      HasCompactSupport.contDiff_convolution_left _ b.hasCompactSupport_normed
        b.contDiff_normed hind_li
    -- pointwise convolution formula
    have hχeval : ∀ ζ, χ ζ = ∫ t, ρ t • ind (ζ - t) ∂volume := by
      intro ζ
      rw [hχdef]
      rw [MeasureTheory.convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply]
    -- the plateau: value 1 on the (r/4)-thickening
    have hχone : ∀ ζ ∈ Metric.thickening (r / 4) C, χ ζ = 1 := by
      intro ζ hζ
      rw [hχeval ζ]
      have hpt : ∀ t, ρ t • ind (ζ - t) = ρ t := by
        intro t
        by_cases ht : ρ t = 0
        · rw [ht]
          simp
        · have htsupp : t ∈ Function.support ρ := ht
          rw [hρdef, b.support_normed_eq] at htsupp
          have htn : ‖t‖ < r / 4 := by
            have := Metric.mem_ball.mp htsupp
            rwa [dist_zero_right] at this
          obtain ⟨c', hc', hdist⟩ := Metric.mem_thickening_iff.mp hζ
          have hζt : ζ - t ∈ A := by
            rw [hAdef, Metric.mem_thickening_iff]
            refine ⟨c', hc', ?_⟩
            calc dist (ζ - t) c' ≤ dist (ζ - t) ζ + dist ζ c' := dist_triangle _ _ _
              _ < r / 4 + r / 4 := by
                  apply add_lt_add_of_lt_of_le _ hdist.le
                  rw [dist_eq_norm]
                  simpa using htn
              _ = r / 2 := by ring
          rw [hinddef, Set.indicator_of_mem hζt]
          simp
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact hρ1
    -- vanishing outside the (3r/4)-thickening
    have hχ0out : ∀ ζ, ζ ∉ Metric.thickening (3 * r / 4) C → χ ζ = 0 := by
      intro ζ hζ
      rw [hχeval ζ]
      have hpt : ∀ t, ρ t • ind (ζ - t) = 0 := by
        intro t
        by_cases ht : ρ t = 0
        · rw [ht]
          simp
        · have htsupp : t ∈ Function.support ρ := ht
          rw [hρdef, b.support_normed_eq] at htsupp
          have htn : ‖t‖ < r / 4 := by
            have := Metric.mem_ball.mp htsupp
            rwa [dist_zero_right] at this
          have hζt : ζ - t ∉ A := by
            rw [hAdef, Metric.mem_thickening_iff]
            rintro ⟨c', hc', hdist⟩
            apply hζ
            rw [Metric.mem_thickening_iff]
            refine ⟨c', hc', ?_⟩
            calc dist ζ c' ≤ dist ζ (ζ - t) + dist (ζ - t) c' := dist_triangle _ _ _
              _ < r / 4 + r / 2 := by
                  apply add_lt_add_of_le_of_lt _ hdist
                  rw [dist_eq_norm]
                  simpa using htn.le
              _ = 3 * r / 4 := by ring
          rw [hinddef, Set.indicator_of_notMem hζt]
          simp
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact integral_zero ℂ ℝ
    -- support control
    have hχ_ts : tsupport χ ⊆ Metric.cthickening (3 * r / 4) C := by
      apply closure_minimal _ Metric.isClosed_cthickening
      intro ζ hζ
      by_contra hout
      have h0 : χ ζ = 0 := by
        apply hχ0out
        intro hin
        exact hout ((Metric.thickening_subset_cthickening _ _) hin)
      exact hζ h0
    have hχ_tsO : tsupport χ ⊆ O := by
      refine hχ_ts.trans ((Metric.cthickening_mono ?_ _).trans hrsub)
      linarith
    have h34 : 3 * r / 4 ≤ r := by linarith
    have hχcs : HasCompactSupport χ :=
      IsCompact.of_isClosed_subset hCc.cthickening (isClosed_tsupport _)
        (hχ_ts.trans (Metric.cthickening_mono h34 _))
    -- range in [0,1]
    have hint_pt : ∀ ζ, Integrable (fun t => ρ t • ind (ζ - t)) volume := by
      intro ζ
      apply Integrable.mono' hρint
      · apply AEStronglyMeasurable.smul
          b.continuous_normed.aestronglyMeasurable
        exact (hind_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      · apply Filter.Eventually.of_forall
        intro t
        rw [smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρnn t)
          (hind_nonneg (ζ - t)))]
        calc ρ t * ind (ζ - t) ≤ ρ t * 1 :=
              mul_le_mul_of_nonneg_left (hind_le1 _) (hρnn t)
          _ = ρ t := mul_one _
    have hχ_nonneg : ∀ ζ, 0 ≤ χ ζ := by
      intro ζ
      rw [hχeval ζ]
      apply integral_nonneg
      intro t
      exact mul_nonneg (hρnn t) (hind_nonneg (ζ - t))
    have hχ_le1 : ∀ ζ, χ ζ ≤ 1 := by
      intro ζ
      rw [hχeval ζ]
      calc (∫ t, ρ t • ind (ζ - t) ∂volume) ≤ ∫ t, ρ t ∂volume := by
            apply integral_mono (hint_pt ζ) hρint
            intro t
            calc ρ t • ind (ζ - t) ≤ ρ t * 1 :=
                  mul_le_mul_of_nonneg_left (hind_le1 _) (hρnn t)
              _ = ρ t := mul_one _
        _ = 1 := hρ1
    exact ⟨χ, Metric.thickening (r / 4) C, hχsm, hχcs, hχ_tsO, Metric.isOpen_thickening,
      Metric.self_subset_thickening (by positivity) C, hχone, hχ_nonneg, hχ_le1⟩
  -- ================= (S9) gluing continuity across a cutoff =================
  have hglueC : ∀ (O : Set ℂ), IsOpen O → ∀ (m : ℂ → ℝ), Continuous m → tsupport m ⊆ O →
      ∀ (h : ℂ → ℂ), ContinuousOn h O → Continuous (fun ζ => m ζ • h ζ) := by
    intro O hOo m hm hts h hh
    rw [continuous_iff_continuousAt]
    intro ζ
    by_cases hζ : ζ ∈ O
    · exact (hm.continuousAt).smul (hh.continuousAt (hOo.mem_nhds hζ))
    · have hζ' : ζ ∉ tsupport m := fun hmem => hζ (hts hmem)
      have hev : (fun ζ => m ζ • h ζ) =ᶠ[nhds ζ] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport m).isOpen_compl.mem_nhds hζ'] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy]
        simp
      exact ContinuousAt.congr continuousAt_const hev.symm
  -- ================= (S10) enorm algebra =================
  have habs2 : ∀ (a x y u : ℂ),
      ‖a * ((u.re : ℂ) * x + (u.im : ℂ) * y)‖ₑ ≤ ‖a‖ₑ * (‖u‖ₑ * (‖x‖ₑ + ‖y‖ₑ)) := by
    intro a x y u
    rw [enorm_mul]
    gcongr
    calc ‖(u.re : ℂ) * x + (u.im : ℂ) * y‖ₑ
        ≤ ‖(u.re : ℂ) * x‖ₑ + ‖(u.im : ℂ) * y‖ₑ := enorm_add_le _ _
      _ = ‖(u.re : ℂ)‖ₑ * ‖x‖ₑ + ‖(u.im : ℂ)‖ₑ * ‖y‖ₑ := by rw [enorm_mul, enorm_mul]
      _ ≤ ‖u‖ₑ * ‖x‖ₑ + ‖u‖ₑ * ‖y‖ₑ := by
          gcongr
          · rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
            apply ENNReal.ofReal_le_ofReal
            rw [Complex.norm_real, Real.norm_eq_abs]
            exact Complex.abs_re_le_norm u
          · rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
            apply ENNReal.ofReal_le_ofReal
            rw [Complex.norm_real, Real.norm_eq_abs]
            exact Complex.abs_im_le_norm u
      _ = ‖u‖ₑ * (‖x‖ₑ + ‖y‖ₑ) := by ring
  have e8_sum_sq : ∀ (a b : ℝ≥0∞), (a + b) ^ (2 : ℕ) ≤ 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
    intro a b
    have h1 : a + b ≤ 2 * max a b := by
      rcases le_total a b with h | h
      · rw [max_eq_right h, two_mul]
        exact add_le_add h le_rfl
      · rw [max_eq_left h, two_mul]
        exact add_le_add le_rfl h
    calc (a + b) ^ (2 : ℕ) ≤ (2 * max a b) ^ (2 : ℕ) := by gcongr
      _ = 4 * (max a b) ^ (2 : ℕ) := by
          rw [mul_pow]
          norm_num
      _ ≤ 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
          gcongr
          rcases le_total a b with h | h
          · rw [max_eq_right h]
            exact le_add_self
          · rw [max_eq_left h]
            exact le_self_add
  -- ================= (S11) the derivative candidate and its measurability =================
  set D : ℂ → ℂ := fun z =>
      ψ' (w (φ z)) * (((v * φ' z).re : ℂ) * gx (φ z) + ((v * φ' z).im : ℂ) * gy (φ z))
    with hDdef
  have hψwφ_cont : ∀ (K : Set ℂ), K ⊆ U → ContinuousOn (fun z => ψ' (w (φ z))) K := by
    intro K hKU
    have hφK : ContinuousOn φ K := hφcont.mono hKU
    have hwφ : ContinuousOn (fun z => w (φ z)) K :=
      hwc.comp hφK (fun z hz => Set.mem_image_of_mem φ (hKU hz))
    exact hψ'cont.comp hwφ (fun z hz => hmaps (Set.mem_image_of_mem φ (hKU hz)))
  have hvφ'_cont : ∀ (K : Set ℂ), K ⊆ U →
      ContinuousOn (fun z => (((v * φ' z).re : ℝ) : ℂ)) K ∧
      ContinuousOn (fun z => (((v * φ' z).im : ℝ) : ℂ)) K := by
    intro K hKU
    have h1 : ContinuousOn (fun z => v * φ' z) K :=
      continuousOn_const.mul (hφ'cont.mono hKU)
    exact ⟨Complex.continuous_ofReal.comp_continuousOn
        (Complex.continuous_re.comp_continuousOn h1),
      Complex.continuous_ofReal.comp_continuousOn
        (Complex.continuous_im.comp_continuousOn h1)⟩
  have hDasm : ∀ (K : Set ℂ), IsCompact K → K ⊆ U →
      AEStronglyMeasurable D (volume.restrict K) := by
    intro K hKc hKU
    have hKmeas := hKc.measurableSet
    have himg : φ '' K ⊆ φ '' U := Set.image_mono hKU
    have hKimgc : IsCompact (φ '' K) := hKc.image_of_continuousOn (hφcont.mono hKU)
    have h1 : AEStronglyMeasurable (fun z => gx (φ z)) (volume.restrict K) :=
      hASMcomp K hKc hKU gx (hgx (φ '' K) himg hKimgc).1
    have h2 : AEStronglyMeasurable (fun z => gy (φ z)) (volume.restrict K) :=
      hASMcomp K hKc hKU gy (hgy (φ '' K) himg hKimgc).1
    obtain ⟨hre, him⟩ := hvφ'_cont K hKU
    rw [hDdef]
    exact ((hψwφ_cont K hKU).aestronglyMeasurable hKmeas).mul
      (((hre.aestronglyMeasurable hKmeas).mul h1).add
        ((him.aestronglyMeasurable hKmeas).mul h2))
  -- ================= the two conclusions =================
  refine ⟨?_, ?_⟩
  · -- (Part 1) the weak directional derivative
    intro φt hφt hcs htsupp
    change ∫ z, ((fderiv ℝ φt z) v) • f z = - ∫ z, φt z • D z
    set K : Set ℂ := tsupport φt with hKdef
    have hKc : IsCompact K := hcs
    have hKU : K ⊆ U := htsupp
    have hKmeas : MeasurableSet K := hKc.measurableSet
    have hKimgc : IsCompact (φ '' K) := hKc.image_of_continuousOn (hφcont.mono hKU)
    have himgU : φ '' K ⊆ φ '' U := Set.image_mono hKU
    -- the cutoff `χ` around `φ '' K` inside `φ '' U`
    obtain ⟨χ, O₁, hχsm, hχcs, hχts, hO₁o, hKO₁, hχone, hχ0, hχ1⟩ :=
      hcut (φ '' K) (φ '' U) hKimgc hU'open himgU
    have hχtsc : IsCompact (tsupport χ) := hχcs
    have hχcont : Continuous χ := hχsm.continuous
    have hχfd0 : ∀ ζ, ζ ∉ tsupport χ → fderiv ℝ χ ζ = 0 := by
      intro ζ hζ
      by_contra hne
      exact hζ (support_fderiv_subset ℝ (Function.mem_support.mpr hne))
    have hχfdO₁ : ∀ ζ ∈ O₁, fderiv ℝ χ ζ = 0 := by
      intro ζ hζ
      have hev : χ =ᶠ[nhds ζ] fun _ => (1 : ℝ) := by
        filter_upwards [hO₁o.mem_nhds hζ] with y hy
        exact hχone y hy
      rw [Filter.EventuallyEq.fderiv_eq hev, fderiv_fun_const]
      rfl
    -- the truncated data `W`, `Gx`, `Gy`
    set W : ℂ → ℂ := fun ζ => χ ζ • w ζ with hWdef
    set Gx : ℂ → ℂ := fun ζ => χ ζ • gx ζ + ((fderiv ℝ χ ζ) 1) • w ζ with hGxdef
    set Gy : ℂ → ℂ := fun ζ => χ ζ • gy ζ + ((fderiv ℝ χ ζ) Complex.I) • w ζ with hGydef
    have hWcont : Continuous W := hglueC (φ '' U) hU'open χ hχcont hχts w hwc
    have hW0 : ∀ ζ, ζ ∉ tsupport χ → W ζ = 0 := by
      intro ζ hζ
      change χ ζ • w ζ = 0
      rw [image_eq_zero_of_notMem_tsupport hζ]
      simp
    have hGx0 : ∀ ζ, ζ ∉ tsupport χ → Gx ζ = 0 := by
      intro ζ hζ
      change χ ζ • gx ζ + ((fderiv ℝ χ ζ) 1) • w ζ = 0
      rw [image_eq_zero_of_notMem_tsupport hζ, hχfd0 ζ hζ]
      simp
    have hGy0 : ∀ ζ, ζ ∉ tsupport χ → Gy ζ = 0 := by
      intro ζ hζ
      change χ ζ • gy ζ + ((fderiv ℝ χ ζ) Complex.I) • w ζ = 0
      rw [image_eq_zero_of_notMem_tsupport hζ, hχfd0 ζ hζ]
      simp
    have hWO₁ : ∀ ζ ∈ O₁, W ζ = w ζ := by
      intro ζ hζ
      change χ ζ • w ζ = w ζ
      rw [hχone ζ hζ]
      exact one_smul ℝ (w ζ)
    have hGxO₁ : ∀ ζ ∈ O₁, Gx ζ = gx ζ := by
      intro ζ hζ
      change χ ζ • gx ζ + ((fderiv ℝ χ ζ) 1) • w ζ = gx ζ
      rw [hχone ζ hζ, hχfdO₁ ζ hζ]
      simp
    have hGyO₁ : ∀ ζ ∈ O₁, Gy ζ = gy ζ := by
      intro ζ hζ
      change χ ζ • gy ζ + ((fderiv ℝ χ ζ) Complex.I) • w ζ = gy ζ
      rw [hχone ζ hζ, hχfdO₁ ζ hζ]
      simp
    -- weak gradient of `W` on `φ '' U` via the Leibniz rule
    have hwloc : LocallyIntegrableOn w (φ '' U) :=
      hwc.locallyIntegrableOn hU'open.measurableSet
    have hgloc : ∀ {g0 : ℂ → ℂ}, MemLpLocOn g0 2 (φ '' U) →
        LocallyIntegrableOn g0 (φ '' U) := by
      intro g0 hg0
      rw [MeasureTheory.locallyIntegrableOn_iff hU'open.isLocallyClosed]
      intro k hk hkc
      haveI : IsFiniteMeasure (volume.restrict k) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hkc.measure_lt_top⟩
      exact memLp_one_iff_integrable.mp ((hg0 k hk hkc).mono_exponent (by norm_num))
    have hWxU' : HasWeakDirDeriv 1 Gx W (φ '' U) :=
      hw.1.smul_smooth hχsm hwloc (hgloc hgx)
    have hWyU' : HasWeakDirDeriv Complex.I Gy W (φ '' U) :=
      hw.2.smul_smooth hχsm hwloc (hgloc hgy)
    -- globalization across the second cutoff
    obtain ⟨χ₂, O₂, hχ₂sm, hχ₂cs, hχ₂ts, hO₂o, hsuppO₂, hχ₂one, hχ₂0, hχ₂1⟩ :=
      hcut (tsupport χ) (φ '' U) hχtsc hU'open hχts
    have hχ₂fdO₂ : ∀ ζ ∈ O₂, fderiv ℝ χ₂ ζ = 0 := by
      intro ζ hζ
      have hev : χ₂ =ᶠ[nhds ζ] fun _ => (1 : ℝ) := by
        filter_upwards [hO₂o.mem_nhds hζ] with y hy
        exact hχ₂one y hy
      rw [Filter.EventuallyEq.fderiv_eq hev, fderiv_fun_const]
      rfl
    have hglob : ∀ (vv : ℂ) (G F : ℂ → ℂ), HasWeakDirDeriv vv G F (φ '' U) →
        (∀ ζ, ζ ∉ tsupport χ → F ζ = 0) → (∀ ζ, ζ ∉ tsupport χ → G ζ = 0) →
        HasWeakDirDeriv vv G F Set.univ := by
      intro vv G F hFU' hF0 hG0 φtt hφtt hcs2 _
      change ∫ ζ, ((fderiv ℝ φtt ζ) vv) • F ζ = - ∫ ζ, φtt ζ • G ζ
      set Φ : ℂ → ℝ := fun ζ => φtt ζ * χ₂ ζ with hΦdef
      have hΦsm : ContDiff ℝ ∞ Φ := hφtt.mul hχ₂sm
      have hΦcs : HasCompactSupport Φ := hcs2.mul_right
      have hΦts : tsupport Φ ⊆ φ '' U := (tsupport_mul_subset_right).trans hχ₂ts
      have hkey := hFU' Φ hΦsm hΦcs hΦts
      have hL : ∀ ζ, ((fderiv ℝ Φ ζ) vv) • F ζ = ((fderiv ℝ φtt ζ) vv) • F ζ := by
        intro ζ
        by_cases hζ : ζ ∈ tsupport χ
        · have hζO₂ : ζ ∈ O₂ := hsuppO₂ hζ
          have hd1 : DifferentiableAt ℝ φtt ζ :=
            (hφtt.differentiable (by norm_num)).differentiableAt
          have hd2 : DifferentiableAt ℝ χ₂ ζ :=
            (hχ₂sm.differentiable (by norm_num)).differentiableAt
          have hprod : (fderiv ℝ Φ ζ) vv
              = φtt ζ * ((fderiv ℝ χ₂ ζ) vv) + χ₂ ζ * ((fderiv ℝ φtt ζ) vv) := by
            rw [hΦdef]
            change (fderiv ℝ (fun y => φtt y * χ₂ y) ζ) vv = _
            rw [fderiv_fun_mul hd1 hd2]
            simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
              smul_eq_mul]
          rw [hprod, hχ₂fdO₂ ζ hζO₂, hχ₂one ζ hζO₂]
          simp
        · rw [hF0 ζ hζ]
          simp
      have hR : ∀ ζ, Φ ζ • G ζ = φtt ζ • G ζ := by
        intro ζ
        by_cases hζ : ζ ∈ tsupport χ
        · have hζO₂ : ζ ∈ O₂ := hsuppO₂ hζ
          change (φtt ζ * χ₂ ζ) • G ζ = φtt ζ • G ζ
          rw [hχ₂one ζ hζO₂, mul_one]
        · rw [hG0 ζ hζ]
          simp
      calc ∫ ζ, ((fderiv ℝ φtt ζ) vv) • F ζ
          = ∫ ζ, ((fderiv ℝ Φ ζ) vv) • F ζ :=
            integral_congr_ae (Filter.Eventually.of_forall (fun ζ => (hL ζ).symm))
        _ = - ∫ ζ, Φ ζ • G ζ := hkey
        _ = - ∫ ζ, φtt ζ • G ζ := by
            rw [integral_congr_ae (Filter.Eventually.of_forall hR)]
    have hWx : HasWeakDirDeriv 1 Gx W Set.univ := hglob 1 Gx W hWxU' hW0 hGx0
    have hWy : HasWeakDirDeriv Complex.I Gy W Set.univ := hglob Complex.I Gy W hWyU' hW0 hGy0
    -- global square-integrability of the truncated data
    have hmemχ : ∀ (g0 : ℂ → ℂ), MemLpLocOn g0 2 (φ '' U) →
        MemLp (fun ζ => χ ζ • g0 ζ) 2 volume := by
      intro g0 hg0
      have hg0S : MemLp g0 2 (volume.restrict (tsupport χ)) := hg0 (tsupport χ) hχts hχtsc
      have hasm : AEStronglyMeasurable (fun ζ => χ ζ • g0 ζ)
          (volume.restrict (tsupport χ)) :=
        (hχcont.aestronglyMeasurable.restrict).smul hg0S.1
      have hmemS : MemLp (fun ζ => χ ζ • g0 ζ) 2 (volume.restrict (tsupport χ)) := by
        apply hg0S.of_le hasm
        apply Filter.Eventually.of_forall
        intro ζ
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ0 ζ)]
        calc χ ζ * ‖g0 ζ‖ ≤ 1 * ‖g0 ζ‖ :=
              mul_le_mul_of_nonneg_right (hχ1 ζ) (norm_nonneg _)
          _ = ‖g0 ζ‖ := one_mul _
      have hind : MemLp ((tsupport χ).indicator (fun ζ => χ ζ • g0 ζ)) 2 volume := by
        constructor
        · exact (aestronglyMeasurable_indicator_iff hχtsc.measurableSet).mpr hmemS.1
        · rw [eLpNorm_indicator_eq_eLpNorm_restrict hχtsc.measurableSet]
          exact hmemS.2
      have heq : (tsupport χ).indicator (fun ζ => χ ζ • g0 ζ) = fun ζ => χ ζ • g0 ζ := by
        funext ζ
        by_cases hζ : ζ ∈ tsupport χ
        · rw [Set.indicator_of_mem hζ]
        · rw [Set.indicator_of_notMem hζ, image_eq_zero_of_notMem_tsupport hζ]
          simp
      rwa [heq] at hind
    have hmemd : ∀ (e : ℂ), MemLp (fun ζ => ((fderiv ℝ χ ζ) e) • w ζ) 2 volume := by
      intro e
      have hcont : Continuous (fun ζ => ((fderiv ℝ χ ζ) e) • w ζ) := by
        apply hglueC (φ '' U) hU'open _
          ((hχsm.continuous_fderiv (by norm_num)).clm_apply continuous_const)
          ((tsupport_fderiv_apply_subset ℝ e).trans hχts) w hwc
      have hcs' : HasCompactSupport (fun ζ => ((fderiv ℝ χ ζ) e) • w ζ) :=
        (HasCompactSupport.fderiv_apply ℝ hχcs e).smul_right
      exact hcont.memLp_of_hasCompactSupport hcs'
    have hGxLp : MemLp Gx 2 volume := (hmemχ gx hgx).add (hmemd 1)
    have hGyLp : MemLp Gy 2 volume := (hmemχ gy hgy).add (hmemd Complex.I)
    have hGxloc : MemLpLocOn Gx 2 Set.univ := fun Kk _ _ => hGxLp.restrict Kk
    have hGyloc : MemLpLocOn Gy 2 Set.univ := fun Kk _ _ => hGyLp.restrict Kk
    -- the smooth approximants
    obtain ⟨R, hR⟩ := hχtsc.isBounded.subset_closedBall 0
    have hgs_all : ∀ n : ℕ, ∃ g : ℂ → ℂ, ContDiff ℝ 1 g ∧
        (∀ ζ ∈ Metric.closedBall 0 R, ‖g ζ - W ζ‖ ≤ 1 / (n + 1)) ∧
        (∫⁻ ζ in Metric.closedBall 0 R,
          GehringLehto.energyDensity (fun ξ => (fderiv ℝ g ξ) 1 - Gx ξ)
            (fun ξ => (fderiv ℝ g ξ) Complex.I - Gy ξ) ζ ∂volume)
          ≤ ENNReal.ofReal (1 / (n + 1)) :=
      fun n => GehringLehto.exists_smooth_approx_L2grad_local hWcont ⟨hWx, hWy⟩
        hGxloc hGyloc 0 R (by positivity)
    choose gs hgs_cd hgs_close hgs_energy using hgs_all
    -- geometry in the target plane and the glued extension of `ψ`
    set T : Set ℂ := w '' (φ '' K) with hTdef
    have hTc : IsCompact T := hKimgc.image_of_continuousOn (hwc.mono himgU)
    have hTV : T ⊆ V := by
      rintro u ⟨ζ, hζ, rfl⟩
      exact hmaps (himgU hζ)
    obtain ⟨rV, hrVpos, hrVsub⟩ := hTc.exists_cthickening_subset_open hV hTV
    set SV : Set ℂ := Metric.cthickening (rV / 2) T with hSVdef
    have hSVc : IsCompact SV := hTc.cthickening
    have hSVV : SV ⊆ V := (Metric.cthickening_mono (by linarith) T).trans hrVsub
    have hTSV : T ⊆ SV := Metric.self_subset_cthickening _
    obtain ⟨χψ, O₃, hχψsm, hχψcs, hχψts, hO₃o, hSVO₃, hχψone, hχψ0, hχψ1⟩ :=
      hcut SV V hSVc hV hSVV
    set ψt : ℂ → ℂ := fun u => χψ u • ψ u with hψtdef
    have hψt_sm : ContDiff ℝ ∞ ψt := by
      rw [contDiff_iff_contDiffAt]
      intro u
      by_cases hu : u ∈ V
      · have hψAtR : AnalyticAt ℝ ψ u :=
          @AnalyticAt.restrictScalars ℝ _ ℂ ℂ _ _ _ _ ℂ _ _ _ IsScalarTower.right _
            IsScalarTower.right _ _ (hψa u hu)
        exact (hχψsm.contDiffAt).smul hψAtR.contDiffAt
      · have hu' : u ∉ tsupport χψ := fun hmem => hu (hχψts hmem)
        have hev : ψt =ᶠ[nhds u] fun _ => (0 : ℂ) := by
          filter_upwards [(isClosed_tsupport χψ).isOpen_compl.mem_nhds hu'] with y hy
          change χψ y • ψ y = 0
          rw [image_eq_zero_of_notMem_tsupport hy]
          simp
        exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hev
    have hψt_cont : Continuous ψt := hψt_sm.continuous
    have hψt_cs : HasCompactSupport ψt := hχψcs.smul_right
    obtain ⟨Mψt, hMψt⟩ := hψt_cont.bounded_above_of_compact_support hψt_cs
    have hψt_eqO₃ : ∀ u ∈ O₃, ψt u = ψ u := by
      intro u hu
      change χψ u • ψ u = ψ u
      rw [hχψone u hu]
      exact one_smul ℝ (ψ u)
    have hψt_fd : ∀ u ∈ O₃, HasFDerivAt ψt (ContinuousLinearMap.mul ℝ ℂ (ψ' u)) u := by
      intro u hu
      have huV : u ∈ V := hχψts (subset_tsupport χψ (by
        rw [Function.mem_support, hχψone u hu]
        norm_num))
      apply (hψR u huV).congr_of_eventuallyEq
      filter_upwards [hO₃o.mem_nhds hu] with y hy
      exact hψt_eqO₃ y hy
    -- membership bookkeeping on `K`
    have hφzO₁ : ∀ z ∈ K, φ z ∈ O₁ := fun z hz => hKO₁ (Set.mem_image_of_mem φ hz)
    have hO₁sub : O₁ ⊆ Metric.closedBall 0 R := by
      intro ζ hζ
      apply hR
      apply subset_tsupport χ
      rw [Function.mem_support, hχone ζ hζ]
      norm_num
    have hwφT : ∀ z ∈ K, w (φ z) ∈ T :=
      fun z hz => Set.mem_image_of_mem w (Set.mem_image_of_mem φ hz)
    have hgs_at : ∀ n, ∀ z ∈ K, ‖gs n (φ z) - w (φ z)‖ ≤ 1 / (n + 1) := by
      intro n z hz
      have h1 := hgs_close n (φ z) (hO₁sub (hφzO₁ z hz))
      rwa [hWO₁ (φ z) (hφzO₁ z hz)] at h1
    -- the composite and the classical integration by parts
    set Fn : ℕ → ℂ → ℂ := fun n z => ψt (gs n (φ z)) with hFndef
    have hFn_cd : ∀ n, ContDiffOn ℝ 1 (Fn n) U := by
      intro n z hz
      have h1 : ContDiffAt ℝ 1 φ z :=
        (@AnalyticAt.restrictScalars ℝ _ ℂ ℂ _ _ _ _ ℂ _ _ _ IsScalarTower.right _
          IsScalarTower.right _ _ (hφa z hz)).contDiffAt
      have h2 : ContDiffAt ℝ 1 (gs n) (φ z) := (hgs_cd n).contDiffAt
      have h3 : ContDiffAt ℝ 1 ψt (gs n (φ z)) :=
        (hψt_sm.of_le (by exact_mod_cast le_top)).contDiffAt
      exact ((h3.comp z (h2.comp z h1)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun y => rfl))).contDiffWithinAt
    have hweak_n : ∀ n, ∫ z, ((fderiv ℝ φt z) v) • Fn n z
        = - ∫ z, φt z • ((fderiv ℝ (Fn n) z) v) :=
      fun n => HasWeakDirDeriv.of_contDiffOn hU (hFn_cd n) φt hφt hcs htsupp
    -- eventual membership of the approximants in the safety compact `SV`
    have h1n : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hSVmem : ∀ᶠ n in Filter.atTop, ∀ z ∈ K, gs n (φ z) ∈ SV := by
      filter_upwards [h1n.eventually (eventually_lt_nhds (show (0 : ℝ) < rV / 2 by linarith))]
        with n hn z hz
      rw [hSVdef]
      apply Metric.mem_cthickening_of_dist_le (gs n (φ z)) (w (φ z)) _ _ (hwφT z hz)
      rw [dist_eq_norm]
      exact (hgs_at n z hz).trans hn.le
    -- the chain rule for the composite at points of `K`
    have hchain : ∀ n, ∀ z ∈ K, gs n (φ z) ∈ SV →
        (fderiv ℝ (Fn n) z) v = ψ' (gs n (φ z))
          * (((v * φ' z).re : ℂ) * ((fderiv ℝ (gs n) (φ z)) 1)
            + ((v * φ' z).im : ℂ) * ((fderiv ℝ (gs n) (φ z)) Complex.I)) := by
      intro n z hz hmem
      have hzU : z ∈ U := hKU hz
      have hgd : DifferentiableAt ℝ (gs n) (φ z) :=
        ((hgs_cd n).differentiable one_ne_zero).differentiableAt
      have h1 : HasFDerivAt (fun x => gs n (φ x))
          ((fderiv ℝ (gs n) (φ z)).comp (ContinuousLinearMap.mul ℝ ℂ (φ' z))) z :=
        HasFDerivAt.comp z hgd.hasFDerivAt (hφR z hzU)
      have hψtz : HasFDerivAt ψt (ContinuousLinearMap.mul ℝ ℂ (ψ' (gs n (φ z))))
          (gs n (φ z)) := hψt_fd (gs n (φ z)) (hSVO₃ hmem)
      have h2 : HasFDerivAt (fun x => ψt (gs n (φ x)))
          ((ContinuousLinearMap.mul ℝ ℂ (ψ' (gs n (φ z)))).comp
            ((fderiv ℝ (gs n) (φ z)).comp (ContinuousLinearMap.mul ℝ ℂ (φ' z)))) z :=
        HasFDerivAt.comp (g := ψt) (f := fun x => gs n (φ x)) z hψtz h1
      have hFnz : fderiv ℝ (Fn n) z
          = (ContinuousLinearMap.mul ℝ ℂ (ψ' (gs n (φ z)))).comp
            ((fderiv ℝ (gs n) (φ z)).comp (ContinuousLinearMap.mul ℝ ℂ (φ' z))) := by
        rw [hFndef]
        exact h2.fderiv
      rw [hFnz]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply']
      congr 1
      have hdec : ∀ (L : ℂ →L[ℝ] ℂ) (a : ℂ),
          L a = (a.re : ℂ) * L 1 + (a.im : ℂ) * L Complex.I := by
        intro L a
        have h3 : a = a.re • (1 : ℂ) + a.im • Complex.I := by
          apply Complex.ext <;> simp
        conv_lhs => rw [h3]
        rw [map_add, map_smul, map_smul]
        simp only [Complex.real_smul]
      rw [hdec (fderiv ℝ (gs n) (φ z)) (φ' z * v), mul_comm (φ' z) v]
    -- the integrability engine
    have integ : ∀ (m : ℂ → ℝ), Continuous m → HasCompactSupport m → tsupport m ⊆ U →
        ∀ {h : ℂ → ℂ}, LocallyIntegrableOn h U → Integrable (fun z => m z • h z) volume := by
      intro m hm hcsm htsuppm h hh
      have hKm : IsCompact (tsupport m) := hcsm
      have hhon : IntegrableOn h (tsupport m) volume :=
        hh.integrableOn_compact_subset htsuppm hKm
      have hon : IntegrableOn (fun z => m z • h z) (tsupport m) volume :=
        hhon.continuousOn_smul hm.continuousOn hKm
      have hsupp : Function.support (fun z => m z • h z) ⊆ tsupport m := by
        intro z hz
        apply subset_tsupport m
        simp only [Function.mem_support] at hz ⊢
        intro hmz
        apply hz
        simp [hmz]
      exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
    have hFnfd_cont : ∀ n, ContinuousOn (fun z => (fderiv ℝ (Fn n) z) v) U := fun n =>
      ((hFn_cd n).continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
    have hJn_int : ∀ n, Integrable (fun z => φt z • ((fderiv ℝ (Fn n) z) v)) volume :=
      fun n => integ φt hφt.continuous hcs htsupp
        ((hFnfd_cont n).locallyIntegrableOn hU.measurableSet)
    -- bounds on the plateau data
    obtain ⟨Mψ', hMψ'⟩ := hSVc.exists_bound_of_continuousOn (hψ'cont.mono hSVV)
    obtain ⟨Mφt, hMφt⟩ := hφt.continuous.bounded_above_of_compact_support hcs
    have hKimg_meas : MeasurableSet (φ '' K) :=
      MeasurableSet.image_of_continuousOn_injOn hKmeas (hφcont.mono hKU) (hφinj.mono hKU)
    -- the `L²` gradient defects
    set Xn : ℕ → ℝ≥0∞ := fun n =>
      ∫⁻ ζ in φ '' K, ‖(fderiv ℝ (gs n) ζ) 1 - gx ζ‖ₑ ^ (2 : ℕ) ∂volume with hXndef
    set Yn : ℕ → ℝ≥0∞ := fun n =>
      ∫⁻ ζ in φ '' K, ‖(fderiv ℝ (gs n) ζ) Complex.I - gy ζ‖ₑ ^ (2 : ℕ) ∂volume with hYndef
    have himgball : φ '' K ⊆ Metric.closedBall 0 R := by
      intro ζ hζ
      exact hO₁sub (hKO₁ hζ)
    have hXYn_le : ∀ n, Xn n ≤ ENNReal.ofReal (1 / (n + 1))
        ∧ Yn n ≤ ENNReal.ofReal (1 / (n + 1)) := by
      intro n
      have hcore : ∀ ζ ∈ φ '' K,
          ‖(fderiv ℝ (gs n) ζ) 1 - gx ζ‖ₑ ^ (2 : ℕ)
            + ‖(fderiv ℝ (gs n) ζ) Complex.I - gy ζ‖ₑ ^ (2 : ℕ)
          = GehringLehto.energyDensity (fun ξ => (fderiv ℝ (gs n) ξ) 1 - Gx ξ)
              (fun ξ => (fderiv ℝ (gs n) ξ) Complex.I - Gy ξ) ζ := by
        intro ζ hζ
        have hζO₁ : ζ ∈ O₁ := hKO₁ hζ
        rw [GehringLehto.energyDensity, hGxO₁ ζ hζO₁, hGyO₁ ζ hζO₁]
        rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
      have hup : (∫⁻ ζ in φ '' K,
          GehringLehto.energyDensity (fun ξ => (fderiv ℝ (gs n) ξ) 1 - Gx ξ)
            (fun ξ => (fderiv ℝ (gs n) ξ) Complex.I - Gy ξ) ζ ∂volume)
          ≤ ENNReal.ofReal (1 / (n + 1)) :=
        le_trans (lintegral_mono_set himgball) (hgs_energy n)
      constructor
      · refine le_trans ?_ hup
        apply setLIntegral_mono' hKimg_meas
        intro ζ hζ
        rw [← hcore ζ hζ]
        exact le_self_add
      · refine le_trans ?_ hup
        apply setLIntegral_mono' hKimg_meas
        intro ζ hζ
        rw [← hcore ζ hζ]
        exact le_add_self
    have hofr0 : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds 0) := by
      have h2 := ENNReal.tendsto_ofReal h1n
      simpa using h2
    have hXn0 : Filter.Tendsto Xn Filter.atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hofr0
        (fun n => zero_le _) (fun n => (hXYn_le n).1)
    have hYn0 : Filter.Tendsto Yn Filter.atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hofr0
        (fun n => zero_le _) (fun n => (hXYn_le n).2)
    -- ==================== generic reduction and bound engines ====================
    have h0K : ∀ (F : ℂ → ℂ) (z : ℂ), z ∉ K → φt z • F z = 0 := by
      intro F z hz
      rw [image_eq_zero_of_notMem_tsupport hz]
      simp
    have hredK : ∀ (F : ℂ → ℂ),
        (∫⁻ z, ‖φt z • F z‖ₑ ∂volume) = ∫⁻ z in K, ‖φt z • F z‖ₑ ∂volume := by
      intro F
      rw [← lintegral_indicator hKmeas]
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, h0K F z hz]
        simp
    have hIntOn : ∀ (F : ℂ → ℂ), AEStronglyMeasurable F (volume.restrict K) →
        (∫⁻ z in K, ‖φt z • F z‖ₑ ∂volume) < ⊤ →
        Integrable (fun z => φt z • F z) volume := by
      intro F hasm hfin
      have heq : (fun z => φt z • F z) = K.indicator (fun z => φt z • F z) := by
        funext z
        by_cases hz : z ∈ K
        · rw [Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz, h0K F z hz]
      rw [heq]
      apply MeasureTheory.IntegrableOn.integrable_indicator _ hKmeas
      constructor
      · exact (hφt.continuous.aestronglyMeasurable.restrict).smul hasm
      · rw [hasFiniteIntegral_iff_enorm]
        exact hfin
    have henorm_smul_le : ∀ (r : ℝ) (x : ℂ), ‖r • x‖ₑ ≤ ‖r‖ₑ * ‖x‖ₑ := by
      intro r x
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm (a := x),
        ← ofReal_norm_eq_enorm (a := r), ← ENNReal.ofReal_mul (norm_nonneg r)]
      exact ENNReal.ofReal_le_ofReal (norm_smul_le r x)
    have hMφt0 : (0 : ℝ) ≤ Mφt := le_trans (norm_nonneg _) (hMφt 0)
    have hkey_pt : ∀ (a x y : ℂ) (z : ℂ),
        ‖φt z • (a * (((v * φ' z).re : ℂ) * x + ((v * φ' z).im : ℂ) * y))‖ₑ
        ≤ ENNReal.ofReal Mφt * (‖a‖ₑ * (‖v‖ₑ * ((‖x‖ₑ + ‖y‖ₑ) * ‖φ' z‖ₑ))) := by
      intro a x y z
      refine le_trans (henorm_smul_le _ _) ?_
      have h1 : ‖φt z‖ₑ ≤ ENNReal.ofReal Mφt := by
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hMφt z)
      refine mul_le_mul' h1 ?_
      refine le_trans (habs2 a x y (v * φ' z)) ?_
      rw [enorm_mul]
      apply le_of_eq
      ring
    -- measurability data on `K`
    have hgxφ_asm : AEStronglyMeasurable (fun z => gx (φ z)) (volume.restrict K) :=
      hASMcomp K hKc hKU gx (hgx (φ '' K) himgU hKimgc).1
    have hgyφ_asm : AEStronglyMeasurable (fun z => gy (φ z)) (volume.restrict K) :=
      hASMcomp K hKc hKU gy (hgy (φ '' K) himgU hKimgc).1
    have hφ'ae : AEMeasurable φ' (volume.restrict K) :=
      (hφ'cont.mono hKU).aemeasurable hKmeas
    -- the weighted `L¹` engine over `K`
    have hL1 : ∀ (q1 q2 : ℂ → ℂ),
        AEStronglyMeasurable (fun z => q1 (φ z)) (volume.restrict K) →
        AEStronglyMeasurable (fun z => q2 (φ z)) (volume.restrict K) →
        (∫⁻ z in K, (‖q1 (φ z)‖ₑ + ‖q2 (φ z)‖ₑ) * ‖φ' z‖ₑ ∂volume)
          ≤ ((∫⁻ ζ in φ '' K, ‖q1 ζ‖ₑ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ)
              + (∫⁻ ζ in φ '' K, ‖q2 ζ‖ₑ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ))
            * (volume K) ^ (1 / 2 : ℝ) := by
      intro q1 q2 h1 h2
      have haem1 : AEMeasurable (fun z => ‖q1 (φ z)‖ₑ * ‖φ' z‖ₑ) (volume.restrict K) :=
        h1.aemeasurable.enorm.mul hφ'ae.enorm
      calc (∫⁻ z in K, (‖q1 (φ z)‖ₑ + ‖q2 (φ z)‖ₑ) * ‖φ' z‖ₑ ∂volume)
          = ∫⁻ z in K, (‖q1 (φ z)‖ₑ * ‖φ' z‖ₑ + ‖q2 (φ z)‖ₑ * ‖φ' z‖ₑ) ∂volume := by
            apply lintegral_congr
            intro z
            ring
        _ = (∫⁻ z in K, ‖q1 (φ z)‖ₑ * ‖φ' z‖ₑ ∂volume)
            + ∫⁻ z in K, ‖q2 (φ z)‖ₑ * ‖φ' z‖ₑ ∂volume := lintegral_add_left' haem1 _
        _ ≤ ((∫⁻ ζ in φ '' K, ‖q1 ζ‖ₑ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ))
              * (volume K) ^ (1 / 2 : ℝ)
            + ((∫⁻ ζ in φ '' K, ‖q2 ζ‖ₑ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ))
              * (volume K) ^ (1 / 2 : ℝ) :=
            add_le_add (hCS K hKc hKU q1 h1) (hCS K hKc hKU q2 h2)
        _ = ((∫⁻ ζ in φ '' K, ‖q1 ζ‖ₑ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ)
              + (∫⁻ ζ in φ '' K, ‖q2 ζ‖ₑ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ))
            * (volume K) ^ (1 / 2 : ℝ) := (add_mul _ _ _).symm
    have hgfin : ∀ (q0 : ℂ → ℂ), MemLpLocOn q0 2 (φ '' U) →
        ((∫⁻ ζ in φ '' K, ‖q0 ζ‖ₑ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ)) < ⊤ :=
      fun q0 hq0 => ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (p_fin (hq0 (φ '' K) himgU hKimgc)).ne
    have hvolK : ((volume K) ^ (1 / 2 : ℝ)) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hKc.measure_lt_top.ne
    have hC2fin : (∫⁻ z in K, (‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ) * ‖φ' z‖ₑ ∂volume) < ⊤ :=
      lt_of_le_of_lt (hL1 gx gy hgxφ_asm hgyφ_asm)
        (ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr ⟨hgfin gx hgx, hgfin gy hgy⟩) hvolK)
    -- the pieces of the split
    set B0 : ℂ → ℂ := fun z =>
      ((v * φ' z).re : ℂ) * gx (φ z) + ((v * φ' z).im : ℂ) * gy (φ z) with hB0def
    have hB0z : ∀ z, B0 z
        = ((v * φ' z).re : ℂ) * gx (φ z) + ((v * φ' z).im : ℂ) * gy (φ z) := fun z => rfl
    have hDz : ∀ z, D z = ψ' (w (φ z)) * B0 z := fun z => rfl
    have hB0asm : AEStronglyMeasurable B0 (volume.restrict K) := by
      obtain ⟨hre, him⟩ := hvφ'_cont K hKU
      exact ((hre.aestronglyMeasurable hKmeas).mul hgxφ_asm).add
        ((him.aestronglyMeasurable hKmeas).mul hgyφ_asm)
    -- integrability of the limit integrand
    obtain ⟨Mψw, hMψw⟩ := hKc.exists_bound_of_continuousOn (hψwφ_cont K hKU)
    have hDfin : (∫⁻ z in K, ‖φt z • D z‖ₑ ∂volume) < ⊤ := by
      have hpt : ∀ z ∈ K, ‖φt z • D z‖ₑ
          ≤ (ENNReal.ofReal Mφt * ENNReal.ofReal Mψw * ‖v‖ₑ)
            * ((‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ) * ‖φ' z‖ₑ) := by
        intro z hz
        rw [hDz z, hB0z z]
        refine le_trans (hkey_pt _ _ _ z) ?_
        rw [show (ENNReal.ofReal Mφt * ENNReal.ofReal Mψw * ‖v‖ₑ)
            * ((‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ) * ‖φ' z‖ₑ)
            = ENNReal.ofReal Mφt * (ENNReal.ofReal Mψw
              * (‖v‖ₑ * ((‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ) * ‖φ' z‖ₑ))) from by ring]
        gcongr
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hMψw z hz)
      calc (∫⁻ z in K, ‖φt z • D z‖ₑ ∂volume)
          ≤ ∫⁻ z in K, (ENNReal.ofReal Mφt * ENNReal.ofReal Mψw * ‖v‖ₑ)
            * ((‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ) * ‖φ' z‖ₑ) ∂volume :=
            setLIntegral_mono' hKmeas hpt
        _ = (ENNReal.ofReal Mφt * ENNReal.ofReal Mψw * ‖v‖ₑ)
            * ∫⁻ z in K, (‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ) * ‖φ' z‖ₑ ∂volume := by
            rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) enorm_ne_top)]
        _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) enorm_lt_top)
            hC2fin
    have hJ_int : Integrable (fun z => φt z • D z) volume :=
      hIntOn D (hDasm K hKc hKU) hDfin
    -- the split pieces `An` and `Bn`
    set An : ℕ → ℂ := fun n => ∫ z, φt z • (ψ' (gs n (φ z))
      * (((v * φ' z).re : ℂ) * ((fderiv ℝ (gs n) (φ z)) 1 - gx (φ z))
        + ((v * φ' z).im : ℂ) * ((fderiv ℝ (gs n) (φ z)) Complex.I - gy (φ z)))) with hAndef
    set Bn : ℕ → ℂ := fun n => ∫ z, φt z •
      ((ψ' (gs n (φ z)) - ψ' (w (φ z))) * B0 z) with hBndef
    -- continuity/measurability of the `n`-th pieces under the membership hypothesis
    have hψgs_cont : ∀ n, (∀ z ∈ K, gs n (φ z) ∈ SV) →
        ContinuousOn (fun z => ψ' (gs n (φ z))) K := by
      intro n hmemn
      have h1 : ContinuousOn (fun z => gs n (φ z)) K :=
        (hgs_cd n).continuous.comp_continuousOn (hφcont.mono hKU)
      exact hψ'cont.comp h1 (fun z hz => hSVV (hmemn z hz))
    have hΔx_asm : ∀ n, AEStronglyMeasurable
        (fun z => (fderiv ℝ (gs n) (φ z)) 1 - gx (φ z)) (volume.restrict K) := by
      intro n
      have h1 : ContinuousOn (fun z => (fderiv ℝ (gs n) (φ z)) 1) K :=
        (((hgs_cd n).continuous_fderiv one_ne_zero).clm_apply
          continuous_const).comp_continuousOn (hφcont.mono hKU)
      exact (h1.aestronglyMeasurable hKmeas).sub hgxφ_asm
    have hΔy_asm : ∀ n, AEStronglyMeasurable
        (fun z => (fderiv ℝ (gs n) (φ z)) Complex.I - gy (φ z)) (volume.restrict K) := by
      intro n
      have h1 : ContinuousOn (fun z => (fderiv ℝ (gs n) (φ z)) Complex.I) K :=
        (((hgs_cd n).continuous_fderiv one_ne_zero).clm_apply
          continuous_const).comp_continuousOn (hφcont.mono hKU)
      exact (h1.aestronglyMeasurable hKmeas).sub hgyφ_asm
    -- the uniform bound for the `An` piece
    have hAbound : ∀ n, (∀ z ∈ K, gs n (φ z) ∈ SV) →
        (∫⁻ z in K, ‖φt z • (ψ' (gs n (φ z))
          * (((v * φ' z).re : ℂ) * ((fderiv ℝ (gs n) (φ z)) 1 - gx (φ z))
            + ((v * φ' z).im : ℂ) * ((fderiv ℝ (gs n) (φ z)) Complex.I - gy (φ z))))‖ₑ
          ∂volume)
        ≤ (ENNReal.ofReal Mφt * ENNReal.ofReal Mψ' * ‖v‖ₑ)
          * (((Xn n) ^ (1 / 2 : ℝ) + (Yn n) ^ (1 / 2 : ℝ)) * (volume K) ^ (1 / 2 : ℝ)) := by
      intro n hmemn
      have hpt : ∀ z ∈ K, ‖φt z • (ψ' (gs n (φ z))
          * (((v * φ' z).re : ℂ) * ((fderiv ℝ (gs n) (φ z)) 1 - gx (φ z))
            + ((v * φ' z).im : ℂ) * ((fderiv ℝ (gs n) (φ z)) Complex.I - gy (φ z))))‖ₑ
          ≤ (ENNReal.ofReal Mφt * ENNReal.ofReal Mψ' * ‖v‖ₑ)
            * ((‖(fderiv ℝ (gs n) (φ z)) 1 - gx (φ z)‖ₑ
              + ‖(fderiv ℝ (gs n) (φ z)) Complex.I - gy (φ z)‖ₑ) * ‖φ' z‖ₑ) := by
        intro z hz
        refine le_trans (hkey_pt _ _ _ z) ?_
        rw [show (ENNReal.ofReal Mφt * ENNReal.ofReal Mψ' * ‖v‖ₑ)
            * ((‖(fderiv ℝ (gs n) (φ z)) 1 - gx (φ z)‖ₑ
              + ‖(fderiv ℝ (gs n) (φ z)) Complex.I - gy (φ z)‖ₑ) * ‖φ' z‖ₑ)
            = ENNReal.ofReal Mφt * (ENNReal.ofReal Mψ'
              * (‖v‖ₑ * ((‖(fderiv ℝ (gs n) (φ z)) 1 - gx (φ z)‖ₑ
                + ‖(fderiv ℝ (gs n) (φ z)) Complex.I - gy (φ z)‖ₑ) * ‖φ' z‖ₑ)))
            from by ring]
        gcongr
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hMψ' _ (hmemn z hz))
      calc (∫⁻ z in K, ‖φt z • (ψ' (gs n (φ z))
            * (((v * φ' z).re : ℂ) * ((fderiv ℝ (gs n) (φ z)) 1 - gx (φ z))
              + ((v * φ' z).im : ℂ)
                * ((fderiv ℝ (gs n) (φ z)) Complex.I - gy (φ z))))‖ₑ ∂volume)
          ≤ ∫⁻ z in K, (ENNReal.ofReal Mφt * ENNReal.ofReal Mψ' * ‖v‖ₑ)
            * ((‖(fderiv ℝ (gs n) (φ z)) 1 - gx (φ z)‖ₑ
              + ‖(fderiv ℝ (gs n) (φ z)) Complex.I - gy (φ z)‖ₑ) * ‖φ' z‖ₑ) ∂volume :=
            setLIntegral_mono' hKmeas hpt
        _ = (ENNReal.ofReal Mφt * ENNReal.ofReal Mψ' * ‖v‖ₑ)
            * ∫⁻ z in K, (‖(fderiv ℝ (gs n) (φ z)) 1 - gx (φ z)‖ₑ
              + ‖(fderiv ℝ (gs n) (φ z)) Complex.I - gy (φ z)‖ₑ) * ‖φ' z‖ₑ ∂volume := by
            rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) enorm_ne_top)]
        _ ≤ (ENNReal.ofReal Mφt * ENNReal.ofReal Mψ' * ‖v‖ₑ)
            * (((Xn n) ^ (1 / 2 : ℝ) + (Yn n) ^ (1 / 2 : ℝ))
              * (volume K) ^ (1 / 2 : ℝ)) := by
            exact mul_le_mul' le_rfl (hL1 _ _ (hΔx_asm n) (hΔy_asm n))
    -- integrability of the `n`-th pieces
    have hAn_int : ∀ n, (∀ z ∈ K, gs n (φ z) ∈ SV) →
        Integrable (fun z => φt z • (ψ' (gs n (φ z))
          * (((v * φ' z).re : ℂ) * ((fderiv ℝ (gs n) (φ z)) 1 - gx (φ z))
            + ((v * φ' z).im : ℂ)
              * ((fderiv ℝ (gs n) (φ z)) Complex.I - gy (φ z))))) volume := by
      intro n hmemn
      apply hIntOn
      · obtain ⟨hre, him⟩ := hvφ'_cont K hKU
        exact (((hψgs_cont n hmemn).aestronglyMeasurable hKmeas)).mul
          (((hre.aestronglyMeasurable hKmeas).mul (hΔx_asm n)).add
            ((him.aestronglyMeasurable hKmeas).mul (hΔy_asm n)))
      · refine lt_of_le_of_lt (hAbound n hmemn) ?_
        apply ENNReal.mul_lt_top
        · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            ENNReal.ofReal_lt_top) enorm_lt_top
        · apply ENNReal.mul_lt_top _ hvolK
          apply ENNReal.add_lt_top.mpr
          constructor
          · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
              (lt_of_le_of_lt ((hXYn_le n).1) ENNReal.ofReal_lt_top).ne
          · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
              (lt_of_le_of_lt ((hXYn_le n).2) ENNReal.ofReal_lt_top).ne
    have hBn_int : ∀ n, (∀ z ∈ K, gs n (φ z) ∈ SV) →
        Integrable (fun z => φt z •
          ((ψ' (gs n (φ z)) - ψ' (w (φ z))) * B0 z)) volume := by
      intro n hmemn
      apply hIntOn
      · exact (((hψgs_cont n hmemn).aestronglyMeasurable hKmeas).sub
          ((hψwφ_cont K hKU).aestronglyMeasurable hKmeas)).mul hB0asm
      · have hpt : ∀ z ∈ K, ‖φt z • ((ψ' (gs n (φ z)) - ψ' (w (φ z))) * B0 z)‖ₑ
            ≤ (ENNReal.ofReal Mφt * ENNReal.ofReal (Mψ' + Mψw) * ‖v‖ₑ)
              * ((‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ) * ‖φ' z‖ₑ) := by
          intro z hz
          rw [hB0z z]
          refine le_trans (hkey_pt _ _ _ z) ?_
          rw [show (ENNReal.ofReal Mφt * ENNReal.ofReal (Mψ' + Mψw) * ‖v‖ₑ)
              * ((‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ) * ‖φ' z‖ₑ)
              = ENNReal.ofReal Mφt * (ENNReal.ofReal (Mψ' + Mψw)
                * (‖v‖ₑ * ((‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ) * ‖φ' z‖ₑ))) from by ring]
          gcongr
          rw [← ofReal_norm_eq_enorm]
          apply ENNReal.ofReal_le_ofReal
          calc ‖ψ' (gs n (φ z)) - ψ' (w (φ z))‖
              ≤ ‖ψ' (gs n (φ z))‖ + ‖ψ' (w (φ z))‖ := norm_sub_le _ _
            _ ≤ Mψ' + Mψw := add_le_add (hMψ' _ (hmemn z hz)) (hMψw z hz)
        calc (∫⁻ z in K, ‖φt z • ((ψ' (gs n (φ z)) - ψ' (w (φ z))) * B0 z)‖ₑ ∂volume)
            ≤ ∫⁻ z in K, (ENNReal.ofReal Mφt * ENNReal.ofReal (Mψ' + Mψw) * ‖v‖ₑ)
              * ((‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ) * ‖φ' z‖ₑ) ∂volume :=
              setLIntegral_mono' hKmeas hpt
          _ = (ENNReal.ofReal Mφt * ENNReal.ofReal (Mψ' + Mψw) * ‖v‖ₑ)
              * ∫⁻ z in K, (‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ) * ‖φ' z‖ₑ ∂volume := by
              rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top
                (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
                enorm_ne_top)]
          _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top
              ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) enorm_lt_top) hC2fin
    -- ==================== `An → 0` ====================
    have hAn0 : Filter.Tendsto An Filter.atTop (nhds 0) := by
      have henormA : ∀ᶠ n in Filter.atTop, ‖An n‖ₑ
          ≤ (ENNReal.ofReal Mφt * ENNReal.ofReal Mψ' * ‖v‖ₑ)
            * (((Xn n) ^ (1 / 2 : ℝ) + (Yn n) ^ (1 / 2 : ℝ))
              * (volume K) ^ (1 / 2 : ℝ)) := by
        filter_upwards [hSVmem] with n hmemn
        rw [hAndef]
        refine le_trans (MeasureTheory.enorm_integral_le_lintegral_enorm _) ?_
        rw [hredK]
        exact hAbound n hmemn
      have hbndA : Filter.Tendsto (fun n =>
          (ENNReal.ofReal Mφt * ENNReal.ofReal Mψ' * ‖v‖ₑ)
            * (((Xn n) ^ (1 / 2 : ℝ) + (Yn n) ^ (1 / 2 : ℝ))
              * (volume K) ^ (1 / 2 : ℝ))) Filter.atTop (nhds 0) := by
        have hrp0 : ((0 : ℝ≥0∞)) ^ (1 / 2 : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
        have hXr : Filter.Tendsto (fun n => (Xn n) ^ (1 / 2 : ℝ)) Filter.atTop (nhds 0) := by
          have hc := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto (0 : ℝ≥0∞)
          have h2 := hc.comp hXn0
          rw [hrp0] at h2
          simpa [Function.comp] using h2
        have hYr : Filter.Tendsto (fun n => (Yn n) ^ (1 / 2 : ℝ)) Filter.atTop (nhds 0) := by
          have hc := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto (0 : ℝ≥0∞)
          have h2 := hc.comp hYn0
          rw [hrp0] at h2
          simpa [Function.comp] using h2
        have h3 : Filter.Tendsto (fun n => (Xn n) ^ (1 / 2 : ℝ) + (Yn n) ^ (1 / 2 : ℝ))
            Filter.atTop (nhds 0) := by
          have h3' := hXr.add hYr
          simpa using h3'
        have hsum : Filter.Tendsto (fun n =>
            ((Xn n) ^ (1 / 2 : ℝ) + (Yn n) ^ (1 / 2 : ℝ)) * (volume K) ^ (1 / 2 : ℝ))
            Filter.atTop (nhds 0) := by
          have h4 := ENNReal.Tendsto.mul_const h3 (Or.inr hvolK.ne)
          simpa using h4
        have h5 : Filter.Tendsto (fun n =>
            (ENNReal.ofReal Mφt * ENNReal.ofReal Mψ' * ‖v‖ₑ)
              * (((Xn n) ^ (1 / 2 : ℝ) + (Yn n) ^ (1 / 2 : ℝ))
                * (volume K) ^ (1 / 2 : ℝ))) Filter.atTop
            (nhds ((ENNReal.ofReal Mφt * ENNReal.ofReal Mψ' * ‖v‖ₑ) * 0)) :=
          ENNReal.Tendsto.const_mul hsum
            (Or.inr (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
              ENNReal.ofReal_ne_top) enorm_ne_top))
        simpa using h5
      have henormA0 : Filter.Tendsto (fun n => ‖An n‖ₑ) Filter.atTop (nhds 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbndA
          (Filter.Eventually.of_forall (fun n => zero_le _)) henormA
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h1 : Filter.Tendsto (fun n => (‖An n‖ₑ).toReal) Filter.atTop
          (nhds ((0 : ℝ≥0∞)).toReal) := (ENNReal.tendsto_toReal (by simp)).comp henormA0
      simpa [toReal_enorm] using h1
    -- ==================== `Bn → 0` ====================
    have hBn0 : Filter.Tendsto Bn Filter.atTop (nhds 0) := by
      have hres : Filter.Tendsto Bn Filter.atTop (nhds (∫ _ : ℂ, (0 : ℂ))) := by
        rw [hBndef]
        apply tendsto_integral_filter_of_dominated_convergence
          (K.indicator (fun z => Mφt * ((Mψ' + Mψw)
            * (‖v‖ * ‖φ' z‖ * (‖gx (φ z)‖ + ‖gy (φ z)‖)))))
        · filter_upwards [hSVmem] with n hmemn
          have heq : (fun z => φt z • ((ψ' (gs n (φ z)) - ψ' (w (φ z))) * B0 z))
              = K.indicator (fun z => φt z • ((ψ' (gs n (φ z)) - ψ' (w (φ z))) * B0 z)) := by
            funext z
            by_cases hz : z ∈ K
            · rw [Set.indicator_of_mem hz]
            · rw [Set.indicator_of_notMem hz]
              exact h0K (fun z => (ψ' (gs n (φ z)) - ψ' (w (φ z))) * B0 z) z hz
          rw [heq, aestronglyMeasurable_indicator_iff hKmeas]
          exact (hφt.continuous.aestronglyMeasurable.restrict).smul
            ((((hψgs_cont n hmemn).aestronglyMeasurable hKmeas).sub
              ((hψwφ_cont K hKU).aestronglyMeasurable hKmeas)).mul hB0asm)
        · filter_upwards [hSVmem] with n hmemn
          apply Filter.Eventually.of_forall
          intro z
          by_cases hz : z ∈ K
          · rw [Set.indicator_of_mem hz]
            calc ‖φt z • ((ψ' (gs n (φ z)) - ψ' (w (φ z))) * B0 z)‖
                = ‖φt z‖ * (‖ψ' (gs n (φ z)) - ψ' (w (φ z))‖ * ‖B0 z‖) := by
                  rw [norm_smul, norm_mul]
              _ ≤ Mφt * ((Mψ' + Mψw) * (‖v‖ * ‖φ' z‖ * (‖gx (φ z)‖ + ‖gy (φ z)‖))) := by
                  have hMψ'0 : (0 : ℝ) ≤ Mψ' :=
                    le_trans (norm_nonneg _) (hMψ' _ (hTSV (hwφT z hz)))
                  have h1 : ‖ψ' (gs n (φ z)) - ψ' (w (φ z))‖ ≤ Mψ' + Mψw :=
                    le_trans (norm_sub_le _ _)
                      (add_le_add (hMψ' _ (hmemn z hz)) (hMψw z hz))
                  have h2 : ‖B0 z‖ ≤ ‖v‖ * ‖φ' z‖ * (‖gx (φ z)‖ + ‖gy (φ z)‖) := by
                    rw [hB0z z]
                    calc ‖((v * φ' z).re : ℂ) * gx (φ z)
                          + ((v * φ' z).im : ℂ) * gy (φ z)‖
                        ≤ ‖((v * φ' z).re : ℂ) * gx (φ z)‖
                          + ‖((v * φ' z).im : ℂ) * gy (φ z)‖ := norm_add_le _ _
                      _ ≤ ‖v * φ' z‖ * ‖gx (φ z)‖ + ‖v * φ' z‖ * ‖gy (φ z)‖ := by
                          apply add_le_add
                          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
                            exact mul_le_mul_of_nonneg_right
                              (Complex.abs_re_le_norm _) (norm_nonneg _)
                          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
                            exact mul_le_mul_of_nonneg_right
                              (Complex.abs_im_le_norm _) (norm_nonneg _)
                      _ = ‖v‖ * ‖φ' z‖ * (‖gx (φ z)‖ + ‖gy (φ z)‖) := by
                          rw [norm_mul]
                          ring
                  have hmid : ‖ψ' (gs n (φ z)) - ψ' (w (φ z))‖ * ‖B0 z‖
                      ≤ (Mψ' + Mψw) * (‖v‖ * ‖φ' z‖ * (‖gx (φ z)‖ + ‖gy (φ z)‖)) :=
                    mul_le_mul h1 h2 (norm_nonneg _)
                      (add_nonneg hMψ'0 (le_trans (norm_nonneg _) (hMψw z hz)))
                  exact mul_le_mul (hMφt z) hmid (by positivity) hMφt0
          · rw [Set.indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport hz]
            simp
        · apply MeasureTheory.IntegrableOn.integrable_indicator _ hKmeas
          constructor
          · apply AEStronglyMeasurable.const_mul
            apply AEStronglyMeasurable.const_mul
            apply AEStronglyMeasurable.mul
            · exact (continuousOn_const.mul
                ((hφ'cont.mono hKU).norm)).aestronglyMeasurable hKmeas
            · exact (hgxφ_asm.norm).add (hgyφ_asm.norm)
          · rw [hasFiniteIntegral_iff_enorm]
            have hpt : ∀ z : ℂ, ‖Mφt * ((Mψ' + Mψw)
                * (‖v‖ * ‖φ' z‖ * (‖gx (φ z)‖ + ‖gy (φ z)‖)))‖ₑ
                = (‖Mφt‖ₑ * ‖Mψ' + Mψw‖ₑ * ‖v‖ₑ)
                  * ((‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ) * ‖φ' z‖ₑ) := by
              intro z
              rw [enorm_mul, enorm_mul, enorm_mul, enorm_mul, enorm_norm, enorm_norm]
              rw [show ‖(‖gx (φ z)‖ + ‖gy (φ z)‖ : ℝ)‖ₑ
                  = ‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ from by
                rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (by positivity),
                  ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
                  ofReal_norm_eq_enorm, ofReal_norm_eq_enorm]]
              ring
            calc (∫⁻ z, ‖Mφt * ((Mψ' + Mψw)
                  * (‖v‖ * ‖φ' z‖ * (‖gx (φ z)‖ + ‖gy (φ z)‖)))‖ₑ
                  ∂(volume.restrict K))
                = ∫⁻ z in K, (‖Mφt‖ₑ * ‖Mψ' + Mψw‖ₑ * ‖v‖ₑ)
                  * ((‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ) * ‖φ' z‖ₑ) ∂volume :=
                  lintegral_congr (fun z => hpt z)
              _ = (‖Mφt‖ₑ * ‖Mψ' + Mψw‖ₑ * ‖v‖ₑ)
                  * ∫⁻ z in K, (‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ) * ‖φ' z‖ₑ ∂volume := by
                  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top
                    (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top) enorm_ne_top)]
              _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top
                  (ENNReal.mul_lt_top enorm_lt_top enorm_lt_top) enorm_lt_top) hC2fin
        · apply Filter.Eventually.of_forall
          intro z
          by_cases hz : z ∈ K
          · have hgz : Filter.Tendsto (fun n => gs n (φ z)) Filter.atTop
                (nhds (w (φ z))) := by
              rw [← tendsto_sub_nhds_zero_iff]
              exact squeeze_zero_norm (fun n => hgs_at n z hz) h1n
            have hψ'c : ContinuousAt ψ' (w (φ z)) :=
              hψ'cont.continuousAt (hV.mem_nhds (hmaps (himgU (Set.mem_image_of_mem φ hz))))
            have h2 : Filter.Tendsto (fun n => ψ' (gs n (φ z)) - ψ' (w (φ z)))
                Filter.atTop (nhds 0) := by
              have h3 := (hψ'c.tendsto.comp hgz).sub_const (ψ' (w (φ z)))
              simpa using h3
            have h4 := ((h2.mul_const (B0 z)).const_smul (φt z))
            simpa using h4
          · have hzero : ∀ n : ℕ, φt z • ((ψ' (gs n (φ z)) - ψ' (w (φ z))) * B0 z)
                = (0 : ℂ) := fun n =>
              h0K (fun z => (ψ' (gs n (φ z)) - ψ' (w (φ z))) * B0 z) z hz
            apply Filter.Tendsto.congr (fun n => (hzero n).symm)
            exact tendsto_const_nhds
      simpa using hres
    -- ==================== the split identity and the limit of `Jn` ====================
    set J : ℂ := ∫ z, φt z • D z with hJdef
    set Jn : ℕ → ℂ := fun n => ∫ z, φt z • ((fderiv ℝ (Fn n) z) v) with hJndef
    have hsplit : ∀ᶠ n in Filter.atTop, Jn n = An n + (Bn n + J) := by
      filter_upwards [hSVmem] with n hmemn
      have hint_id : ∀ z, φt z • ((fderiv ℝ (Fn n) z) v)
          = φt z • (ψ' (gs n (φ z))
              * (((v * φ' z).re : ℂ) * ((fderiv ℝ (gs n) (φ z)) 1 - gx (φ z))
                + ((v * φ' z).im : ℂ) * ((fderiv ℝ (gs n) (φ z)) Complex.I - gy (φ z))))
            + (φt z • ((ψ' (gs n (φ z)) - ψ' (w (φ z))) * B0 z) + φt z • D z) := by
        intro z
        by_cases hz : z ∈ K
        · have hid : (fderiv ℝ (Fn n) z) v
              = ψ' (gs n (φ z))
                * (((v * φ' z).re : ℂ) * ((fderiv ℝ (gs n) (φ z)) 1 - gx (φ z))
                  + ((v * φ' z).im : ℂ) * ((fderiv ℝ (gs n) (φ z)) Complex.I - gy (φ z)))
              + ((ψ' (gs n (φ z)) - ψ' (w (φ z))) * B0 z + D z) := by
            rw [hchain n z hz (hmemn z hz), hDz z, hB0z z]
            ring
          rw [hid]
          module
        · rw [image_eq_zero_of_notMem_tsupport hz]
          simp
      have hBD : Integrable (fun z => φt z • ((ψ' (gs n (φ z)) - ψ' (w (φ z))) * B0 z)
          + φt z • D z) volume := (hBn_int n hmemn).add hJ_int
      have e1 : (∫ z, φt z • ((fderiv ℝ (Fn n) z) v))
          = ∫ z, (φt z • (ψ' (gs n (φ z))
              * (((v * φ' z).re : ℂ) * ((fderiv ℝ (gs n) (φ z)) 1 - gx (φ z))
                + ((v * φ' z).im : ℂ) * ((fderiv ℝ (gs n) (φ z)) Complex.I - gy (φ z))))
            + (φt z • ((ψ' (gs n (φ z)) - ψ' (w (φ z))) * B0 z) + φt z • D z)) :=
        integral_congr_ae (Filter.Eventually.of_forall hint_id)
      have e2 : (∫ z, (φt z • (ψ' (gs n (φ z))
              * (((v * φ' z).re : ℂ) * ((fderiv ℝ (gs n) (φ z)) 1 - gx (φ z))
                + ((v * φ' z).im : ℂ) * ((fderiv ℝ (gs n) (φ z)) Complex.I - gy (φ z))))
            + (φt z • ((ψ' (gs n (φ z)) - ψ' (w (φ z))) * B0 z) + φt z • D z)))
          = (∫ z, φt z • (ψ' (gs n (φ z))
              * (((v * φ' z).re : ℂ) * ((fderiv ℝ (gs n) (φ z)) 1 - gx (φ z))
                + ((v * φ' z).im : ℂ) * ((fderiv ℝ (gs n) (φ z)) Complex.I - gy (φ z)))))
            + ∫ z, (φt z • ((ψ' (gs n (φ z)) - ψ' (w (φ z))) * B0 z) + φt z • D z) :=
        integral_add (hAn_int n hmemn) hBD
      have e3 : (∫ z, (φt z • ((ψ' (gs n (φ z)) - ψ' (w (φ z))) * B0 z) + φt z • D z))
          = (∫ z, φt z • ((ψ' (gs n (φ z)) - ψ' (w (φ z))) * B0 z)) + ∫ z, φt z • D z :=
        integral_add (hBn_int n hmemn) hJ_int
      rw [hJndef, hAndef, hBndef, hJdef]
      simp only
      rw [e1, e2, e3]
    have hJn_tendsto : Filter.Tendsto Jn Filter.atTop (nhds J) := by
      have hlim : Filter.Tendsto (fun n => An n + (Bn n + J)) Filter.atTop
          (nhds (0 + (0 + J))) := hAn0.add (hBn0.add tendsto_const_nhds)
      have heq : (fun n => An n + (Bn n + J)) =ᶠ[Filter.atTop] Jn := by
        filter_upwards [hsplit] with n hn
        exact hn.symm
      have h2 := hlim.congr' heq
      simpa using h2
    -- ==================== the left-hand side ====================
    have hLHS : Filter.Tendsto (fun n => ∫ z, ((fderiv ℝ φt z) v) • Fn n z)
        Filter.atTop (nhds (∫ z, ((fderiv ℝ φt z) v) • f z)) := by
      have hcont_dφt : Continuous (fun z => (fderiv ℝ φt z) v) :=
        (hφt.continuous_fderiv (by norm_num)).clm_apply continuous_const
      have hts_dφt : tsupport (fun z => (fderiv ℝ φt z) v) ⊆ K :=
        tsupport_fderiv_apply_subset ℝ v
      have hMψt0 : (0 : ℝ) ≤ Mψt := le_trans (norm_nonneg _) (hMψt 0)
      apply MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun z => ‖(fderiv ℝ φt z) v‖ * Mψt)
      · intro n
        have hcontn : Continuous (fun z => ((fderiv ℝ φt z) v) • Fn n z) := by
          rw [continuous_iff_continuousAt]
          intro z
          by_cases hz : z ∈ U
          · apply (hcont_dφt.continuousAt).smul
            have h1 : ContinuousAt (fun x => gs n (φ x)) z :=
              ((hgs_cd n).continuous.continuousAt).comp
                ((hφcont.continuousAt (hU.mem_nhds hz)))
            exact (hψt_cont.continuousAt).comp h1
          · have hznot : z ∉ tsupport (fun z => (fderiv ℝ φt z) v) :=
              fun hmem => hz (hKU (hts_dφt hmem))
            have hev : (fun z => ((fderiv ℝ φt z) v) • Fn n z) =ᶠ[nhds z] fun _ => 0 := by
              filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hznot] with y hy
              rw [image_eq_zero_of_notMem_tsupport hy]
              simp
            exact ContinuousAt.congr continuousAt_const hev.symm
        exact hcontn.aestronglyMeasurable
      · apply Continuous.integrable_of_hasCompactSupport
        · exact hcont_dφt.norm.mul continuous_const
        · exact (HasCompactSupport.fderiv_apply ℝ hcs v).norm.mul_right
      · intro n
        apply Filter.Eventually.of_forall
        intro z
        calc ‖((fderiv ℝ φt z) v) • Fn n z‖
            ≤ ‖(fderiv ℝ φt z) v‖ * ‖Fn n z‖ := norm_smul_le _ _
          _ ≤ ‖(fderiv ℝ φt z) v‖ * Mψt :=
              mul_le_mul_of_nonneg_left (hMψt _) (norm_nonneg _)
      · apply Filter.Eventually.of_forall
        intro z
        by_cases hz : z ∈ K
        · have hφzball : φ z ∈ Metric.closedBall 0 R := hO₁sub (hφzO₁ z hz)
          have hgz : Filter.Tendsto (fun n => gs n (φ z)) Filter.atTop
              (nhds (W (φ z))) := by
            rw [← tendsto_sub_nhds_zero_iff]
            exact squeeze_zero_norm (fun n => hgs_close n (φ z) hφzball) h1n
          have hval : ψt (W (φ z)) = f z := by
            rw [hWO₁ (φ z) (hφzO₁ z hz),
              hψt_eqO₃ (w (φ z)) (hSVO₃ (hTSV (hwφT z hz))), hfeq (hKU hz)]
          have h2 : Filter.Tendsto (fun n => Fn n z) Filter.atTop (nhds (f z)) := by
            rw [← hval]
            exact (hψt_cont.continuousAt.tendsto).comp hgz
          exact h2.const_smul _
        · have hznot : z ∉ tsupport (fun z => (fderiv ℝ φt z) v) :=
            fun hmem => hz (hts_dφt hmem)
          have hzero : (fderiv ℝ φt z) v = 0 :=
            image_eq_zero_of_notMem_tsupport (f := fun z => (fderiv ℝ φt z) v) hznot
          rw [hzero]
          have h0' : ∀ n : ℕ, (0 : ℝ) • Fn n z = (0 : ℝ) • f z := by
            intro n
            module
          exact tendsto_const_nhds.congr (fun n => (h0' n).symm)
    -- ==================== conclusion ====================
    have hneg : Filter.Tendsto (fun n => ∫ z, ((fderiv ℝ φt z) v) • Fn n z)
        Filter.atTop (nhds (- J)) := by
      have heqfun : (fun n => ∫ z, ((fderiv ℝ φt z) v) • Fn n z)
          = fun n => - Jn n := funext hweak_n
      rw [heqfun]
      exact hJn_tendsto.neg
    exact tendsto_nhds_unique hLHS hneg
  · -- (Part 2) local square-integrability of `D` on `U`
    intro K hKU hKc
    have hKmeas := hKc.measurableSet
    have himg : φ '' K ⊆ φ '' U := Set.image_mono hKU
    have hKimgc : IsCompact (φ '' K) := hKc.image_of_continuousOn (hφcont.mono hKU)
    refine ⟨hDasm K hKc hKU, ?_⟩
    rw [p_conv2]
    apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    rw [← lt_top_iff_ne_top]
    obtain ⟨Mψ, hMψ⟩ := hKc.exists_bound_of_continuousOn (hψwφ_cont K hKU)
    -- the pointwise square bound
    have hpt : ∀ z ∈ K, ‖D z‖ₑ ^ (2 : ℕ)
        ≤ 4 * (ENNReal.ofReal Mψ * ‖v‖ₑ) ^ (2 : ℕ)
          * (‖φ' z‖ₑ ^ (2 : ℕ) * ‖gx (φ z)‖ₑ ^ (2 : ℕ)
            + ‖φ' z‖ₑ ^ (2 : ℕ) * ‖gy (φ z)‖ₑ ^ (2 : ℕ)) := by
      intro z hz
      have hb1 : ‖D z‖ₑ ≤ ENNReal.ofReal Mψ
          * (‖v‖ₑ * ‖φ' z‖ₑ * (‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ)) := by
        rw [hDdef]
        refine le_trans (habs2 _ _ _ _) ?_
        rw [← enorm_mul]
        gcongr
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hMψ z hz)
      calc ‖D z‖ₑ ^ (2 : ℕ)
          ≤ (ENNReal.ofReal Mψ
              * (‖v‖ₑ * ‖φ' z‖ₑ * (‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ))) ^ (2 : ℕ) := by gcongr
        _ = (ENNReal.ofReal Mψ * ‖v‖ₑ) ^ (2 : ℕ) * ‖φ' z‖ₑ ^ (2 : ℕ)
            * (‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ) ^ (2 : ℕ) := by ring
        _ ≤ (ENNReal.ofReal Mψ * ‖v‖ₑ) ^ (2 : ℕ) * ‖φ' z‖ₑ ^ (2 : ℕ)
            * (4 * (‖gx (φ z)‖ₑ ^ (2 : ℕ) + ‖gy (φ z)‖ₑ ^ (2 : ℕ))) := by
            gcongr
            exact e8_sum_sq _ _
        _ = 4 * (ENNReal.ofReal Mψ * ‖v‖ₑ) ^ (2 : ℕ)
            * (‖φ' z‖ₑ ^ (2 : ℕ) * ‖gx (φ z)‖ₑ ^ (2 : ℕ)
              + ‖φ' z‖ₑ ^ (2 : ℕ) * ‖gy (φ z)‖ₑ ^ (2 : ℕ)) := by ring
    -- integrate
    have hφ'ae : AEMeasurable φ' (volume.restrict K) :=
      (hφ'cont.mono hKU).aemeasurable hKmeas
    have h1 : AEStronglyMeasurable (fun z => gx (φ z)) (volume.restrict K) :=
      hASMcomp K hKc hKU gx (hgx (φ '' K) himg hKimgc).1
    have haem : AEMeasurable
        (fun z => ‖φ' z‖ₑ ^ (2 : ℕ) * ‖gx (φ z)‖ₑ ^ (2 : ℕ)) (volume.restrict K) :=
      (hφ'ae.enorm.pow_const 2).mul (h1.aemeasurable.enorm.pow_const 2)
    calc (∫⁻ z, ‖D z‖ₑ ^ (2 : ℕ) ∂(volume.restrict K))
        ≤ ∫⁻ z in K, 4 * (ENNReal.ofReal Mψ * ‖v‖ₑ) ^ (2 : ℕ)
          * (‖φ' z‖ₑ ^ (2 : ℕ) * ‖gx (φ z)‖ₑ ^ (2 : ℕ)
            + ‖φ' z‖ₑ ^ (2 : ℕ) * ‖gy (φ z)‖ₑ ^ (2 : ℕ)) ∂volume :=
          setLIntegral_mono' hKmeas hpt
      _ = 4 * (ENNReal.ofReal Mψ * ‖v‖ₑ) ^ (2 : ℕ)
          * ∫⁻ z in K, (‖φ' z‖ₑ ^ (2 : ℕ) * ‖gx (φ z)‖ₑ ^ (2 : ℕ)
            + ‖φ' z‖ₑ ^ (2 : ℕ) * ‖gy (φ z)‖ₑ ^ (2 : ℕ)) ∂volume := by
          rw [lintegral_const_mul' _ _ (by
            exact ENNReal.mul_ne_top (by norm_num)
              (ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top)))]
      _ < ⊤ := by
          apply ENNReal.mul_lt_top
          · exact ENNReal.mul_lt_top (by norm_num)
              (ENNReal.pow_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top enorm_lt_top))
          · rw [lintegral_add_left' haem]
            apply ENNReal.add_lt_top.mpr
            constructor
            · rw [← hCoV K hKmeas hKU (fun ζ => ‖gx ζ‖ₑ ^ (2 : ℕ))]
              exact p_fin (hgx (φ '' K) himg hKimgc)
            · rw [← hCoV K hKmeas hKU (fun ζ => ‖gy ζ‖ₑ ^ (2 : ℕ))]
              exact p_fin (hgy (φ '' K) himg hKimgc)

/-- **`W^{1,2}` removability of a point.** A single point has zero `W^{1,2}`-capacity: if `f`
is continuous on the open set `Ω`, `g` is locally square-integrable on `Ω`, and `g` is a weak
directional derivative of `f` in the direction `v` on `Ω \ {p}`, then `g` is a weak
directional derivative of `f` in the direction `v` on all of `Ω`. -/
theorem HasWeakDirDeriv.removable_singleton {f g : ℂ → ℂ} {v p : ℂ} {Ω : Set ℂ}
    (h : HasWeakDirDeriv v g f (Ω \ {p})) (hΩ : IsOpen Ω)
    (hf : ContinuousOn f Ω) (hg : MemLpLocOn g 2 Ω) :
    HasWeakDirDeriv v g f Ω := by
  classical
  haveI : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  haveI : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  haveI : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  by_cases hp : p ∈ Ω
  swap
  · rwa [Set.diff_singleton_eq_self hp] at h
  intro φ hφ hcs htsupp
  change ∫ z, ((fderiv ℝ φ z) v) • f z = - ∫ z, φ z • g z
  set K : Set ℂ := tsupport φ with hKdef
  have hKc : IsCompact K := hcs
  have hKΩ : K ⊆ Ω := htsupp
  -- A safety radius around the puncture.
  obtain ⟨r, hr, hrball⟩ := Metric.isOpen_iff.mp hΩ p hp
  set δ₀ : ℝ := r / 4 with hδ₀def
  have hδ₀pos : 0 < δ₀ := by positivity
  have hball : Metric.closedBall p (2 * δ₀) ⊆ Ω := by
    intro z hz
    apply hrball
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    have : 2 * δ₀ < r := by rw [hδ₀def]; linarith
    linarith
  -- The compact carrier `KK` on which `f` is bounded.
  set KK : Set ℂ := K ∪ Metric.closedBall p (2 * δ₀) with hKKdef
  have hKKc : IsCompact KK := hKc.union (isCompact_closedBall _ _)
  have hKKΩ : KK ⊆ Ω := Set.union_subset hKΩ hball
  obtain ⟨Mf, hMf⟩ := hKKc.exists_bound_of_continuousOn (hf.mono hKKΩ)
  have hMf0 : 0 ≤ Mf := le_trans (norm_nonneg _)
    (hMf p (Set.mem_union_right _ (Metric.mem_closedBall_self (by positivity))))
  obtain ⟨Mφ, hMφ⟩ := hφ.continuous.bounded_above_of_compact_support hcs
  -- The shrinking scale sequence `δs k = δ₀ / (k+1) → 0`.
  set δs : ℕ → ℝ := fun k => δ₀ / (k + 1) with hδsdef
  have hδpos : ∀ k, 0 < δs k := fun k => by positivity
  have hδle : ∀ k, δs k ≤ δ₀ := by
    intro k
    rw [hδsdef]
    have h1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    calc δ₀ / ((k : ℝ) + 1) ≤ δ₀ / 1 := by
          apply div_le_div_of_nonneg_left hδ₀pos.le (by norm_num) h1
      _ = δ₀ := div_one δ₀
  have hδid : ∀ k : ℕ, ((k : ℝ) + 1) * δs k = δ₀ := by
    intro k
    have hk0 : ((k : ℝ) + 1) ≠ 0 := by positivity
    rw [hδsdef, mul_comm]
    exact div_mul_cancel₀ δ₀ hk0
  have hδtend : Filter.Tendsto δs Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun k : ℕ => δ₀ / ((k : ℝ) + 1)) Filter.atTop (nhds 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      exact Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    simpa [hδsdef] using h2
  -- The reference cutoff at scale `δ₀` and its rescalings `χs k` at scale `δs k`.
  obtain ⟨χ₁, hχ₁sm, hχ₁cs, hχ₁0, hχ₁1, hχ₁one, hχ₁supp, C₀, hC₀0, hC₀⟩ :=
    exists_cutoff_ball p δ₀ hδ₀pos
  set c : ℕ → ℂ := fun k => ((((k : ℝ) + 1) : ℝ) : ℂ) with hcdef
  have hcnorm : ∀ k, ‖c k‖ = (k : ℝ) + 1 := by
    intro k
    rw [hcdef]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  set A : ℕ → ℂ → ℂ := fun k z => p + c k * (z - p) with hAdef
  have hA_fd : ∀ k z, HasFDerivAt (A k)
      (c k • ContinuousLinearMap.id ℝ ℂ) z := by
    intro k z
    have h1 : HasFDerivAt (fun z : ℂ => z - p) (ContinuousLinearMap.id ℝ ℂ) z :=
      (hasFDerivAt_id z).sub_const p
    have h2 := (h1.const_mul (c k)).const_add p
    have h3 : c k • ContinuousLinearMap.id ℝ ℂ
        = (c k) • (ContinuousLinearMap.id ℝ ℂ) := rfl
    exact h2
  have hA_sm : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (A k) := by
    intro k
    exact contDiff_const.add (contDiff_const.mul (contDiff_id.sub contDiff_const))
  have hA_dist : ∀ k z, dist (A k z) p = ((k : ℝ) + 1) * dist z p := by
    intro k z
    rw [hAdef]
    simp only [dist_eq_norm, add_sub_cancel_left]
    rw [norm_mul, hcnorm]
  set χs : ℕ → ℂ → ℝ := fun k z => χ₁ (A k z) with hχsdef
  have hχsm : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (χs k) := fun k => hχ₁sm.comp (hA_sm k)
  have hχ0 : ∀ k z, 0 ≤ χs k z := fun k z => hχ₁0 _
  have hχ1 : ∀ k z, χs k z ≤ 1 := fun k z => hχ₁1 _
  have hχone : ∀ k, ∀ z ∈ Metric.ball p (δs k), χs k z = 1 := by
    intro k z hz
    apply hχ₁one
    rw [Metric.mem_ball] at hz ⊢
    rw [hA_dist]
    calc ((k : ℝ) + 1) * dist z p < ((k : ℝ) + 1) * δs k := by
          apply mul_lt_mul_of_pos_left hz (by positivity)
      _ = δ₀ := hδid k
  have hχsupp : ∀ k, tsupport (χs k) ⊆ Metric.closedBall p (3 * δs k / 2) := by
    intro k
    apply closure_minimal _ Metric.isClosed_closedBall
    intro z hz
    have hAz : A k z ∈ tsupport χ₁ := subset_tsupport χ₁ (by
      simp only [Function.mem_support] at hz ⊢
      exact hz)
    have h1 := hχ₁supp hAz
    rw [Metric.mem_closedBall] at h1 ⊢
    rw [hA_dist] at h1
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [← hδid k] at h1
    calc dist z p = (((k : ℝ) + 1) * dist z p) / ((k : ℝ) + 1) := by field_simp
      _ ≤ (3 * (((k : ℝ) + 1) * δs k) / 2) / ((k : ℝ) + 1) := by
          apply div_le_div_of_nonneg_right h1 hk1.le
      _ = 3 * δs k / 2 := by field_simp
  have hχcs : ∀ k, HasCompactSupport (χs k) := by
    intro k
    exact IsCompact.of_isClosed_subset (isCompact_closedBall p (3 * δs k / 2))
      (isClosed_tsupport _) (hχsupp k)
  -- The scaled derivative bound `‖(fderiv χs k z) v‖ ≤ (k+1) * (C₀/δ₀) * ‖v‖`.
  have hχfd : ∀ k z, ‖(fderiv ℝ (χs k) z) v‖ ≤ ((k : ℝ) + 1) * (C₀ / δ₀) * ‖v‖ := by
    intro k z
    have hχ₁d : DifferentiableAt ℝ χ₁ (A k z) :=
      (hχ₁sm.differentiable (by norm_num)).differentiableAt
    have hcomp : HasFDerivAt (χs k)
        ((fderiv ℝ χ₁ (A k z)).comp (c k • ContinuousLinearMap.id ℝ ℂ)) z :=
      hχ₁d.hasFDerivAt.comp z (hA_fd k z)
    rw [hcomp.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply]
    calc ‖(fderiv ℝ χ₁ (A k z)) (c k • v)‖
        ≤ ‖fderiv ℝ χ₁ (A k z)‖ * ‖c k • v‖ := (fderiv ℝ χ₁ (A k z)).le_opNorm _
      _ = ‖fderiv ℝ χ₁ (A k z)‖ * (((k:ℝ)+1) * ‖v‖) := by
          rw [smul_eq_mul, norm_mul, hcnorm]
      _ ≤ (C₀ / δ₀) * (((k:ℝ)+1) * ‖v‖) := by
          apply mul_le_mul_of_nonneg_right (hC₀ _) (by positivity)
      _ = ((k:ℝ)+1) * (C₀ / δ₀) * ‖v‖ := by ring
  -- Outside the closed ball of radius `3δs k/2` the derivative of the cutoff vanishes.
  have hχfd0 : ∀ k z, z ∉ Metric.closedBall p (3 * δs k / 2) → (fderiv ℝ (χs k) z) v = 0 := by
    intro k z hz
    have hz' : z ∉ tsupport (χs k) := fun hmem => hz (hχsupp k hmem)
    have : fderiv ℝ (χs k) z = 0 := by
      by_contra hne
      exact hz' (support_fderiv_subset ℝ (Function.mem_support.mpr hne))
    rw [this]
    rfl
  -- Local integrability of `f` and `g` on `Ω`, and the basic integrability engine.
  have hfli : LocallyIntegrableOn f Ω := hf.locallyIntegrableOn hΩ.measurableSet
  have hgli : LocallyIntegrableOn g Ω := by
    rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro k hk hkc
    haveI : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hkc.measure_lt_top⟩
    have h1le : (1 : ℝ≥0∞) ≤ 2 := by norm_num
    exact memLp_one_iff_integrable.mp ((hg k hk hkc).mono_exponent h1le)
  have integ : ∀ (m : ℂ → ℝ), Continuous m → HasCompactSupport m → tsupport m ⊆ Ω →
      ∀ {h : ℂ → ℂ}, LocallyIntegrableOn h Ω → Integrable (fun z => m z • h z) volume := by
    intro m hm hcsm htsuppm h hh
    have hK : IsCompact (tsupport m) := hcsm
    have hhon : IntegrableOn h (tsupport m) volume :=
      hh.integrableOn_compact_subset htsuppm hK
    have hon : IntegrableOn (fun z => m z • h z) (tsupport m) volume :=
      hhon.continuousOn_smul hm.continuousOn hK
    have hsupp : Function.support (fun z => m z • h z) ⊆ tsupport m := by
      intro z hz
      apply subset_tsupport m
      simp only [Function.mem_support] at hz ⊢
      intro hmz; apply hz; simp [hmz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  -- The truncated test functions `φs k = φ · (1 - χs k)` and their admissibility.
  set φs : ℕ → ℂ → ℝ := fun k z => φ z * (1 - χs k z) with hφsdef
  have hφs_sm : ∀ k, ContDiff ℝ ∞ (φs k) :=
    fun k => hφ.mul (contDiff_const.sub (hχsm k))
  have hφs_cs : ∀ k, HasCompactSupport (φs k) := fun k => hcs.mul_right
  have hφs_le : ∀ k z, |φs k z| ≤ |φ z| := by
    intro k z
    rw [hφsdef]
    simp only [abs_mul]
    have h1 : |1 - χs k z| ≤ 1 := by
      rw [abs_le]
      constructor
      · have := hχ1 k z; linarith
      · have := hχ0 k z; linarith
    calc |φ z| * |1 - χs k z| ≤ |φ z| * 1 :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |φ z| := mul_one _
  have hφs_ts : ∀ k, tsupport (φs k) ⊆ Ω \ {p} := by
    intro k z hz
    have h1 : z ∈ K := tsupport_mul_subset_left hz
    have h2 : z ∈ tsupport (fun z => 1 - χs k z) := tsupport_mul_subset_right hz
    have h3 : z ∉ Metric.ball p (δs k) := by
      have hsub : Function.support (fun z => 1 - χs k z) ⊆ (Metric.ball p (δs k))ᶜ := by
        intro w hw
        simp only [Function.mem_support] at hw
        intro hwball
        exact hw (by rw [hχone k w hwball]; ring)
      have := closure_minimal hsub (Metric.isOpen_ball.isClosed_compl) h2
      exact this
    refine ⟨hKΩ h1, ?_⟩
    intro hzp
    rw [Set.mem_singleton_iff] at hzp
    subst hzp
    exact h3 (Metric.mem_ball_self (hδpos k))
  -- The truncated integration-by-parts identities.
  have hIk : ∀ k, ∫ z, ((fderiv ℝ (φs k) z) v) • f z = - ∫ z, φs k z • g z :=
    fun k => h (φs k) (hφs_sm k) (hφs_cs k) (hφs_ts k)
  -- The product-rule split of `fderiv (φs k)`.
  have hsplit : ∀ k z, (fderiv ℝ (φs k) z) v
      = (1 - χs k z) * ((fderiv ℝ φ z) v) - φ z * ((fderiv ℝ (χs k) z) v) := by
    intro k z
    have hφd : DifferentiableAt ℝ φ z := (hφ.differentiable (by norm_num)).differentiableAt
    have hχd : DifferentiableAt ℝ (χs k) z :=
      ((hχsm k).differentiable (by norm_num)).differentiableAt
    have hmul := fderiv_fun_mul (𝕜 := ℝ) hφd (hχd.const_sub 1)
    have hsub : fderiv ℝ (fun w => 1 - χs k w) z = - fderiv ℝ (χs k) z :=
      ((hχd.hasFDerivAt.const_sub 1).fderiv)
    rw [hφsdef]
    simp only
    rw [hmul, hsub]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply, smul_eq_mul]
    ring
  -- The three integral pieces.
  set Ak : ℕ → ℂ := fun k => ∫ z, ((1 - χs k z) * ((fderiv ℝ φ z) v)) • f z with hAkdef
  set Bk : ℕ → ℂ := fun k => ∫ z, (φ z * ((fderiv ℝ (χs k) z) v)) • f z with hBkdef
  set Ck : ℕ → ℂ := fun k => ∫ z, φs k z • g z with hCkdef
  have hcont_dφ : Continuous (fun z => (fderiv ℝ φ z) v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs_dφ : HasCompactSupport (fun z => (fderiv ℝ φ z) v) :=
    HasCompactSupport.fderiv_apply ℝ hcs v
  have hts_dφ : tsupport (fun z => (fderiv ℝ φ z) v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans htsupp
  have hint_m1 : ∀ k, Integrable (fun z => ((1 - χs k z) * ((fderiv ℝ φ z) v)) • f z) volume := by
    intro k
    apply integ _ ((continuous_const.sub (hχsm k).continuous).mul hcont_dφ)
      hcs_dφ.mul_left (subset_trans tsupport_mul_subset_right hts_dφ) hfli
  have hint_m2 : ∀ k, Integrable (fun z => (φ z * ((fderiv ℝ (χs k) z) v)) • f z) volume := by
    intro k
    have hcont_dχ : Continuous (fun z => (fderiv ℝ (χs k) z) v) :=
      ((hχsm k).continuous_fderiv (by norm_num)).clm_apply continuous_const
    apply integ _ (hφ.continuous.mul hcont_dχ) hcs.mul_right
      (subset_trans tsupport_mul_subset_left htsupp) hfli
  have hIk' : ∀ k, Ak k - Bk k = - Ck k := by
    intro k
    have h1 : (∫ z, ((fderiv ℝ (φs k) z) v) • f z) = Ak k - Bk k := by
      rw [hAkdef, hBkdef]
      simp only
      rw [← integral_sub (hint_m1 k) (hint_m2 k)]
      apply integral_congr_ae
      filter_upwards with z
      rw [hsplit k z]
      module
    rw [← h1, hIk k, hCkdef]
  -- ==================== Limit (A): `Ak → ∫ (∂ᵥφ) • f`. ====================
  have hA : Filter.Tendsto Ak Filter.atTop (nhds (∫ z, ((fderiv ℝ φ z) v) • f z)) := by
    rw [hAkdef]
    apply MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun z => ‖(fderiv ℝ φ z) v‖ * Mf)
    · -- a.e. strong measurability of each integrand
      intro k
      have heq : (fun z => ((1 - χs k z) * ((fderiv ℝ φ z) v)) • f z)
          = K.indicator (fun z => ((1 - χs k z) * ((fderiv ℝ φ z) v)) • f z) := by
        funext z
        by_cases hz : z ∈ K
        · rw [Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz]
          have hznot : z ∉ tsupport (fun x => (fderiv ℝ φ x) v) :=
            fun hmem => hz (tsupport_fderiv_apply_subset ℝ v hmem)
          rw [image_eq_zero_of_notMem_tsupport hznot]
          simp
      rw [heq]
      rw [aestronglyMeasurable_indicator_iff hKc.measurableSet]
      exact (((continuous_const.sub (hχsm k).continuous).mul
        hcont_dφ).aestronglyMeasurable.restrict).smul
        ((hf.mono hKΩ).aestronglyMeasurable hKc.measurableSet)
    · apply Continuous.integrable_of_hasCompactSupport
      · exact hcont_dφ.norm.mul continuous_const
      · exact hcs_dφ.norm.mul_right
    · intro k
      apply Filter.Eventually.of_forall
      intro z
      by_cases hz : z ∈ K
      · calc ‖((1 - χs k z) * ((fderiv ℝ φ z) v)) • f z‖
            = |1 - χs k z| * ‖(fderiv ℝ φ z) v‖ * ‖f z‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
          _ ≤ 1 * ‖(fderiv ℝ φ z) v‖ * Mf := by
              have h1 : |1 - χs k z| ≤ 1 := by
                rw [abs_le]
                exact ⟨by have := hχ1 k z; linarith, by have := hχ0 k z; linarith⟩
              have h2 : ‖f z‖ ≤ Mf := hMf z (Set.mem_union_left _ hz)
              apply mul_le_mul (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h2
                (norm_nonneg _) (by positivity)
          _ = ‖(fderiv ℝ φ z) v‖ * Mf := by ring
      · have hznot : z ∉ tsupport (fun x => (fderiv ℝ φ x) v) :=
          fun hmem => hz (tsupport_fderiv_apply_subset ℝ v hmem)
        rw [image_eq_zero_of_notMem_tsupport hznot]
        simp
    · -- pointwise a.e. convergence: away from `p` the cutoff is eventually zero
      have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ p := by
        rw [MeasureTheory.ae_iff]
        have : {z : ℂ | ¬z ≠ p} = {p} := by
          ext z
          simp [Set.mem_singleton_iff]
        rw [this]
        exact measure_singleton p
      filter_upwards [hae] with z hz
      have hev : ∀ᶠ k in Filter.atTop, χs k z = 0 := by
        have hzp : 0 < dist z p := dist_pos.mpr hz
        have hev1 : ∀ᶠ k in Filter.atTop, δs k < dist z p / 2 :=
          hδtend.eventually (eventually_lt_nhds (by positivity))
        filter_upwards [hev1] with k hk
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have := hχsupp k hmem
        rw [Metric.mem_closedBall] at this
        nlinarith
      apply Filter.Tendsto.congr'
        (Filter.EventuallyEq.symm ?_) tendsto_const_nhds
      filter_upwards [hev] with k hk
      rw [hk]
      simp
  -- ==================== Limit (B): `Bk → 0`. ====================
  have hB : Filter.Tendsto Bk Filter.atTop (nhds 0) := by
    set vb : ℝ := (volume (Metric.ball (0 : ℂ) 1)).toReal with hvbdef
    have hvb0 : 0 ≤ vb := ENNReal.toReal_nonneg
    have htend : Filter.Tendsto
        (fun k => Mφ * ((C₀ / δ₀) * ‖v‖) * Mf * (9 / 4 * δ₀ * vb) * δs k)
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun k => Mφ * ((C₀ / δ₀) * ‖v‖) * Mf * (9 / 4 * δ₀ * vb) * δs k)
          Filter.atTop (nhds (Mφ * ((C₀ / δ₀) * ‖v‖) * Mf * (9 / 4 * δ₀ * vb) * 0)) :=
        hδtend.const_mul _
      simpa using h1
    refine squeeze_zero_norm (fun k => ?_) htend
    -- the per-`k` bound
    have hvanish : ∀ z ∉ Metric.closedBall p (3 * δs k / 2),
        (φ z * ((fderiv ℝ (χs k) z) v)) • f z = 0 := by
      intro z hz
      rw [hχfd0 k z hz]
      simp
    have hBk_eq : Bk k = ∫ z in Metric.closedBall p (3 * δs k / 2),
        (φ z * ((fderiv ℝ (χs k) z) v)) • f z := by
      rw [hBkdef]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero hvanish).symm
    have hMφ0 : 0 ≤ Mφ := le_trans (norm_nonneg _) (hMφ 0)
    have hCb0 : (0:ℝ) ≤ ((k:ℝ)+1) * (C₀ / δ₀) * ‖v‖ := by positivity
    have hptbd : ∀ z ∈ Metric.closedBall p (3 * δs k / 2),
        ‖(φ z * ((fderiv ℝ (χs k) z) v)) • f z‖
          ≤ Mφ * (((k:ℝ)+1) * (C₀ / δ₀) * ‖v‖) * Mf := by
      intro z hz
      have hzKK : z ∈ KK := by
        apply Set.mem_union_right
        rw [Metric.mem_closedBall] at hz ⊢
        have := hδle k
        nlinarith
      calc ‖(φ z * ((fderiv ℝ (χs k) z) v)) • f z‖
          = |φ z| * ‖(fderiv ℝ (χs k) z) v‖ * ‖f z‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
        _ ≤ Mφ * (((k:ℝ)+1) * (C₀ / δ₀) * ‖v‖) * Mf := by
            have h1 : |φ z| ≤ Mφ := by
              have := hMφ z
              rwa [Real.norm_eq_abs] at this
            apply mul_le_mul (mul_le_mul h1 (hχfd k z) (norm_nonneg _) hMφ0)
              (hMf z hzKK) (norm_nonneg _) (by positivity)
    have hvol : volume (Metric.closedBall p (3 * δs k / 2)) < ⊤ :=
      (isCompact_closedBall _ _).measure_lt_top
    have hbd := norm_setIntegral_le_of_norm_le_const (μ := volume) hvol hptbd
    rw [← hBk_eq] at hbd
    refine le_trans hbd ?_
    -- compute the volume and rearrange
    have hrad : (0:ℝ) ≤ 3 * δs k / 2 := by positivity
    have hvol_eq : (volume : Measure ℂ).real (Metric.closedBall p (3 * δs k / 2))
        = (3 * δs k / 2) ^ 2 * vb := by
      rw [measureReal_def, Measure.addHaar_closedBall _ _ hrad, Complex.finrank_real_complex]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hvbdef]
    rw [hvol_eq]
    apply le_of_eq
    have hkey : (((k:ℝ)+1) * (C₀ / δ₀) * ‖v‖) * ((3 * δs k / 2) ^ 2 * vb)
        = ((C₀ / δ₀) * ‖v‖) * (9 / 4 * (((k:ℝ)+1) * δs k) * δs k * vb) := by ring
    calc Mφ * (((k:ℝ)+1) * (C₀ / δ₀) * ‖v‖) * Mf * ((3 * δs k / 2) ^ 2 * vb)
        = Mφ * Mf * ((((k:ℝ)+1) * (C₀ / δ₀) * ‖v‖) * ((3 * δs k / 2) ^ 2 * vb)) := by ring
      _ = Mφ * Mf * (((C₀ / δ₀) * ‖v‖) * (9 / 4 * δ₀ * δs k * vb)) := by
          rw [hkey, hδid k]
      _ = Mφ * ((C₀ / δ₀) * ‖v‖) * Mf * (9 / 4 * δ₀ * vb) * δs k := by ring
  -- ==================== Limit (C): `Ck → ∫ φ • g`. ====================
  have hgK : IntegrableOn g K volume := by
    haveI : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp ((hg K hKΩ hKc).mono_exponent (by norm_num))
  have hgasm : AEStronglyMeasurable g (volume.restrict K) := (hg K hKΩ hKc).1
  have hC : Filter.Tendsto Ck Filter.atTop (nhds (∫ z, φ z • g z)) := by
    rw [hCkdef]
    apply MeasureTheory.tendsto_integral_of_dominated_convergence
      (K.indicator (fun z => Mφ * ‖g z‖))
    · intro k
      have heq : (fun z => φs k z • g z) = K.indicator (fun z => φs k z • g z) := by
        funext z
        by_cases hz : z ∈ K
        · rw [Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz]
          have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
          rw [hφsdef]
          simp [hφz]
      rw [heq]
      rw [aestronglyMeasurable_indicator_iff hKc.measurableSet]
      exact ((hφs_sm k).continuous.aestronglyMeasurable.restrict).smul hgasm
    · exact MeasureTheory.IntegrableOn.integrable_indicator
        (hgK.norm.const_mul Mφ) hKc.measurableSet
    · intro k
      apply Filter.Eventually.of_forall
      intro z
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz]
        calc ‖φs k z • g z‖ = |φs k z| * ‖g z‖ := by
              rw [norm_smul, Real.norm_eq_abs]
          _ ≤ Mφ * ‖g z‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              refine le_trans (hφs_le k z) ?_
              have := hMφ z
              rwa [Real.norm_eq_abs] at this
      · rw [Set.indicator_of_notMem hz]
        have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
        have : φs k z = 0 := by rw [hφsdef]; simp [hφz]
        rw [this]
        simp
    · have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ p := by
        rw [MeasureTheory.ae_iff]
        have : {z : ℂ | ¬z ≠ p} = {p} := by
          ext z
          simp [Set.mem_singleton_iff]
        rw [this]
        exact measure_singleton p
      filter_upwards [hae] with z hz
      have hev : ∀ᶠ k in Filter.atTop, χs k z = 0 := by
        have hzp : 0 < dist z p := dist_pos.mpr hz
        have hev1 : ∀ᶠ k in Filter.atTop, δs k < dist z p / 2 :=
          hδtend.eventually (eventually_lt_nhds (by positivity))
        filter_upwards [hev1] with k hk
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have := hχsupp k hmem
        rw [Metric.mem_closedBall] at this
        nlinarith
      apply Filter.Tendsto.congr'
        (Filter.EventuallyEq.symm ?_) tendsto_const_nhds
      filter_upwards [hev] with k hk
      rw [hφsdef]
      simp only [hk]
      ring_nf
  -- ==================== Assembly. ====================
  have hAB : Filter.Tendsto (fun k => Ak k - Bk k) Filter.atTop
      (nhds ((∫ z, ((fderiv ℝ φ z) v) • f z) - 0)) := hA.sub hB
  have hnegC : Filter.Tendsto (fun k => - Ck k) Filter.atTop
      (nhds (- ∫ z, φ z • g z)) := hC.neg
  have heq : (fun k => Ak k - Bk k) = fun k => - Ck k := funext hIk'
  rw [heq] at hAB
  have := tendsto_nhds_unique hAB hnegC
  rw [sub_zero] at this
  exact this

end RiemannDynamics

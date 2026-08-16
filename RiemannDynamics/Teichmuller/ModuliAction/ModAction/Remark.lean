/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.ModuliAction.ModAction.Group

/-!
# Upper-half-plane moduli re-markings: data and the Wirtinger quotient

The bundled upper-half-plane re-marking data, its extraction from the moduli
group, and the measurability, bound, and invariance of the Wirtinger quotient
of a re-marked solution.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-! ## Upper-half-plane moduli re-markings

The plane moduli group is a strict sub-groupoid of the classical Teichmüller modular
action: the boundary map of a plane element fixes `∞`, while the boundary realization of a
general mapping class need not. The classical modular action acts on coefficients through
quasiconformal self-maps of the upper half plane compatible with `Γ₀`, with no plane
extension; the plane elements embed by restriction. -/

/-- An **upper-half-plane moduli re-marking** over `Γ₀`: a quasiconformal self-map of the
upper half plane with coefficient bound below `1`, compatible with `Γ₀` on both sides on
the upper half plane. -/
structure ModGroupUpper (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) where
  /-- The re-marking map on the upper half plane. -/
  g : ℂ → ℂ
  /-- A two-sided inverse of the re-marking on the upper half plane. -/
  ginv : ℂ → ℂ
  /-- The Beltrami bound of the re-marking. -/
  κ : ℝ
  /-- The Beltrami bound is below `1`. -/
  hκ : κ < 1
  /-- The re-marking is an upper-half-plane quasiconformal map. -/
  qc : IsQCUpper g ginv κ
  /-- Forward `Γ₀`-compatibility on the upper half plane. -/
  compat : ∀ γ ∈ Γ₀, ∃ γ' ∈ Γ₀, ∀ z : ℂ, 0 < z.im →
    g (moebiusMap γ z) = moebiusMap γ' (g z)
  /-- Backward `Γ₀`-compatibility on the upper half plane. -/
  compat' : ∀ γ' ∈ Γ₀, ∃ γ ∈ Γ₀, ∀ z : ℂ, 0 < z.im →
    g (moebiusMap γ z) = moebiusMap γ' (g z)

/-- A plane moduli-group element mapping the upper half plane into itself restricts to an
upper-half-plane re-marking: symmetry carries the half-plane preservation to the inverse,
and the almost-everywhere compatibility upgrades to every point of the upper half plane by
continuity. -/
theorem exists_modGroupUpper_of_modGroup {F : ℂ ≃ₜ ℂ} (hF : F ∈ modGroup Γ₀)
    (hup : ∀ z : ℂ, 0 < z.im → 0 < (F z).im) :
    ∃ P : ModGroupUpper Γ₀, P.g = ⇑F := by
  obtain ⟨⟨K, hK⟩, hsym, hcompat, hcompat'⟩ := mem_modGroup_iff.mp hF
  have hK1 : 1 ≤ K := hK.1
  have hκ : (K - 1) / (K + 1) < 1 := by
    rw [div_lt_one (by linarith : (0 : ℝ) < K + 1)]
    linarith
  have hqc : IsQCUpper (⇑F) (⇑F.symm) ((K - 1) / (K + 1)) :=
    isQCUpper_of_isQCGeometric hK hsym hup
      (fun z => F.symm_apply_apply z) (fun z => F.apply_symm_apply z)
  have hcompatU : ∀ γ ∈ Γ₀, ∃ γ' ∈ Γ₀, ∀ z : ℂ, 0 < z.im →
      F (moebiusMap γ z) = moebiusMap γ' (F z) := by
    intro γ hγ
    obtain ⟨γ', hγ', hae⟩ := hcompat γ hγ
    exact ⟨γ', hγ', fun z hz => modGroup_equivariant_offPole hF hae z
      (moebiusDenom_ne_zero_of_im_ne_zero γ (ne_of_gt hz))⟩
  have hcompatU' : ∀ γ' ∈ Γ₀, ∃ γ ∈ Γ₀, ∀ z : ℂ, 0 < z.im →
      F (moebiusMap γ z) = moebiusMap γ' (F z) := by
    intro γ' hγ'
    obtain ⟨γ, hγ, hae⟩ := hcompat' γ' hγ'
    exact ⟨γ, hγ, fun z hz => modGroup_equivariant_offPole hF hae z
      (moebiusDenom_ne_zero_of_im_ne_zero γ (ne_of_gt hz))⟩
  exact ⟨⟨⇑F, ⇑F.symm, (K - 1) / (K + 1), hκ, hqc, hcompatU, hcompatU'⟩, rfl⟩

/-- The **Wirtinger quotient** of a map: the ratio of the conjugate-linear and the
complex-linear parts of its real derivative. -/
noncomputable def wirtingerQuotient (f : ℂ → ℂ) (z : ℂ) : ℂ := dzbar f z / dz f z

/-- The Wirtinger quotient of a re-marked solution is measurable. -/
theorem measurable_wirtingerQuotient_remark (x : TeichRep Γ₀) (P : ModGroupUpper Γ₀) :
    Measurable (wirtingerQuotient (x.w ∘ P.g)) := by
  have h1 : Measurable fun z : ℂ => (fderiv ℝ (x.w ∘ P.g) z) 1 :=
    (measurable_fderiv ℝ (x.w ∘ P.g)).apply_continuousLinearMap 1
  have hI : Measurable fun z : ℂ => (fderiv ℝ (x.w ∘ P.g) z) Complex.I :=
    (measurable_fderiv ℝ (x.w ∘ P.g)).apply_continuousLinearMap Complex.I
  have hdz : Measurable (dz (x.w ∘ P.g)) := by
    change Measurable fun z : ℂ => (1 / 2 : ℂ)
      * ((fderiv ℝ (x.w ∘ P.g) z) 1 - Complex.I * (fderiv ℝ (x.w ∘ P.g) z) Complex.I)
    exact (h1.sub (hI.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have hdzbar : Measurable (dzbar (x.w ∘ P.g)) := by
    change Measurable fun z : ℂ => (1 / 2 : ℂ)
      * ((fderiv ℝ (x.w ∘ P.g) z) 1 + Complex.I * (fderiv ℝ (x.w ∘ P.g) z) Complex.I)
    exact (h1.add (hI.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  change Measurable fun z : ℂ => dzbar (x.w ∘ P.g) z / dz (x.w ∘ P.g) z
  exact hdzbar.div hdz

/-- The Wirtinger quotient of a re-marked solution is essentially bounded below `1` on the
upper half plane: dilatations multiply under composition. -/
theorem wirtingerQuotient_remark_bound (x : TeichRep Γ₀) (P : ModGroupUpper Γ₀) :
    eLpNormEssSup (wirtingerQuotient (x.w ∘ P.g))
      (volume.restrict {z : ℂ | 0 < z.im}) < 1 := by
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  -- Wirtinger measurability of the re-marking map
  have hg1 : Measurable fun z : ℂ => (fderiv ℝ P.g z) 1 :=
    (measurable_fderiv ℝ P.g).apply_continuousLinearMap 1
  have hgI : Measurable fun z : ℂ => (fderiv ℝ P.g z) Complex.I :=
    (measurable_fderiv ℝ P.g).apply_continuousLinearMap Complex.I
  have hdzg : Measurable (dz P.g) := by
    change Measurable fun z : ℂ => (1 / 2 : ℂ)
      * ((fderiv ℝ P.g z) 1 - Complex.I * (fderiv ℝ P.g z) Complex.I)
    exact (hg1.sub (hgI.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have hdzbarg : Measurable (dzbar P.g) := by
    change Measurable fun z : ℂ => (1 / 2 : ℂ)
      * ((fderiv ℝ P.g z) 1 + Complex.I * (fderiv ℝ P.g z) Complex.I)
    exact (hg1.add (hgI.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have hdetmeas : Measurable fun z : ℂ => (fderiv ℝ P.g z).det := by
    have hfun : (fun z : ℂ => (fderiv ℝ P.g z).det)
        = fun z : ℂ => ‖dz P.g z‖ ^ 2 - ‖dzbar P.g z‖ ^ 2 :=
      funext fun z => det_fderiv_eq_wirtinger P.g z
    rw [hfun]
    exact (hdzg.norm.pow_const 2).sub (hdzbarg.norm.pow_const 2)
  -- preimages of null sets under `P.g` are null on the differentiability set: the image of
  -- a positive-Jacobian piece has measure `∫ |det|` by the area formula, and it sits in a
  -- null set, forcing the piece to be null
  have hpull : ∀ N : Set ℂ, volume N = 0 →
      ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
        (DifferentiableAt ℝ P.g z ∧ 0 < (fderiv ℝ P.g z).det) → P.g z ∉ N := by
    intro N hN
    have hgae : AEMeasurable P.g (volume.restrict {z : ℂ | 0 < z.im}) :=
      P.qc.cont.aemeasurable hU
    have hgeq : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), P.g z = hgae.mk P.g z :=
      hgae.ae_eq_mk
    have hbadnull : (volume.restrict {z : ℂ | 0 < z.im})
        {z : ℂ | ¬ P.g z = hgae.mk P.g z} = 0 := ae_iff.mp hgeq
    obtain ⟨T, hTsub, hTmeas, hTnull⟩ : ∃ T : Set ℂ,
        {z : ℂ | ¬ P.g z = hgae.mk P.g z} ⊆ T ∧ MeasurableSet T
          ∧ (volume.restrict {z : ℂ | 0 < z.im}) T = 0 :=
      ⟨toMeasurable (volume.restrict {z : ℂ | 0 < z.im}) {z : ℂ | ¬ P.g z = hgae.mk P.g z},
        subset_toMeasurable _ _, measurableSet_toMeasurable _ _,
        by rw [measure_toMeasurable]; exact hbadnull⟩
    obtain ⟨N', hNsub, hN'meas, hN'null⟩ : ∃ N' : Set ℂ,
        N ⊆ N' ∧ MeasurableSet N' ∧ volume N' = 0 :=
      ⟨toMeasurable volume N, subset_toMeasurable _ _, measurableSet_toMeasurable _ _,
        by rw [measure_toMeasurable]; exact hN⟩
    set S : Set ℂ := ({z : ℂ | 0 < z.im} ∩ {z : ℂ | DifferentiableAt ℝ P.g z}
      ∩ {z : ℂ | 0 < (fderiv ℝ P.g z).det} ∩ (hgae.mk P.g ⁻¹' N')) \ T with hSdef
    have hSmeas : MeasurableSet S :=
      (((hU.inter (measurableSet_of_differentiableAt ℝ P.g)).inter
        (measurableSet_lt measurable_const hdetmeas)).inter
          (hgae.measurable_mk hN'meas)).diff hTmeas
    have hSfacts : ∀ z ∈ S, 0 < z.im ∧ DifferentiableAt ℝ P.g z
        ∧ 0 < (fderiv ℝ P.g z).det ∧ P.g z ∈ N' ∧ z ∉ T := by
      intro z hz
      rw [hSdef] at hz
      obtain ⟨⟨⟨⟨hz1, hz2⟩, hz3⟩, hz4⟩, hz5⟩ := hz
      have hgz : P.g z = hgae.mk P.g z := by
        by_contra hne
        exact hz5 (hTsub hne)
      exact ⟨hz1, hz2, hz3, by rw [hgz]; exact hz4, hz5⟩
    have hfd : ∀ z ∈ S, HasFDerivWithinAt P.g (fderiv ℝ P.g z) S z := fun z hz =>
      ((hSfacts z hz).2.1.hasFDerivAt).hasFDerivWithinAt
    have hinjS : Set.InjOn P.g S := by
      intro p hp q hq hpq
      have h1 := P.qc.left_inv p (hSfacts p hp).1
      have h2 := P.qc.left_inv q (hSfacts q hq).1
      rw [← h1, ← h2, hpq]
    have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hfd hinjS
      (fun _ => (1 : ℝ≥0∞))
    rw [setLIntegral_one] at hcov
    simp only [mul_one] at hcov
    have himgnull : volume (P.g '' S) = 0 := by
      refine le_antisymm (le_trans (measure_mono ?_) hN'null.le) (zero_le)
      rintro w ⟨z, hz, rfl⟩
      exact (hSfacts z hz).2.2.2.1
    have hint0 : ∫⁻ z in S, ENNReal.ofReal |(fderiv ℝ P.g z).det| = 0 := by
      rw [← hcov]
      exact himgnull
    have hSnull : volume S = 0 := by
      have hmeasint : Measurable fun z : ℂ => ENNReal.ofReal |(fderiv ℝ P.g z).det| :=
        (continuous_abs.measurable.comp hdetmeas).ennreal_ofReal
      have h2 := (lintegral_eq_zero_iff hmeasint).mp hint0
      have h2' : ∀ᵐ z ∂(volume.restrict S),
          ENNReal.ofReal |(fderiv ℝ P.g z).det| = 0 := by
        filter_upwards [h2] with z hz2
        simpa using hz2
      have h3 : ∀ᵐ z : ℂ, z ∈ S → ENNReal.ofReal |(fderiv ℝ P.g z).det| = 0 :=
        (ae_restrict_iff' hSmeas).mp h2'
      rw [ae_iff] at h3
      refine le_antisymm (le_trans (measure_mono ?_) h3.le) (zero_le)
      intro z hz
      simp only [Set.mem_ofPred_eq, Classical.not_imp]
      refine ⟨hz, ?_⟩
      intro h0
      rw [ENNReal.ofReal_eq_zero] at h0
      have hpos := abs_pos.mpr (ne_of_gt (hSfacts z hz).2.2.1)
      linarith
    rw [ae_iff, Measure.restrict_apply' hU]
    have hTH : volume (T ∩ {z : ℂ | 0 < z.im}) = 0 := by
      rw [Measure.restrict_apply hTmeas] at hTnull
      exact hTnull
    refine measure_mono_null ?_ (measure_union_null hTH hSnull)
    intro z hz
    obtain ⟨hzbad, hzU⟩ := hz
    simp only [Set.mem_ofPred_eq, Classical.not_imp, not_not] at hzbad
    obtain ⟨⟨hdiff, hdet⟩, hgN⟩ := hzbad
    by_cases hzT : z ∈ T
    · exact Or.inl ⟨hzT, hzU⟩
    · refine Or.inr ?_
      rw [hSdef]
      have hgz : P.g z = hgae.mk P.g z := by
        by_contra hne
        exact hzT (hTsub hne)
      exact ⟨⟨⟨⟨hzU, hdiff⟩, hdet⟩, by rw [Set.mem_preimage, ← hgz]; exact hNsub hgN⟩, hzT⟩
  -- dilatation constants
  have ha0 : 0 ≤ max P.κ 0 := le_max_right _ _
  have ha1 : max P.κ 0 < 1 := max_lt P.hκ zero_lt_one
  have hbw0 : 0 ≤ x.b.normInf := x.b.normInf_nonneg
  have hbw1 : x.b.normInf < 1 := x.b.normInf_lt_one
  have h1pab : 0 < 1 + max P.κ 0 * x.b.normInf := by nlinarith [mul_nonneg ha0 hbw0]
  have hκ'0 : 0 ≤ (max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf) :=
    div_nonneg (by linarith) h1pab.le
  have hκ'1 : (max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf) < 1 := by
    rw [div_lt_one h1pab]
    nlinarith [mul_pos (sub_pos.mpr ha1) (sub_pos.mpr hbw1)]
  -- the sharp composition estimate on squared norms, with the shared cross term
  have hsharp : ∀ a b s t q R : ℝ, 0 ≤ a → a < 1 → 0 ≤ b → b < 1 → 0 ≤ s → 0 ≤ t →
      0 ≤ q → t ≤ a * s → q ≤ b → |R| ≤ q * s * t →
      (t ^ 2 + q ^ 2 * s ^ 2 + 2 * R) * (1 + a * b) ^ 2
        ≤ (a + b) ^ 2 * (s ^ 2 + q ^ 2 * t ^ 2 + 2 * R) := by
    intro a b s t q R ha0' ha1' hb0' hb1' hs ht hq htas hqb hRb
    have hqst : R ≤ q * s * t := (abs_le.mp hRb).2
    have hlin : (t + q * s) * (1 + a * b) ≤ (a + b) * (s + q * t) := by
      have h1 : 0 ≤ (1 - a ^ 2) * ((b - q) * s) :=
        mul_nonneg (by nlinarith) (mul_nonneg (by linarith) hs)
      have h2 : 0 ≤ (1 + a * b - q * (a + b)) * (a * s - t) := by
        refine mul_nonneg ?_ (by linarith)
        nlinarith [mul_le_mul_of_nonneg_right hqb (show (0:ℝ) ≤ a + b by linarith),
          mul_nonneg hb0' (sub_nonneg.mpr hb1'.le)]
      nlinarith [h1, h2]
    have hXnn : 0 ≤ (t + q * s) * (1 + a * b) :=
      mul_nonneg (add_nonneg ht (mul_nonneg hq hs))
        (by nlinarith [mul_nonneg ha0' hb0'])
    have hYnn : 0 ≤ (a + b) * (s + q * t) := le_trans hXnn hlin
    have hsq : ((t + q * s) * (1 + a * b)) ^ 2 ≤ ((a + b) * (s + q * t)) ^ 2 := by
      nlinarith [hlin, hXnn, hYnn]
    have hfac : 0 ≤ (q * s * t - R) * ((1 + a * b) ^ 2 - (a + b) ^ 2) := by
      refine mul_nonneg (by linarith) ?_
      nlinarith [mul_pos (mul_pos (mul_pos (show (0:ℝ) < 1 + a by linarith)
        (show (0:ℝ) < 1 + b by linarith)) (show (0:ℝ) < 1 - a by linarith))
        (show (0:ℝ) < 1 - b by linarith)]
    nlinarith [hsq, hfac]
  -- the almost-everywhere good set of the plane solution
  have hbw_ae : ∀ᵐ w : ℂ, ‖x.b.μ w‖ ≤ x.b.normInf := by
    filter_upwards [enorm_ae_le_eLpNormEssSup x.b.μ volume] with w hw
    have h2 := ENNReal.toReal_mono (ne_top_of_lt x.b.bound) hw
    simpa [BeltramiCoeff.normInf, enorm_eq_nnnorm] using h2
  have hwgood : ∀ᵐ w : ℂ, DifferentiableAt ℝ x.w w ∧ 0 < (fderiv ℝ x.w w).det
      ∧ dzbar x.w w = x.b.μ w * dz x.w w ∧ ‖x.b.μ w‖ ≤ x.b.normInf := by
    filter_upwards [x.w_isQCAnalytic.1.2, x.w_isQCAnalytic.2.2, hbw_ae] with w h1 h2 h3
    refine ⟨?_, h1, h2, h3⟩
    by_contra hnd
    rw [fderiv_zero_of_not_differentiableAt hnd] at h1
    simp [ContinuousLinearMap.det] at h1
  have hNnull : volume {w : ℂ | ¬ (DifferentiableAt ℝ x.w w ∧ 0 < (fderiv ℝ x.w w).det
      ∧ dzbar x.w w = x.b.μ w * dz x.w w ∧ ‖x.b.μ w‖ ≤ x.b.normInf)} = 0 :=
    ae_iff.mp hwgood
  refine lt_of_le_of_lt (eLpNormEssSup_le_of_ae_enorm_bound ?_)
    (ENNReal.ofReal_lt_one.mpr hκ'1)
  filter_upwards [P.qc.jac, P.qc.belt, hpull _ hNnull] with z hjac hbelt htr
  have hgdiff : DifferentiableAt ℝ P.g z := by
    by_contra hnd
    rw [fderiv_zero_of_not_differentiableAt hnd] at hjac
    simp [ContinuousLinearMap.det] at hjac
  have hw4 := htr ⟨hgdiff, hjac⟩
  simp only [not_not] at hw4
  obtain ⟨hwdiff, hwdet, hwbelt, hwmu⟩ := hw4
  -- chain rule with the Beltrami substitution
  have hcompeq : x.w ∘ P.g = fun w : ℂ => x.w (P.g w) := rfl
  have hdzF := dz_comp hgdiff hwdiff
  have hdzbarF := dzbar_comp hgdiff hwdiff
  have hdzF' : dz (x.w ∘ P.g) z
      = dz x.w (P.g z) * (dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)) := by
    rw [hcompeq, hdzF, hwbelt]
    ring
  have hdzbarF' : dzbar (x.w ∘ P.g) z
      = dz x.w (P.g z) * (dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)) := by
    rw [hcompeq, hdzbarF, hwbelt]
    ring
  -- nonvanishing from the positive Jacobians
  have hpne : dz x.w (P.g z) ≠ 0 := by
    intro h0
    rw [det_fderiv_eq_wirtinger, h0] at hwdet
    simp only [norm_zero] at hwdet
    nlinarith [norm_nonneg (dzbar x.w (P.g z)), sq_nonneg ‖dzbar x.w (P.g z)‖]
  have hgs : ‖dzbar P.g z‖ < ‖dz P.g z‖ := by
    rw [det_fderiv_eq_wirtinger] at hjac
    nlinarith [norm_nonneg (dz P.g z), norm_nonneg (dzbar P.g z)]
  have htle : ‖dzbar P.g z‖ ≤ max P.κ 0 * ‖dz P.g z‖ :=
    le_trans hbelt (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  -- the shared cross term and the two squared-norm expansions
  have hnumSq : ‖dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)‖ ^ 2
      = ‖dzbar P.g z‖ ^ 2 + ‖x.b.μ (P.g z)‖ ^ 2 * ‖dz P.g z‖ ^ 2
        + 2 * (dz P.g z * dzbar P.g z * starRingEnd ℂ (x.b.μ (P.g z))).re := by
    simp only [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_conj]
    have hcross : dzbar P.g z * starRingEnd ℂ (x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z))
        = dz P.g z * dzbar P.g z * starRingEnd ℂ (x.b.μ (P.g z)) := by
      rw [map_mul, Complex.conj_conj]
      ring
    rw [hcross]
  have hdenSq : ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖ ^ 2
      = ‖dz P.g z‖ ^ 2 + ‖x.b.μ (P.g z)‖ ^ 2 * ‖dzbar P.g z‖ ^ 2
        + 2 * (dz P.g z * dzbar P.g z * starRingEnd ℂ (x.b.μ (P.g z))).re := by
    simp only [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_conj]
    have hcross : dz P.g z * starRingEnd ℂ (x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z))
        = dz P.g z * dzbar P.g z * starRingEnd ℂ (x.b.μ (P.g z)) := by
      rw [map_mul, Complex.conj_conj]
      ring
    rw [hcross]
  have hRb : |(dz P.g z * dzbar P.g z * starRingEnd ℂ (x.b.μ (P.g z))).re|
      ≤ ‖x.b.μ (P.g z)‖ * ‖dz P.g z‖ * ‖dzbar P.g z‖ := by
    refine le_trans (Complex.abs_re_le_norm _) ?_
    rw [norm_mul, norm_mul, RCLike.norm_conj]
    exact le_of_eq (by ring)
  have hkey2 := hsharp (max P.κ 0) x.b.normInf ‖dz P.g z‖ ‖dzbar P.g z‖ ‖x.b.μ (P.g z)‖
    ((dz P.g z * dzbar P.g z * starRingEnd ℂ (x.b.μ (P.g z))).re)
    ha0 ha1 hbw0 hbw1 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) htle hwmu hRb
  have hkey3 : ‖dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)‖ ^ 2
      * (1 + max P.κ 0 * x.b.normInf) ^ 2
      ≤ (max P.κ 0 + x.b.normInf) ^ 2
        * ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖ ^ 2 := by
    rw [hnumSq, hdenSq]
    exact hkey2
  have hnormle : ‖dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)‖
      * (1 + max P.κ 0 * x.b.normInf)
      ≤ (max P.κ 0 + x.b.normInf)
        * ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖ := by
    nlinarith [hkey3,
      mul_nonneg (norm_nonneg (dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)))
        h1pab.le,
      mul_nonneg (show (0:ℝ) ≤ max P.κ 0 + x.b.normInf by linarith)
        (norm_nonneg (dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)))]
  -- positivity of the denominator
  have hdenpos : 0 < ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖ := by
    have h4 := norm_add_le (dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z))
      (-(x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)))
    simp only [add_neg_cancel_right, norm_neg] at h4
    have h5 : ‖x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖
        ≤ x.b.normInf * ‖dzbar P.g z‖ := by
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_right hwmu (norm_nonneg _)
    have h6 : x.b.normInf * ‖dzbar P.g z‖ < ‖dz P.g z‖ :=
      lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hbw1.le) hgs
    linarith
  have hFdzpos : 0 < ‖dz (x.w ∘ P.g) z‖ := by
    rw [hdzF', norm_mul]
    exact mul_pos (norm_pos_iff.mpr hpne) hdenpos
  have hnumle : ‖dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)‖
      ≤ (max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf)
        * ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h1pab]
    exact hnormle
  have hquot : ‖wirtingerQuotient (x.w ∘ P.g) z‖
      ≤ (max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf) := by
    have hq : wirtingerQuotient (x.w ∘ P.g) z
        = dzbar (x.w ∘ P.g) z / dz (x.w ∘ P.g) z := rfl
    rw [hq, norm_div, div_le_iff₀ hFdzpos]
    calc ‖dzbar (x.w ∘ P.g) z‖
        = ‖dz x.w (P.g z)‖
          * ‖dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)‖ := by
          rw [hdzbarF', norm_mul]
      _ ≤ ‖dz x.w (P.g z)‖ * ((max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf)
          * ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖) :=
        mul_le_mul_of_nonneg_left hnumle (norm_nonneg _)
      _ = (max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf)
          * (‖dz x.w (P.g z)‖
            * ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖) := by ring
      _ = (max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf)
          * ‖dz (x.w ∘ P.g) z‖ := by rw [hdzF', norm_mul]
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hquot

/-- The Wirtinger quotient of a re-marked solution satisfies the `Γ₀`-invariance law on the
upper half plane: chain the compatibility of the re-marking with the equivariance of the
normalized solution through the almost-everywhere chain rule. -/
theorem wirtingerQuotient_remark_invariant (x : TeichRep Γ₀) (P : ModGroupUpper Γ₀) :
    ∀ γ ∈ Γ₀, ∀ᵐ z : ℂ ∂(volume.restrict {z : ℂ | 0 < z.im}),
      wirtingerQuotient (x.w ∘ P.g) (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
        = wirtingerQuotient (x.w ∘ P.g) z
          * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 := by
  intro γ hγ
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have hUopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  -- Wirtinger measurability of the re-marking map
  have hg1 : Measurable fun z : ℂ => (fderiv ℝ P.g z) 1 :=
    (measurable_fderiv ℝ P.g).apply_continuousLinearMap 1
  have hgI : Measurable fun z : ℂ => (fderiv ℝ P.g z) Complex.I :=
    (measurable_fderiv ℝ P.g).apply_continuousLinearMap Complex.I
  have hdzg : Measurable (dz P.g) := by
    change Measurable fun z : ℂ => (1 / 2 : ℂ)
      * ((fderiv ℝ P.g z) 1 - Complex.I * (fderiv ℝ P.g z) Complex.I)
    exact (hg1.sub (hgI.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have hdzbarg : Measurable (dzbar P.g) := by
    change Measurable fun z : ℂ => (1 / 2 : ℂ)
      * ((fderiv ℝ P.g z) 1 + Complex.I * (fderiv ℝ P.g z) Complex.I)
    exact (hg1.add (hgI.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have hdetmeas : Measurable fun z : ℂ => (fderiv ℝ P.g z).det := by
    have hfun : (fun z : ℂ => (fderiv ℝ P.g z).det)
        = fun z : ℂ => ‖dz P.g z‖ ^ 2 - ‖dzbar P.g z‖ ^ 2 :=
      funext fun z => det_fderiv_eq_wirtinger P.g z
    rw [hfun]
    exact (hdzg.norm.pow_const 2).sub (hdzbarg.norm.pow_const 2)
  -- preimages of null sets under `P.g` are null on the differentiability set
  have hpull : ∀ N : Set ℂ, volume N = 0 →
      ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
        (DifferentiableAt ℝ P.g z ∧ 0 < (fderiv ℝ P.g z).det) → P.g z ∉ N := by
    intro N hN
    have hgae : AEMeasurable P.g (volume.restrict {z : ℂ | 0 < z.im}) :=
      P.qc.cont.aemeasurable hU
    have hgeq : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), P.g z = hgae.mk P.g z :=
      hgae.ae_eq_mk
    have hbadnull : (volume.restrict {z : ℂ | 0 < z.im})
        {z : ℂ | ¬ P.g z = hgae.mk P.g z} = 0 := ae_iff.mp hgeq
    obtain ⟨T, hTsub, hTmeas, hTnull⟩ : ∃ T : Set ℂ,
        {z : ℂ | ¬ P.g z = hgae.mk P.g z} ⊆ T ∧ MeasurableSet T
          ∧ (volume.restrict {z : ℂ | 0 < z.im}) T = 0 :=
      ⟨toMeasurable (volume.restrict {z : ℂ | 0 < z.im}) {z : ℂ | ¬ P.g z = hgae.mk P.g z},
        subset_toMeasurable _ _, measurableSet_toMeasurable _ _,
        by rw [measure_toMeasurable]; exact hbadnull⟩
    obtain ⟨N', hNsub, hN'meas, hN'null⟩ : ∃ N' : Set ℂ,
        N ⊆ N' ∧ MeasurableSet N' ∧ volume N' = 0 :=
      ⟨toMeasurable volume N, subset_toMeasurable _ _, measurableSet_toMeasurable _ _,
        by rw [measure_toMeasurable]; exact hN⟩
    set S : Set ℂ := ({z : ℂ | 0 < z.im} ∩ {z : ℂ | DifferentiableAt ℝ P.g z}
      ∩ {z : ℂ | 0 < (fderiv ℝ P.g z).det} ∩ (hgae.mk P.g ⁻¹' N')) \ T with hSdef
    have hSmeas : MeasurableSet S :=
      (((hU.inter (measurableSet_of_differentiableAt ℝ P.g)).inter
        (measurableSet_lt measurable_const hdetmeas)).inter
          (hgae.measurable_mk hN'meas)).diff hTmeas
    have hSfacts : ∀ z ∈ S, 0 < z.im ∧ DifferentiableAt ℝ P.g z
        ∧ 0 < (fderiv ℝ P.g z).det ∧ P.g z ∈ N' ∧ z ∉ T := by
      intro z hz
      rw [hSdef] at hz
      obtain ⟨⟨⟨⟨hz1, hz2⟩, hz3⟩, hz4⟩, hz5⟩ := hz
      have hgz : P.g z = hgae.mk P.g z := by
        by_contra hne
        exact hz5 (hTsub hne)
      exact ⟨hz1, hz2, hz3, by rw [hgz]; exact hz4, hz5⟩
    have hfd : ∀ z ∈ S, HasFDerivWithinAt P.g (fderiv ℝ P.g z) S z := fun z hz =>
      ((hSfacts z hz).2.1.hasFDerivAt).hasFDerivWithinAt
    have hinjS : Set.InjOn P.g S := by
      intro p hp q hq hpq
      have h1 := P.qc.left_inv p (hSfacts p hp).1
      have h2 := P.qc.left_inv q (hSfacts q hq).1
      rw [← h1, ← h2, hpq]
    have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hfd hinjS
      (fun _ => (1 : ℝ≥0∞))
    rw [setLIntegral_one] at hcov
    simp only [mul_one] at hcov
    have himgnull : volume (P.g '' S) = 0 := by
      refine le_antisymm (le_trans (measure_mono ?_) hN'null.le) (zero_le)
      rintro w ⟨z, hz, rfl⟩
      exact (hSfacts z hz).2.2.2.1
    have hint0 : ∫⁻ z in S, ENNReal.ofReal |(fderiv ℝ P.g z).det| = 0 := by
      rw [← hcov]
      exact himgnull
    have hSnull : volume S = 0 := by
      have hmeasint : Measurable fun z : ℂ => ENNReal.ofReal |(fderiv ℝ P.g z).det| :=
        (continuous_abs.measurable.comp hdetmeas).ennreal_ofReal
      have h2 := (lintegral_eq_zero_iff hmeasint).mp hint0
      have h2' : ∀ᵐ z ∂(volume.restrict S),
          ENNReal.ofReal |(fderiv ℝ P.g z).det| = 0 := by
        filter_upwards [h2] with z hz2
        simpa using hz2
      have h3 : ∀ᵐ z : ℂ, z ∈ S → ENNReal.ofReal |(fderiv ℝ P.g z).det| = 0 :=
        (ae_restrict_iff' hSmeas).mp h2'
      rw [ae_iff] at h3
      refine le_antisymm (le_trans (measure_mono ?_) h3.le) (zero_le)
      intro z hz
      simp only [Set.mem_ofPred_eq, Classical.not_imp]
      refine ⟨hz, ?_⟩
      intro h0
      rw [ENNReal.ofReal_eq_zero] at h0
      have hpos := abs_pos.mpr (ne_of_gt (hSfacts z hz).2.2.1)
      linarith
    rw [ae_iff, Measure.restrict_apply' hU]
    have hTH : volume (T ∩ {z : ℂ | 0 < z.im}) = 0 := by
      rw [Measure.restrict_apply hTmeas] at hTnull
      exact hTnull
    refine measure_mono_null ?_ (measure_union_null hTH hSnull)
    intro z hz
    obtain ⟨hzbad, hzU⟩ := hz
    simp only [Set.mem_ofPred_eq, Classical.not_imp, not_not] at hzbad
    obtain ⟨⟨hdiff, hdet⟩, hgN⟩ := hzbad
    by_cases hzT : z ∈ T
    · exact Or.inl ⟨hzT, hzU⟩
    · refine Or.inr ?_
      rw [hSdef]
      have hgz : P.g z = hgae.mk P.g z := by
        by_contra hne
        exact hzT (hTsub hne)
      exact ⟨⟨⟨⟨hzU, hdiff⟩, hdet⟩, by rw [Set.mem_preimage, ← hgz]; exact hNsub hgN⟩, hzT⟩
  -- the exact conjugation identity on the upper half plane
  obtain ⟨γ', hγ'm, hcompat⟩ := P.compat γ hγ
  obtain ⟨W, hW⟩ := exists_sl2_equivariant x.w_isQCAnalytic x.w_zero x.w_one x.w_conj γ'
    (x.inv γ' hγ'm)
  have him0 : ∀ w : ℂ, 0 < w.im → (x.w w).im ≠ 0 := by
    rcases x.w_halfPlane_dichotomy with ⟨hpos, -⟩ | ⟨hneg, -⟩
    · exact fun w hw => ne_of_gt (hpos w hw)
    · exact fun w hw => ne_of_lt (hneg w hw)
  have hFconj : ∀ w : ℂ, 0 < w.im
      → (x.w ∘ P.g) (moebiusMap γ w) = moebiusMap W ((x.w ∘ P.g) w) := by
    intro w hw
    have hgw : 0 < (P.g w).im := P.qc.mapsTo w hw
    have h1 : P.g (moebiusMap γ w) = moebiusMap γ' (P.g w) := hcompat w hw
    change x.w (P.g (moebiusMap γ w)) = moebiusMap W (x.w (P.g w))
    rw [h1]
    exact hW (P.g w) (moebiusDenom_ne_zero_of_im_ne_zero γ' (ne_of_gt hgw))
  -- the composite is differentiable almost everywhere on the upper half plane
  have hwdiffae : ∀ᵐ w : ℂ, DifferentiableAt ℝ x.w w := by
    filter_upwards [x.w_isQCAnalytic.1.2] with w h1
    by_contra hnd
    rw [fderiv_zero_of_not_differentiableAt hnd] at h1
    simp [ContinuousLinearMap.det] at h1
  have hNnull : volume {w : ℂ | ¬ DifferentiableAt ℝ x.w w} = 0 := ae_iff.mp hwdiffae
  have hGood : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      DifferentiableAt ℝ (x.w ∘ P.g) z := by
    filter_upwards [P.qc.jac, hpull _ hNnull] with z hjac htr
    have hgdiff : DifferentiableAt ℝ P.g z := by
      by_contra hnd
      rw [fderiv_zero_of_not_differentiableAt hnd] at hjac
      simp [ContinuousLinearMap.det] at hjac
    have hw4 := htr ⟨hgdiff, hjac⟩
    simp only [not_not] at hw4
    exact hw4.comp z hgdiff
  have hGoodG : ∀ᵐ z : ℂ, z ∈ {z : ℂ | 0 < z.im} → DifferentiableAt ℝ (x.w ∘ P.g) z :=
    (ae_restrict_iff' hU).mp hGood
  -- transport of an a.e. plane statement along the Möbius map `γ`
  have haeMoeb : ∀ Q : ℂ → Prop,
      (∀ᵐ w : ℂ, Q w) → ∀ᵐ z : ℂ, moebiusDenom γ z ≠ 0 → Q (moebiusMap γ z) := by
    intro Q hQ
    have hopen : IsOpen {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0} := by
      have hc : Continuous (moebiusDenom γ⁻¹) := by
        unfold moebiusDenom
        fun_prop
      exact isOpen_compl_singleton.preimage hc
    rw [ae_iff] at hQ ⊢
    have himg : volume (moebiusMap γ⁻¹ ''
        (toMeasurable volume {w | ¬ Q w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0})) = 0 := by
      have hSmeas : MeasurableSet
          (toMeasurable volume {w | ¬ Q w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0}) :=
        (measurableSet_toMeasurable _ _).inter hopen.measurableSet
      have hSnull : volume
          (toMeasurable volume {w | ¬ Q w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0}) = 0 := by
        refine le_antisymm (le_trans (measure_mono Set.inter_subset_left) ?_) (zero_le)
        rw [measure_toMeasurable]
        exact hQ.le
      have hfd : ∀ w ∈ toMeasurable volume {w | ¬ Q w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0},
          HasFDerivWithinAt (moebiusMap γ⁻¹) (fderiv ℝ (moebiusMap γ⁻¹) w)
            (toMeasurable volume {w | ¬ Q w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0}) w := by
        intro w hw
        have hder := hasDerivAt_moebiusMap γ⁻¹ hw.2
        exact ((hder.complexToReal_fderiv).differentiableAt.hasFDerivAt).hasFDerivWithinAt
      have hinjOn : Set.InjOn (moebiusMap γ⁻¹)
          (toMeasurable volume {w | ¬ Q w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0}) := by
        intro a ha b hb hab
        have ha1 : moebiusMap γ (moebiusMap γ⁻¹ a) = a := by
          rw [moebiusMap_mul γ γ⁻¹ a ha.2, mul_inv_cancel, moebiusMap_one]
        have hb1 : moebiusMap γ (moebiusMap γ⁻¹ b) = b := by
          rw [moebiusMap_mul γ γ⁻¹ b hb.2, mul_inv_cancel, moebiusMap_one]
        rw [← ha1, ← hb1, hab]
      have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hfd hinjOn
        (fun _ => (1 : ℝ≥0∞))
      rw [setLIntegral_one, setLIntegral_measure_zero _ _ hSnull] at hcov
      exact hcov
    refine measure_mono_null ?_ himg
    intro z hz
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hz
    obtain ⟨hden, hbad⟩ := hz
    have hd1 : moebiusDenom γ⁻¹ (moebiusMap γ z) * moebiusDenom γ z = 1 := by
      rw [moebiusDenom_mul γ⁻¹ γ z hden, inv_mul_cancel, moebiusDenom_one]
    have hdinv : moebiusDenom γ⁻¹ (moebiusMap γ z) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hd1
      exact zero_ne_one hd1
    refine ⟨moebiusMap γ z, ⟨subset_toMeasurable _ _ hbad, hdinv⟩, ?_⟩
    rw [moebiusMap_mul γ⁻¹ γ z hden, inv_mul_cancel, moebiusMap_one]
  have hGoodT := haeMoeb (fun w : ℂ => w ∈ {z : ℂ | 0 < z.im}
    → DifferentiableAt ℝ (x.w ∘ P.g) w) hGoodG
  -- differentiate the exact conjugation identity at a.e. point of the upper half plane
  filter_upwards [ae_restrict_of_ae hGoodT, ae_restrict_mem hU, ae_restrict_of_ae hGoodG]
    with z htrans hzU hgood
  have hz : 0 < z.im := hzU
  have hdenγ : moebiusDenom γ z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ (ne_of_gt hz)
  have hγim : 0 < (moebiusMap γ z).im := moebiusMap_im_pos γ hz
  have hDz : DifferentiableAt ℝ (x.w ∘ P.g) z := hgood hzU
  have hDp : DifferentiableAt ℝ (x.w ∘ P.g) (moebiusMap γ z) := htrans hdenγ hγim
  have hev : (fun w : ℂ => (x.w ∘ P.g) (moebiusMap γ w))
      =ᶠ[nhds z] fun w : ℂ => moebiusMap W ((x.w ∘ P.g) w) := by
    filter_upwards [hUopen.mem_nhds hz] with w hw
    exact hFconj w hw
  have hfde : fderiv ℝ (fun w : ℂ => (x.w ∘ P.g) (moebiusMap γ w)) z
      = fderiv ℝ (fun w : ℂ => moebiusMap W ((x.w ∘ P.g) w)) z := hev.fderiv_eq
  have hdzEq : dz (fun w : ℂ => (x.w ∘ P.g) (moebiusMap γ w)) z
      = dz (fun w : ℂ => moebiusMap W ((x.w ∘ P.g) w)) z := by
    unfold dz
    rw [hfde]
  have hdzbEq : dzbar (fun w : ℂ => (x.w ∘ P.g) (moebiusMap γ w)) z
      = dzbar (fun w : ℂ => moebiusMap W ((x.w ∘ P.g) w)) z := by
    unfold dzbar
    rw [hfde]
  have hγd := hasDerivAt_moebiusMap γ hdenγ
  have hFzim : ((x.w ∘ P.g) z).im ≠ 0 := him0 (P.g z) (P.qc.mapsTo z hz)
  have hWd : moebiusDenom W ((x.w ∘ P.g) z) ≠ 0 :=
    moebiusDenom_ne_zero_of_im_ne_zero W hFzim
  have hWdd := hasDerivAt_moebiusMap W hWd
  have hLdz : dz (fun w : ℂ => (x.w ∘ P.g) (moebiusMap γ w)) z
      = dz (x.w ∘ P.g) (moebiusMap γ z) * ((moebiusDenom γ z) ^ 2)⁻¹ := by
    have hcr := dz_comp_of_holomorphicAt hγd.differentiableAt hDp
    rw [hγd.deriv] at hcr
    simpa [Function.comp_def] using hcr
  have hLdzb : dzbar (fun w : ℂ => (x.w ∘ P.g) (moebiusMap γ w)) z
      = dzbar (x.w ∘ P.g) (moebiusMap γ z)
        * starRingEnd ℂ (((moebiusDenom γ z) ^ 2)⁻¹) := by
    have hcr := dzbar_comp_of_holomorphicAt hγd.differentiableAt hDp
    rw [hγd.deriv] at hcr
    simpa [Function.comp_def] using hcr
  have hWreal : DifferentiableAt ℝ (moebiusMap W) ((x.w ∘ P.g) z) :=
    (differentiableAt_complex_iff_differentiableAt_real.mp hWdd.differentiableAt).1
  have hdzW : dz (moebiusMap W) ((x.w ∘ P.g) z)
      = ((moebiusDenom W ((x.w ∘ P.g) z)) ^ 2)⁻¹ := by
    rw [dz_eq_deriv_of_differentiableAt hWdd.differentiableAt, hWdd.deriv]
  have hdzbW : dzbar (moebiusMap W) ((x.w ∘ P.g) z) = 0 :=
    dzbar_eq_zero_of_differentiableAt hWdd.differentiableAt
  have hRdz : dz (fun w : ℂ => moebiusMap W ((x.w ∘ P.g) w)) z
      = ((moebiusDenom W ((x.w ∘ P.g) z)) ^ 2)⁻¹ * dz (x.w ∘ P.g) z := by
    have hcr := dz_comp hDz hWreal
    rw [hdzW, hdzbW, zero_mul, add_zero] at hcr
    exact hcr
  have hRdzb : dzbar (fun w : ℂ => moebiusMap W ((x.w ∘ P.g) w)) z
      = ((moebiusDenom W ((x.w ∘ P.g) z)) ^ 2)⁻¹ * dzbar (x.w ∘ P.g) z := by
    have hcr := dzbar_comp hDz hWreal
    rw [hdzW, hdzbW, zero_mul, add_zero] at hcr
    exact hcr
  have hEq1 : dz (x.w ∘ P.g) (moebiusMap γ z) * ((moebiusDenom γ z) ^ 2)⁻¹
      = ((moebiusDenom W ((x.w ∘ P.g) z)) ^ 2)⁻¹ * dz (x.w ∘ P.g) z := by
    rw [← hLdz, ← hRdz]
    exact hdzEq
  have hEq2 : dzbar (x.w ∘ P.g) (moebiusMap γ z)
      * starRingEnd ℂ (((moebiusDenom γ z) ^ 2)⁻¹)
      = ((moebiusDenom W ((x.w ∘ P.g) z)) ^ 2)⁻¹ * dzbar (x.w ∘ P.g) z := by
    rw [← hLdzb, ← hRdzb]
    exact hdzbEq
  -- divide out the two Wirtinger identities
  have hq1 : wirtingerQuotient (x.w ∘ P.g) (moebiusMap γ z)
      = dzbar (x.w ∘ P.g) (moebiusMap γ z) / dz (x.w ∘ P.g) (moebiusMap γ z) := rfl
  have hq2 : wirtingerQuotient (x.w ∘ P.g) z
      = dzbar (x.w ∘ P.g) z / dz (x.w ∘ P.g) z := rfl
  rw [hq1, hq2]
  have hD2 : (moebiusDenom γ z) ^ 2 ≠ 0 := pow_ne_zero 2 hdenγ
  have hE2 : (moebiusDenom W ((x.w ∘ P.g) z)) ^ 2 ≠ 0 := pow_ne_zero 2 hWd
  have hcD : starRingEnd ℂ (moebiusDenom γ z) ≠ 0 := by simpa using hdenγ
  have hcD2 : (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 ≠ 0 := pow_ne_zero 2 hcD
  rw [map_inv₀, map_pow] at hEq2
  by_cases hdzz : dz (x.w ∘ P.g) z = 0
  · have hA0 : dz (x.w ∘ P.g) (moebiusMap γ z) = 0 := by
      have h5 := hEq1
      rw [hdzz, mul_zero] at h5
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact h6
      · exact absurd h6 (inv_ne_zero hD2)
    rw [hA0, hdzz, div_zero, div_zero, zero_mul, zero_mul]
  · have hAne : dz (x.w ∘ P.g) (moebiusMap γ z) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hEq1
      rcases mul_eq_zero.mp hEq1.symm with h6 | h6
      · exact inv_ne_zero hE2 h6
      · exact hdzz h6
    have hAval : dz (x.w ∘ P.g) (moebiusMap γ z)
        = ((moebiusDenom W ((x.w ∘ P.g) z)) ^ 2)⁻¹ * dz (x.w ∘ P.g) z
          * (moebiusDenom γ z) ^ 2 := by
      have h7 := congrArg (fun t : ℂ => t * (moebiusDenom γ z) ^ 2) hEq1
      simpa [inv_mul_cancel_right₀ hD2] using h7
    have hBval : dzbar (x.w ∘ P.g) (moebiusMap γ z)
        = ((moebiusDenom W ((x.w ∘ P.g) z)) ^ 2)⁻¹ * dzbar (x.w ∘ P.g) z
          * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 := by
      have h8 := congrArg (fun t : ℂ => t * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2) hEq2
      simpa [inv_mul_cancel_right₀ hcD2] using h8
    rw [hAval, hBval]
    field_simp

end RiemannDynamics

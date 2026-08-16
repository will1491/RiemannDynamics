/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.ModuliAction.ModAction.Remark

/-!
# The re-marked solution is quasiconformal on the upper half plane

The composite of a normalized solution with an upper re-marking is an
upper-half-plane quasiconformal pair at the combined Beltrami bound.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

set_option maxHeartbeats 400000 in
-- The Sobolev field runs a two-scale mollification limit through the change-of-variables
-- estimate; the single-declaration elaboration exceeds the default heartbeat budget.
/-- Composition closure on the upper half plane: the re-marked solution `x.w ∘ P.g` is an
upper-half-plane quasiconformal map. Its inverse is the inverse re-marking after the
global inverse of the solution, and its coefficient bound is `(a + b) / (1 + a * b)` for
the re-marking bound `a = max P.κ 0` and the solution bound `b = ‖x.b.μ‖_∞`. -/
theorem TeichRep.isQCUpper_remark (x : TeichRep Γ₀) (P : ModGroupUpper Γ₀) :
    IsQCUpper (x.w ∘ P.g) (P.ginv ∘ Function.invFun x.w)
      ((max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf)) := by
  have hUopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have hxc : Continuous x.w := x.w_isQCAnalytic.1.1.continuous
  have hxinj : Function.Injective x.w := x.w_injective
  have hxsurj : Function.Surjective x.w := x.w_isQCAnalytic.1.1.bijective.surjective
  -- the image of the upper half plane is the upper half plane
  have hximg : x.w '' {z : ℂ | 0 < z.im} = {z : ℂ | 0 < z.im} := by
    rcases x.w_halfPlane_dichotomy with ⟨-, himg⟩ | ⟨hneg, -⟩
    · exact himg
    · exfalso
      have h1 : 0 < (Complex.I).im := by simp
      have h2 := x.w_mapsTo_upper Complex.I h1
      have h3 := hneg Complex.I h1
      linarith
  -- the global inverse of the normalized solution preserves the upper half plane
  have hinvmem : ∀ z : ℂ, 0 < z.im → 0 < (Function.invFun x.w z).im := by
    intro z hz
    have hzimg : z ∈ x.w '' {z : ℂ | 0 < z.im} := by
      rw [hximg]
      exact hz
    obtain ⟨u, hu, huz⟩ := hzimg
    have hval : Function.invFun x.w z = u := by
      rw [← huz]
      exact Function.leftInverse_invFun hxinj u
    rw [hval]
    exact hu
  -- identification of the set-inverse with the homeomorphism inverse
  have hhomeo : IsHomeomorph x.w := x.w_isQCAnalytic.1.1
  have hinvW : Function.invFun x.w = ⇑(IsHomeomorph.homeomorph x.w hhomeo).symm := by
    funext z
    apply hxinj
    rw [Function.invFun_eq (hxsurj z)]
    have h1 := (IsHomeomorph.homeomorph x.w hhomeo).apply_symm_apply z
    rw [IsHomeomorph.homeomorph_apply] at h1
    rw [h1]
  -- ===== Wirtinger measurability of the re-marking map =====
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
  -- ===== preimages of null sets under `P.g` are null on the positive-Jacobian set =====
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
  -- ===== dilatation constants =====
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
  -- ===== the sharp composition estimate on squared norms =====
  have hsharp : ∀ a b s t q R : ℝ, 0 ≤ a → a < 1 → 0 ≤ b → b < 1 → 0 ≤ s → 0 ≤ t →
      0 ≤ q → t ≤ a * s → q ≤ b → |R| ≤ q * s * t →
      (t ^ 2 + q ^ 2 * s ^ 2 + 2 * R) * (1 + a * b) ^ 2
        ≤ (a + b) ^ 2 * (s ^ 2 + q ^ 2 * t ^ 2 + 2 * R) := by
    intro a b s t q R ha0' ha1' hb0' hb1' hs ht hq htas hqb hRb
    have hqst : R ≤ q * s * t := (abs_le.mp hRb).2
    have hab0 : 0 ≤ a * b := mul_nonneg ha0' hb0'
    have hlin : (t + q * s) * (1 + a * b) ≤ (a + b) * (s + q * t) := by
      have ha2 : 0 ≤ 1 - a ^ 2 := by
        have hid : 1 - a ^ 2 = (1 - a) * (1 + a) := by ring
        rw [hid]
        exact mul_nonneg (by linarith) (by linarith)
      have h1 : 0 ≤ (1 - a ^ 2) * ((b - q) * s) :=
        mul_nonneg ha2 (mul_nonneg (by linarith) hs)
      have h2 : 0 ≤ (1 + a * b - q * (a + b)) * (a * s - t) := by
        refine mul_nonneg ?_ (by linarith)
        nlinarith [mul_le_mul_of_nonneg_right hqb (show (0:ℝ) ≤ a + b by linarith),
          mul_nonneg hb0' (sub_nonneg.mpr hb1'.le)]
      linarith [h1, h2]
    have hXnn : 0 ≤ (t + q * s) * (1 + a * b) :=
      mul_nonneg (add_nonneg ht (mul_nonneg hq hs)) (by linarith)
    have hsq : ((t + q * s) * (1 + a * b)) ^ 2 ≤ ((a + b) * (s + q * t)) ^ 2 :=
      pow_le_pow_left₀ hXnn hlin 2
    have hfac : 0 ≤ (q * s * t - R) * ((1 + a * b) ^ 2 - (a + b) ^ 2) := by
      refine mul_nonneg (by linarith) ?_
      have hyy : 0 ≤ ((1 + a) * (1 + b)) * ((1 - a) * (1 - b)) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith))
          (mul_nonneg (by linarith) (by linarith))
      have hid2 : (1 + a * b) ^ 2 - (a + b) ^ 2
          = ((1 + a) * (1 + b)) * ((1 - a) * (1 - b)) := by ring
      rw [hid2]
      exact hyy
    have h3 : (t ^ 2 + q ^ 2 * s ^ 2 + 2 * (q * s * t)) * (1 + a * b) ^ 2
        ≤ (a + b) ^ 2 * (s ^ 2 + q ^ 2 * t ^ 2 + 2 * (q * s * t)) := by
      calc (t ^ 2 + q ^ 2 * s ^ 2 + 2 * (q * s * t)) * (1 + a * b) ^ 2
          = ((t + q * s) * (1 + a * b)) ^ 2 := by ring
        _ ≤ ((a + b) * (s + q * t)) ^ 2 := hsq
        _ = (a + b) ^ 2 * (s ^ 2 + q ^ 2 * t ^ 2 + 2 * (q * s * t)) := by ring
    have h4 : 0 ≤ q * s * t * (1 + a * b) ^ 2 - R * (1 + a * b) ^ 2
        - q * s * t * (a + b) ^ 2 + R * (a + b) ^ 2 := by
      have hid3 : q * s * t * (1 + a * b) ^ 2 - R * (1 + a * b) ^ 2
          - q * s * t * (a + b) ^ 2 + R * (a + b) ^ 2
          = (q * s * t - R) * ((1 + a * b) ^ 2 - (a + b) ^ 2) := by ring
      rw [hid3]
      exact hfac
    linarith [h3, h4]
  -- ===== the almost-everywhere good set of the plane solution =====
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
  -- ===== the almost-everywhere Beltrami band of the composite =====
  have hband : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      ‖dzbar (x.w ∘ P.g) z‖
          ≤ (max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf)
            * ‖dz (x.w ∘ P.g) z‖
        ∧ 0 < ‖dz (x.w ∘ P.g) z‖ := by
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
      have hsq2 : (‖dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)‖
          * (1 + max P.κ 0 * x.b.normInf)) ^ 2
          ≤ ((max P.κ 0 + x.b.normInf)
            * ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖) ^ 2 := by
        calc (‖dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)‖
            * (1 + max P.κ 0 * x.b.normInf)) ^ 2
            = ‖dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)‖ ^ 2
              * (1 + max P.κ 0 * x.b.normInf) ^ 2 := by ring
          _ ≤ (max P.κ 0 + x.b.normInf) ^ 2
              * ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖ ^ 2 := hkey3
          _ = ((max P.κ 0 + x.b.normInf)
              * ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖) ^ 2 := by ring
      exact (pow_le_pow_iff_left₀
        (mul_nonneg (norm_nonneg _) h1pab.le)
        (mul_nonneg (by linarith) (norm_nonneg _)) (by norm_num)).mp hsq2
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
    refine ⟨?_, hFdzpos⟩
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- mapsTo
    intro z hz
    exact x.w_mapsTo_upper _ (P.qc.mapsTo z hz)
  · -- mapsTo'
    intro z hz
    exact P.qc.mapsTo' _ (hinvmem z hz)
  · -- left_inv
    intro z hz
    have h1 : Function.invFun x.w (x.w (P.g z)) = P.g z :=
      Function.leftInverse_invFun hxinj (P.g z)
    calc (P.ginv ∘ Function.invFun x.w) ((x.w ∘ P.g) z)
        = P.ginv (Function.invFun x.w (x.w (P.g z))) := rfl
      _ = P.ginv (P.g z) := by rw [h1]
      _ = z := P.qc.left_inv z hz
  · -- right_inv
    intro z hz
    have hu : 0 < (Function.invFun x.w z).im := hinvmem z hz
    have h1 : P.g (P.ginv (Function.invFun x.w z)) = Function.invFun x.w z :=
      P.qc.right_inv _ hu
    calc (x.w ∘ P.g) ((P.ginv ∘ Function.invFun x.w) z)
        = x.w (P.g (P.ginv (Function.invFun x.w z))) := rfl
      _ = x.w (Function.invFun x.w z) := by rw [h1]
      _ = z := Function.invFun_eq (hxsurj z)
  · -- cont
    exact hxc.comp_continuousOn P.qc.cont
  · -- cont'
    refine P.qc.cont'.comp ?_ ?_
    · rw [hinvW]
      exact (IsHomeomorph.homeomorph x.w hhomeo).symm.continuous.continuousOn
    · intro z hz
      exact hinvmem z hz
  · -- sobolev
    have hle1 : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by norm_num
    have hne0 : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by norm_num
    have : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
    have : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
    have : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
    have hxLI : LocallyIntegrable x.w volume := hxc.locallyIntegrable
    have hxdiff : ∀ᵐ w : ℂ, DifferentiableAt ℝ x.w w :=
      IsQCAnalytic.ae_differentiableAt x.w_isQCAnalytic
    -- ===== the pointwise linear-map representation in Wirtinger form =====
    have hrepr : ∀ (L : ℂ →L[ℝ] ℂ) (w : ℂ),
        L w = (1 / 2 : ℂ) * ((L 1) - Complex.I * (L Complex.I)) * w
          + (1 / 2 : ℂ) * ((L 1) + Complex.I * (L Complex.I)) * (starRingEnd ℂ w) := by
      intro L w
      have hLw : L w = (↑w.re : ℂ) * L 1 + (↑w.im : ℂ) * L Complex.I := by
        conv_lhs => rw [show w = w.re • (1 : ℂ) + w.im • Complex.I by
          rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
        rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
      have hcw : starRingEnd ℂ w = (↑w.re : ℂ) - ↑w.im * Complex.I := by
        conv_lhs => rw [← Complex.re_add_im w]
        simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
        ring
      have hw : w = (↑w.re : ℂ) + ↑w.im * Complex.I := (Complex.re_add_im w).symm
      rw [hLw, hcw]
      set a : ℂ := (↑w.re : ℂ) with ha
      set b : ℂ := (↑w.im : ℂ) with hb
      rw [hw]
      linear_combination (b * L Complex.I) * Complex.I_mul_I
    -- ===== a.e. good facts of `P.g` on the upper half plane =====
    have hggood : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
        DifferentiableAt ℝ P.g z ∧ 0 < (fderiv ℝ P.g z).det
          ∧ ‖dzbar P.g z‖ ≤ max P.κ 0 * ‖dz P.g z‖ := by
      filter_upwards [P.qc.jac, P.qc.belt] with z hjac hbelt
      have hgdiff : DifferentiableAt ℝ P.g z := by
        by_contra hnd
        rw [fderiv_zero_of_not_differentiableAt hnd] at hjac
        simp [ContinuousLinearMap.det] at hjac
      exact ⟨hgdiff, hjac,
        le_trans hbelt (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩
    -- ===== pointwise distortion: `‖(Dg)v‖² ≤ C₀ · det(Dg)` for unit `v` =====
    have hdistort : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), ∀ v : ℂ, ‖v‖ = 1 →
        ‖(fderiv ℝ P.g z) v‖ ^ 2
          ≤ (1 + max P.κ 0) / (1 - max P.κ 0) * (fderiv ℝ P.g z).det := by
      filter_upwards [hggood] with z hz v hv
      obtain ⟨hgdiff, hjac, hbelt⟩ := hz
      have happ : (fderiv ℝ P.g z) v = dz P.g z * v + dzbar P.g z * starRingEnd ℂ v := by
        have h1 := hrepr (fderiv ℝ P.g z) v
        rw [h1]
        simp only [dz, dzbar]
      have hnorm : ‖(fderiv ℝ P.g z) v‖ ≤ ‖dz P.g z‖ + ‖dzbar P.g z‖ := by
        rw [happ]
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, norm_mul, RCLike.norm_conj, hv, mul_one, mul_one]
      rw [det_fderiv_eq_wirtinger]
      set a := max P.κ 0 with hadef
      set s := ‖dz P.g z‖ with hsdef
      set t := ‖dzbar P.g z‖ with htdef
      have hs0 : 0 ≤ s := norm_nonneg _
      have ht0 : 0 ≤ t := norm_nonneg _
      have hden : 0 < 1 - a := by linarith
      have hB : ‖(fderiv ℝ P.g z) v‖ ^ 2 ≤ (s + t) ^ 2 := by
        have := norm_nonneg ((fderiv ℝ P.g z) v)
        nlinarith [hnorm]
      refine le_trans hB ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hden]
      nlinarith [mul_nonneg (sub_nonneg.mpr hbelt) (add_nonneg hs0 ht0)]
    -- ===== the almost-everywhere chain rule for the composite =====
    have hchain : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
        DifferentiableAt ℝ P.g z ∧ DifferentiableAt ℝ x.w (P.g z) ∧
          fderiv ℝ (x.w ∘ P.g) z = (fderiv ℝ x.w (P.g z)).comp (fderiv ℝ P.g z) := by
      have hN : volume {w : ℂ | ¬ DifferentiableAt ℝ x.w w} = 0 := ae_iff.mp hxdiff
      filter_upwards [hggood, hpull _ hN] with z hz htr
      obtain ⟨hgdiff, hjac, -⟩ := hz
      have hxd : DifferentiableAt ℝ x.w (P.g z) := by
        have h2 := htr ⟨hgdiff, hjac⟩
        simpa using h2
      exact ⟨hgdiff, hxd, fderiv_comp z hxd hgdiff⟩
    -- ===== the forward area estimate on subsets of the upper half plane =====
    have hArea : ∀ S : Set ℂ, MeasurableSet S → S ⊆ {z : ℂ | 0 < z.im} →
        ∀ B : Set ℂ, P.g '' S ⊆ B → ∀ h : ℂ → ℝ≥0∞,
        ∫⁻ z in S, ENNReal.ofReal ((fderiv ℝ P.g z).det) * h (P.g z)
          ≤ ∫⁻ u in B, h u := by
      intro S hSmeas hSsub B hB h
      set Sg := S ∩ ({z : ℂ | DifferentiableAt ℝ P.g z}
        ∩ {z : ℂ | 0 < (fderiv ℝ P.g z).det}) with hSgdef
      have hSgmeas : MeasurableSet Sg :=
        hSmeas.inter ((measurableSet_of_differentiableAt ℝ P.g).inter
          (measurableSet_lt measurable_const hdetmeas))
      have hSgsub : Sg ⊆ S := Set.inter_subset_left
      have hnull : volume (S \ Sg) = 0 := by
        have h1 : (volume.restrict {z : ℂ | 0 < z.im})
            {z : ℂ | ¬ (DifferentiableAt ℝ P.g z ∧ 0 < (fderiv ℝ P.g z).det)} = 0 :=
          ae_iff.mp (hggood.mono fun z hz => ⟨hz.1, hz.2.1⟩)
        rw [Measure.restrict_apply' hU] at h1
        refine measure_mono_null ?_ h1
        intro z hz
        obtain ⟨hzS, hzn⟩ := hz
        refine ⟨?_, hSsub hzS⟩
        intro hgood
        exact hzn ⟨hzS, hgood.1, hgood.2⟩
      have hSeq : Sg =ᵐ[volume] S := by
        refine ae_eq_set.mpr ⟨?_, hnull⟩
        rw [Set.sdiff_eq_empty.mpr hSgsub]
        exact measure_empty
      have hstep1 : ∫⁻ z in S, ENNReal.ofReal ((fderiv ℝ P.g z).det) * h (P.g z)
          = ∫⁻ z in Sg, ENNReal.ofReal ((fderiv ℝ P.g z).det) * h (P.g z) := by
        rw [Measure.restrict_congr_set hSeq]
      have hfd : ∀ z ∈ Sg, HasFDerivWithinAt P.g (fderiv ℝ P.g z) Sg z := fun z hz =>
        (hz.2.1.hasFDerivAt).hasFDerivWithinAt
      have hinj : Set.InjOn P.g Sg := by
        intro p hp q hq hpq
        have h1 := P.qc.left_inv p (hSsub (hSgsub hp))
        have h2 := P.qc.left_inv q (hSsub (hSgsub hq))
        rw [← h1, ← h2, hpq]
      have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSgmeas hfd hinj h
      have hstep2 : ∫⁻ z in Sg, ENNReal.ofReal ((fderiv ℝ P.g z).det) * h (P.g z)
          = ∫⁻ u in P.g '' Sg, h u := by
        rw [hcov]
        refine lintegral_congr_ae ?_
        refine (ae_restrict_iff' hSgmeas).mpr (Filter.Eventually.of_forall fun z hz => ?_)
        change ENNReal.ofReal ((fderiv ℝ P.g z).det) * h (P.g z)
          = ENNReal.ofReal |(fderiv ℝ P.g z).det| * h (P.g z)
        rw [abs_of_pos hz.2.2]
      have hstep3 : ∫⁻ u in P.g '' Sg, h u ≤ ∫⁻ u in B, h u := by
        refine lintegral_mono' (Measure.restrict_mono ?_ le_rfl) le_rfl
        exact subset_trans (Set.image_mono hSgsub) hB
      rw [hstep1, hstep2]
      exact hstep3
    -- ===== `L²` on compacts of the composite directional derivative =====
    have hgradL2 : ∀ v : ℂ, ‖v‖ = 1 →
        MemLpLocOn (fun z => (fderiv ℝ (x.w ∘ P.g) z) v) 2 {z : ℂ | 0 < z.im} := by
      intro v hv Kc hKcU hKcc
      have : IsFiniteMeasure (volume.restrict Kc) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hKcc.measure_lt_top⟩
      refine ⟨((measurable_fderiv ℝ (x.w ∘ P.g)).apply_continuousLinearMap
        v).aestronglyMeasurable, ?_⟩
      obtain ⟨R1, hR1⟩ : ∃ R1 : ℝ, P.g '' Kc ⊆ Metric.ball 0 R1 := by
        obtain ⟨R1, hR1⟩ := (hKcc.image_of_continuousOn
          (P.qc.cont.mono hKcU)).isBounded.subset_ball (0 : ℂ)
        exact ⟨R1, hR1⟩
      have hptwise : ∀ᵐ z ∂(volume.restrict Kc),
          ‖(fderiv ℝ (x.w ∘ P.g) z) v‖ₑ ^ 2
            ≤ ENNReal.ofReal ((fderiv ℝ P.g z).det)
              * (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                * ‖fderiv ℝ x.w (P.g z)‖ₑ ^ 2) := by
        have hres : volume.restrict Kc ≤ volume.restrict {z : ℂ | 0 < z.im} := by
          exact Measure.restrict_mono hKcU le_rfl
        have hC0 : (0:ℝ) ≤ (1 + max P.κ 0) / (1 - max P.κ 0) :=
          div_nonneg (by linarith) (by linarith)
        filter_upwards [(ae_mono hres) hchain, (ae_mono hres) hdistort,
          (ae_mono hres) hggood] with z hz hd hgg
        obtain ⟨hgdiff, hxd, hcomp⟩ := hz
        have hdet0 : (0:ℝ) ≤ (fderiv ℝ P.g z).det := hgg.2.1.le
        have h1 : ‖(fderiv ℝ (x.w ∘ P.g) z) v‖
            ≤ ‖fderiv ℝ x.w (P.g z)‖ * ‖(fderiv ℝ P.g z) v‖ := by
          rw [hcomp, ContinuousLinearMap.comp_apply]
          exact (fderiv ℝ x.w (P.g z)).le_opNorm _
        have h2 := hd v hv
        have h3 : ‖(fderiv ℝ (x.w ∘ P.g) z) v‖ ^ 2
            ≤ (fderiv ℝ P.g z).det
              * ((1 + max P.κ 0) / (1 - max P.κ 0) * ‖fderiv ℝ x.w (P.g z)‖ ^ 2) := by
          have h4 : ‖(fderiv ℝ (x.w ∘ P.g) z) v‖ ^ 2
              ≤ ‖fderiv ℝ x.w (P.g z)‖ ^ 2 * ‖(fderiv ℝ P.g z) v‖ ^ 2 := by
            have h5 := mul_self_le_mul_self (norm_nonneg _) h1
            have h6 : 0 ≤ ‖fderiv ℝ x.w (P.g z)‖ * ‖(fderiv ℝ P.g z) v‖ :=
              mul_nonneg (norm_nonneg _) (norm_nonneg _)
            nlinarith
          have h7 : (0:ℝ) ≤ ‖fderiv ℝ x.w (P.g z)‖ ^ 2 := sq_nonneg _
          nlinarith [mul_le_mul_of_nonneg_left h2 h7]
        calc ‖(fderiv ℝ (x.w ∘ P.g) z) v‖ₑ ^ 2
            = ENNReal.ofReal (‖(fderiv ℝ (x.w ∘ P.g) z) v‖ ^ 2) := by
              rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
          _ ≤ ENNReal.ofReal ((fderiv ℝ P.g z).det
                * ((1 + max P.κ 0) / (1 - max P.κ 0) * ‖fderiv ℝ x.w (P.g z)‖ ^ 2)) :=
              ENNReal.ofReal_le_ofReal h3
          _ = ENNReal.ofReal ((fderiv ℝ P.g z).det)
                * (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                  * ‖fderiv ℝ x.w (P.g z)‖ₑ ^ 2) := by
              rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
                ENNReal.ofReal_mul hdet0, ENNReal.ofReal_mul hC0]
      have hmain : ∫⁻ z in Kc, ‖(fderiv ℝ (x.w ∘ P.g) z) v‖ₑ ^ 2
          ≤ ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
            * ∫⁻ u in Metric.ball 0 R1, ‖fderiv ℝ x.w u‖ₑ ^ 2 := by
        refine le_trans (lintegral_mono_ae hptwise) ?_
        have h8 := hArea Kc hKcc.measurableSet hKcU (Metric.ball 0 R1) hR1
          (fun u => ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
            * ‖fderiv ℝ x.w u‖ₑ ^ 2)
        refine le_trans h8 ?_
        rw [lintegral_const_mul']
        exact ENNReal.ofReal_ne_top
      have hfin : ∫⁻ z in Kc, ‖(fderiv ℝ (x.w ∘ P.g) z) v‖ₑ ^ 2 < ⊤ := by
        refine lt_of_le_of_lt hmain ?_
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (lt_top_iff_ne_top.mpr (IsQCAnalytic.lintegralSq_fderiv_ball_ne_top
            x.w_isQCAnalytic R1))
      rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
      have hconv : ∀ z : ℂ, ‖(fderiv ℝ (x.w ∘ P.g) z) v‖ₑ ^ ((2:ℝ≥0∞).toReal)
          = ‖(fderiv ℝ (x.w ∘ P.g) z) v‖ₑ ^ (2:ℕ) := by
        intro z
        rw [ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast]
        norm_num
      simpa only [hconv] using hfin
    -- ===== the weak-derivative identity for the composite =====
    have hKEY : ∀ (v : ℂ) (gv0 : ℂ → ℂ), (v = 1 ∨ v = Complex.I) →
        HasWeakDirDeriv v gv0 P.g {z : ℂ | 0 < z.im} →
        MemLpLocOn gv0 2 {z : ℂ | 0 < z.im} →
        HasWeakDirDeriv v (fun z => (fderiv ℝ (x.w ∘ P.g) z) v) (x.w ∘ P.g)
          {z : ℂ | 0 < z.im} := by
      intro v gv0 hv1I hwd hgvL2
      have hv1 : ‖v‖ = 1 := by
        rcases hv1I with rfl | rfl
        · simp
        · simp
      intro φ hφs hφc hφsupp
      have hKc : IsCompact (tsupport φ) := hφc
      have hKU : tsupport φ ⊆ {z : ℂ | 0 < z.im} := hφsupp
      obtain ⟨d, hd0, hdU⟩ := hKc.exists_cthickening_subset_open hUopen hKU
      set r : ℝ := d / 3 with hrdef
      have hr0 : 0 < r := by rw [hrdef]; positivity
      have hmono : ∀ {s t : ℝ}, s ≤ t →
          Metric.cthickening s (tsupport φ) ⊆ Metric.cthickening t (tsupport φ) :=
        fun hst => Metric.cthickening_mono hst _
      have hK1U : Metric.cthickening r (tsupport φ) ⊆ {z : ℂ | 0 < z.im} :=
        (hmono (by rw [hrdef]; linarith)).trans hdU
      have hK3meas : MeasurableSet (Metric.cthickening d (tsupport φ)) :=
        Metric.isClosed_cthickening.measurableSet
      have hK3c : IsCompact (Metric.cthickening d (tsupport φ)) := hKc.cthickening
      have hK3fin : IsFiniteMeasure (volume.restrict (Metric.cthickening d (tsupport φ))) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hK3c.measure_lt_top⟩
      -- ===== the smooth cutoff, by mollifying an indicator =====
      set β : ContDiffBump (0:ℂ) :=
        { rIn := r / 2, rOut := r,
          rIn_pos := by positivity,
          rIn_lt_rOut := by linarith } with hβdef
      set ind : ℂ → ℝ :=
        (Metric.cthickening (2*r) (tsupport φ)).indicator (fun _ => (1:ℝ)) with hinddef
      have hindmeas : Measurable ind :=
        measurable_const.indicator Metric.isClosed_cthickening.measurableSet
      have hindLI : LocallyIntegrable ind volume := by
        refine Integrable.locallyIntegrable ?_
        rw [hinddef, integrable_indicator_iff Metric.isClosed_cthickening.measurableSet]
        refine integrableOn_const ?_ ?_
        · exact hKc.cthickening.measure_lt_top.ne
        · simp
      set χ : ℂ → ℝ :=
        MeasureTheory.convolution (β.normed volume) ind
          (ContinuousLinearMap.lsmul ℝ ℝ) volume with hχdef
      have hβsupp : Function.support (β.normed volume) ⊆ Metric.ball 0 r := by
        rw [β.support_normed_eq]
      have hχsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ :=
        HasCompactSupport.contDiff_convolution_left _ β.hasCompactSupport_normed
          β.contDiff_normed hindLI
      have hcthstep : ∀ {δ : ℝ}, 0 ≤ δ → ∀ z w : ℂ, z ∈ Metric.cthickening δ (tsupport φ) →
          dist w z ≤ r → w ∈ Metric.cthickening (δ + r) (tsupport φ) := by
        intro δ hδ0 z w hz hd'
        rw [Metric.mem_cthickening_iff] at hz ⊢
        refine le_trans (Metric.infEDist_le_infEDist_add_edist (y := z)) ?_
        rw [edist_dist]
        calc Metric.infEDist z (tsupport φ) + ENNReal.ofReal (dist w z)
            ≤ ENNReal.ofReal δ + ENNReal.ofReal r :=
              add_le_add hz (ENNReal.ofReal_le_ofReal hd')
          _ = ENNReal.ofReal (δ + r) := (ENNReal.ofReal_add hδ0 hr0.le).symm
      -- ===== values of the cutoff =====
      have hχ1 : ∀ z ∈ Metric.cthickening r (tsupport φ), χ z = 1 := by
        intro z hz
        have h := dist_convolution_le (μ := volume) (z₀ := (1:ℝ)) (x₀ := z) (R := r)
          (le_refl (0:ℝ)) hβsupp β.nonneg_normed β.integral_normed
          hindmeas.aestronglyMeasurable
          (fun w hw => by
            have hw2 : w ∈ Metric.cthickening (r + r) (tsupport φ) :=
              hcthstep hr0.le z w hz (Metric.mem_ball.mp hw).le
            have hw2' : w ∈ Metric.cthickening (2*r) (tsupport φ) := by
              rw [show (2:ℝ)*r = r + r by ring]
              exact hw2
            rw [hinddef]
            rw [Set.indicator_of_mem hw2']
            simp)
        have h2 : dist (χ z) 1 = 0 := le_antisymm h dist_nonneg
        exact dist_eq_zero.mp h2
      have hχ0 : ∀ z : ℂ, z ∉ Metric.cthickening d (tsupport φ) → χ z = 0 := by
        intro z hz
        have h := dist_convolution_le (μ := volume) (z₀ := (0:ℝ)) (x₀ := z) (R := r)
          (le_refl (0:ℝ)) hβsupp β.nonneg_normed β.integral_normed
          hindmeas.aestronglyMeasurable
          (fun w hw => by
            have hwn : w ∉ Metric.cthickening (2*r) (tsupport φ) := by
              intro hwc
              have hz2 : z ∈ Metric.cthickening (2*r + r) (tsupport φ) := by
                refine hcthstep (by linarith) w z hwc ?_
                rw [dist_comm]
                exact (Metric.mem_ball.mp hw).le
              have h3 : (2*r + r : ℝ) = d := by rw [hrdef]; ring
              rw [h3] at hz2
              exact hz hz2
            rw [hinddef]
            rw [Set.indicator_of_notMem hwn]
            simp)
        have h2 : dist (χ z) 0 = 0 := le_antisymm h dist_nonneg
        simpa using dist_eq_zero.mp h2
      have hχ01 : ∀ z : ℂ, 0 ≤ χ z ∧ χ z ≤ 1 := by
        intro z
        have h := dist_convolution_le (μ := volume) (z₀ := ((1:ℝ)/2)) (x₀ := z) (R := r)
          (ε := (1:ℝ)/2) (by norm_num) hβsupp β.nonneg_normed β.integral_normed
          hindmeas.aestronglyMeasurable
          (fun w _ => by
            rw [hinddef]
            by_cases hw2 : w ∈ Metric.cthickening (2*r) (tsupport φ)
            · rw [Set.indicator_of_mem hw2]
              rw [Real.dist_eq]
              norm_num
            · rw [Set.indicator_of_notMem hw2]
              rw [Real.dist_eq]
              norm_num)
        rw [Real.dist_eq] at h
        have h2 := abs_le.mp h
        constructor <;> linarith [h2.1, h2.2]
      have htsχ : tsupport χ ⊆ Metric.cthickening d (tsupport φ) := by
        refine closure_minimal ?_ Metric.isClosed_cthickening
        intro z hz
        by_contra hzn
        exact hz (hχ0 z hzn)
      have hdχ0 : ∀ z ∈ Metric.thickening r (tsupport φ), fderiv ℝ χ z = 0 := by
        intro z hz
        have hev : χ =ᶠ[nhds z] fun _ => (1:ℝ) :=
          Filter.eventually_of_mem (Metric.isOpen_thickening.mem_nhds hz)
            (fun w hw => hχ1 w (Metric.thickening_subset_cthickening _ _ hw))
        rw [Filter.EventuallyEq.fderiv_eq hev]
        simp
      have hdχK3 : ∀ z : ℂ, z ∉ Metric.cthickening d (tsupport φ) → fderiv ℝ χ z = 0 := by
        intro z hz
        have hev : χ =ᶠ[nhds z] fun _ => (0:ℝ) :=
          Filter.eventually_of_mem
            (Metric.isClosed_cthickening.isOpen_compl.mem_nhds hz)
            (fun w hw => hχ0 w hw)
        rw [Filter.EventuallyEq.fderiv_eq hev]
        simp
      -- ===== the localized inner map and its weak derivative datum =====
      set gt : ℂ → ℂ := fun w => if 0 < w.im then P.g w else 0 with hgtdef
      have hgtU : ∀ w : ℂ, 0 < w.im → gt w = P.g w := fun w hw => if_pos hw
      have hgtcont : ContinuousOn gt {z : ℂ | 0 < z.im} :=
        P.qc.cont.congr fun w hw => if_pos hw
      set G : ℂ → ℂ := fun w => χ w • gt w with hGdef
      have hGeq : ∀ w ∈ Metric.cthickening r (tsupport φ), G w = P.g w := by
        intro w hw
        rw [hGdef]
        simp only
        rw [hχ1 w hw, hgtU w (hK1U hw)]
        exact one_smul ℝ _
      have hGzero : ∀ w : ℂ, w ∉ Metric.cthickening d (tsupport φ) → G w = 0 := by
        intro w hw
        rw [hGdef]
        simp only
        rw [hχ0 w hw]
        exact zero_smul ℝ _
      have hGcont : Continuous G := by
        rw [continuous_iff_continuousAt]
        intro w
        by_cases hw : 0 < w.im
        · exact (hχsmooth.continuous.continuousOn.smul hgtcont).continuousAt
            (hUopen.mem_nhds hw)
        · have hwn : w ∉ Metric.cthickening d (tsupport φ) := fun hc => hw (hdU hc)
          have hev : G =ᶠ[nhds w] fun _ => (0:ℂ) :=
            Filter.eventually_of_mem
              (Metric.isClosed_cthickening.isOpen_compl.mem_nhds hwn)
              (fun u hu => hGzero u hu)
          exact ContinuousAt.congr (continuousAt_const (y := (0:ℂ))) hev.symm
      have hGsupp : HasCompactSupport G :=
        HasCompactSupport.intro hKc.cthickening hGzero
      have hGLI : LocallyIntegrable G volume := hGcont.locallyIntegrable
      have hGunif : UniformContinuous G :=
        hGsupp.uniformContinuous_of_continuous hGcont
      -- ===== the localized weak-derivative datum =====
      set Gv : ℂ → ℂ := fun w => χ w • gv0 w + ((fderiv ℝ χ w) v) • gt w with hGvdef
      have hGvzero : ∀ w : ℂ, w ∉ Metric.cthickening d (tsupport φ) → Gv w = 0 := by
        intro w hw
        rw [hGvdef]
        simp only
        rw [hχ0 w hw, hdχK3 w hw]
        simp
      have hGvind : Gv = (Metric.cthickening d (tsupport φ)).indicator Gv := by
        funext w
        by_cases hw : w ∈ Metric.cthickening d (tsupport φ)
        · rw [Set.indicator_of_mem hw]
        · rw [Set.indicator_of_notMem hw, hGvzero w hw]
      have hgv0K3 : MemLp gv0 2 (volume.restrict (Metric.cthickening d (tsupport φ))) :=
        hgvL2 _ hdU hK3c
      have hgtK3 : AEStronglyMeasurable gt
          (volume.restrict (Metric.cthickening d (tsupport φ))) :=
        ((hgtcont.mono hdU).aemeasurable hK3meas).aestronglyMeasurable
      have hχcont : Continuous χ := hχsmooth.continuous
      have hdχvcont : Continuous fun w => (fderiv ℝ χ w) v := by
        have h1 : Continuous fun w => fderiv ℝ χ w :=
          hχsmooth.continuous_fderiv hne0
        exact h1.clm_apply continuous_const
      have hpc1 : MemLp (fun w => χ w • gv0 w) 2
          (volume.restrict (Metric.cthickening d (tsupport φ))) := by
        refine MemLp.of_le hgv0K3 (hχcont.aestronglyMeasurable.smul
          hgv0K3.aestronglyMeasurable) ?_
        refine Filter.Eventually.of_forall fun w => ?_
        rw [norm_smul]
        have h2 : ‖χ w‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_le]
          exact ⟨by linarith [(hχ01 w).1], (hχ01 w).2⟩
        exact mul_le_of_le_one_left (norm_nonneg _) h2
      obtain ⟨M1, hM1⟩ := hK3c.exists_bound_of_continuousOn (hgtcont.mono hdU)
      obtain ⟨M2, hM2⟩ := hK3c.exists_bound_of_continuousOn hdχvcont.continuousOn
      have hpc2 : MemLp (fun w => ((fderiv ℝ χ w) v) • gt w) 2
          (volume.restrict (Metric.cthickening d (tsupport φ))) := by
        refine MemLp.of_bound (hdχvcont.aestronglyMeasurable.smul hgtK3)
          (max M2 0 * max M1 0) ?_
        refine (ae_restrict_iff' hK3meas).mpr (Filter.Eventually.of_forall fun w hw => ?_)
        rw [norm_smul]
        refine mul_le_mul (le_trans (hM2 w hw) (le_max_left _ _))
          (le_trans (hM1 w hw) (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
      have hGvK3L2 : MemLp Gv 2
          (volume.restrict (Metric.cthickening d (tsupport φ))) := by
        have h3 := hpc1.add hpc2
        exact h3
      have hGvsm : AEStronglyMeasurable Gv volume := by
        rw [hGvind]
        exact (aestronglyMeasurable_indicator_iff hK3meas).mpr hGvK3L2.aestronglyMeasurable
      have hGvL2 : MemLp Gv 2 volume := by
        refine ⟨hGvsm, ?_⟩
        have h4 : eLpNorm Gv 2 volume
            = eLpNorm Gv 2 (volume.restrict (Metric.cthickening d (tsupport φ))) := by
          conv_lhs => rw [hGvind]
          exact eLpNorm_indicator_eq_eLpNorm_restrict hK3meas
        rw [h4]
        exact hGvK3L2.2
      have hGvInt : Integrable Gv volume := by
        rw [hGvind, integrable_indicator_iff hK3meas]
        exact (hGvK3L2.mono_exponent one_le_two).integrable le_rfl
      have hGvLI : LocallyIntegrable Gv volume := hGvInt.locallyIntegrable
      have hχd : Differentiable ℝ χ := hχsmooth.differentiable hne0
      -- ===== integrability of the cutoff pairings =====
      have hIntgt : ∀ c : ℂ → ℝ, Continuous c →
          (∀ w : ℂ, w ∉ Metric.cthickening d (tsupport φ) → c w = 0) →
          Integrable (fun w => c w • gt w) volume := by
        intro c hc hczero
        have hind : (fun w => c w • gt w)
            = (Metric.cthickening d (tsupport φ)).indicator (fun w => c w • gt w) := by
          funext w
          by_cases hw : w ∈ Metric.cthickening d (tsupport φ)
          · rw [Set.indicator_of_mem hw]
          · rw [Set.indicator_of_notMem hw, hczero w hw]
            exact zero_smul ℝ _
        rw [hind, integrable_indicator_iff hK3meas]
        obtain ⟨Mc, hMc⟩ := hK3c.exists_bound_of_continuousOn hc.continuousOn
        have hmb : MemLp (fun w => c w • gt w) 1
            (volume.restrict (Metric.cthickening d (tsupport φ))) := by
          refine MemLp.of_bound (hc.aestronglyMeasurable.smul hgtK3)
            (max Mc 0 * max M1 0) ?_
          refine (ae_restrict_iff' hK3meas).mpr (Filter.Eventually.of_forall fun w hw => ?_)
          rw [norm_smul]
          refine mul_le_mul (le_trans (hMc w hw) (le_max_left _ _))
            (le_trans (hM1 w hw) (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
        exact hmb.integrable le_rfl
      have hIntgv : ∀ c : ℂ → ℝ, Continuous c →
          (∀ w : ℂ, w ∉ Metric.cthickening d (tsupport φ) → c w = 0) →
          Integrable (fun w => c w • gv0 w) volume := by
        intro c hc hczero
        have hind : (fun w => c w • gv0 w)
            = (Metric.cthickening d (tsupport φ)).indicator (fun w => c w • gv0 w) := by
          funext w
          by_cases hw : w ∈ Metric.cthickening d (tsupport φ)
          · rw [Set.indicator_of_mem hw]
          · rw [Set.indicator_of_notMem hw, hczero w hw]
            exact zero_smul ℝ _
        rw [hind, integrable_indicator_iff hK3meas]
        obtain ⟨Mc, hMc⟩ := hK3c.exists_bound_of_continuousOn hc.continuousOn
        have hmb : MemLp (fun w => c w • gv0 w) 2
            (volume.restrict (Metric.cthickening d (tsupport φ))) := by
          refine MemLp.of_le (hgv0K3.const_smul (max Mc 0))
            (hc.aestronglyMeasurable.smul hgv0K3.aestronglyMeasurable) ?_
          refine (ae_restrict_iff' hK3meas).mpr (Filter.Eventually.of_forall fun w hw => ?_)
          rw [norm_smul, Pi.smul_apply, norm_smul]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          have h10 : ‖max Mc 0‖ = max Mc 0 := Real.norm_of_nonneg (le_max_right _ _)
          rw [h10]
          exact le_trans (hMc w hw) (le_max_left _ _)
        exact (hmb.mono_exponent one_le_two).integrable le_rfl
      -- ===== the weak directional derivative of the localization on the plane =====
      have hGweak : HasWeakDirDeriv v Gv G Set.univ := by
        intro ψ hψs hψc hψsub
        have hψd : Differentiable ℝ ψ := hψs.differentiable hne0
        have hψχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => ψ w * χ w) := hψs.mul hχsmooth
        have hψχc : HasCompactSupport (fun w => ψ w * χ w) := hψc.mul_right
        have hψχts : tsupport (fun w => ψ w * χ w)
            ⊆ Metric.cthickening d (tsupport φ) := by
          refine subset_trans (closure_mono ?_) htsχ
          intro w hw
          rw [Function.mem_support] at hw ⊢
          intro h0
          exact hw (by rw [h0, mul_zero])
        have hψχU : tsupport (fun w => ψ w * χ w) ⊆ {z : ℂ | 0 < z.im} :=
          hψχts.trans hdU
        have hIBP := hwd (fun w => ψ w * χ w) hψχs hψχc hψχU
        have hprod : ∀ z : ℂ, (fderiv ℝ (fun w => ψ w * χ w) z) v
            = ψ z * ((fderiv ℝ χ z) v) + χ z * ((fderiv ℝ ψ z) v) := by
          intro z
          have h13 : HasFDerivAt (fun w => ψ w * χ w)
              (ψ z • fderiv ℝ χ z + χ z • fderiv ℝ ψ z) z :=
            (hψd z).hasFDerivAt.mul (hχd z).hasFDerivAt
          rw [h13.fderiv]
          simp [add_apply, smul_apply, smul_eq_mul]
        have hdψχ0 : ∀ z : ℂ, z ∉ Metric.cthickening d (tsupport φ) →
            (fderiv ℝ (fun w => ψ w * χ w) z) v = 0 := by
          intro z hz
          have h5 : z ∉ tsupport (fun w => ψ w * χ w) := fun hc => hz (hψχts hc)
          have h6 : fderiv ℝ (fun w => ψ w * χ w) z = 0 := by
            by_contra h8
            exact h5 (support_fderiv_subset ℝ (Function.mem_support.mpr h8))
          rw [h6]
          rfl
        have hLrw : ∫ z, ((fderiv ℝ (fun w => ψ w * χ w) z) v) • P.g z
            = ∫ z, ((fderiv ℝ (fun w => ψ w * χ w) z) v) • gt z := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          change ((fderiv ℝ (fun w => ψ w * χ w) z) v) • P.g z
            = ((fderiv ℝ (fun w => ψ w * χ w) z) v) • gt z
          by_cases hz : 0 < z.im
          · rw [hgtU z hz]
          · have hz3 : z ∉ Metric.cthickening d (tsupport φ) := fun hc => hz (hdU hc)
            rw [hdψχ0 z hz3]
            simp
        have hsplit : ∀ z : ℂ, ((fderiv ℝ ψ z) v) • G z
            = ((fderiv ℝ (fun w => ψ w * χ w) z) v) • gt z
              - (ψ z * ((fderiv ℝ χ z) v)) • gt z := by
          intro z
          rw [hGdef]
          simp only
          rw [hprod z]
          simp only [Complex.real_smul]
          push_cast
          ring
        have hdψχcont : Continuous fun z => (fderiv ℝ (fun w => ψ w * χ w) z) v :=
          (hψχs.continuous_fderiv hne0).clm_apply continuous_const
        have hI1 : Integrable
            (fun z => ((fderiv ℝ (fun w => ψ w * χ w) z) v) • gt z) volume :=
          hIntgt _ hdψχcont hdψχ0
        have hI2 : Integrable (fun z => (ψ z * ((fderiv ℝ χ z) v)) • gt z) volume :=
          hIntgt _ (hψs.continuous.mul hdχvcont)
            (fun w hw => by rw [hdχK3 w hw]; simp)
        have hI3 : Integrable (fun z => (ψ z * χ z) • gv0 z) volume :=
          hIntgv _ (hψs.continuous.mul hχcont)
            (fun w hw => by rw [hχ0 w hw]; simp)
        calc ∫ z, ((fderiv ℝ ψ z) v) • G z
            = ∫ z, (((fderiv ℝ (fun w => ψ w * χ w) z) v) • gt z
                - (ψ z * ((fderiv ℝ χ z) v)) • gt z) :=
              integral_congr_ae (Filter.Eventually.of_forall fun z => hsplit z)
          _ = (∫ z, ((fderiv ℝ (fun w => ψ w * χ w) z) v) • gt z)
                - ∫ z, (ψ z * ((fderiv ℝ χ z) v)) • gt z := integral_sub hI1 hI2
          _ = (∫ z, ((fderiv ℝ (fun w => ψ w * χ w) z) v) • P.g z)
                - ∫ z, (ψ z * ((fderiv ℝ χ z) v)) • gt z := by rw [hLrw]
          _ = (- ∫ z, ((fun w => ψ w * χ w) z) • gv0 z)
                - ∫ z, (ψ z * ((fderiv ℝ χ z) v)) • gt z := by rw [hIBP]
          _ = - ((∫ z, (ψ z * χ z) • gv0 z)
                + ∫ z, (ψ z * ((fderiv ℝ χ z) v)) • gt z) := by ring
          _ = - ∫ z, ((ψ z * χ z) • gv0 z + (ψ z * ((fderiv ℝ χ z) v)) • gt z) := by
              rw [integral_add hI3 hI2]
          _ = - ∫ z, ψ z • Gv z := by
              refine congrArg Neg.neg
                (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))
              rw [hGvdef]
              simp only [Complex.real_smul]
              push_cast
              ring
      -- ===== almost-everywhere differentiability of the localization =====
      have haxis : ∀ᵐ z : ℂ, z.im ≠ 0 := by
        rw [ae_iff]
        have hset : {a : ℂ | ¬a.im ≠ 0} = {z : ℂ | z.im = 0} := by
          ext a
          simp
        rw [hset]
        exact volume_imZero
      have hgae2 : ∀ᵐ z : ℂ, z ∈ {z : ℂ | 0 < z.im} →
          (DifferentiableAt ℝ P.g z ∧ 0 < (fderiv ℝ P.g z).det) :=
        (ae_restrict_iff' hU).mp (hggood.mono fun z hz => ⟨hz.1, hz.2.1⟩)
      have hGdiff : ∀ᵐ z : ℂ, DifferentiableAt ℝ G z := by
        filter_upwards [haxis, hgae2] with z hz1 hz2
        rcases lt_or_gt_of_ne hz1 with hneg | hpos
        · have hzn : z ∉ Metric.cthickening d (tsupport φ) := by
            intro hc
            have h11 : (0:ℝ) < z.im := hdU hc
            linarith
          have hev : G =ᶠ[nhds z] fun _ => (0:ℂ) :=
            Filter.eventually_of_mem
              (Metric.isClosed_cthickening.isOpen_compl.mem_nhds hzn)
              (fun u hu => hGzero u hu)
          exact (differentiableAt_const (0:ℂ)).congr_of_eventuallyEq hev
        · obtain ⟨hgd, hdet⟩ := hz2 hpos
          have hev : G =ᶠ[nhds z] fun w => χ w • P.g w :=
            Filter.eventually_of_mem (hUopen.mem_nhds hpos)
              (fun w hw => by
                rw [hGdef]
                simp only
                rw [hgtU w hw])
          exact ((hχd z).smul hgd).congr_of_eventuallyEq hev
      have hGveq : ∀ᵐ z : ℂ, (fderiv ℝ G z) v = Gv z :=
        fderiv_ae_eq_weakDirDeriv hGweak (locallyIntegrableOn_univ.mpr hGvLI)
          hGdiff hv1I hGLI
      have hGveqPg : ∀ᵐ z : ℂ, z ∈ Metric.thickening r (tsupport φ) →
          Gv z = (fderiv ℝ P.g z) v := by
        filter_upwards [hGveq] with z hz hmem
        have hev : G =ᶠ[nhds z] P.g :=
          Filter.eventually_of_mem (Metric.isOpen_thickening.mem_nhds hmem)
            (fun w hw => hGeq w (Metric.thickening_subset_cthickening _ _ hw))
        rw [← hz, Filter.EventuallyEq.fderiv_eq hev]
      -- ===== the mollifier sequence =====
      set Θ : ℕ → ContDiffBump (0:ℂ) := fun n =>
        { rIn := 1/(n+2), rOut := 2/(n+2),
          rIn_pos := by positivity,
          rIn_lt_rOut := by
            have h1 : (0:ℝ) < 1/((n:ℝ)+2) := by positivity
            have h2 : (2:ℝ)/((n:ℝ)+2) = 1/((n:ℝ)+2) + 1/((n:ℝ)+2) := by ring
            linarith } with hΘdef
      have hΘrout : Filter.Tendsto (fun n : ℕ => (Θ n).rOut) Filter.atTop (nhds 0) := by
        have h1 := (tendsto_const_div_atTop_nhds_zero_nat (2:ℝ)).comp
          (Filter.tendsto_add_atTop_nat 2)
        have h2 : ((fun n : ℕ => (2:ℝ)/(n:ℝ)) ∘ fun n : ℕ => n + 2)
            = fun n : ℕ => (Θ n).rOut := by
          funext n
          simp only [Function.comp, hΘdef]
          push_cast
          ring
        rwa [h2] at h1
      have hΘsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, (Θ n).rOut < ε :=
        fun ε hε => hΘrout.eventually_lt_const hε
      have hΘsupp : ∀ n, Function.support ((Θ n).normed volume)
          ⊆ Metric.ball 0 ((Θ n).rOut) := by
        intro n
        rw [(Θ n).support_normed_eq]
      -- ===== the two mollifications =====
      set A : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((Θ n).normed volume) x.w
        (ContinuousLinearMap.lsmul ℝ ℝ) volume with hAdef
      have hAsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A n) := fun n =>
        HasCompactSupport.contDiff_convolution_left _ (Θ n).hasCompactSupport_normed
          (Θ n).contDiff_normed hxLI
      set gm : ℕ → ℂ → ℂ := fun m => MeasureTheory.convolution ((Θ m).normed volume) G
        (ContinuousLinearMap.lsmul ℝ ℝ) volume with hgmdef
      have hgmsm : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gm m) := fun m =>
        HasCompactSupport.contDiff_convolution_left _ (Θ m).hasCompactSupport_normed
          (Θ m).contDiff_normed hGLI
      set CV : ℕ → ℂ → ℂ := fun m => MeasureTheory.convolution ((Θ m).normed volume) Gv
        (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCVdef
      have hgmderiv : ∀ (m : ℕ) (z : ℂ), (fderiv ℝ (gm m) z) v = CV m z := fun m z =>
        fderiv_convolution_normed_apply_eq hGweak hGLI hGvLI (Θ m).contDiff_normed
          (Θ m).hasCompactSupport_normed z
      have hCVcont : ∀ m : ℕ, Continuous (CV m) := fun m =>
        HasCompactSupport.continuous_convolution_left _
          (Θ m).hasCompactSupport_normed ((Θ m).contDiff_normed (n := 0)).continuous
          hGvLI
      have hCVconv : Filter.Tendsto (fun m => eLpNorm (CV m - Gv) 2 volume)
          Filter.atTop (nhds 0) :=
        eLpNorm_convolution_normed_sub_tendsto_zero hGvL2 Θ hΘrout
      -- ===== uniform convergence of the inner mollification =====
      have hgmconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in Filter.atTop, ∀ w : ℂ,
          dist (gm m w) (G w) ≤ ε := by
        intro ε hε
        obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.mp hGunif ε hε
        filter_upwards [hΘsmall δ hδ0] with m hm w
        refine dist_convolution_le hε.le (hΘsupp m) (Θ m).nonneg_normed
          (Θ m).integral_normed hGcont.aestronglyMeasurable ?_
        intro u hu
        exact (hδ (lt_of_lt_of_le (Metric.mem_ball.mp hu) hm.le)).le
      -- ===== the image compact, its ball, and uniform outer convergence =====
      set Kg : Set ℂ := P.g '' tsupport φ with hKgdef
      have hKgc : IsCompact Kg := hKc.image_of_continuousOn (P.qc.cont.mono hKU)
      obtain ⟨R0, hR0⟩ := hKgc.isBounded.subset_ball (0:ℂ)
      set Kg1 : Set ℂ := Metric.cthickening 1 Kg with hKg1def
      have hKg1c : IsCompact Kg1 := hKgc.cthickening
      have hKgsub : Kg ⊆ Kg1 := Metric.self_subset_cthickening _
      have hnearKg1 : ∀ u ∈ Kg, ∀ w : ℂ, dist w u ≤ 1 → w ∈ Kg1 := by
        intro u hu w hw
        rw [hKg1def, Metric.mem_cthickening_iff]
        refine le_trans (Metric.infEDist_le_infEDist_add_edist (y := u)) ?_
        rw [Metric.infEDist_zero_of_mem hu, zero_add, edist_dist]
        exact ENNReal.ofReal_le_ofReal hw
      have hAconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, ∀ u ∈ Kg,
          dist (A n u) (x.w u) ≤ ε := by
        intro ε hε
        have huc := hKg1c.uniformContinuousOn_of_continuous hxc.continuousOn
        obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
        filter_upwards [hΘsmall (min δ 1) (lt_min hδ0 one_pos)] with n hn u hu
        refine dist_convolution_le hε.le (hΘsupp n) (Θ n).nonneg_normed
          (Θ n).integral_normed hxc.aestronglyMeasurable ?_
        intro w hw
        have hd1 : dist w u < min δ 1 := lt_of_lt_of_le (Metric.mem_ball.mp hw) hn.le
        have hwKg1 : w ∈ Kg1 :=
          hnearKg1 u hu w (le_trans hd1.le (min_le_right _ _))
        exact (hδ w hwKg1 u (hKgsub hu) (lt_of_lt_of_le hd1 (min_le_left _ _))).le
      -- ===== the mollified-differential energy decay on the image ball =====
      have henergy := mollified_fderiv_ball_energy_tendsto_zero x.w_isQCAnalytic R0 Θ hΘrout
      -- ===== support and bound bookkeeping for the test function =====
      have hKmeas : MeasurableSet (tsupport φ) := (isClosed_tsupport φ).measurableSet
      have hKvol : volume (tsupport φ) < ⊤ := hKc.measure_lt_top
      have hφzero : ∀ z : ℂ, z ∉ tsupport φ → φ z = 0 :=
        fun z hz => image_eq_zero_of_notMem_tsupport hz
      have hdφcont : Continuous fun z : ℂ => (fderiv ℝ φ z) v :=
        (hφs.continuous_fderiv hne0).clm_apply continuous_const
      have hdφzero : ∀ z : ℂ, z ∉ tsupport φ → (fderiv ℝ φ z) v = 0 := by
        intro z hz
        have h6 : fderiv ℝ φ z = 0 := by
          by_contra h8
          exact hz (support_fderiv_subset ℝ (Function.mem_support.mpr h8))
        rw [h6]
        rfl
      obtain ⟨Mφ0, hMφ0⟩ := hKc.exists_bound_of_continuousOn hφs.continuous.continuousOn
      have hMφ : ∀ z : ℂ, ‖φ z‖ ≤ max Mφ0 0 := by
        intro z
        by_cases hz : z ∈ tsupport φ
        · exact le_trans (hMφ0 z hz) (le_max_left _ _)
        · rw [hφzero z hz, norm_zero]
          exact le_max_right _ _
      obtain ⟨Md0, hMd0⟩ := hKc.exists_bound_of_continuousOn hdφcont.continuousOn
      have hMdφ : ∀ z : ℂ, ‖(fderiv ℝ φ z) v‖ ≤ max Md0 0 := by
        intro z
        by_cases hz : z ∈ tsupport φ
        · exact le_trans (hMd0 z hz) (le_max_left _ _)
        · rw [hdφzero z hz, norm_zero]
          exact le_max_right _ _
      -- ===== integrability engines =====
      have hIntCont : ∀ (c : ℂ → ℝ) (H : ℂ → ℂ), Continuous c →
          (∀ z : ℂ, z ∉ tsupport φ → c z = 0) → Continuous H →
          Integrable (fun z => c z • H z) volume := by
        intro c H hc hc0 hH
        refine (hc.smul hH).integrable_of_hasCompactSupport ?_
        refine HasCompactSupport.intro hKc fun z hz => ?_
        change c z • H z = 0
        rw [hc0 z hz]
        exact zero_smul ℝ _
      have hIntCLM : ∀ (T : ℂ → (ℂ →L[ℝ] ℂ)), Continuous T → ∀ (MT : ℝ),
          (∀ z ∈ tsupport φ, ‖T z‖ ≤ MT) → ∀ (Y : ℂ → ℂ), AEStronglyMeasurable Y volume →
          Integrable Y volume → Integrable (fun z => φ z • ((T z) (Y z))) volume := by
        intro T hT MT hMT Y hYm hYi
        have hsm : AEStronglyMeasurable (fun z => φ z • ((T z) (Y z))) volume := by
          refine (hφs.continuous.aestronglyMeasurable).smul ?_
          have h1 : Continuous fun p : (ℂ →L[ℝ] ℂ) × ℂ => p.1 p.2 :=
            isBoundedBilinearMap_apply.continuous
          exact h1.comp_aestronglyMeasurable ((hT.aestronglyMeasurable).prodMk hYm)
        refine Integrable.mono' (hYi.norm.const_mul (max Mφ0 0 * max MT 0)) hsm ?_
        refine Filter.Eventually.of_forall fun z => ?_
        rw [norm_smul]
        by_cases hz : z ∈ tsupport φ
        · have h2 : ‖(T z) (Y z)‖ ≤ max MT 0 * ‖Y z‖ :=
            le_trans ((T z).le_opNorm _) (mul_le_mul_of_nonneg_right
              (le_trans (hMT z hz) (le_max_left _ _)) (norm_nonneg _))
          calc ‖φ z‖ * ‖(T z) (Y z)‖
              ≤ (max Mφ0 0) * (max MT 0 * ‖Y z‖) :=
                mul_le_mul (hMφ z) h2 (norm_nonneg _) (le_max_right _ _)
            _ = max Mφ0 0 * max MT 0 * ‖Y z‖ := by ring
        · rw [hφzero z hz, norm_zero, zero_mul]
          positivity
      -- ===== lintegral support restriction =====
      have hlsupp : ∀ X : ℂ → ℂ, (∀ z : ℂ, z ∉ tsupport φ → X z = 0) →
          ∫⁻ z, ‖X z‖ₑ = ∫⁻ z in tsupport φ, ‖X z‖ₑ := by
        intro X hX0
        rw [← lintegral_indicator hKmeas]
        congr 1
        funext z
        by_cases hz : z ∈ tsupport φ
        · rw [Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz, hX0 z hz]
          simp
      -- ===== the `ε`-threshold engine in `ℝ≥0∞` =====
      have hthreshold : ∀ (D : ℝ≥0∞), D ≠ ⊤ → ∀ ε : ℝ≥0∞, 0 < ε →
          ∃ ε' : ℝ, 0 < ε' ∧ ENNReal.ofReal ε' * D ≤ ε := by
        intro D hD ε hε
        by_cases hεtop : ε = ⊤
        · exact ⟨1, one_pos, by rw [hεtop]; exact le_top⟩
        · have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
          have hDr : 0 ≤ D.toReal := ENNReal.toReal_nonneg
          refine ⟨ε.toReal / (D.toReal + 1), by positivity, ?_⟩
          have hDle : D ≤ ENNReal.ofReal D.toReal := le_of_eq (ENNReal.ofReal_toReal hD).symm
          calc ENNReal.ofReal (ε.toReal / (D.toReal + 1)) * D
              ≤ ENNReal.ofReal (ε.toReal / (D.toReal + 1))
                * ENNReal.ofReal D.toReal := mul_le_mul_right hDle _
            _ = ENNReal.ofReal (ε.toReal / (D.toReal + 1) * D.toReal) := by
                rw [ENNReal.ofReal_mul (by positivity)]
            _ ≤ ENNReal.ofReal ε.toReal := by
                refine ENNReal.ofReal_le_ofReal ?_
                rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
                nlinarith
            _ = ε := ENNReal.ofReal_toReal hεtop
      -- ===== the sup-convergence L¹ engine =====
      have hsupL1 : ∀ (c : ℂ → ℝ) (Mc : ℝ), (∀ z : ℂ, ‖c z‖ ≤ Mc) →
          (∀ z : ℂ, z ∉ tsupport φ → c z = 0) →
          ∀ (H : ℕ → ℂ → ℂ) (Hl : ℂ → ℂ),
          (∀ ε : ℝ, 0 < ε → ∀ᶠ m in Filter.atTop, ∀ z ∈ tsupport φ, ‖H m z - Hl z‖ ≤ ε) →
          Filter.Tendsto (fun m => ∫⁻ z, ‖c z • H m z - c z • Hl z‖ₑ)
            Filter.atTop (nhds 0) := by
        intro c Mc hMc hc0 H Hl hconv
        rw [ENNReal.tendsto_atTop_zero]
        intro ε hε
        obtain ⟨ε', hε'0, hε'⟩ := hthreshold
          (ENNReal.ofReal (Mc + 1) * volume (tsupport φ))
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKvol.ne) ε hε
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hconv ε' hε'0)
        refine ⟨N, fun m hm => ?_⟩
        have hbd : ∫⁻ z, ‖c z • H m z - c z • Hl z‖ₑ
            ≤ ENNReal.ofReal ((Mc + 1) * ε') * volume (tsupport φ) := by
          have heq0 : ∀ z : ℂ, c z • H m z - c z • Hl z = c z • (H m z - Hl z) :=
            fun z => (smul_sub _ _ _).symm
          have hsupp0 : ∀ z : ℂ, z ∉ tsupport φ → c z • H m z - c z • Hl z = 0 := by
            intro z hz
            rw [heq0 z, hc0 z hz]
            exact zero_smul ℝ _
          rw [hlsupp _ hsupp0]
          have hptb : ∀ z ∈ tsupport φ, ‖c z • H m z - c z • Hl z‖ₑ
              ≤ ENNReal.ofReal ((Mc + 1) * ε') := by
            intro z hz
            rw [heq0 z, ← ofReal_norm]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [norm_smul]
            have hMc0 : 0 ≤ Mc := le_trans (norm_nonneg _) (hMc 0)
            refine mul_le_mul (le_trans (hMc z) (by linarith)) (hN m hm z hz)
              (norm_nonneg _) (by linarith)
          calc ∫⁻ z in tsupport φ, ‖c z • H m z - c z • Hl z‖ₑ
              ≤ ∫⁻ _ in tsupport φ, ENNReal.ofReal ((Mc + 1) * ε') := by
                refine lintegral_mono_ae ?_
                exact (ae_restrict_iff' hKmeas).mpr (Filter.Eventually.of_forall hptb)
            _ = ENNReal.ofReal ((Mc + 1) * ε') * volume (tsupport φ) := by
                rw [setLIntegral_const]
        refine le_trans hbd ?_
        have heq1 : ENNReal.ofReal ((Mc + 1) * ε')
            = ENNReal.ofReal ε' * ENNReal.ofReal (Mc + 1) := by
          rw [← ENNReal.ofReal_mul (by
            have hMc0 : 0 ≤ Mc := le_trans (norm_nonneg _) (hMc 0)
            linarith)]
          ring_nf
        rw [heq1, mul_assoc]
        exact hε'
      -- ===== an `L²`-to-`L¹` restriction bound on the support =====
      have hL2K : ∀ Y : ℂ → ℂ, AEStronglyMeasurable Y volume →
          ∫⁻ z in tsupport φ, ‖Y z‖ₑ
            ≤ eLpNorm Y 2 volume * (volume (tsupport φ)) ^ ((1:ℝ)/2) := by
        intro Y hY
        have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq
          (volume.restrict (tsupport φ)) (by constructor <;> norm_num :
            (2:ℝ).HolderConjugate 2)
          (f := fun z => ‖Y z‖ₑ) (g := fun _ => 1)
          (hY.enorm.restrict) aemeasurable_const
        simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow] at hcs
        refine le_trans hcs ?_
        have h2 : (∫⁻ z in tsupport φ, ‖Y z‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)
            ≤ eLpNorm Y 2 volume := by
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
          simp only [ENNReal.toReal_ofNat]
          rw [one_div]
          exact ENNReal.rpow_le_rpow (setLIntegral_le_lintegral _ _) (by norm_num)
        have h3 : (∫⁻ (_ : ℂ) in tsupport φ, (1:ℝ≥0∞)) ^ ((1:ℝ)/2)
            = (volume (tsupport φ)) ^ ((1:ℝ)/2) := by
          rw [setLIntegral_one]
        rw [h3]
        exact mul_le_mul_left h2 _
      -- ===== the per-`n` mollified identity =====
      have hGKg : ∀ z ∈ tsupport φ, G z ∈ Kg := by
        intro z hz
        rw [hGeq z (Metric.self_subset_cthickening _ hz)]
        exact ⟨z, hz, rfl⟩
      have hGvfin : ∫⁻ z in tsupport φ, ‖Gv z‖ₑ < ⊤ :=
        lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hGvInt.2
      set QD : ℕ → ℂ → ℝ≥0∞ :=
        fun n u => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ with hQDdef
      set CB : ℝ≥0∞ := (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
        * volume (tsupport φ)) ^ ((1:ℝ)/2) with hCBdef
      have hEn : ∀ n : ℕ, ∫ z, ((fderiv ℝ φ z) v) • (A n (G z))
          = - ∫ z, φ z • ((fderiv ℝ (A n) (G z)) (Gv z)) := by
        intro n
        have hDncont : Continuous fun u : ℂ => fderiv ℝ (A n) u :=
          (hAsm n).continuous_fderiv hne0
        obtain ⟨MD0, hMD0⟩ := hKg1c.exists_bound_of_continuousOn hDncont.continuousOn
        -- (I) per-`m` smooth integration by parts
        have hIBPm : ∀ m : ℕ, ∫ z, ((fderiv ℝ φ z) v) • (A n (gm m z))
            = - ∫ z, φ z • ((fderiv ℝ (A n) (gm m z))
                ((CV m) z)) := by
          intro m
          have hcomp : ContDiffOn ℝ 1 (A n ∘ gm m) Set.univ :=
            (((hAsm n).comp (hgmsm m)).of_le hle1).contDiffOn
          have hIBP0 := HasWeakDirDeriv.of_contDiffOn (v := v) isOpen_univ hcomp φ hφs hφc
            (Set.subset_univ _)
          calc ∫ z, ((fderiv ℝ φ z) v) • (A n (gm m z))
              = ∫ z, ((fderiv ℝ φ z) v) • ((A n ∘ gm m) z) := rfl
            _ = - ∫ z, φ z • ((fderiv ℝ (A n ∘ gm m) z) v) := hIBP0
            _ = - ∫ z, φ z • ((fderiv ℝ (A n) (gm m z))
                  ((CV m) z)) := by
                refine congrArg Neg.neg (integral_congr_ae
                  (Filter.Eventually.of_forall fun z => ?_))
                have hd1 : DifferentiableAt ℝ (A n) (gm m z) :=
                  ((hAsm n).differentiable hne0).differentiableAt
                have hd2 : DifferentiableAt ℝ (gm m) z :=
                  ((hgmsm m).differentiable hne0).differentiableAt
                simp only
                rw [fderiv_comp z hd1 hd2, ContinuousLinearMap.comp_apply, hgmderiv m z]
        -- (II) the left `m`-limit
        have hLconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in Filter.atTop, ∀ z ∈ tsupport φ,
            ‖A n (gm m z) - A n (G z)‖ ≤ ε := by
          intro ε hε
          have hucA := hKg1c.uniformContinuousOn_of_continuous
            (hAsm n).continuous.continuousOn
          obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.mp hucA ε hε
          filter_upwards [hgmconv (min (δ/2) 1) (lt_min (by linarith) one_pos)] with m hm z hz
          have h1 := hm z
          have hGz : G z ∈ Kg1 := hKgsub (hGKg z hz)
          have hgmz : gm m z ∈ Kg1 :=
            hnearKg1 (G z) (hGKg z hz) (gm m z) (le_trans h1 (min_le_right _ _))
          have h2 : dist (gm m z) (G z) < δ :=
            lt_of_le_of_lt (le_trans h1 (min_le_left _ _)) (by linarith)
          rw [← dist_eq_norm]
          exact (hδ (gm m z) hgmz (G z) hGz h2).le
        have hLlim : Filter.Tendsto (fun m => ∫ z, ((fderiv ℝ φ z) v) • (A n (gm m z)))
            Filter.atTop (nhds (∫ z, ((fderiv ℝ φ z) v) • (A n (G z)))) := by
          refine tendsto_integral_of_L1 _ (hIntCont _ _ hdφcont hdφzero
            ((hAsm n).continuous.comp hGcont)).aestronglyMeasurable ?_ ?_
          · exact Filter.Eventually.of_forall fun m =>
              hIntCont _ _ hdφcont hdφzero ((hAsm n).continuous.comp (hgmsm m).continuous)
          · exact hsupL1 _ _ hMdφ hdφzero _ _ hLconv
        -- (III) the right `m`-limit
        have hRlim : Filter.Tendsto (fun m => ∫ z, φ z • ((fderiv ℝ (A n) (gm m z))
              ((CV m) z)))
            Filter.atTop (nhds (∫ z, φ z • ((fderiv ℝ (A n) (G z)) (Gv z)))) := by
          have hTcont : Continuous fun z => fderiv ℝ (A n) (G z) := hDncont.comp hGcont
          have hTbd : ∀ z ∈ tsupport φ, ‖fderiv ℝ (A n) (G z)‖ ≤ MD0 :=
            fun z hz => hMD0 _ (hKgsub (hGKg z hz))
          refine tendsto_integral_of_L1 _
            (hIntCLM _ hTcont MD0 hTbd Gv hGvsm hGvInt).aestronglyMeasurable ?_ ?_
          · filter_upwards with m
            exact hIntCont _ _ hφs.continuous hφzero
              ((hDncont.comp (hgmsm m).continuous).clm_apply (hCVcont m))
          · -- the `L¹` difference limit
            rw [ENNReal.tendsto_atTop_zero]
            intro ε hε
            set CMD : ℝ≥0∞ := ENNReal.ofReal (max Mφ0 0 * (max MD0 0 + 1)) with hCMDdef
            have hCMDtop : CMD ≠ ⊤ := ENNReal.ofReal_ne_top
            set Cvol : ℝ≥0∞ := (volume (tsupport φ)) ^ ((1:ℝ)/2) with hCvoldef
            have hCvoltop : Cvol ≠ ⊤ := by
              rw [hCvoldef]
              exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hKvol.ne).ne
            obtain ⟨ε1, hε10, hε1⟩ := hthreshold (CMD * Cvol)
              (ENNReal.mul_ne_top hCMDtop hCvoltop) (ε/2) (ENNReal.half_pos hε.ne')
            obtain ⟨ε2, hε20, hε2⟩ := hthreshold
              (ENNReal.ofReal (max Mφ0 0) * ∫⁻ z in tsupport φ, ‖Gv z‖ₑ)
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGvfin.ne) (ε/2)
              (ENNReal.half_pos hε.ne')
            -- eventual smallness of the convolution error in `L²`
            obtain ⟨N1, hN1⟩ := (ENNReal.tendsto_atTop_zero.mp hCVconv)
              (ENNReal.ofReal ε1) (ENNReal.ofReal_pos.mpr hε10)
            -- eventual uniform closeness of the differentials along the tube
            have hDuc := hKg1c.uniformContinuousOn_of_continuous hDncont.continuousOn
            obtain ⟨δ2, hδ20, hδ2⟩ := Metric.uniformContinuousOn_iff.mp hDuc ε2 hε20
            obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp
              (hgmconv (min (δ2/2) 1) (lt_min (by linarith) one_pos))
            refine ⟨max N1 N2, fun m hm => ?_⟩
            have hmN1 : N1 ≤ m := le_trans (le_max_left _ _) hm
            have hmN2 : N2 ≤ m := le_trans (le_max_right _ _) hm
            -- names for the two pieces
            set Ym : ℂ → ℂ := fun z => CV m z - Gv z with hYmdef
            have hYmsm : AEStronglyMeasurable Ym volume :=
              (hCVcont m).aestronglyMeasurable.sub hGvsm
            -- pointwise split
            have hptw : ∀ z : ℂ, ‖φ z • ((fderiv ℝ (A n) (gm m z))
                  ((CV m) z))
                - φ z • ((fderiv ℝ (A n) (G z)) (Gv z))‖ₑ
                ≤ ‖φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))‖ₑ
                  + ‖φ z • (((fderiv ℝ (A n) (gm m z)) - (fderiv ℝ (A n) (G z))) (Gv z))‖ₑ := by
              intro z
              have halg : φ z • ((fderiv ℝ (A n) (gm m z)) ((CV m) z))
                  - φ z • ((fderiv ℝ (A n) (G z)) (Gv z))
                  = φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))
                    + φ z • (((fderiv ℝ (A n) (gm m z)) - (fderiv ℝ (A n) (G z))) (Gv z)) := by
                rw [hYmdef]
                simp only [map_sub, sub_apply, Complex.real_smul]
                ring
              rw [halg]
              exact enorm_add_le _ _
            have hsm1 : AEStronglyMeasurable
                (fun z => φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))) volume := by
              refine (hφs.continuous.aestronglyMeasurable).smul ?_
              exact (isBoundedBilinearMap_apply.continuous).comp_aestronglyMeasurable
                (((hDncont.comp (hgmsm m).continuous).aestronglyMeasurable).prodMk hYmsm)
            have hbound1 : ∫⁻ z, ‖φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))‖ₑ ≤ ε/2 := by
              have hz1 : ∀ z : ℂ, z ∉ tsupport φ →
                  φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z)) = 0 := by
                intro z hz
                rw [hφzero z hz]
                exact zero_smul ℝ _
              rw [hlsupp _ hz1]
              have hpt1 : ∀ z ∈ tsupport φ,
                  ‖φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))‖ₑ
                    ≤ ENNReal.ofReal (max Mφ0 0 * (max MD0 0 + 1)) * ‖Ym z‖ₑ := by
                intro z hz
                have hgmz : gm m z ∈ Kg1 :=
                  hnearKg1 (G z) (hGKg z hz) (gm m z)
                    (le_trans (hN2 m hmN2 z) (min_le_right _ _))
                have hb1 : ‖φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))‖
                    ≤ (max Mφ0 0 * (max MD0 0 + 1)) * ‖Ym z‖ := by
                  rw [norm_smul]
                  have hb2 : ‖(fderiv ℝ (A n) (gm m z)) (Ym z)‖
                      ≤ (max MD0 0 + 1) * ‖Ym z‖ := by
                    refine le_trans ((fderiv ℝ (A n) (gm m z)).le_opNorm _) ?_
                    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                    have := hMD0 _ hgmz
                    have h13 : MD0 ≤ max MD0 0 := le_max_left _ _
                    linarith
                  calc ‖φ z‖ * ‖(fderiv ℝ (A n) (gm m z)) (Ym z)‖
                      ≤ (max Mφ0 0) * ((max MD0 0 + 1) * ‖Ym z‖) := by
                        refine mul_le_mul (hMφ z) hb2 (norm_nonneg _) (le_max_right _ _)
                    _ = (max Mφ0 0 * (max MD0 0 + 1)) * ‖Ym z‖ := by ring
                calc ‖φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))‖ₑ
                    = ENNReal.ofReal ‖φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))‖ :=
                      (ofReal_norm _).symm
                  _ ≤ ENNReal.ofReal ((max Mφ0 0 * (max MD0 0 + 1)) * ‖Ym z‖) :=
                      ENNReal.ofReal_le_ofReal hb1
                  _ = ENNReal.ofReal (max Mφ0 0 * (max MD0 0 + 1)) * ‖Ym z‖ₑ := by
                      rw [ENNReal.ofReal_mul (by positivity), ofReal_norm]
              calc ∫⁻ z in tsupport φ, ‖φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))‖ₑ
                  ≤ ∫⁻ z in tsupport φ,
                      ENNReal.ofReal (max Mφ0 0 * (max MD0 0 + 1)) * ‖Ym z‖ₑ :=
                    lintegral_mono_ae ((ae_restrict_iff' hKmeas).mpr
                      (Filter.Eventually.of_forall hpt1))
                _ = CMD * ∫⁻ z in tsupport φ, ‖Ym z‖ₑ := by
                    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hCMDdef]
                _ ≤ CMD * (eLpNorm Ym 2 volume * Cvol) := by
                    refine mul_le_mul_right ?_ _
                    rw [hCvoldef]
                    exact hL2K Ym hYmsm
                _ = (CMD * Cvol) * eLpNorm Ym 2 volume := by ring
                _ ≤ (CMD * Cvol) * ENNReal.ofReal ε1 :=
                    mul_le_mul_right (hN1 m hmN1) _
                _ = ENNReal.ofReal ε1 * (CMD * Cvol) := by ring
                _ ≤ ε/2 := hε1
            have hbound2 : ∫⁻ z, ‖φ z • (((fderiv ℝ (A n) (gm m z))
                  - (fderiv ℝ (A n) (G z))) (Gv z))‖ₑ ≤ ε/2 := by
              have hz2 : ∀ z : ℂ, z ∉ tsupport φ →
                  φ z • (((fderiv ℝ (A n) (gm m z)) - (fderiv ℝ (A n) (G z))) (Gv z)) = 0 := by
                intro z hz
                rw [hφzero z hz]
                exact zero_smul ℝ _
              rw [hlsupp _ hz2]
              have hpt2 : ∀ z ∈ tsupport φ,
                  ‖φ z • (((fderiv ℝ (A n) (gm m z)) - (fderiv ℝ (A n) (G z))) (Gv z))‖ₑ
                    ≤ ENNReal.ofReal (max Mφ0 0) * ENNReal.ofReal ε2 * ‖Gv z‖ₑ := by
                intro z hz
                have hgmz : gm m z ∈ Kg1 :=
                  hnearKg1 (G z) (hGKg z hz) (gm m z)
                    (le_trans (hN2 m hmN2 z) (min_le_right _ _))
                have hdd : dist (gm m z) (G z) < δ2 :=
                  lt_of_le_of_lt (le_trans (hN2 m hmN2 z) (min_le_left _ _)) (by linarith)
                have hopb : ‖(fderiv ℝ (A n) (gm m z)) - (fderiv ℝ (A n) (G z))‖ ≤ ε2 := by
                  rw [← dist_eq_norm]
                  exact (hδ2 (gm m z) hgmz (G z) (hKgsub (hGKg z hz)) hdd).le
                have hb1 : ‖φ z • (((fderiv ℝ (A n) (gm m z))
                      - (fderiv ℝ (A n) (G z))) (Gv z))‖
                    ≤ (max Mφ0 0) * (ε2 * ‖Gv z‖) := by
                  rw [norm_smul]
                  refine mul_le_mul (hMφ z) ?_ (norm_nonneg _) (le_max_right _ _)
                  refine le_trans (((fderiv ℝ (A n) (gm m z))
                    - (fderiv ℝ (A n) (G z))).le_opNorm _) ?_
                  exact mul_le_mul_of_nonneg_right hopb (norm_nonneg _)
                calc ‖φ z • (((fderiv ℝ (A n) (gm m z))
                      - (fderiv ℝ (A n) (G z))) (Gv z))‖ₑ
                    = ENNReal.ofReal ‖φ z • (((fderiv ℝ (A n) (gm m z))
                        - (fderiv ℝ (A n) (G z))) (Gv z))‖ := (ofReal_norm _).symm
                  _ ≤ ENNReal.ofReal ((max Mφ0 0) * (ε2 * ‖Gv z‖)) :=
                      ENNReal.ofReal_le_ofReal hb1
                  _ = ENNReal.ofReal (max Mφ0 0) * ENNReal.ofReal ε2 * ‖Gv z‖ₑ := by
                      rw [ENNReal.ofReal_mul (le_max_right _ _),
                        ENNReal.ofReal_mul hε20.le, ofReal_norm, mul_assoc]
              calc ∫⁻ z in tsupport φ, ‖φ z • (((fderiv ℝ (A n) (gm m z))
                    - (fderiv ℝ (A n) (G z))) (Gv z))‖ₑ
                  ≤ ∫⁻ z in tsupport φ,
                      ENNReal.ofReal (max Mφ0 0) * ENNReal.ofReal ε2 * ‖Gv z‖ₑ :=
                    lintegral_mono_ae ((ae_restrict_iff' hKmeas).mpr
                      (Filter.Eventually.of_forall hpt2))
                _ = ENNReal.ofReal (max Mφ0 0) * ENNReal.ofReal ε2
                      * ∫⁻ z in tsupport φ, ‖Gv z‖ₑ := by
                    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top
                      ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
                _ = ENNReal.ofReal ε2
                      * (ENNReal.ofReal (max Mφ0 0) * ∫⁻ z in tsupport φ, ‖Gv z‖ₑ) := by
                    ring
                _ ≤ ε/2 := hε2
            calc ∫⁻ z, ‖φ z • ((fderiv ℝ (A n) (gm m z))
                  ((CV m) z))
                - φ z • ((fderiv ℝ (A n) (G z)) (Gv z))‖ₑ
                ≤ ∫⁻ z, (‖φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))‖ₑ
                  + ‖φ z • (((fderiv ℝ (A n) (gm m z))
                    - (fderiv ℝ (A n) (G z))) (Gv z))‖ₑ) := lintegral_mono hptw
              _ = (∫⁻ z, ‖φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))‖ₑ)
                  + ∫⁻ z, ‖φ z • (((fderiv ℝ (A n) (gm m z))
                    - (fderiv ℝ (A n) (G z))) (Gv z))‖ₑ :=
                  lintegral_add_left' hsm1.enorm _
              _ ≤ ε/2 + ε/2 := add_le_add hbound1 hbound2
              _ = ε := ENNReal.add_halves ε
        -- combine the three `m`-facts
        exact tendsto_nhds_unique hLlim
          ((hRlim.neg).congr fun m => (hIBPm m).symm)
      -- ===== the Cauchy–Schwarz/area estimate =====
      have hJfacts : ∀ᵐ z ∂(volume.restrict (tsupport φ)),
          ENNReal.ofReal ((fderiv ℝ P.g z).det) ≠ 0
            ∧ ‖(fderiv ℝ P.g z) v‖ₑ ^ (2:ℕ)
              ≤ ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                * ENNReal.ofReal ((fderiv ℝ P.g z).det) := by
        have hres : volume.restrict (tsupport φ) ≤ volume.restrict {z : ℂ | 0 < z.im} :=
          Measure.restrict_mono hKU le_rfl
        filter_upwards [(ae_mono hres) hggood, (ae_mono hres) hdistort] with z hz hd
        constructor
        · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
          exact hz.2.1
        · have h2 := hd v hv1
          calc ‖(fderiv ℝ P.g z) v‖ₑ ^ (2:ℕ)
              = ENNReal.ofReal (‖(fderiv ℝ P.g z) v‖ ^ 2) := by
                rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
            _ ≤ ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0) * (fderiv ℝ P.g z).det) :=
                ENNReal.ofReal_le_ofReal h2
            _ = ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                  * ENNReal.ofReal ((fderiv ℝ P.g z).det) := by
                rw [ENNReal.ofReal_mul (div_nonneg (by linarith) (by linarith))]
      have hCSJ : ∀ Q : ℂ → ℝ≥0∞, Measurable Q →
          ∫⁻ z in tsupport φ, Q (P.g z) * ‖(fderiv ℝ P.g z) v‖ₑ
            ≤ ((∫⁻ u in Metric.ball 0 R0, Q u ^ (2:ℕ)) ^ ((1:ℝ)/2))
              * (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                * volume (tsupport φ)) ^ ((1:ℝ)/2) := by
        intro Q hQ
        have hgaeK : AEMeasurable P.g (volume.restrict (tsupport φ)) :=
          (P.qc.cont.mono hKU).aemeasurable hKmeas
        have hf1m : AEMeasurable (fun z => Q (P.g z)
            * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ ((1:ℝ)/2))
            (volume.restrict (tsupport φ)) :=
          (hQ.comp_aemeasurable hgaeK).mul
            ((hdetmeas.ennreal_ofReal.aemeasurable.mono_measure
              (Measure.restrict_le_self)).pow_const _)
        have hf2m : AEMeasurable (fun z => ‖(fderiv ℝ P.g z) v‖ₑ
            * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2)))
            (volume.restrict (tsupport φ)) := by
          refine AEMeasurable.mul ?_ ?_
          · exact (((measurable_fderiv ℝ P.g).apply_continuousLinearMap v).enorm).aemeasurable
          · exact (hdetmeas.ennreal_ofReal.aemeasurable.mono_measure
              (Measure.restrict_le_self)).pow_const _
        have hsplit : ∀ᵐ z ∂(volume.restrict (tsupport φ)),
            Q (P.g z) * ‖(fderiv ℝ P.g z) v‖ₑ
              = (Q (P.g z) * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ ((1:ℝ)/2))
                * (‖(fderiv ℝ P.g z) v‖ₑ
                  * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2))) := by
          filter_upwards [hJfacts] with z hz
          have hJ0 : ENNReal.ofReal ((fderiv ℝ P.g z).det) ≠ 0 := hz.1
          have hJt : ENNReal.ofReal ((fderiv ℝ P.g z).det) ≠ ⊤ := ENNReal.ofReal_ne_top
          have hone : (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ ((1:ℝ)/2)
              * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2)) = 1 := by
            rw [← ENNReal.rpow_add _ _ hJ0 hJt]
            norm_num
          calc Q (P.g z) * ‖(fderiv ℝ P.g z) v‖ₑ
              = Q (P.g z) * ‖(fderiv ℝ P.g z) v‖ₑ
                * ((ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ ((1:ℝ)/2)
                  * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2))) := by
                rw [hone, mul_one]
            _ = (Q (P.g z) * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ ((1:ℝ)/2))
                * (‖(fderiv ℝ P.g z) v‖ₑ
                  * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2))) := by
                ring
        have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (tsupport φ))
          (by constructor <;> norm_num : (2:ℝ).HolderConjugate 2) hf1m hf2m
        have hstepA : ∫⁻ z in tsupport φ, Q (P.g z) * ‖(fderiv ℝ P.g z) v‖ₑ
            = ∫⁻ z in tsupport φ,
                ((fun z => Q (P.g z) * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ ((1:ℝ)/2))
                * fun z => ‖(fderiv ℝ P.g z) v‖ₑ
                  * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2))) z :=
          lintegral_congr_ae (hsplit.mono fun z hz => by simpa using hz)
        rw [hstepA]
        refine le_trans hcs ?_
        -- first factor: the area estimate
        have hfac1 : (∫⁻ z in tsupport φ,
            (Q (P.g z) * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ ((1:ℝ)/2)) ^ (2:ℝ))
              ^ ((1:ℝ)/2)
            ≤ ((∫⁻ u in Metric.ball 0 R0, Q u ^ (2:ℕ)) ^ ((1:ℝ)/2)) := by
          refine ENNReal.rpow_le_rpow ?_ (by norm_num)
          have heq2 : ∀ z : ℂ,
              (Q (P.g z) * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ ((1:ℝ)/2)) ^ (2:ℝ)
              = ENNReal.ofReal ((fderiv ℝ P.g z).det) * (Q (P.g z)) ^ (2:ℕ) := by
            intro z
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
              ← ENNReal.rpow_mul (ENNReal.ofReal ((fderiv ℝ P.g z).det)),
              ← ENNReal.rpow_natCast (Q (P.g z)) 2]
            norm_num
            rw [mul_comm]
          calc ∫⁻ z in tsupport φ,
              (Q (P.g z) * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ ((1:ℝ)/2)) ^ (2:ℝ)
              = ∫⁻ z in tsupport φ,
                ENNReal.ofReal ((fderiv ℝ P.g z).det) * (Q (P.g z)) ^ (2:ℕ) :=
                lintegral_congr fun z => heq2 z
            _ ≤ ∫⁻ u in Metric.ball 0 R0, Q u ^ (2:ℕ) :=
                hArea (tsupport φ) hKmeas hKU (Metric.ball 0 R0)
                  (by rw [← hKgdef]; exact hR0) (fun u => Q u ^ (2:ℕ))
        -- second factor: the distortion bound
        have hfac2 : (∫⁻ z in tsupport φ,
            (‖(fderiv ℝ P.g z) v‖ₑ
              * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2))) ^ (2:ℝ))
              ^ ((1:ℝ)/2)
            ≤ (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
              * volume (tsupport φ)) ^ ((1:ℝ)/2) := by
          refine ENNReal.rpow_le_rpow ?_ (by norm_num)
          have hptb : ∀ᵐ z ∂(volume.restrict (tsupport φ)),
              (‖(fderiv ℝ P.g z) v‖ₑ
                * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2))) ^ (2:ℝ)
              ≤ ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0)) := by
            filter_upwards [hJfacts] with z hz
            have hJ0 : ENNReal.ofReal ((fderiv ℝ P.g z).det) ≠ 0 := hz.1
            have hJt : ENNReal.ofReal ((fderiv ℝ P.g z).det) ≠ ⊤ := ENNReal.ofReal_ne_top
            have hexp : (‖(fderiv ℝ P.g z) v‖ₑ
                * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2))) ^ (2:ℝ)
                = ‖(fderiv ℝ P.g z) v‖ₑ ^ (2:ℕ)
                  * (ENNReal.ofReal ((fderiv ℝ P.g z).det))⁻¹ := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
                ← ENNReal.rpow_mul (ENNReal.ofReal ((fderiv ℝ P.g z).det)),
                ← ENNReal.rpow_natCast (‖(fderiv ℝ P.g z) v‖ₑ) 2]
              norm_num
              rw [ENNReal.rpow_neg_one]
            rw [hexp]
            calc ‖(fderiv ℝ P.g z) v‖ₑ ^ (2:ℕ) * (ENNReal.ofReal ((fderiv ℝ P.g z).det))⁻¹
                ≤ (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                    * ENNReal.ofReal ((fderiv ℝ P.g z).det))
                  * (ENNReal.ofReal ((fderiv ℝ P.g z).det))⁻¹ :=
                  mul_le_mul_left hz.2 _
              _ = ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                  * (ENNReal.ofReal ((fderiv ℝ P.g z).det)
                    * (ENNReal.ofReal ((fderiv ℝ P.g z).det))⁻¹) := by ring
              _ = ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0)) := by
                  rw [ENNReal.mul_inv_cancel hz.1 ENNReal.ofReal_ne_top, mul_one]
          calc ∫⁻ z in tsupport φ,
              (‖(fderiv ℝ P.g z) v‖ₑ
                * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2))) ^ (2:ℝ)
              ≤ ∫⁻ _ in tsupport φ,
                ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0)) :=
                lintegral_mono_ae hptb
            _ = ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                * volume (tsupport φ) := setLIntegral_const _ _
        exact mul_le_mul' hfac1 hfac2
      -- ===== restriction form of the gradient identification =====
      have hGvK : ∀ᵐ z ∂(volume.restrict (tsupport φ)), Gv z = (fderiv ℝ P.g z) v := by
        filter_upwards [ae_restrict_of_ae hGveqPg, ae_restrict_mem hKmeas] with z h1 h2
        exact h1 (Metric.self_subset_thickening hr0 _ h2)
      -- ===== the left `n`-limit =====
      have hLconvN : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, ∀ z ∈ tsupport φ,
          ‖A n (G z) - x.w (G z)‖ ≤ ε := by
        intro ε hε
        filter_upwards [hAconv ε hε] with n hn z hz
        rw [← dist_eq_norm]
        exact hn (G z) (hGKg z hz)
      have hLlimN : Filter.Tendsto (fun n => ∫ z, ((fderiv ℝ φ z) v) • (A n (G z)))
          Filter.atTop (nhds (∫ z, ((fderiv ℝ φ z) v) • (x.w (G z)))) := by
        refine tendsto_integral_of_L1 _
          (hIntCont _ _ hdφcont hdφzero (hxc.comp hGcont)).aestronglyMeasurable ?_ ?_
        · exact Filter.Eventually.of_forall fun n =>
            hIntCont _ _ hdφcont hdφzero ((hAsm n).continuous.comp hGcont)
        · exact hsupL1 _ _ hMdφ hdφzero _ _ hLconvN
      -- ===== the right `n`-limit through the Cauchy–Schwarz/area estimate =====
      have hQxm : Measurable fun u : ℂ => ‖fderiv ℝ x.w u‖ₑ :=
        (measurable_fderiv ℝ x.w).enorm
      have hxball : ∫⁻ u in Metric.ball 0 R0, (fun u : ℂ => ‖fderiv ℝ x.w u‖ₑ) u ^ (2:ℕ)
          ≠ ⊤ := by
        have h1 := IsQCAnalytic.lintegralSq_fderiv_ball_ne_top x.w_isQCAnalytic R0
        simpa [enorm_eq_nnnorm] using h1
      have hIntlim : Integrable (fun z => φ z • ((fderiv ℝ x.w (G z)) (Gv z))) volume := by
        constructor
        · refine (hφs.continuous.aestronglyMeasurable).smul ?_
          exact (isBoundedBilinearMap_apply.continuous).comp_aestronglyMeasurable
            ((((measurable_fderiv ℝ x.w).comp
              hGcont.measurable).aestronglyMeasurable).prodMk hGvsm)
        · rw [hasFiniteIntegral_iff_enorm]
          have hz0 : ∀ z : ℂ, z ∉ tsupport φ →
              φ z • ((fderiv ℝ x.w (G z)) (Gv z)) = 0 := by
            intro z hz
            rw [hφzero z hz]
            exact zero_smul ℝ _
          rw [hlsupp _ hz0]
          have hptb : ∀ᵐ z ∂(volume.restrict (tsupport φ)),
              ‖φ z • ((fderiv ℝ x.w (G z)) (Gv z))‖ₑ
                ≤ ENNReal.ofReal (max Mφ0 0)
                  * ((fun u : ℂ => ‖fderiv ℝ x.w u‖ₑ) (P.g z)
                    * ‖(fderiv ℝ P.g z) v‖ₑ) := by
            filter_upwards [hGvK, ae_restrict_mem hKmeas] with z h1 h2
            have hGz : G z = P.g z := hGeq z (Metric.self_subset_cthickening _ h2)
            rw [hGz, h1]
            calc ‖φ z • ((fderiv ℝ x.w (P.g z)) ((fderiv ℝ P.g z) v))‖ₑ
                = ENNReal.ofReal ‖φ z • ((fderiv ℝ x.w (P.g z)) ((fderiv ℝ P.g z) v))‖ :=
                  (ofReal_norm _).symm
              _ ≤ ENNReal.ofReal ((max Mφ0 0)
                    * (‖fderiv ℝ x.w (P.g z)‖ * ‖(fderiv ℝ P.g z) v‖)) := by
                  refine ENNReal.ofReal_le_ofReal ?_
                  rw [norm_smul]
                  refine mul_le_mul (hMφ z)
                    ((fderiv ℝ x.w (P.g z)).le_opNorm _) (norm_nonneg _)
                    (le_max_right _ _)
              _ = ENNReal.ofReal (max Mφ0 0)
                    * ((fun u : ℂ => ‖fderiv ℝ x.w u‖ₑ) (P.g z)
                      * ‖(fderiv ℝ P.g z) v‖ₑ) := by
                  rw [ENNReal.ofReal_mul (le_max_right _ _),
                    ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
                    ofReal_norm]
          calc ∫⁻ z in tsupport φ, ‖φ z • ((fderiv ℝ x.w (G z)) (Gv z))‖ₑ
              ≤ ∫⁻ z in tsupport φ, ENNReal.ofReal (max Mφ0 0)
                  * ((fun u : ℂ => ‖fderiv ℝ x.w u‖ₑ) (P.g z)
                    * ‖(fderiv ℝ P.g z) v‖ₑ) := lintegral_mono_ae hptb
            _ = ENNReal.ofReal (max Mφ0 0) * ∫⁻ z in tsupport φ,
                  (fun u : ℂ => ‖fderiv ℝ x.w u‖ₑ) (P.g z) * ‖(fderiv ℝ P.g z) v‖ₑ :=
                lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
            _ < ⊤ := by
                refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
                refine lt_of_le_of_lt (hCSJ _ hQxm) ?_
                refine ENNReal.mul_lt_top ?_ ?_
                · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
                    hxball
                · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
                    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKvol.ne)
      have hRlimN : Filter.Tendsto
          (fun n => ∫ z, φ z • ((fderiv ℝ (A n) (G z)) (Gv z)))
          Filter.atTop (nhds (∫ z, φ z • ((fderiv ℝ x.w (G z)) (Gv z)))) := by
        refine tendsto_integral_of_L1 _ hIntlim.aestronglyMeasurable ?_ ?_
        · refine Filter.Eventually.of_forall fun n => ?_
          have hDncont : Continuous fun u : ℂ => fderiv ℝ (A n) u :=
            (hAsm n).continuous_fderiv hne0
          obtain ⟨MD0, hMD0⟩ := hKg1c.exists_bound_of_continuousOn hDncont.continuousOn
          exact hIntCLM _ (hDncont.comp hGcont) MD0
            (fun z hz => hMD0 _ (hKgsub (hGKg z hz))) Gv hGvsm hGvInt
        · -- the `L¹` difference limit via the energy decay
          have hboundall : ∀ n : ℕ,
              ∫⁻ z, ‖φ z • ((fderiv ℝ (A n) (G z)) (Gv z))
                - φ z • ((fderiv ℝ x.w (G z)) (Gv z))‖ₑ
              ≤ ENNReal.ofReal (max Mφ0 0)
                * (((∫⁻ u in Metric.ball 0 R0,
                    (fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ) u ^ (2:ℕ))
                      ^ ((1:ℝ)/2))
                  * (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                    * volume (tsupport φ)) ^ ((1:ℝ)/2)) := by
            intro n
            have hz0 : ∀ z : ℂ, z ∉ tsupport φ →
                φ z • ((fderiv ℝ (A n) (G z)) (Gv z))
                  - φ z • ((fderiv ℝ x.w (G z)) (Gv z)) = 0 := by
              intro z hz
              rw [hφzero z hz]
              simp
            rw [hlsupp _ hz0]
            have hptb : ∀ᵐ z ∂(volume.restrict (tsupport φ)),
                ‖φ z • ((fderiv ℝ (A n) (G z)) (Gv z))
                  - φ z • ((fderiv ℝ x.w (G z)) (Gv z))‖ₑ
                ≤ ENNReal.ofReal (max Mφ0 0)
                  * ((fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ) (P.g z)
                    * ‖(fderiv ℝ P.g z) v‖ₑ) := by
              filter_upwards [hGvK, ae_restrict_mem hKmeas] with z h1 h2
              have hGz : G z = P.g z := hGeq z (Metric.self_subset_cthickening _ h2)
              have halg2 : φ z • ((fderiv ℝ (A n) (G z)) (Gv z))
                  - φ z • ((fderiv ℝ x.w (G z)) (Gv z))
                  = φ z • (((fderiv ℝ (A n) (P.g z) - fderiv ℝ x.w (P.g z)))
                      ((fderiv ℝ P.g z) v)) := by
                rw [hGz, h1, sub_apply]
                simp only [Complex.real_smul]
                ring
              rw [halg2]
              calc ‖φ z • (((fderiv ℝ (A n) (P.g z) - fderiv ℝ x.w (P.g z)))
                    ((fderiv ℝ P.g z) v))‖ₑ
                  = ENNReal.ofReal ‖φ z • (((fderiv ℝ (A n) (P.g z)
                      - fderiv ℝ x.w (P.g z))) ((fderiv ℝ P.g z) v))‖ :=
                    (ofReal_norm _).symm
                _ ≤ ENNReal.ofReal ((max Mφ0 0)
                      * (‖fderiv ℝ (A n) (P.g z) - fderiv ℝ x.w (P.g z)‖
                        * ‖(fderiv ℝ P.g z) v‖)) := by
                    refine ENNReal.ofReal_le_ofReal ?_
                    rw [norm_smul]
                    refine mul_le_mul (hMφ z)
                      ((fderiv ℝ (A n) (P.g z) - fderiv ℝ x.w (P.g z)).le_opNorm _)
                      (norm_nonneg _) (le_max_right _ _)
                _ = ENNReal.ofReal (max Mφ0 0)
                      * ((fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ) (P.g z)
                        * ‖(fderiv ℝ P.g z) v‖ₑ) := by
                    rw [ENNReal.ofReal_mul (le_max_right _ _),
                      ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
                      ofReal_norm]
            have hQnm : Measurable fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ := by
              have hDncont : Continuous fun u : ℂ => fderiv ℝ (A n) u :=
                (hAsm n).continuous_fderiv hne0
              exact (hDncont.measurable.sub (measurable_fderiv ℝ x.w)).enorm
            calc ∫⁻ z in tsupport φ, ‖φ z • ((fderiv ℝ (A n) (G z)) (Gv z))
                  - φ z • ((fderiv ℝ x.w (G z)) (Gv z))‖ₑ
                ≤ ∫⁻ z in tsupport φ, ENNReal.ofReal (max Mφ0 0)
                    * ((fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ) (P.g z)
                      * ‖(fderiv ℝ P.g z) v‖ₑ) := lintegral_mono_ae hptb
              _ = ENNReal.ofReal (max Mφ0 0) * ∫⁻ z in tsupport φ,
                    (fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ) (P.g z)
                      * ‖(fderiv ℝ P.g z) v‖ₑ :=
                  lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
              _ ≤ ENNReal.ofReal (max Mφ0 0)
                  * (((∫⁻ u in Metric.ball 0 R0,
                      (fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ) u ^ (2:ℕ))
                        ^ ((1:ℝ)/2))
                    * (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                      * volume (tsupport φ)) ^ ((1:ℝ)/2)) :=
                  mul_le_mul_right (hCSJ _ hQnm) _
          have hEnergyN : Filter.Tendsto (fun n => ∫⁻ u in Metric.ball 0 R0,
              (fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ) u ^ (2:ℕ))
              Filter.atTop (nhds 0) := by
            have h1 := henergy
            refine h1.congr fun n => ?_
            refine lintegral_congr fun u => ?_
            simp [enorm_eq_nnnorm, hAdef]
          have hbtend : Filter.Tendsto (fun n => ENNReal.ofReal (max Mφ0 0)
              * (((∫⁻ u in Metric.ball 0 R0,
                  (fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ) u ^ (2:ℕ))
                    ^ ((1:ℝ)/2))
                * (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                  * volume (tsupport φ)) ^ ((1:ℝ)/2)))
              Filter.atTop (nhds 0) := by
            have h2 : Filter.Tendsto (fun n => (∫⁻ u in Metric.ball 0 R0,
                (fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ) u ^ (2:ℕ))
                  ^ ((1:ℝ)/2)) Filter.atTop (nhds 0) := by
              have h3 := (ENNReal.continuous_rpow_const (y := (1:ℝ)/2)).continuousAt
                (x := 0)
              have h4 := h3.tendsto.comp hEnergyN
              simpa [ENNReal.zero_rpow_of_pos, Function.comp_def] using h4
            have h5 := ENNReal.Tendsto.mul_const h2
              (b := (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                * volume (tsupport φ)) ^ ((1:ℝ)/2))
              (Or.inr ((ENNReal.rpow_lt_top_of_nonneg (by norm_num)
                (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKvol.ne)).ne))
            have h6 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (max Mφ0 0)) h5
              (Or.inr ENNReal.ofReal_ne_top)
            simpa using h6
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbtend
            (fun n => zero_le) (fun n => hboundall n)
      -- ===== final assembly =====
      have hgoal1 : ∫ z, ((fderiv ℝ φ z) v) • ((x.w ∘ P.g) z)
          = ∫ z, ((fderiv ℝ φ z) v) • (x.w (G z)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        change ((fderiv ℝ φ z) v) • ((x.w ∘ P.g) z) = ((fderiv ℝ φ z) v) • (x.w (G z))
        by_cases hz : z ∈ tsupport φ
        · have h1 : G z = P.g z := hGeq z (Metric.self_subset_cthickening _ hz)
          rw [h1]
          rfl
        · rw [hdφzero z hz]
          simp
      have hkeyeq := tendsto_nhds_unique hLlimN ((hRlimN.neg).congr fun n => (hEn n).symm)
      have hgoal2 : ∫ z, φ z • ((fderiv ℝ x.w (G z)) (Gv z))
          = ∫ z, φ z • ((fderiv ℝ (x.w ∘ P.g) z) v) := by
        have hch : ∀ᵐ z : ℂ, z ∈ {z : ℂ | 0 < z.im} →
            (DifferentiableAt ℝ P.g z ∧ DifferentiableAt ℝ x.w (P.g z) ∧
              fderiv ℝ (x.w ∘ P.g) z = (fderiv ℝ x.w (P.g z)).comp (fderiv ℝ P.g z)) :=
          (ae_restrict_iff' hU).mp hchain
        refine integral_congr_ae ?_
        filter_upwards [hGveqPg, hch] with z h1 h2
        by_cases hz : z ∈ tsupport φ
        · have hGz : G z = P.g z := hGeq z (Metric.self_subset_cthickening _ hz)
          have hGvz : Gv z = (fderiv ℝ P.g z) v :=
            h1 (Metric.self_subset_thickening hr0 _ hz)
          have hcz := h2 (hKU hz)
          rw [hGz, hGvz, hcz.2.2, ContinuousLinearMap.comp_apply]
        · rw [hφzero z hz]
          simp
      calc ∫ z, ((fderiv ℝ φ z) v) • ((x.w ∘ P.g) z)
          = ∫ z, ((fderiv ℝ φ z) v) • (x.w (G z)) := hgoal1
        _ = - ∫ z, φ z • ((fderiv ℝ x.w (G z)) (Gv z)) := hkeyeq
        _ = - ∫ z, φ z • ((fderiv ℝ (x.w ∘ P.g) z) v) := congrArg Neg.neg hgoal2
    -- ===== assemble the local Sobolev membership =====
    obtain ⟨hgLp0, gx0, gy0, ⟨hgx0, hgy0⟩, hmx0, hmy0⟩ := P.qc.sobolev
    refine ⟨?_, fun z => (fderiv ℝ (x.w ∘ P.g) z) 1,
      fun z => (fderiv ℝ (x.w ∘ P.g) z) Complex.I,
      ⟨hKEY 1 gx0 (Or.inl rfl) hgx0 hmx0,
        hKEY Complex.I gy0 (Or.inr rfl) hgy0 hmy0⟩,
      hgradL2 1 (by simp), hgradL2 Complex.I (by simp)⟩
    intro Kc hKcU hKcc
    have : IsFiniteMeasure (volume.restrict Kc) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKcc.measure_lt_top⟩
    have hFcont : ContinuousOn (x.w ∘ P.g) {z : ℂ | 0 < z.im} :=
      hxc.comp_continuousOn P.qc.cont
    obtain ⟨MF, hMF⟩ := hKcc.exists_bound_of_continuousOn (hFcont.mono hKcU)
    refine MemLp.of_bound (((hFcont.mono hKcU).aemeasurable
      hKcc.measurableSet).aestronglyMeasurable) MF ?_
    exact (ae_restrict_iff' hKcc.measurableSet).mpr (Filter.Eventually.of_forall hMF)
  · -- jac
    filter_upwards [hband] with z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hB0 : 0 ≤ ‖dzbar (x.w ∘ P.g) z‖ := norm_nonneg _
    rw [det_fderiv_eq_wirtinger]
    set c := (max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf) with hc
    set A := ‖dz (x.w ∘ P.g) z‖ with hA
    set B := ‖dzbar (x.w ∘ P.g) z‖ with hB
    have hcc : c * c < 1 := by
      have h3 : c * c ≤ c := mul_le_of_le_one_left hκ'0 hκ'1.le
      linarith
    have h1 : B * B ≤ (c * A) * (c * A) := mul_self_le_mul_self hB0 hz1
    have h2 : 0 < (1 - c * c) * (A * A) := mul_pos (by linarith) (mul_pos hz2 hz2)
    nlinarith [h1, h2]
  · -- belt
    filter_upwards [hband] with z hz
    exact hz.1

end RiemannDynamics

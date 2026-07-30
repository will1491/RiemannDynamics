/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Flow.Weights

/-!
# Moebius transport of the weights, the local flow, and trajectories

Transport of the Wirtinger quotient and the weight functionals along a Moebius map, the
local flow of a natural chart, and horizontal trajectories with their germ, uniqueness,
reversal and extension properties.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

/-- Square root of a doubled product pair: `√((2A)(2B)) = 2√(AB)` in `ℝ≥0∞`. -/
theorem four_rpow_half {A B : ℝ≥0∞} :
    (2 * A * (2 * B)) ^ (1 / 2 : ℝ) = 2 * (A * B) ^ (1 / 2 : ℝ) := by
  rw [show 2 * A * (2 * B) = 4 * (A * B) by ring,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2)]
  congr 1
  rw [show (4 : ℝ≥0∞) = 2 ^ (2 : ℕ) by norm_num, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

/-- **The Reich–Strebel main inequality from symmetrized flow data**: the two-orientation
flow interface still produces the Reich–Strebel bound — each orientation contributes its
leafwise estimate, and only the orientation-symmetrized invariances are consumed. -/
theorem reich_strebel_of_flowDataSym
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) {h hinv : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1)
    (hqc : IsQCUpper h hinv κ)
    (fd : VerticalFlowDataSym Γ q h κ)
    (hcov : ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
        ‖q (h z)‖ₑ * ENNReal.ofReal ((fderiv ℝ h z).det) ≤ q.l1Norm) :
    q.l1Norm ≤ ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
      ‖q z‖ₑ * ENNReal.ofReal
        (‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ^ 2
          / (1 - ‖wirtingerQuotient h z‖ ^ 2)) := by
  set ω : Set ℂ := UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I with hωdef
  have hsubH : ω ⊆ {z : ℂ | 0 < z.im} := by
    rintro w ⟨τ, -, rfl⟩
    simpa using τ.im_pos
  set N : ℝ≥0∞ := q.l1Norm with hNdef
  have hNint : N = ∫⁻ z in ω, ‖q z‖ₑ := rfl
  have hN : N ≠ ⊤ := q.l1Norm_ne_top hΓ hfree hcc
  set A : ℝ≥0∞ := ∫⁻ z in ω, rsU q h κ z * ‖q z‖ₑ with hAdef
  set B : ℝ≥0∞ := ∫⁻ z in ω, rsWeightM q h κ z * ‖q z‖ₑ with hBdef
  have haegood : ∀ᵐ z ∂(volume.restrict ω), z ∈ fd.good :=
    ae_restrict_of_ae_restrict_of_subset hsubH fd.good_ae
  have haeW : ∀ᵐ z ∂(volume.restrict ω),
      rsWeightM q h κ z = rsWeight q h z :=
    ae_restrict_of_ae_restrict_of_subset hsubH (ae_rsWeightM_eq hqc hκ)
  have haeU : ∀ᵐ z ∂(volume.restrict ω),
      rsU q h κ z * ‖q z‖ₑ
        ≤ ‖q (h z)‖ₑ * ENNReal.ofReal ((fderiv ℝ h z).det) :=
    ae_restrict_of_ae_restrict_of_subset hsubH (ae_rsU_mul_le hqc hκ)
  have hBI : B = ∫⁻ z in ω, ‖q z‖ₑ * ENNReal.ofReal
      (‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ^ 2
        / (1 - ‖wirtingerQuotient h z‖ ^ 2)) := by
    calc B = ∫⁻ z in ω, rsWeight q h z * ‖q z‖ₑ :=
          lintegral_congr_ae (haeW.mono fun z hz => by
            change rsWeightM q h κ z * ‖q z‖ₑ = rsWeight q h z * ‖q z‖ₑ
            rw [hz])
      _ = _ := lintegral_congr fun z => by
          show rsWeight q h z * ‖q z‖ₑ = _
          rw [rsWeight, mul_comm]
  have hAN : A ≤ N := (lintegral_mono_ae haeU).trans hcov
  have hqe : Measurable fun z : ℂ => ‖q z‖ₑ := q.measurable.enorm
  have hFU : Measurable fun p : ℝ × ℂ =>
      rsU q h κ (fd.flow p.1 p.2) + rsU q h κ (fd.flow (-p.1) p.2) :=
    fd.meas_U.add (fd.meas_U.comp ((measurable_fst.neg).prodMk measurable_snd))
  have hFW : Measurable fun p : ℝ × ℂ =>
      rsWeightM q h κ (fd.flow p.1 p.2) + rsWeightM q h κ (fd.flow (-p.1) p.2) :=
    fd.meas_W.add (fd.meas_W.comp ((measurable_fst.neg).prodMk measurable_snd))
  have hCC : (2 * fd.C + 2 * fd.C) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top fd.hC,
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top fd.hC⟩
  have key : ∀ T : ℝ, 0 < T →
      (ENNReal.ofReal T + ENNReal.ofReal T) * N
        ≤ ENNReal.ofReal T * (2 * ((A * B) ^ (1 / 2 : ℝ)))
          + (2 * fd.C + 2 * fd.C) * N := by
    intro T hT
    set aT : ℂ → ℝ≥0∞ := fun z => ∫⁻ t in Set.Icc (0 : ℝ) T,
      (rsU q h κ (fd.flow t z) + rsU q h κ (fd.flow (-t) z)) with haTdef
    set bT : ℂ → ℝ≥0∞ := fun z => ∫⁻ t in Set.Icc (0 : ℝ) T,
      (rsWeightM q h κ (fd.flow t z) + rsWeightM q h κ (fd.flow (-t) z)) with hbTdef
    have haTmeas : Measurable aT := (hFU.comp measurable_swap).lintegral_prod_right'
    have hbTmeas : Measurable bT := (hFW.comp measurable_swap).lintegral_prod_right'
    have hXmeas : Measurable fun z => aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) :=
      (ENNReal.continuous_rpow_const.measurable.comp haTmeas).mul
        (ENNReal.continuous_rpow_const.measurable.comp hbTmeas)
    have hstep1 : (ENNReal.ofReal T + ENNReal.ofReal T) * N
        ≤ ∫⁻ z in ω, (aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ)
            + (2 * fd.C + 2 * fd.C)) * ‖q z‖ₑ := by
      rw [hNint, ← lintegral_const_mul' _ _
        (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)]
      refine lintegral_mono_ae ?_
      filter_upwards [haegood] with z hz
      exact mul_le_mul_left (leaf_pointwise_sym hκ fd hz hT) _
    have hstep2 : ∫⁻ z in ω, (aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ)
          + (2 * fd.C + 2 * fd.C)) * ‖q z‖ₑ
        = (∫⁻ z in ω, aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) * ‖q z‖ₑ)
          + (2 * fd.C + 2 * fd.C) * N := by
      calc ∫⁻ z in ω, (aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ)
              + (2 * fd.C + 2 * fd.C)) * ‖q z‖ₑ
          = ∫⁻ z in ω, (aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) * ‖q z‖ₑ
              + (2 * fd.C + 2 * fd.C) * ‖q z‖ₑ) := lintegral_congr fun z => add_mul _ _ _
        _ = (∫⁻ z in ω, aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) * ‖q z‖ₑ)
              + ∫⁻ z in ω, (2 * fd.C + 2 * fd.C) * ‖q z‖ₑ :=
            lintegral_add_left (hXmeas.mul hqe) _
        _ = _ := by rw [lintegral_const_mul' _ _ hCC, ← hNint]
    have hstep3 : ∫⁻ z in ω, aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) * ‖q z‖ₑ
        = ∫⁻ z in ω, (aT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ) * (bT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ) :=
      lintegral_congr fun z => (geom_mean_mul enorm_ne_top).symm
    have hstep4 : ∫⁻ z in ω,
        (aT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ) * (bT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ)
        ≤ (∫⁻ z in ω, aT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ)
          * (∫⁻ z in ω, bT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ) :=
      lintegral_sqrt_mul_sqrt_le ((haTmeas.mul hqe).aemeasurable)
        ((hbTmeas.mul hqe).aemeasurable)
    have hstep5 : ∫⁻ z in ω, aT z * ‖q z‖ₑ = ENNReal.ofReal T * (2 * A) :=
      fubini_invar q hFU (fun t => (fd.invar_U t).trans (by rw [← hAdef])) T
    have hstep6 : ∫⁻ z in ω, bT z * ‖q z‖ₑ = ENNReal.ofReal T * (2 * B) :=
      fubini_invar q hFW (fun t => (fd.invar_W t).trans (by rw [← hBdef])) T
    calc (ENNReal.ofReal T + ENNReal.ofReal T) * N
        ≤ ∫⁻ z in ω, (aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ)
            + (2 * fd.C + 2 * fd.C)) * ‖q z‖ₑ := hstep1
      _ = (∫⁻ z in ω, aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) * ‖q z‖ₑ)
            + (2 * fd.C + 2 * fd.C) * N := hstep2
      _ = (∫⁻ z in ω, (aT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ) * (bT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ))
            + (2 * fd.C + 2 * fd.C) * N := by rw [hstep3]
      _ ≤ (∫⁻ z in ω, aT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ)
            * (∫⁻ z in ω, bT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ)
            + (2 * fd.C + 2 * fd.C) * N := add_le_add hstep4 le_rfl
      _ = (ENNReal.ofReal T * (2 * A)) ^ (1 / 2 : ℝ)
            * (ENNReal.ofReal T * (2 * B)) ^ (1 / 2 : ℝ)
            + (2 * fd.C + 2 * fd.C) * N := by rw [hstep5, hstep6]
      _ = ENNReal.ofReal T * ((2 * A * (2 * B)) ^ (1 / 2 : ℝ))
            + (2 * fd.C + 2 * fd.C) * N := by
          rw [mul_rpow_half_mul ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal T * (2 * ((A * B) ^ (1 / 2 : ℝ)))
            + (2 * fd.C + 2 * fd.C) * N := by rw [four_rpow_half]
  have hK2 : (2 * fd.C + 2 * fd.C) * N ≠ ⊤ := ENNReal.mul_ne_top hCC hN
  have key2 : ∀ T : ℝ, 0 < T → ENNReal.ofReal T * (2 * N)
      ≤ ENNReal.ofReal T * (2 * ((A * B) ^ (1 / 2 : ℝ)))
        + (2 * fd.C + 2 * fd.C) * N := by
    intro T hT
    calc ENNReal.ofReal T * (2 * N)
        = (ENNReal.ofReal T + ENNReal.ofReal T) * N := by ring
      _ ≤ _ := key T hT
  have hNS2 : 2 * N ≤ 2 * ((A * B) ^ (1 / 2 : ℝ)) :=
    le_of_forall_ofReal_mul_le hK2 key2
  have hNS : N ≤ (A * B) ^ (1 / 2 : ℝ) :=
    (ENNReal.mul_le_mul_iff_right (by norm_num : (2:ℝ≥0∞) ≠ 0)
      ENNReal.ofNat_ne_top).mp hNS2
  have hfin : N ≤ (N * (∫⁻ z in ω, ‖q z‖ₑ * ENNReal.ofReal
      (‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ^ 2
        / (1 - ‖wirtingerQuotient h z‖ ^ 2)))) ^ (1 / 2 : ℝ) :=
    hNS.trans (ENNReal.rpow_le_rpow (mul_le_mul' hAN hBI.le) (by norm_num))
  exact le_of_le_sqrt_mul hN hfin

/-- **Wirtinger derivatives under a deck transformation**: for `h` commuting with the
Möbius map of `γ` near `z`, `∂h(γz) = e⁻² d² ∂h(z)` and `∂̄h(γz) = e⁻² conj(d²) ∂̄h(z)`,
where `d, e` are the Möbius denominators at `z` and at `h z`. -/
theorem wirtinger_moebius {h : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hhz : 0 < (h z).im)
    (hcomm : ∀ w : ℂ, 0 < w.im → h (moebiusMap γ w) = moebiusMap γ (h w))
    (hdiff : DifferentiableAt ℝ h z) (hdiffγ : DifferentiableAt ℝ h (moebiusMap γ z)) :
    dz h (moebiusMap γ z)
        = (moebiusDenom γ (h z) ^ 2)⁻¹ * moebiusDenom γ z ^ 2 * dz h z
      ∧ dzbar h (moebiusMap γ z)
        = (moebiusDenom γ (h z) ^ 2)⁻¹ * conj (moebiusDenom γ z ^ 2) * dzbar h z := by
  have hd : moebiusDenom γ z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne'
  have hdM : HasDerivAt (moebiusMap γ) ((moebiusDenom γ z ^ 2)⁻¹) z :=
    hasDerivAt_moebiusMap_of_im_pos γ hz
  have hdMh : HasDerivAt (moebiusMap γ) ((moebiusDenom γ (h z) ^ 2)⁻¹) (h z) :=
    hasDerivAt_moebiusMap_of_im_pos γ hhz
  have hγC : DifferentiableAt ℂ (moebiusMap γ) z := hdM.differentiableAt
  have hγCh : DifferentiableAt ℂ (moebiusMap γ) (h z) := hdMh.differentiableAt
  have hγR : DifferentiableAt ℝ (moebiusMap γ) z := moebius_diffAt γ hz
  have hγRh : DifferentiableAt ℝ (moebiusMap γ) (h z) := moebius_diffAt γ hhz
  have hdzγ : dz (moebiusMap γ) z = (moebiusDenom γ z ^ 2)⁻¹ := by
    rw [dz_eq_deriv_of_differentiableAt hγC, hdM.deriv]
  have hdzbarγ : dzbar (moebiusMap γ) z = 0 := dzbar_eq_zero_of_differentiableAt hγC
  have hdzγh : dz (moebiusMap γ) (h z) = (moebiusDenom γ (h z) ^ 2)⁻¹ := by
    rw [dz_eq_deriv_of_differentiableAt hγCh, hdMh.deriv]
  have hdzbarγh : dzbar (moebiusMap γ) (h z) = 0 :=
    dzbar_eq_zero_of_differentiableAt hγCh
  have hev : (fun w => h (moebiusMap γ w)) =ᶠ[nhds z] fun w => moebiusMap γ (h w) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz]
      with w hw
    exact hcomm w hw
  have hfeq : fderiv ℝ (fun w => h (moebiusMap γ w)) z
      = fderiv ℝ (fun w => moebiusMap γ (h w)) z := hev.fderiv_eq
  have hE1 : dz h (moebiusMap γ z) * (moebiusDenom γ z ^ 2)⁻¹
      = (moebiusDenom γ (h z) ^ 2)⁻¹ * dz h z := by
    have hL := dz_comp (f := moebiusMap γ) (g := h) hγR hdiffγ
    have hR := dz_comp (f := h) (g := moebiusMap γ) hdiff hγRh
    have hLR : dz (fun w => h (moebiusMap γ w)) z
        = dz (fun w => moebiusMap γ (h w)) z := by simp only [dz, hfeq]
    rw [hL, hR, hdzγ, hdzbarγ, hdzγh, hdzbarγh] at hLR
    simpa using hLR
  have hE2 : dzbar h (moebiusMap γ z) * conj ((moebiusDenom γ z ^ 2)⁻¹)
      = (moebiusDenom γ (h z) ^ 2)⁻¹ * dzbar h z := by
    have hL := dzbar_comp (f := moebiusMap γ) (g := h) hγR hdiffγ
    have hR := dzbar_comp (f := h) (g := moebiusMap γ) hdiff hγRh
    have hLR : dzbar (fun w => h (moebiusMap γ w)) z
        = dzbar (fun w => moebiusMap γ (h w)) z := by simp only [dzbar, hfeq]
    rw [hL, hR, hdzγ, hdzbarγ, hdzγh, hdzbarγh] at hLR
    simpa using hLR
  have hd2 : (moebiusDenom γ z ^ 2) ≠ 0 := pow_ne_zero 2 hd
  constructor
  · calc dz h (moebiusMap γ z)
        = dz h (moebiusMap γ z) * (moebiusDenom γ z ^ 2)⁻¹ * moebiusDenom γ z ^ 2 := by
          field_simp
      _ = (moebiusDenom γ (h z) ^ 2)⁻¹ * dz h z * moebiusDenom γ z ^ 2 := by rw [hE1]
      _ = (moebiusDenom γ (h z) ^ 2)⁻¹ * moebiusDenom γ z ^ 2 * dz h z := by ring
  · have hcinv : conj ((moebiusDenom γ z ^ 2)⁻¹) * conj (moebiusDenom γ z ^ 2) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hd2, map_one]
    calc dzbar h (moebiusMap γ z)
        = dzbar h (moebiusMap γ z) * conj ((moebiusDenom γ z ^ 2)⁻¹)
          * conj (moebiusDenom γ z ^ 2) := by rw [mul_assoc, hcinv, mul_one]
      _ = (moebiusDenom γ (h z) ^ 2)⁻¹ * dzbar h z * conj (moebiusDenom γ z ^ 2) := by
          rw [hE2]
      _ = (moebiusDenom γ (h z) ^ 2)⁻¹ * conj (moebiusDenom γ z ^ 2) * dzbar h z := by
          ring

/-- The Wirtinger quotient transforms by the unimodular phase `conj(d²)/d²` under a deck
transformation. -/
theorem wq_moebius {h : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hhz : 0 < (h z).im)
    (hcomm : ∀ w : ℂ, 0 < w.im → h (moebiusMap γ w) = moebiusMap γ (h w))
    (hdiff : DifferentiableAt ℝ h z) (hdiffγ : DifferentiableAt ℝ h (moebiusMap γ z)) :
    wirtingerQuotient h (moebiusMap γ z)
      = conj (moebiusDenom γ z ^ 2) / moebiusDenom γ z ^ 2 * wirtingerQuotient h z := by
  obtain ⟨h1, h2⟩ := wirtinger_moebius γ hz hhz hcomm hdiff hdiffγ
  have hd2 : moebiusDenom γ z ^ 2 ≠ 0 :=
    pow_ne_zero 2 (moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne')
  have he2 : moebiusDenom γ (h z) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (moebiusDenom_ne_zero_of_im_ne_zero γ hhz.ne')
  have he : moebiusDenom γ (h z) ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ hhz.ne'
  rcases eq_or_ne (dz h z) 0 with h0 | h0
  · rw [wirtingerQuotient, wirtingerQuotient, h1, h0]
    simp
  · rw [wirtingerQuotient, wirtingerQuotient, h1, h2]
    field_simp

/-- The unimodular direction `q/|q|` transforms by the opposite phase `d²/conj(d²)`. -/
theorem theta_moebius {q : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : 0 < z.im)
    (hqz : q (moebiusMap γ z) = moebiusDenom γ z ^ 4 * q z) :
    q (moebiusMap γ z) / (‖q (moebiusMap γ z)‖ : ℂ)
      = moebiusDenom γ z ^ 2 / conj (moebiusDenom γ z ^ 2) * (q z / (‖q z‖ : ℂ)) := by
  have hd : moebiusDenom γ z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne'
  have hc2 : moebiusDenom γ z * conj (moebiusDenom γ z)
      = ((‖moebiusDenom γ z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hnorm4 : ((‖moebiusDenom γ z‖ ^ 4 : ℝ) : ℂ)
      = conj (moebiusDenom γ z ^ 2) * moebiusDenom γ z ^ 2 := by
    have h4 : ((‖moebiusDenom γ z‖ ^ 4 : ℝ) : ℂ)
        = ((‖moebiusDenom γ z‖ ^ 2 : ℝ) : ℂ) ^ 2 := by
      push_cast
      ring
    rw [h4, ← hc2, map_pow]
    ring
  rcases eq_or_ne (q z) 0 with h0 | h0
  · rw [hqz, h0, mul_zero, zero_div, mul_zero]
  · have hcne : conj (moebiusDenom γ z ^ 2) ≠ 0 := by
      intro hcc
      have : moebiusDenom γ z ^ 2 = 0 := by
        have := congrArg conj hcc
        rwa [Complex.conj_conj, map_zero] at this
      exact pow_ne_zero 2 hd this
    have hnq : (‖q z‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0)
    rw [hqz, norm_mul, norm_pow, Complex.ofReal_mul, hnorm4]
    field_simp

/-- **Exact deck invariance of the Beltrami phase product** `μ · q/|q|`. -/
theorem wq_theta_moebius {q h : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hhz : 0 < (h z).im)
    (hqz : q (moebiusMap γ z) = moebiusDenom γ z ^ 4 * q z)
    (hcomm : ∀ w : ℂ, 0 < w.im → h (moebiusMap γ w) = moebiusMap γ (h w))
    (hdiff : DifferentiableAt ℝ h z) (hdiffγ : DifferentiableAt ℝ h (moebiusMap γ z)) :
    wirtingerQuotient h (moebiusMap γ z)
        * (q (moebiusMap γ z) / (‖q (moebiusMap γ z)‖ : ℂ))
      = wirtingerQuotient h z * (q z / (‖q z‖ : ℂ)) := by
  have hd2 : moebiusDenom γ z ^ 2 ≠ 0 :=
    pow_ne_zero 2 (moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne')
  have hcne : conj (moebiusDenom γ z ^ 2) ≠ 0 := by
    intro hcc
    have h' := congrArg conj hcc
    rw [Complex.conj_conj, map_zero] at h'
    exact hd2 h'
  have hd : moebiusDenom γ z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne'
  rw [wq_moebius γ hz hhz hcomm hdiff hdiffγ, theta_moebius γ hz hqz]
  field_simp

/-- **Exact deck invariance of the Reich–Strebel pullback** `rsQ`: the weight-4
automorphy of `q`, the equivariance of `h`, and the Möbius chain rule cancel all
denominator phases. -/
theorem rsQ_moebius {q h : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hhz : 0 < (h z).im)
    (hqz : q (moebiusMap γ z) = moebiusDenom γ z ^ 4 * q z)
    (hqhz : q (moebiusMap γ (h z)) = moebiusDenom γ (h z) ^ 4 * q (h z))
    (hcomm : ∀ w : ℂ, 0 < w.im → h (moebiusMap γ w) = moebiusMap γ (h w))
    (hdiff : DifferentiableAt ℝ h z) (hdiffγ : DifferentiableAt ℝ h (moebiusMap γ z)) :
    rsQ q h (moebiusMap γ z) = rsQ q h z := by
  obtain ⟨h1, -⟩ := wirtinger_moebius γ hz hhz hcomm hdiff hdiffγ
  have hwqθ := wq_theta_moebius γ hz hhz hqz hcomm hdiff hdiffγ
  have hd4 : moebiusDenom γ z ^ 4 ≠ 0 :=
    pow_ne_zero 4 (moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne')
  have he2 : moebiusDenom γ (h z) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (moebiusDenom_ne_zero_of_im_ne_zero γ hhz.ne')
  rw [rsQ, rsQ, hcomm z hz, hqhz, h1, hwqθ, hqz]
  have hnum : moebiusDenom γ (h z) ^ 4 * q (h z)
        * ((moebiusDenom γ (h z) ^ 2)⁻¹ * moebiusDenom γ z ^ 2 * dz h z) ^ 2
        * (1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))) ^ 2
      = moebiusDenom γ z ^ 4
        * (q (h z) * dz h z ^ 2
            * (1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))) ^ 2) := by
    have heq : moebiusDenom γ (h z) ^ 2 * (moebiusDenom γ (h z) ^ 2)⁻¹ = 1 :=
      mul_inv_cancel₀ he2
    linear_combination (q (h z) * moebiusDenom γ z ^ 4 * dz h z ^ 2
      * (1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))) ^ 2
      * ((moebiusDenom γ (h z) ^ 2)⁻¹ * moebiusDenom γ (h z) ^ 2 + 1)) * heq
  rw [hnum, neg_div, neg_div, mul_div_mul_left _ _ hd4]

/-- The norm of the Wirtinger quotient is deck-invariant. -/
theorem norm_wq_moebius {h : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hhz : 0 < (h z).im)
    (hcomm : ∀ w : ℂ, 0 < w.im → h (moebiusMap γ w) = moebiusMap γ (h w))
    (hdiff : DifferentiableAt ℝ h z) (hdiffγ : DifferentiableAt ℝ h (moebiusMap γ z)) :
    ‖wirtingerQuotient h (moebiusMap γ z)‖ = ‖wirtingerQuotient h z‖ := by
  have hd2 : ‖moebiusDenom γ z ^ 2‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (pow_ne_zero 2 (moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne'))
  rw [wq_moebius γ hz hhz hcomm hdiff hdiffγ, norm_mul, norm_div,
    RCLike.norm_conj, div_self hd2, one_mul]

/-- Deck invariance of the image vertical-leaf density. -/
theorem rsDensity_moebius {q h : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hhz : 0 < (h z).im)
    (hqz : q (moebiusMap γ z) = moebiusDenom γ z ^ 4 * q z)
    (hqhz : q (moebiusMap γ (h z)) = moebiusDenom γ (h z) ^ 4 * q (h z))
    (hcomm : ∀ w : ℂ, 0 < w.im → h (moebiusMap γ w) = moebiusMap γ (h w))
    (hdiff : DifferentiableAt ℝ h z) (hdiffγ : DifferentiableAt ℝ h (moebiusMap γ z)) :
    rsDensity q h (moebiusMap γ z) = rsDensity q h z := by
  rw [rsDensity, rsDensity, rsQ_moebius γ hz hhz hqz hqhz hcomm hdiff hdiffγ]

/-- Deck invariance of the Reich–Strebel weight. -/
theorem rsWeight_moebius {q h : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hhz : 0 < (h z).im)
    (hqz : q (moebiusMap γ z) = moebiusDenom γ z ^ 4 * q z)
    (hcomm : ∀ w : ℂ, 0 < w.im → h (moebiusMap γ w) = moebiusMap γ (h w))
    (hdiff : DifferentiableAt ℝ h z) (hdiffγ : DifferentiableAt ℝ h (moebiusMap γ z)) :
    rsWeight q h (moebiusMap γ z) = rsWeight q h z := by
  rw [rsWeight, rsWeight, wq_theta_moebius γ hz hhz hqz hcomm hdiff hdiffγ,
    norm_wq_moebius γ hz hhz hcomm hdiff hdiffγ]

/-- Deck invariance of the floored Reich–Strebel weight. -/
theorem rsWeightM_moebius {q h : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (κ : ℝ) {z : ℂ} (hz : 0 < z.im) (hhz : 0 < (h z).im)
    (hqz : q (moebiusMap γ z) = moebiusDenom γ z ^ 4 * q z)
    (hcomm : ∀ w : ℂ, 0 < w.im → h (moebiusMap γ w) = moebiusMap γ (h w))
    (hdiff : DifferentiableAt ℝ h z) (hdiffγ : DifferentiableAt ℝ h (moebiusMap γ z)) :
    rsWeightM q h κ (moebiusMap γ z) = rsWeightM q h κ z := by
  rw [rsWeightM, rsWeightM, rsWeight_moebius γ hz hhz hqz hcomm hdiff hdiffγ]

/-- Deck invariance of the first Cauchy–Schwarz factor. -/
theorem rsU_moebius {q h : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (κ : ℝ) {z : ℂ} (hz : 0 < z.im) (hhz : 0 < (h z).im)
    (hqz : q (moebiusMap γ z) = moebiusDenom γ z ^ 4 * q z)
    (hqhz : q (moebiusMap γ (h z)) = moebiusDenom γ (h z) ^ 4 * q (h z))
    (hcomm : ∀ w : ℂ, 0 < w.im → h (moebiusMap γ w) = moebiusMap γ (h w))
    (hdiff : DifferentiableAt ℝ h z) (hdiffγ : DifferentiableAt ℝ h (moebiusMap γ z)) :
    rsU q h κ (moebiusMap γ z) = rsU q h κ z := by
  rw [rsU, rsU, rsDensity_moebius γ hz hhz hqz hqhz hcomm hdiff hdiffγ,
    rsWeightM_moebius γ κ hz hhz hqz hcomm hdiff hdiffγ]

/-- **Packaging of the symmetrized flow data**: given the flow, its regular set, the two
leafwise minimal-variation bounds, and the two symmetrized invariance identities, the
composed measurability fields are discharged from joint measurability of the flow, and
the interface theorem `reich_strebel_of_flowDataSym` applies. -/
noncomputable def verticalFlowDataSym_of_leafLb
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ) (h : ℂ → ℂ) (κ : ℝ) (hh : Measurable h)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (flow : ℝ → ℂ → ℂ)
    (hflow : Measurable fun p : ℝ × ℂ => flow p.1 p.2)
    (good : Set ℂ)
    (good_ae : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∈ good)
    (leaf_lb : ∀ z ∈ good, ∀ T : ℝ, 0 < T →
      ENNReal.ofReal T
        ≤ (∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity q h (flow t z)) + 2 * C)
    (leaf_lb_neg : ∀ z ∈ good, ∀ T : ℝ, 0 < T →
      ENNReal.ofReal T
        ≤ (∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity q h (flow (-t) z)) + 2 * C)
    (invar_U : ∀ t : ℝ,
      ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
        (rsU q h κ (flow t z) + rsU q h κ (flow (-t) z)) * ‖q z‖ₑ
        = 2 * ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
          rsU q h κ z * ‖q z‖ₑ)
    (invar_W : ∀ t : ℝ,
      ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
        (rsWeightM q h κ (flow t z) + rsWeightM q h κ (flow (-t) z)) * ‖q z‖ₑ
        = 2 * ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
          rsWeightM q h κ z * ‖q z‖ₑ) :
    VerticalFlowDataSym Γ q h κ where
  C := C
  hC := hC
  flow := flow
  good := good
  good_ae := good_ae
  meas_D := (measurable_rsDensity q.measurable hh).comp hflow
  meas_U := (measurable_rsU q.measurable hh κ).comp hflow
  meas_W := (measurable_rsWeightM q.measurable h κ).comp hflow
  leaf_lb := leaf_lb
  leaf_lb_neg := leaf_lb_neg
  invar_U := invar_U
  invar_W := invar_W

/-- The **chart-translation local flow**: transport by time `t` in the natural chart `Φ`
over the chart domain `S` — the inverse-chart image of the translated development. -/
noncomputable def localFlow (Φ : ℂ → ℂ) (S : Set ℂ) (t : ℝ) (w : ℂ) : ℂ :=
  Function.invFunOn Φ S (Φ w + t)

/-- The local flow stays in the chart domain while the development stays in the
developed image. -/
theorem localFlow_mem {Φ : ℂ → ℂ} {S : Set ℂ} {t : ℝ} {w : ℂ}
    (h : Φ w + (t : ℂ) ∈ Φ '' S) : localFlow Φ S t w ∈ S := by
  obtain ⟨a, ha, hfa⟩ := h
  exact Function.invFunOn_mem ⟨a, ha, hfa⟩

/-- The defining development identity of the local flow: `Φ` of the flow is the
translated development. -/
theorem localFlow_dev {Φ : ℂ → ℂ} {S : Set ℂ} {t : ℝ} {w : ℂ}
    (h : Φ w + (t : ℂ) ∈ Φ '' S) : Φ (localFlow Φ S t w) = Φ w + t := by
  obtain ⟨a, ha, hfa⟩ := h
  exact Function.invFunOn_eq ⟨a, ha, hfa⟩

/-- The local flow at time zero is the identity on the chart domain. -/
theorem localFlow_zero {Φ : ℂ → ℂ} {S : Set ℂ} (hinj : Set.InjOn Φ S) {w : ℂ}
    (hw : w ∈ S) : localFlow Φ S 0 w = w := by
  have h0 : Φ w + ((0 : ℝ) : ℂ) = Φ w := by simp
  have hex : ∃ a ∈ S, Φ a = Φ w + ((0 : ℝ) : ℂ) := ⟨w, hw, h0.symm⟩
  exact hinj (Function.invFunOn_mem hex) hw (by rw [Function.invFunOn_eq hex, h0])

/-- The cocycle law of the local flow inside a single chart. -/
theorem localFlow_add {Φ : ℂ → ℂ} {S : Set ℂ} {s t : ℝ} {w : ℂ}
    (hs : Φ w + (s : ℂ) ∈ Φ '' S) :
    localFlow Φ S t (localFlow Φ S s w) = localFlow Φ S (s + t) w := by
  change Function.invFunOn Φ S (Φ (localFlow Φ S s w) + (t : ℂ)) = _
  rw [localFlow_dev hs]
  unfold localFlow
  congr 1
  push_cast
  ring

/-- **Unit developed velocity of the local flow line**: where the chart derivative does
not vanish, the flow line is differentiable in time with velocity `1/Φ'` — in the chart
the motion is the unit horizontal translation. -/
theorem localFlow_hasDerivAt {Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦ : DifferentiableOn ℂ Φ S) (hinj : Set.InjOn Φ S) {w : ℂ} {t : ℝ}
    (hp : Φ w + (t : ℂ) ∈ Φ '' S)
    (hder : deriv Φ (localFlow Φ S t w) ≠ 0) :
    HasDerivAt (fun u : ℝ => localFlow Φ S u w)
      ((deriv Φ (localFlow Φ S t w))⁻¹) t := by
  set p := localFlow Φ S t w with hpdef
  have hpS : p ∈ S := localFlow_mem hp
  have hΦp : Φ p = Φ w + t := localFlow_dev hp
  have han : AnalyticAt ℂ Φ p := (hΦ.analyticOnNhd hS) p hpS
  have hstrict : HasStrictDerivAt Φ (deriv Φ p) p :=
    (han.contDiffAt (n := 1)).hasStrictDerivAt one_ne_zero
  set g := hstrict.localInverse Φ (deriv Φ p) p hder with hgdef
  have himg : Φ '' S ∈ nhds (Φ p) := by
    rw [← hstrict.map_nhds_eq hder]
    exact Filter.image_mem_map (hS.mem_nhds hpS)
  have hι : Filter.Tendsto (fun u : ℝ => Φ w + (u : ℂ)) (nhds t) (nhds (Φ p)) :=
    (continuous_const.add Complex.continuous_ofReal).tendsto' t (Φ p) hΦp.symm
  have hgleft : g (Φ p) = p := (hstrict.eventually_left_inverse hder).self_of_nhds
  have hgcont : ContinuousAt g (Φ p) :=
    (hstrict.to_localInverse hder).hasDerivAt.continuousAt
  have hgS : ∀ᶠ y in nhds (Φ p), g y ∈ S := by
    rw [ContinuousAt, hgleft] at hgcont
    exact hgcont (hS.mem_nhds hpS)
  have hgright : ∀ᶠ y in nhds (Φ p), Φ (g y) = y :=
    hstrict.eventually_right_inverse hder
  have heq : (fun u : ℝ => localFlow Φ S u w)
      =ᶠ[nhds t] fun u : ℝ => g (Φ w + (u : ℂ)) := by
    filter_upwards [hι himg, hι hgS, hι hgright] with u hu h1u h2u
    exact hinj (localFlow_mem hu) h1u (by rw [localFlow_dev hu, h2u])
  have hg' : HasDerivAt g ((deriv Φ p)⁻¹) (Φ w + (t : ℂ)) :=
    hΦp ▸ (hstrict.to_localInverse hder).hasDerivAt
  have hG : HasDerivAt (fun ζ : ℂ => g (Φ w + ζ)) ((deriv Φ p)⁻¹) ((t : ℝ) : ℂ) :=
    HasDerivAt.comp_const_add (Φ w) ((t : ℝ) : ℂ) hg'
  have hcomp : HasDerivAt (fun u : ℝ => g (Φ w + (u : ℂ))) ((deriv Φ p)⁻¹) t :=
    hG.comp_ofReal
  exact hcomp.congr_of_eventuallyEq heq

/-- **Chart-level `|q|` area identity**: in a natural chart of `−q` the `|q|` area of a
measurable chart subset equals the Lebesgue area of its development. -/
theorem chart_lintegral {q Φ : ℂ → ℂ} {S A : Set ℂ} (hS : IsOpen S)
    (hΦ : DifferentiableOn ℂ Φ S) (hinj : Set.InjOn Φ S)
    (hsq : ∀ z ∈ S, deriv Φ z ^ 2 = -q z)
    (hA : MeasurableSet A) (hAS : A ⊆ S) :
    volume (Φ '' A) = ∫⁻ z in A, ‖q z‖ₑ := by
  have hdiff : ∀ x ∈ A, DifferentiableAt ℂ Φ x := fun x hx =>
    hΦ.differentiableAt (hS.mem_nhds (hAS hx))
  have hf' : ∀ x ∈ A, HasFDerivWithinAt Φ (fderiv ℝ Φ x) A x := by
    intro x hx
    have hR : DifferentiableAt ℝ Φ x :=
      (differentiableAt_complex_iff_differentiableAt_real.mp (hdiff x hx)).1
    exact hR.hasFDerivAt.hasFDerivWithinAt
  have hAF := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA hf'
    (hinj.mono hAS) (fun _ => (1 : ℝ≥0∞))
  calc volume (Φ '' A) = ∫⁻ _ in Φ '' A, 1 := (setLIntegral_one _).symm
    _ = ∫⁻ x in A, ENNReal.ofReal |(fderiv ℝ Φ x).det| * 1 := hAF
    _ = ∫⁻ z in A, ‖q z‖ₑ := by
        refine setLIntegral_congr_fun hA (fun x hx => ?_)
        have hdet : (fderiv ℝ Φ x).det = ‖deriv Φ x‖ ^ 2 := by
          rw [det_fderiv_eq_wirtinger, dzbar_eq_zero_of_differentiableAt (hdiff x hx),
            dz_eq_deriv_of_differentiableAt (hdiff x hx), norm_zero]
          ring
        have hq : ‖deriv Φ x‖ ^ 2 = ‖q x‖ := by
          rw [← norm_pow, hsq x (hAS hx), norm_neg]
        rw [mul_one, hdet, hq, abs_of_nonneg (norm_nonneg _), ofReal_norm_eq_enorm]

/-- The development of the local-flow image is the translated development. -/
theorem localFlow_image {Φ : ℂ → ℂ} {S A : Set ℂ} {t : ℝ}
    (hA : ∀ w ∈ A, Φ w + (t : ℂ) ∈ Φ '' S) :
    Φ '' (localFlow Φ S t '' A) = (fun ζ => ζ + (t : ℂ)) '' (Φ '' A) := by
  ext y
  constructor
  · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨Φ w, ⟨w, hw, rfl⟩, (localFlow_dev (hA w hw)).symm⟩
  · rintro ⟨y', ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨localFlow Φ S t w, ⟨w, hw, rfl⟩, localFlow_dev (hA w hw)⟩

/-- **Chart-level flow invariance of the `|q|` area**: transporting a chart subset by the
local flow preserves the `|q|` mass — in the development it is translation invariance of
the planar Lebesgue measure. -/
theorem chart_flow_lintegral {q Φ : ℂ → ℂ} {S A : Set ℂ} {t : ℝ} (hS : IsOpen S)
    (hΦ : DifferentiableOn ℂ Φ S) (hinj : Set.InjOn Φ S)
    (hsq : ∀ z ∈ S, deriv Φ z ^ 2 = -q z)
    (hA : MeasurableSet A) (hAS : A ⊆ S)
    (hmove : ∀ w ∈ A, Φ w + (t : ℂ) ∈ Φ '' S)
    (hB : MeasurableSet (localFlow Φ S t '' A)) :
    ∫⁻ z in localFlow Φ S t '' A, ‖q z‖ₑ = ∫⁻ z in A, ‖q z‖ₑ := by
  have hBS : localFlow Φ S t '' A ⊆ S := by
    rintro x ⟨w, hw, rfl⟩
    exact localFlow_mem (hmove w hw)
  rw [← chart_lintegral hS hΦ hinj hsq hA hAS,
    ← chart_lintegral hS hΦ hinj hsq hB hBS, localFlow_image hmove]
  have himg : (fun ζ : ℂ => ζ + (t : ℂ)) '' (Φ '' A)
      = (fun ζ : ℂ => ζ + -(t : ℂ)) ⁻¹' (Φ '' A) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨y + -(t : ℂ), hy, by ring⟩
  rw [himg, measure_preimage_add_right]

/-- A **vertical trajectory** of `q` on a set of times: a continuous curve carried by
`−q`-natural charts avoiding the zeros, in which the development is the unit-speed
horizontal translation. -/
structure IsTrajOn (q : ℂ → ℂ) (σ : ℝ → ℂ) (s : Set ℝ) : Prop where
  cont : ContinuousOn σ s
  chart : ∀ t ∈ s, ∃ U : Set ℂ, IsOpen U ∧ σ t ∈ U ∧ U ⊆ {z : ℂ | 0 < z.im} ∧
    (∀ w ∈ U, q w ≠ 0) ∧ ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ U ∧ Set.InjOn Φ U ∧
    (∀ w ∈ U, deriv Φ w ^ 2 = -q w) ∧
    ∀ᶠ u in nhdsWithin t s, σ u ∈ U ∧ Φ (σ u) = Φ (σ t) + ((u - t : ℝ) : ℂ)

/-- **Trajectory seed**: through every regular point of the upper half plane there is a
vertical trajectory on a symmetric time interval, built from one natural chart by the
local translation flow. -/
theorem exists_traj_seed {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) {z : ℂ} (hz : 0 < z.im)
    (hq0 : q z ≠ 0) :
    ∃ δ > 0, ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc (-δ) δ) := by
  have hH : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨r, hr, hsubH, Φ, hΦd, hΦinj, hΦsq⟩ :=
    exists_natural_chart (q := fun w => -q w) hH hq.neg hz (neg_ne_zero.mpr hq0)
  have hqc : ContinuousAt q z := hq.continuousOn.continuousAt (hH.mem_nhds hz)
  obtain ⟨r₁, hr₁, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hqc (isOpen_ne.mem_nhds hq0) : q ⁻¹' {w | w ≠ 0} ∈ nhds z)
      (Metric.ball_mem_nhds z hr))
  set S : Set ℂ := Metric.ball z r₁ with hSdef
  have hSr : S ⊆ Metric.ball z r := fun w hw => (hball hw).2
  have hSne : ∀ w ∈ S, q w ≠ 0 := fun w hw => (hball hw).1
  have hSopen : IsOpen S := Metric.isOpen_ball
  have hSH : S ⊆ {z : ℂ | 0 < z.im} := hSr.trans hsubH
  have hzS : z ∈ S := Metric.mem_ball_self hr₁
  have hΦdS : DifferentiableOn ℂ Φ S := hΦd.mono hSr
  have hΦinjS : Set.InjOn Φ S := hΦinj.mono hSr
  have hΦsqS : ∀ w ∈ S, deriv Φ w ^ 2 = -q w := fun w hw => hΦsq w (hSr hw)
  have hder : ∀ w ∈ S, deriv Φ w ≠ 0 := by
    intro w hw h0
    exact hSne w hw (by have := hΦsqS w hw; rw [h0] at this; simpa using this.symm)
  -- the developed image is a neighborhood of the developed center
  have han : AnalyticAt ℂ Φ z := (hΦdS.analyticOnNhd hSopen) z hzS
  have hstrict : HasStrictDerivAt Φ (deriv Φ z) z :=
    (han.contDiffAt (n := 1)).hasStrictDerivAt one_ne_zero
  have himg : Φ '' S ∈ nhds (Φ z) := by
    rw [← hstrict.map_nhds_eq (hder z hzS)]
    exact Filter.image_mem_map (hSopen.mem_nhds hzS)
  obtain ⟨δ₂, hδ₂, hδball⟩ := Metric.mem_nhds_iff.mp himg
  set δ : ℝ := δ₂ / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hmove : ∀ u : ℝ, |u| ≤ δ → Φ z + (u : ℂ) ∈ Φ '' S := by
    intro u hu
    refine hδball (Metric.mem_ball.mpr ?_)
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
    linarith
  set σ : ℝ → ℂ := fun u => localFlow Φ S u z with hσdef
  have hmem : ∀ u ∈ Set.Icc (-δ) δ, Φ z + (u : ℂ) ∈ Φ '' S := fun u hu =>
    hmove u (abs_le.mpr ⟨hu.1, hu.2⟩)
  have hσdev : ∀ u ∈ Set.Icc (-δ) δ, Φ (σ u) = Φ z + u := fun u hu =>
    localFlow_dev (hmem u hu)
  have hσS : ∀ u ∈ Set.Icc (-δ) δ, σ u ∈ S := fun u hu => localFlow_mem (hmem u hu)
  have hσcont : ContinuousOn σ (Set.Icc (-δ) δ) := by
    intro u hu
    exact (localFlow_hasDerivAt hSopen hΦdS hΦinjS (hmem u hu)
      (hder _ (hσS u hu))).continuousAt.continuousWithinAt
  refine ⟨δ, hδ, σ, localFlow_zero hΦinjS hzS, hσcont, ?_⟩
  intro t ht
  refine ⟨S, hSopen, hσS t ht, hSH, hSne, Φ, hΦdS, hΦinjS, hΦsqS, ?_⟩
  filter_upwards [eventually_mem_nhdsWithin] with u hu
  refine ⟨hσS u hu, ?_⟩
  rw [hσdev u hu, hσdev t ht]
  push_cast
  ring

/-- **Forward germ propagation**: two vertical trajectories that agree strictly before a
time `c` and at `c` agree near `c` within the time interval — the chart branch
classification pins the sign by the backward overlap. -/
theorem traj_germ {q : ℂ → ℂ} {σ₁ σ₂ : ℝ → ℂ} {a b c : ℝ}
    (h₁ : IsTrajOn q σ₁ (Set.Icc a b)) (h₂ : IsTrajOn q σ₂ (Set.Icc a b))
    (hc : c ∈ Set.Icc a b) (hac : a < c)
    (hup : ∀ u ∈ Set.Ico a c, σ₁ u = σ₂ u) (hcc : σ₁ c = σ₂ c) :
    ∀ᶠ u in nhdsWithin c (Set.Icc a b), σ₁ u = σ₂ u := by
  obtain ⟨U₁, hU₁o, hpU₁, -, -, Φ₁, hΦ₁d, hΦ₁inj, hΦ₁sq, hev₁⟩ := h₁.chart c hc
  obtain ⟨U₂, hU₂o, hpU₂', -, -, Φ₂, hΦ₂d, hΦ₂inj, hΦ₂sq, hev₂⟩ := h₂.chart c hc
  set p : ℂ := σ₁ c with hpdef
  have hpU₂ : p ∈ U₂ := by rw [hcc]; exact hpU₂'
  set Ω : Set ℂ := connectedComponentIn (U₁ ∩ U₂) p with hΩdef
  have hΩo : IsOpen Ω := (hU₁o.inter hU₂o).connectedComponentIn
  have hΩconn : IsPreconnected Ω := isPreconnected_connectedComponentIn
  have hpΩ : p ∈ Ω := mem_connectedComponentIn ⟨hpU₁, hpU₂⟩
  have hΩsub : Ω ⊆ U₁ ∩ U₂ := connectedComponentIn_subset _ _
  have hsq' : ∀ z ∈ Ω, deriv Φ₂ z ^ 2 = deriv Φ₁ z ^ 2 := fun z hz => by
    rw [hΦ₂sq z (hΩsub hz).2, hΦ₁sq z (hΩsub hz).1]
  have hσ₁Ω : ∀ᶠ u in nhdsWithin c (Set.Icc a b), σ₁ u ∈ Ω :=
    (h₁.cont c hc) (hΩo.mem_nhds hpΩ)
  have hσ₂Ω : ∀ᶠ u in nhdsWithin c (Set.Icc a b), σ₂ u ∈ Ω := by
    have h2c : ContinuousWithinAt σ₂ (Set.Icc a b) c := h₂.cont c hc
    exact h2c (hcc ▸ hΩo.mem_nhds hpΩ)
  have hΦ₂p : Φ₂ (σ₂ c) = Φ₂ p := by rw [hcc]
  rcases open_branch_classification hΩo hΩconn hpΩ
      (hΦ₁d.mono (hΩsub.trans Set.inter_subset_left))
      (hΦ₂d.mono (hΩsub.trans Set.inter_subset_right)) hsq' with hplus | hminus
  · filter_upwards [hev₁, hev₂, hσ₁Ω, hσ₂Ω] with u h1u h2u hΩ1 hΩ2
    have hval : Φ₁ (σ₂ u) = Φ₁ p + ((u - c : ℝ) : ℂ) := by
      have h := hplus (σ₂ u) hΩ2
      have h2 := h2u.2
      rw [hΦ₂p] at h2
      rw [h2] at h
      linear_combination -h
    exact hΦ₁inj (hΩsub hΩ1).1 (hΩsub hΩ2).1 (by rw [h1u.2, hval])
  · exfalso
    have hsubIco : Set.Ico a c ⊆ Set.Icc a b := fun u hu =>
      ⟨hu.1, le_trans hu.2.le hc.2⟩
    have hne : (nhdsWithin c (Set.Ico a c)).NeBot := by
      refine mem_closure_iff_nhdsWithin_neBot.mp ?_
      rw [closure_Ico hac.ne]
      exact ⟨hac.le, le_refl c⟩
    have hmono : nhdsWithin c (Set.Ico a c) ≤ nhdsWithin c (Set.Icc a b) :=
      nhdsWithin_mono c hsubIco
    have hbig := (hev₁.and (hev₂.and hσ₂Ω)).filter_mono hmono
    obtain ⟨u, huIco, h1u, h2u, hΩ2⟩ := (eventually_mem_nhdsWithin.and hbig).exists
    have hval : Φ₁ (σ₂ u) = Φ₁ p - ((u - c : ℝ) : ℂ) := by
      have h := hminus (σ₂ u) hΩ2
      have h2 := h2u.2
      rw [hΦ₂p] at h2
      rw [h2] at h
      linear_combination h
    have hval1 : Φ₁ (σ₁ u) = Φ₁ p + ((u - c : ℝ) : ℂ) := h1u.2
    have hueq : σ₁ u = σ₂ u := hup u huIco
    have hzero : ((u - c : ℝ) : ℂ) = 0 := by
      have := hval1.symm.trans (by rw [hueq, hval])
      linear_combination this / 2
    have : u = c := by
      have h0 : (u - c : ℝ) = 0 := by exact_mod_cast hzero
      linarith
    exact absurd this (ne_of_lt huIco.2)

/-- **Uniqueness of vertical trajectories**: two trajectories on `[a, b]` with the same
germ at `a` coincide on all of `[a, b]`. -/
theorem traj_unique {q : ℂ → ℂ} {σ₁ σ₂ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (h₁ : IsTrajOn q σ₁ (Set.Icc a b)) (h₂ : IsTrajOn q σ₂ (Set.Icc a b))
    (hgerm : ∀ᶠ u in nhdsWithin a (Set.Icc a b), σ₁ u = σ₂ u) :
    Set.EqOn σ₁ σ₂ (Set.Icc a b) := by
  set A : Set ℝ := {t | t ∈ Set.Icc a b ∧ ∀ u ∈ Set.Icc a t, σ₁ u = σ₂ u} with hAdef
  have haa : σ₁ a = σ₂ a := hgerm.self_of_nhdsWithin (Set.left_mem_Icc.mpr hab)
  have haA : a ∈ A := by
    refine ⟨Set.left_mem_Icc.mpr hab, fun u hu => ?_⟩
    have hua : u = a := le_antisymm hu.2 hu.1
    rw [hua]
    exact haa
  have hbdd : BddAbove A := ⟨b, fun t ht => ht.1.2⟩
  set c : ℝ := sSup A with hcdef
  have hcA : a ≤ c := le_csSup hbdd haA
  have hcb : c ≤ b := csSup_le ⟨a, haA⟩ (fun t ht => ht.1.2)
  have hc : c ∈ Set.Icc a b := ⟨hcA, hcb⟩
  have hup : ∀ u ∈ Set.Ico a c, σ₁ u = σ₂ u := by
    intro u hu
    obtain ⟨t, htA, hut⟩ := exists_lt_of_lt_csSup ⟨a, haA⟩ hu.2
    exact htA.2 u ⟨hu.1, hut.le⟩
  have hsubIco : Set.Ico a c ⊆ Set.Icc a b := fun u hu =>
    ⟨hu.1, le_trans hu.2.le hcb⟩
  have hcc : σ₁ c = σ₂ c := by
    rcases eq_or_lt_of_le hcA with heq | hac
    · rw [← heq]
      exact haa
    · haveI hne : (nhdsWithin c (Set.Ico a c)).NeBot := by
        refine mem_closure_iff_nhdsWithin_neBot.mp ?_
        rw [closure_Ico hac.ne]
        exact ⟨hac.le, le_refl c⟩
      have hlim₁ : Filter.Tendsto σ₁ (nhdsWithin c (Set.Ico a c)) (nhds (σ₁ c)) :=
        (h₁.cont c hc).mono_left (nhdsWithin_mono c hsubIco)
      have hlim₂ : Filter.Tendsto σ₂ (nhdsWithin c (Set.Ico a c)) (nhds (σ₂ c)) :=
        (h₂.cont c hc).mono_left (nhdsWithin_mono c hsubIco)
      have heqf : σ₂ =ᶠ[nhdsWithin c (Set.Ico a c)] σ₁ :=
        eventually_mem_nhdsWithin.mono fun u hu => (hup u hu).symm
      exact tendsto_nhds_unique hlim₁ (hlim₂.congr' heqf)
  rcases eq_or_lt_of_le hcb with heqb | hclt
  · intro u hu
    rcases eq_or_lt_of_le hu.2 with hub | hub
    · rw [hub, ← heqb]
      exact hcc
    · exact hup u ⟨hu.1, by rw [heqb]; exact hub⟩
  · exfalso
    have hgermc : ∀ᶠ u in nhdsWithin c (Set.Icc a b), σ₁ u = σ₂ u := by
      rcases eq_or_lt_of_le hcA with heq | hac
      · rw [← heq]
        exact hgerm
      · exact traj_germ h₁ h₂ hc hac hup hcc
    obtain ⟨V, hVopen, hcV, hVsub⟩ := mem_nhdsWithin.mp hgermc
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVopen c hcV
    set t' : ℝ := min b (c + ε / 2) with ht'def
    have ht'c : c < t' := lt_min hclt (by linarith)
    have ht'A : t' ∈ A := by
      refine ⟨⟨le_trans hcA ht'c.le, min_le_left _ _⟩, ?_⟩
      intro u hu
      rcases lt_or_ge u c with huc | huc
      · exact hup u ⟨hu.1, huc⟩
      · rcases eq_or_lt_of_le huc with hueq | hult
        · rw [← hueq]
          exact hcc
        · refine hVsub ⟨hball ?_, ⟨hu.1, le_trans hu.2 (min_le_left _ _)⟩⟩
          rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
          have hu2 := le_trans hu.2 (min_le_right _ _)
          linarith
    have := le_csSup hbdd ht'A
    linarith
/-- **Time reversal** of a vertical trajectory: reversing time and negating the chart
gives a vertical trajectory on the reflected time set. -/
theorem traj_reverse {q : ℂ → ℂ} {σ : ℝ → ℂ} {s : Set ℝ}
    (h : IsTrajOn q σ s) :
    IsTrajOn q (fun u => σ (-u)) ((fun u : ℝ => -u) ⁻¹' s) := by
  have hmap : ∀ t : ℝ, t ∈ (fun u : ℝ => -u) ⁻¹' s →
      Filter.Tendsto (fun u : ℝ => -u) (nhdsWithin t ((fun u : ℝ => -u) ⁻¹' s))
        (nhdsWithin (-t) s) := by
    intro t _
    refine Filter.Tendsto.inf (continuous_neg.tendsto t) ?_
    exact Filter.tendsto_principal_principal.mpr fun u hu => hu
  constructor
  · intro t ht
    exact ContinuousWithinAt.comp (h.cont (-t) ht)
      (continuous_neg.continuousWithinAt) (fun u hu => hu)
  · intro t ht
    obtain ⟨U, hUo, hmem, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ := h.chart (-t) ht
    refine ⟨U, hUo, hmem, hUH, hUne, fun z => -Φ z, hΦd.neg, ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      exact hΦinj hx hy (neg_injective hxy)
    · intro w hw
      have hd : deriv (fun z => -Φ z) w = -deriv Φ w := by
        simp [deriv.fun_neg]
      rw [hd]
      rw [show (-deriv Φ w) ^ 2 = deriv Φ w ^ 2 by ring]
      exact hΦsq w hw
    · have := (hmap t ht).eventually hev
      filter_upwards [this] with u hu
      refine ⟨hu.1, ?_⟩
      have h2 := hu.2
      rw [h2]
      push_cast
      ring

/-- Reflection symmetry of the symmetric interval under negation. -/
theorem neg_preimage_Icc (δ : ℝ) :
    (fun u : ℝ => -u) ⁻¹' Set.Icc (-δ) δ = Set.Icc (-δ) δ := by
  ext u
  simp only [Set.mem_preimage, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- **Branch alignment of a seed at the endpoint of a trajectory**: a seed through the
endpoint may be reoriented so that, in the endpoint chart of the incoming trajectory,
its development continues the incoming development with unit speed. -/
theorem traj_align {q : ℂ → ℂ} {σ τ : ℝ → ℂ} {b δ : ℝ} (hb : 0 ≤ b) (hδ : 0 < δ)
    (hσ : IsTrajOn q σ (Set.Icc 0 b)) (hτ : IsTrajOn q τ (Set.Icc (-δ) δ))
    (hmatch : τ 0 = σ b) :
    ∃ υ : ℝ → ℂ, υ 0 = σ b ∧ IsTrajOn q υ (Set.Icc (-δ) δ) ∧
      ∃ U : Set ℂ, IsOpen U ∧ σ b ∈ U ∧ U ⊆ {z : ℂ | 0 < z.im} ∧
      (∀ w ∈ U, q w ≠ 0) ∧ ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ U ∧ Set.InjOn Φ U ∧
        (∀ w ∈ U, deriv Φ w ^ 2 = -q w) ∧
        (∀ᶠ u in nhdsWithin b (Set.Icc 0 b),
          σ u ∈ U ∧ Φ (σ u) = Φ (σ b) + ((u - b : ℝ) : ℂ)) ∧
        (∀ᶠ v in nhdsWithin 0 (Set.Icc (-δ) δ), υ v ∈ U ∧ Φ (υ v) = Φ (σ b) + (v : ℂ)) := by
  have hbmem : b ∈ Set.Icc (0 : ℝ) b := Set.right_mem_Icc.mpr hb
  have h0mem : (0 : ℝ) ∈ Set.Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hevσ⟩ := hσ.chart b hbmem
  obtain ⟨Uτ, hUτo, hpUτ', -, -, Φτ, hΦτd, hΦτinj, hΦτsq, hevτ⟩ := hτ.chart 0 h0mem
  set p : ℂ := σ b with hpdef
  have hτ0 : τ 0 = p := hmatch
  have hpUτ : p ∈ Uτ := hτ0 ▸ hpUτ'
  set Ω : Set ℂ := connectedComponentIn (U ∩ Uτ) p with hΩdef
  have hΩo : IsOpen Ω := (hUo.inter hUτo).connectedComponentIn
  have hΩconn : IsPreconnected Ω := isPreconnected_connectedComponentIn
  have hpΩ : p ∈ Ω := mem_connectedComponentIn ⟨hpU, hpUτ⟩
  have hΩsub : Ω ⊆ U ∩ Uτ := connectedComponentIn_subset _ _
  have hsq' : ∀ z ∈ Ω, deriv Φτ z ^ 2 = deriv Φ z ^ 2 := fun z hz => by
    rw [hΦτsq z (hΩsub hz).2, hΦsq z (hΩsub hz).1]
  have hτΩ : ∀ᶠ v in nhdsWithin 0 (Set.Icc (-δ) δ), τ v ∈ Ω :=
    (hτ.cont 0 h0mem) (hτ0 ▸ hΩo.mem_nhds hpΩ)
  have hΦτ0 : Φτ (τ 0) = Φτ p := by rw [hτ0]
  rcases open_branch_classification hΩo hΩconn hpΩ
      (hΦd.mono (hΩsub.trans Set.inter_subset_left))
      (hΦτd.mono (hΩsub.trans Set.inter_subset_right)) hsq' with hplus | hminus
  · refine ⟨τ, hτ0, hτ, U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hevσ, ?_⟩
    filter_upwards [hevτ, hτΩ] with v hv hvΩ
    refine ⟨(hΩsub hvΩ).1, ?_⟩
    have h := hplus (τ v) hvΩ
    have h2 := hv.2
    rw [hΦτ0] at h2
    rw [h2] at h
    rw [show ((v - 0 : ℝ) : ℂ) = (v : ℂ) by push_cast; ring] at h
    linear_combination -h
  · have hneg : Filter.Tendsto (fun v : ℝ => -v)
        (nhdsWithin 0 (Set.Icc (-δ) δ)) (nhdsWithin 0 (Set.Icc (-δ) δ)) := by
      refine Filter.Tendsto.inf ?_ ?_
      · have hn := (continuous_neg : Continuous fun v : ℝ => -v).tendsto 0
        rwa [neg_zero] at hn
      · refine Filter.tendsto_principal_principal.mpr fun v hv => ?_
        rw [Set.mem_Icc] at hv ⊢
        constructor <;> linarith [hv.1, hv.2]
    have hrev := traj_reverse hτ
    rw [neg_preimage_Icc δ] at hrev
    refine ⟨fun v => τ (-v), by change τ (-0) = _; rw [neg_zero]; exact hτ0, hrev,
      U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hevσ, ?_⟩
    filter_upwards [hneg.eventually hevτ, hneg.eventually hτΩ] with v hv hvΩ
    refine ⟨(hΩsub hvΩ).1, ?_⟩
    have h := hminus (τ (-v)) hvΩ
    have h2 := hv.2
    rw [hΦτ0] at h2
    rw [h2] at h
    rw [show ((-v - 0 : ℝ) : ℂ) = -(v : ℂ) by push_cast; ring] at h
    linear_combination h

/-- Below the junction the extended time interval induces the same within-filter. -/
theorem nhdsWithin_left {b b' t : ℝ} (hbb : b ≤ b') (ht : t < b) :
    nhdsWithin t (Set.Icc 0 b') = nhdsWithin t (Set.Icc 0 b) := by
  have hio : Set.Iio b ∈ nhds t := Iio_mem_nhds ht
  rw [nhdsWithin_restrict' _ hio, nhdsWithin_restrict' (Set.Icc 0 b) hio]
  congr 1
  ext u
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, by linarith⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, by linarith⟩, h3⟩

/-- Above the junction the full time interval induces the same within-filter as the
right piece. -/
theorem nhdsWithin_right {b δ t : ℝ} (h0 : 0 ≤ b) (ht : b < t) :
    nhdsWithin t (Set.Icc 0 (b + δ)) = nhdsWithin t (Set.Icc b (b + δ)) := by
  have hio : Set.Ioi b ∈ nhds t := Ioi_mem_nhds ht
  rw [nhdsWithin_restrict' _ hio, nhdsWithin_restrict' (Set.Icc b (b + δ)) hio]
  congr 1
  ext u
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioi]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by linarith, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by linarith, h2⟩, h3⟩

/-- The within-filter of the glued interval at any point splits over the two pieces. -/
theorem nhdsWithin_split {b δ t : ℝ} (hb : 0 ≤ b) (hδ : 0 ≤ δ) :
    nhdsWithin t (Set.Icc 0 (b + δ))
      = nhdsWithin t (Set.Icc 0 b) ⊔ nhdsWithin t (Set.Icc b (b + δ)) := by
  rw [← nhdsWithin_union, Set.Icc_union_Icc_eq_Icc hb (by linarith)]

/-- The time shift carries the right-piece within-filter to the seed interval filter. -/
theorem tendsto_shift {b δ t : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun u : ℝ => u - b) (nhdsWithin t (Set.Icc b (b + δ)))
      (nhdsWithin (t - b) (Set.Icc (-δ) δ)) := by
  refine Filter.Tendsto.inf ((continuous_sub_right b).tendsto t) ?_
  refine Filter.tendsto_principal_principal.mpr fun u hu => ?_
  rw [Set.mem_Icc] at hu ⊢
  constructor <;> linarith [hu.1, hu.2]

/-- **Trajectory extension**: a vertical trajectory on `[0, b]` extends beyond `b` — the
aligned seed at the endpoint continues the development with unit speed. -/
theorem traj_extend {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) {σ : ℝ → ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hσ : IsTrajOn q σ (Set.Icc 0 b)) :
    ∃ δ > 0, ∃ σ' : ℝ → ℂ, Set.EqOn σ' σ (Set.Icc 0 b) ∧
      IsTrajOn q σ' (Set.Icc 0 (b + δ)) := by
  have hbmem : b ∈ Set.Icc (0 : ℝ) b := Set.right_mem_Icc.mpr hb
  obtain ⟨U₀, -, hpU₀, hU₀H, hU₀ne, -⟩ := hσ.chart b hbmem
  obtain ⟨δ, hδ, τ, hτ0, hτ⟩ := exists_traj_seed hq (hU₀H hpU₀) (hU₀ne _ hpU₀)
  obtain ⟨υ, hυ0, hυ, U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hevL, hevR⟩ :=
    traj_align hb hδ hσ hτ hτ0
  set σ' : ℝ → ℂ := fun u => if u ≤ b then σ u else υ (u - b) with hσ'def
  have hEq : Set.EqOn σ' σ (Set.Icc 0 b) := fun u hu => if_pos hu.2
  have hσ'b : σ' b = σ b := if_pos le_rfl
  have hEqR : ∀ u ∈ Set.Icc b (b + δ), σ' u = υ (u - b) := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with heq | hlt
    · rw [← heq, hσ'b, show b - b = (0 : ℝ) by ring, hυ0]
    · exact if_neg (not_le.mpr hlt)
  have hshift0 : Filter.Tendsto (fun u : ℝ => u - b)
      (nhdsWithin b (Set.Icc b (b + δ))) (nhdsWithin 0 (Set.Icc (-δ) δ)) := by
    have h := tendsto_shift (t := b) (b := b) hδ
    rwa [show b - b = (0 : ℝ) by ring] at h
  have h0mem : (0 : ℝ) ∈ Set.Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  refine ⟨δ, hδ, σ', hEq, ?_, ?_⟩
  · intro t ht
    rcases lt_trichotomy t b with htb | heq | htb
    · change Filter.Tendsto σ' (nhdsWithin t (Set.Icc 0 (b + δ))) (nhds (σ' t))
      rw [nhdsWithin_left (by linarith) htb, hEq ⟨ht.1, htb.le⟩]
      exact Filter.Tendsto.congr'
        (eventually_mem_nhdsWithin.mono fun u hu => (hEq hu).symm)
        (hσ.cont t ⟨ht.1, htb.le⟩)
    · subst heq
      change Filter.Tendsto σ' (nhdsWithin t (Set.Icc 0 (t + δ))) (nhds (σ' t))
      rw [nhdsWithin_split hb hδ.le, Filter.tendsto_sup]
      constructor
      · rw [hσ'b]
        exact Filter.Tendsto.congr'
          (eventually_mem_nhdsWithin.mono fun u hu => (hEq hu).symm)
          (hσ.cont t hbmem)
      · rw [hσ'b, ← hυ0]
        refine Filter.Tendsto.congr'
          (eventually_mem_nhdsWithin.mono fun u hu => (hEqR u hu).symm) ?_
        exact Filter.Tendsto.comp (hυ.cont 0 h0mem) hshift0
    · change Filter.Tendsto σ' (nhdsWithin t (Set.Icc 0 (b + δ))) (nhds (σ' t))
      have htmem : t - b ∈ Set.Icc (-δ) δ := ⟨by linarith, by linarith [ht.2]⟩
      rw [nhdsWithin_right hb htb, hEqR t ⟨htb.le, ht.2⟩]
      refine Filter.Tendsto.congr'
        (eventually_mem_nhdsWithin.mono fun u hu => (hEqR u hu).symm) ?_
      exact Filter.Tendsto.comp (hυ.cont (t - b) htmem) (tendsto_shift hδ)
  · intro t ht
    rcases lt_trichotomy t b with htb | heq | htb
    · obtain ⟨Ut, hUto, hptU, hUtH, hUtne, Φt, hΦtd, hΦtinj, hΦtsq, hevt⟩ :=
        hσ.chart t ⟨ht.1, htb.le⟩
      refine ⟨Ut, hUto, by rw [hEq ⟨ht.1, htb.le⟩]; exact hptU, hUtH, hUtne,
        Φt, hΦtd, hΦtinj, hΦtsq, ?_⟩
      rw [nhdsWithin_left (by linarith) htb]
      filter_upwards [hevt, eventually_mem_nhdsWithin] with u hu huIcc
      rw [hEq huIcc, hEq ⟨ht.1, htb.le⟩]
      exact hu
    · subst heq
      refine ⟨U, hUo, by rw [hσ'b]; exact hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, ?_⟩
      rw [nhdsWithin_split hb hδ.le, Filter.eventually_sup]
      constructor
      · filter_upwards [hevL, eventually_mem_nhdsWithin] with u hu huIcc
        rw [hEq huIcc, hσ'b]
        refine ⟨hu.1, ?_⟩
        rw [hu.2]
      · filter_upwards [hshift0.eventually hevR, eventually_mem_nhdsWithin]
          with u hu huIcc
        rw [hEqR u huIcc, hσ'b]
        exact hu
    · have htmem : t - b ∈ Set.Icc (-δ) δ := ⟨by linarith, by linarith [ht.2]⟩
      obtain ⟨Ut, hUto, hptU, hUtH, hUtne, Φt, hΦtd, hΦtinj, hΦtsq, hevt⟩ :=
        hυ.chart (t - b) htmem
      refine ⟨Ut, hUto, by rw [hEqR t ⟨htb.le, ht.2⟩]; exact hptU, hUtH, hUtne,
        Φt, hΦtd, hΦtinj, hΦtsq, ?_⟩
      rw [nhdsWithin_right hb htb]
      filter_upwards [(tendsto_shift hδ).eventually hevt,
        eventually_mem_nhdsWithin] with u hu huIcc
      rw [hEqR u huIcc, hEqR t ⟨htb.le, ht.2⟩]
      refine ⟨hu.1, ?_⟩
      rw [hu.2]
      congr 1
      push_cast
      ring

/-- **Interior derivative of a vertical trajectory**: at an interior time the trajectory
is differentiable, with speed of squared norm `1/|q|` — unit flat speed. -/
theorem traj_hasDerivAt {q : ℂ → ℂ} {σ : ℝ → ℂ} {s : Set ℝ} {t : ℝ}
    (hσ : IsTrajOn q σ s) (ht : t ∈ s) (hnhds : s ∈ nhds t) :
    ∃ d : ℂ, HasDerivAt σ d t ∧ ‖d‖ ^ 2 * ‖q (σ t)‖ = 1 := by
  obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ := hσ.chart t ht
  rw [nhdsWithin_eq_nhds.mpr hnhds] at hev
  set p : ℂ := σ t with hpdef
  have hq0 : q p ≠ 0 := hUne p hpU
  have hder : deriv Φ p ≠ 0 := by
    intro h0
    apply hq0
    have := hΦsq p hpU
    rw [h0] at this
    simpa using this.symm
  have han : AnalyticAt ℂ Φ p := (hΦd.analyticOnNhd hUo) p hpU
  have hstrict : HasStrictDerivAt Φ (deriv Φ p) p :=
    (han.contDiffAt (n := 1)).hasStrictDerivAt one_ne_zero
  set g : ℂ → ℂ := hstrict.localInverse Φ (deriv Φ p) p hder with hgdef
  have hgleft : ∀ᶠ x in nhds p, g (Φ x) = x := hstrict.eventually_left_inverse hder
  have hcont : ContinuousAt σ t := by
    have := hσ.cont t ht
    rwa [ContinuousWithinAt, nhdsWithin_eq_nhds.mpr hnhds] at this
  have hσp : ∀ᶠ v in nhds t, g (Φ (σ v)) = σ v := hcont hgleft
  have heq : σ =ᶠ[nhds t] fun v : ℝ => g (Φ p + ((v - t : ℝ) : ℂ)) := by
    filter_upwards [hσp, hev] with v hv hv2
    rw [← hv, hv2.2]
  have hg' : HasDerivAt g ((deriv Φ p)⁻¹) (Φ p) :=
    (hstrict.to_localInverse hder).hasDerivAt
  have hG : HasDerivAt (fun ζ : ℂ => g (Φ p + ζ)) ((deriv Φ p)⁻¹)
      (((t - t : ℝ) : ℂ)) := by
    refine HasDerivAt.comp_const_add (Φ p) _ ?_
    rw [show Φ p + ((t - t : ℝ) : ℂ) = Φ p by push_cast; ring]
    exact hg'
  have hF : HasDerivAt (fun v : ℝ => g (Φ p + ((v - t : ℝ) : ℂ)))
      ((deriv Φ p)⁻¹) t := by
    have h1 : HasDerivAt (fun v : ℝ => g (Φ p + ((v : ℝ) : ℂ))) ((deriv Φ p)⁻¹)
        (t - t) := by
      have := hG.comp_ofReal (z := t - t)
      simpa using this
    have h2 := HasDerivAt.comp_sub_const (x := t) (a := t) h1
    simpa using h2
  have hd : HasDerivAt σ ((deriv Φ p)⁻¹) t := hF.congr_of_eventuallyEq heq
  refine ⟨(deriv Φ p)⁻¹, hd, ?_⟩
  have hnorm : ‖deriv Φ p‖ ^ 2 = ‖q p‖ := by
    rw [← norm_pow, hΦsq p hpU, norm_neg]
  rw [norm_inv, inv_pow, hnorm]
  exact inv_mul_cancel₀ (by simpa using hq0)

/-- **Flat-speed Lipschitz bound**: a trajectory whose track satisfies a lower bound on
`|q|` is Lipschitz with constant `√(1/m)` on interior closed subintervals. -/
theorem traj_dist_le {q : ℂ → ℂ} {σ : ℝ → ℂ} {c : ℝ}
    (hσ : IsTrajOn q σ (Set.Ico 0 c)) {m : ℝ} (hm : 0 < m)
    (hbound : ∀ t ∈ Set.Ico 0 c, m ≤ ‖q (σ t)‖)
    {s u : ℝ} (hs : 0 < s) (hsu : s ≤ u) (hu : u < c) :
    ‖σ u - σ s‖ ≤ Real.sqrt m⁻¹ * (u - s) := by
  have hex : ∀ x ∈ Set.Icc s u, ∃ d : ℂ, HasDerivAt σ d x ∧ ‖d‖ ^ 2 * ‖q (σ x)‖ = 1 := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hs hx.1
    have hxc : x < c := lt_of_le_of_lt hx.2 hu
    exact traj_hasDerivAt hσ ⟨hx0.le, hxc⟩ (Ico_mem_nhds hx0 hxc)
  choose! d hd1 hd2 using hex
  have hf : ∀ x ∈ Set.Icc s u, HasDerivWithinAt σ (d x) (Set.Icc s u) x := fun x hx =>
    (hd1 x hx).hasDerivWithinAt
  have hboundd : ∀ x ∈ Set.Ico s u, ‖d x‖ ≤ Real.sqrt m⁻¹ := by
    intro x hx
    have hxI : x ∈ Set.Icc s u := ⟨hx.1, hx.2.le⟩
    have hx0 : 0 < x := lt_of_lt_of_le hs hx.1
    have hxc : x < c := lt_of_lt_of_le hx.2 hu.le
    have hq : m ≤ ‖q (σ x)‖ := hbound x ⟨hx0.le, hxc⟩
    have hqpos : 0 < ‖q (σ x)‖ := lt_of_lt_of_le hm hq
    have hsq : ‖d x‖ ^ 2 = ‖q (σ x)‖⁻¹ := by
      have h := hd2 x hxI
      field_simp
      linarith [h]
    have hle : ‖d x‖ ^ 2 ≤ m⁻¹ := by
      rw [hsq]
      exact inv_anti₀ hm hq
    calc ‖d x‖ = Real.sqrt (‖d x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt m⁻¹ := Real.sqrt_le_sqrt hle
  have := norm_image_sub_le_of_norm_deriv_le_segment' hf hboundd u
    (Set.right_mem_Icc.mpr hsu)
  linarith [this]

/-- **Limit at a finite escape time**: a trajectory on `[0, c)` whose track keeps `|q|`
bounded below converges at `c`. -/
theorem traj_limit {q : ℂ → ℂ} {σ : ℝ → ℂ} {c : ℝ} (hc : 0 < c)
    (hσ : IsTrajOn q σ (Set.Ico 0 c)) {m : ℝ} (hm : 0 < m)
    (hbound : ∀ t ∈ Set.Ico 0 c, m ≤ ‖q (σ t)‖) :
    ∃ w : ℂ, Filter.Tendsto σ (nhdsWithin c (Set.Ico 0 c)) (nhds w) := by
  haveI hne : (nhdsWithin c (Set.Ico 0 c)).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [closure_Ico hc.ne]
    exact ⟨hc.le, le_refl c⟩
  have hcauchy : Cauchy (Filter.map σ (nhdsWithin c (Set.Ico 0 c))) := by
    refine Metric.cauchy_iff.mpr ⟨Filter.map_neBot, ?_⟩
    intro ε hε
    set M : ℝ := Real.sqrt m⁻¹ with hMdef
    have hM0 : 0 ≤ M := Real.sqrt_nonneg _
    set δ : ℝ := min (ε / (2 * (M + 1))) (c / 2) with hδdef
    have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
    have hδc : c - δ ≥ c / 2 := by
      have := min_le_right (ε / (2 * (M + 1))) (c / 2)
      simp only [← hδdef] at this
      linarith
    refine ⟨σ '' (Set.Ico (c - δ) c ∩ Set.Ico 0 c), ?_, ?_⟩
    · refine Filter.image_mem_map (mem_nhdsWithin.mpr ⟨Set.Ioo (c - δ) (c + 1),
        isOpen_Ioo, ⟨by linarith, by linarith⟩, ?_⟩)
      rintro x ⟨hx1, hx2⟩
      exact ⟨⟨hx1.1.le, hx2.2⟩, hx2⟩
    · rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
      have hgap : ∀ v w : ℝ, v ∈ Set.Ico (c - δ) c ∩ Set.Ico 0 c →
          w ∈ Set.Ico (c - δ) c ∩ Set.Ico 0 c → v ≤ w → dist (σ w) (σ v) < ε := by
        intro v w hv hw hvw
        have hv0 : 0 < v := lt_of_lt_of_le (by linarith) hv.1.1
        rw [dist_eq_norm]
        calc ‖σ w - σ v‖ ≤ M * (w - v) :=
              traj_dist_le hσ hm hbound hv0 hvw hw.1.2
          _ ≤ M * δ := by
              have h1 : w - v ≤ δ := by
                have := hv.1.1
                have := hw.1.2
                linarith
              exact mul_le_mul_of_nonneg_left h1 hM0
          _ ≤ M * (ε / (2 * (M + 1))) :=
              mul_le_mul_of_nonneg_left (min_le_left _ _) hM0
          _ < ε := by
              rw [div_eq_mul_inv]
              have hM1 : 0 < M + 1 := by linarith
              have h2 : M * (ε * (2 * (M + 1))⁻¹) = ε * (M / (2 * (M + 1))) := by
                field_simp
              rw [h2]
              have h3 : M / (2 * (M + 1)) < 1 := by
                rw [div_lt_one (by positivity)]
                linarith
              calc ε * (M / (2 * (M + 1))) < ε * 1 :=
                    mul_lt_mul_of_pos_left h3 hε
                _ = ε := mul_one ε
      rcases le_total a b with hab | hab
      · rw [dist_comm]
        exact hgap a b ha hb hab
      · exact hgap b a hb ha hab
  obtain ⟨w, hw⟩ := CompleteSpace.complete hcauchy
  exact ⟨w, hw⟩

/-- Local step for the ambient development: at each tracked time the ambient chart
develops the trajectory affinely with a local sign. -/
theorem traj_ambient_local {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    {σ : ℝ → ℂ} {I : Set ℝ} (hσ : IsTrajOn q σ I)
    {a b : ℝ} (hI : Set.Icc a b ⊆ I) {t : ℝ} (ht : t ∈ Set.Icc a b)
    (htS : σ t ∈ S) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ᶠ u in nhdsWithin t (Set.Icc a b),
        Φ (σ u) = Φ (σ t) + ε * ((u - t : ℝ) : ℂ) := by
  obtain ⟨U, hUo, hpU, -, -, Φt, hΦtd, hΦtinj, hΦtsq, hev⟩ := hσ.chart t (hI ht)
  set p : ℂ := σ t with hpdef
  set Ω : Set ℂ := connectedComponentIn (U ∩ S) p with hΩdef
  have hΩo : IsOpen Ω := (hUo.inter hS).connectedComponentIn
  have hΩconn : IsPreconnected Ω := isPreconnected_connectedComponentIn
  have hpΩ : p ∈ Ω := mem_connectedComponentIn ⟨hpU, htS⟩
  have hΩsub : Ω ⊆ U ∩ S := connectedComponentIn_subset _ _
  have hsq' : ∀ z ∈ Ω, deriv Φ z ^ 2 = deriv Φt z ^ 2 := fun z hz => by
    rw [hΦsq z (hΩsub hz).2, hΦtsq z (hΩsub hz).1]
  have hmono : nhdsWithin t (Set.Icc a b) ≤ nhdsWithin t I := nhdsWithin_mono t hI
  have hσΩ' : ∀ᶠ u in nhdsWithin t I, σ u ∈ Ω :=
    (hσ.cont t (hI ht)) (hΩo.mem_nhds hpΩ)
  have hσΩ : ∀ᶠ u in nhdsWithin t (Set.Icc a b), σ u ∈ Ω := hσΩ'.filter_mono hmono
  have hev' := hev.filter_mono hmono
  rcases open_branch_classification hΩo hΩconn hpΩ
      (hΦtd.mono (hΩsub.trans Set.inter_subset_left))
      (hΦd.mono (hΩsub.trans Set.inter_subset_right)) hsq' with hplus | hminus
  · refine ⟨1, Or.inl rfl, ?_⟩
    filter_upwards [hev', hσΩ] with u hu hΩu
    have h := hplus (σ u) hΩu
    rw [hu.2] at h
    rw [h, hplus p hpΩ]
    push_cast
    ring
  · refine ⟨-1, Or.inr rfl, ?_⟩
    filter_upwards [hev', hσΩ] with u hu hΩu
    have h := hminus (σ u) hΩu
    rw [hu.2] at h
    rw [h, hminus p hpΩ]
    push_cast
    ring

/-- **Coherent affine development in an ambient chart**: while a trajectory stays in the
domain of a natural chart, its development there is globally affine of one slope `±1`. -/
theorem traj_ambient_affine {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    {σ : ℝ → ℂ} {I : Set ℝ} (hσ : IsTrajOn q σ I)
    {a b : ℝ} (hab : a ≤ b) (hI : Set.Icc a b ⊆ I)
    (htrack : ∀ t ∈ Set.Icc a b, σ t ∈ S) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ t ∈ Set.Icc a b, Φ (σ t) = Φ (σ a) + ε * ((t - a : ℝ) : ℂ) := by
  have hamem : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  obtain ⟨ε, hε, heva⟩ := traj_ambient_local hS hΦd hΦsq hσ hI hamem (htrack a hamem)
  refine ⟨ε, hε, ?_⟩
  set A : Set ℝ := {t | t ∈ Set.Icc a b ∧
    ∀ u ∈ Set.Icc a t, Φ (σ u) = Φ (σ a) + ε * ((u - a : ℝ) : ℂ)} with hAdef
  have haA : a ∈ A := by
    refine ⟨hamem, fun u hu => ?_⟩
    have hua : u = a := le_antisymm hu.2 hu.1
    rw [hua]
    push_cast
    ring
  have hbdd : BddAbove A := ⟨b, fun t ht => ht.1.2⟩
  set c : ℝ := sSup A with hcdef
  have hcA : a ≤ c := le_csSup hbdd haA
  have hcb : c ≤ b := csSup_le ⟨a, haA⟩ (fun t ht => ht.1.2)
  have hc : c ∈ Set.Icc a b := ⟨hcA, hcb⟩
  have hup : ∀ u ∈ Set.Ico a c, Φ (σ u) = Φ (σ a) + ε * ((u - a : ℝ) : ℂ) := by
    intro u hu
    obtain ⟨t, htA, hut⟩ := exists_lt_of_lt_csSup ⟨a, haA⟩ hu.2
    exact htA.2 u ⟨hu.1, hut.le⟩
  have hsubIco : Set.Ico a c ⊆ Set.Icc a b := fun u hu => ⟨hu.1, le_trans hu.2.le hcb⟩
  have hΦcont : ContinuousWithinAt (fun u => Φ (σ u)) (Set.Icc a b) c := by
    have hΦca : ContinuousAt Φ (σ c) :=
      (hΦd.differentiableAt (hS.mem_nhds (htrack c hc))).continuousAt
    exact hΦca.comp_continuousWithinAt ((hσ.cont c (hI hc)).mono hI)
  have hcc : Φ (σ c) = Φ (σ a) + ε * ((c - a : ℝ) : ℂ) := by
    rcases eq_or_lt_of_le hcA with heq | hac
    · rw [← heq]
      push_cast
      ring
    · haveI hne : (nhdsWithin c (Set.Ico a c)).NeBot := by
        refine mem_closure_iff_nhdsWithin_neBot.mp ?_
        rw [closure_Ico hac.ne]
        exact ⟨hac.le, le_refl c⟩
      have hlim : Filter.Tendsto (fun u => Φ (σ u)) (nhdsWithin c (Set.Ico a c))
          (nhds (Φ (σ c))) := hΦcont.mono_left (nhdsWithin_mono c hsubIco)
      have hlim2 : Filter.Tendsto (fun u : ℝ => Φ (σ a) + ε * ((u - a : ℝ) : ℂ))
          (nhdsWithin c (Set.Ico a c)) (nhds (Φ (σ a) + ε * ((c - a : ℝ) : ℂ))) := by
        refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
        exact (continuous_const.add (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_sub_right a)))).tendsto c
      have heqf : (fun u : ℝ => Φ (σ a) + ε * ((u - a : ℝ) : ℂ))
          =ᶠ[nhdsWithin c (Set.Ico a c)] fun u => Φ (σ u) :=
        eventually_mem_nhdsWithin.mono fun u hu => (hup u hu).symm
      exact tendsto_nhds_unique hlim (hlim2.congr' heqf)
  obtain ⟨εc, hεc, hevc⟩ := traj_ambient_local hS hΦd hΦsq hσ hI hc (htrack c hc)
  rcases eq_or_lt_of_le hcb with heqb | hclt
  · intro t htmem
    rcases eq_or_lt_of_le htmem.2 with htb | htb
    · rw [htb, ← heqb]
      exact hcc
    · exact hup t ⟨htmem.1, by rw [heqb]; exact htb⟩
  · exfalso
    have hab' : a < b := lt_of_le_of_lt hcA hclt
    have hεceq : εc = ε := by
      rcases eq_or_lt_of_le hcA with heq | hac
      · have hevc' : ∀ᶠ u in nhdsWithin a (Set.Icc a b),
            Φ (σ u) = Φ (σ a) + εc * ((u - a : ℝ) : ℂ) := by
          rw [← heq] at hevc
          exact hevc
        haveI hne : (nhdsWithin a (Set.Ioc a b)).NeBot := by
          refine mem_closure_iff_nhdsWithin_neBot.mp ?_
          rw [closure_Ioc hab'.ne]
          exact ⟨le_refl a, hab'.le⟩
        have hmono2 : nhdsWithin a (Set.Ioc a b) ≤ nhdsWithin a (Set.Icc a b) :=
          nhdsWithin_mono a (fun u hu => ⟨hu.1.le, hu.2⟩)
        obtain ⟨u, huIoc, h1, h2⟩ := (eventually_mem_nhdsWithin.and
          ((heva.filter_mono hmono2).and (hevc'.filter_mono hmono2))).exists
        have hune : ((u - a : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt huIoc.1))
        have := h1.symm.trans h2
        have hmul : ε * ((u - a : ℝ) : ℂ) = εc * ((u - a : ℝ) : ℂ) := by
          linear_combination this
        have : (ε : ℂ) = (εc : ℂ) := mul_right_cancel₀ hune hmul
        exact_mod_cast this.symm
      · haveI hne : (nhdsWithin c (Set.Ico a c)).NeBot := by
          refine mem_closure_iff_nhdsWithin_neBot.mp ?_
          rw [closure_Ico hac.ne]
          exact ⟨hac.le, le_refl c⟩
        have hmono2 : nhdsWithin c (Set.Ico a c) ≤ nhdsWithin c (Set.Icc a b) :=
          nhdsWithin_mono c hsubIco
        obtain ⟨u, huIco, h1⟩ := (eventually_mem_nhdsWithin.and
          (hevc.filter_mono hmono2)).exists
        have hune : ((u - c : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_lt huIco.2))
        have h2 := hup u huIco
        have hmul : εc * ((u - c : ℝ) : ℂ) = ε * ((u - c : ℝ) : ℂ) := by
          have h3 := hcc
          have h4 := h1
          rw [h2] at h4
          push_cast at h3 h4 ⊢
          linear_combination -h4 - h3
        have : (εc : ℂ) = (ε : ℂ) := mul_right_cancel₀ hune hmul
        exact_mod_cast this
    rw [hεceq] at hevc
    obtain ⟨V, hVo, hcV, hVsub⟩ := mem_nhdsWithin.mp hevc
    obtain ⟨δ', hδ', hballV⟩ := Metric.isOpen_iff.mp hVo c hcV
    set t' : ℝ := min b (c + δ' / 2) with ht'def
    have ht'c : c < t' := lt_min hclt (by linarith)
    have ht'A : t' ∈ A := by
      refine ⟨⟨le_trans hcA ht'c.le, min_le_left _ _⟩, ?_⟩
      intro u hu
      rcases le_or_gt u c with huc | huc
      · rcases eq_or_lt_of_le huc with hueq | hult
        · rw [hueq]
          exact hcc
        · exact hup u ⟨hu.1, hult⟩
      · have huV : Φ (σ u) = Φ (σ c) + ε * ((u - c : ℝ) : ℂ) := by
          refine hVsub ⟨hballV ?_, ⟨hu.1, le_trans hu.2 (min_le_left _ _)⟩⟩
          rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
          have := le_trans hu.2 (min_le_right _ _)
          linarith
        rw [huV, hcc]
        push_cast
        ring
    linarith [le_csSup hbdd ht'A]

/-- **Tail development at the limit time**: a trajectory converging at `c` inside one
natural chart develops affinely with a single sign up to the limit value. -/
theorem traj_tail_affine {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    {σ : ℝ → ℂ} {c : ℝ} (hc : 0 < c) (hσ : IsTrajOn q σ (Set.Ico 0 c))
    {w : ℂ} (hwS : w ∈ S)
    (hlim : Filter.Tendsto σ (nhdsWithin c (Set.Ico 0 c)) (nhds w))
    (htail : ∀ᶠ u in nhdsWithin c (Set.Ico 0 c), σ u ∈ S) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ᶠ u in nhdsWithin c (Set.Ico 0 c),
        Φ (σ u) = Φ w + ε * ((u - c : ℝ) : ℂ) := by
  obtain ⟨V, hVo, hcV, hVsub⟩ := mem_nhdsWithin.mp htail
  obtain ⟨η₀, hη₀, hball⟩ := Metric.isOpen_iff.mp hVo c hcV
  set η : ℝ := min η₀ c with hηdef
  have hη : 0 < η := lt_min hη₀ hc
  have hηc : η ≤ c := min_le_right _ _
  set a₀ : ℝ := c - η / 2 with ha₀def
  set m₀ : ℝ := c - η / 4 with hm₀def
  have ha₀0 : 0 < a₀ := by
    have : η / 2 < c := by linarith
    linarith
  have ha₀m : a₀ < m₀ := by linarith
  have hm₀c : m₀ < c := by linarith
  have htrackIco : ∀ u ∈ Set.Ico a₀ c, σ u ∈ S := by
    intro u hu
    refine hVsub ⟨hball ?_, ⟨by linarith [hu.1], hu.2⟩⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith [hu.2]), neg_sub]
    have := hu.1
    have := min_le_left η₀ c
    linarith
  have hsubI : ∀ b₀ : ℝ, b₀ < c → Set.Icc a₀ b₀ ⊆ Set.Ico 0 c := fun b₀ hb₀ u hu =>
    ⟨by linarith [hu.1], lt_of_le_of_lt hu.2 hb₀⟩
  obtain ⟨ε, hε, haff⟩ := traj_ambient_affine hS hΦd hΦsq hσ ha₀m.le
    (hsubI m₀ hm₀c) (fun t ht => htrackIco t ⟨ht.1, lt_of_le_of_lt ht.2 hm₀c⟩)
  have hall : ∀ u ∈ Set.Ico a₀ c, Φ (σ u) = Φ (σ a₀) + ε * ((u - a₀ : ℝ) : ℂ) := by
    intro u hu
    rcases le_total u m₀ with hum | hum
    · exact haff u ⟨hu.1, hum⟩
    · obtain ⟨ε', hε', haff'⟩ := traj_ambient_affine hS hΦd hΦsq hσ
        (le_trans ha₀m.le hum) (hsubI u hu.2)
        (fun t ht => htrackIco t ⟨ht.1, lt_of_le_of_lt ht.2 hu.2⟩)
      have hpin : ε' = ε := by
        have h1 := haff' m₀ ⟨ha₀m.le, hum⟩
        have h2 := haff m₀ (Set.right_mem_Icc.mpr ha₀m.le)
        have hne : ((m₀ - a₀ : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr ha₀m.ne')
        have hmul : (ε' : ℂ) * ((m₀ - a₀ : ℝ) : ℂ) = ε * ((m₀ - a₀ : ℝ) : ℂ) := by
          rw [h2] at h1
          linear_combination -h1
        exact_mod_cast mul_right_cancel₀ hne hmul
      rw [← hpin]
      exact haff' u (Set.right_mem_Icc.mpr (le_trans ha₀m.le hum))
  haveI hne : (nhdsWithin c (Set.Ico 0 c)).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [closure_Ico hc.ne]
    exact ⟨hc.le, le_refl c⟩
  have hevIco : ∀ᶠ u in nhdsWithin c (Set.Ico 0 c), u ∈ Set.Ico a₀ c := by
    refine mem_nhdsWithin.mpr ⟨Set.Ioo a₀ (c + 1), isOpen_Ioo,
      ⟨by linarith, by linarith⟩, ?_⟩
    rintro u ⟨hu1, hu2⟩
    exact ⟨hu1.1.le, hu2.2⟩
  have hΦw : Φ w = Φ (σ a₀) + ε * ((c - a₀ : ℝ) : ℂ) := by
    have hΦca : ContinuousAt Φ w :=
      (hΦd.differentiableAt (hS.mem_nhds hwS)).continuousAt
    have h1 : Filter.Tendsto (fun u => Φ (σ u)) (nhdsWithin c (Set.Ico 0 c))
        (nhds (Φ w)) := hΦca.tendsto.comp hlim
    have h2 : Filter.Tendsto (fun u : ℝ => Φ (σ a₀) + ε * ((u - a₀ : ℝ) : ℂ))
        (nhdsWithin c (Set.Ico 0 c))
        (nhds (Φ (σ a₀) + ε * ((c - a₀ : ℝ) : ℂ))) := by
      refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
      exact (continuous_const.add (continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_sub_right a₀)))).tendsto c
    have heqf : (fun u : ℝ => Φ (σ a₀) + ε * ((u - a₀ : ℝ) : ℂ))
        =ᶠ[nhdsWithin c (Set.Ico 0 c)] fun u => Φ (σ u) :=
      hevIco.mono fun u hu => (hall u hu).symm
    exact tendsto_nhds_unique h1 (h2.congr' heqf)
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hevIco] with u hu
  rw [hall u hu, hΦw]
  push_cast
  ring

/-- Below the limit time the closed and half-open time intervals induce the same
within-filter. -/
theorem nhdsWithin_Ico {c t : ℝ} (ht : t < c) :
    nhdsWithin t (Set.Icc 0 c) = nhdsWithin t (Set.Ico 0 c) := by
  have hio : Set.Iio c ∈ nhds t := Iio_mem_nhds ht
  rw [nhdsWithin_restrict' _ hio, nhdsWithin_restrict' (Set.Ico 0 c) hio]
  congr 1
  ext u
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ico, Set.mem_Iio]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h3⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h2.le⟩, h3⟩

/-- **Limit closure**: a trajectory on `[0, c)` converging at `c` to a regular point of
the upper half plane closes to a trajectory on `[0, c]`. -/
theorem traj_close {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    {σ : ℝ → ℂ} {c : ℝ} (hc : 0 < c) (hσ : IsTrajOn q σ (Set.Ico 0 c))
    {w : ℂ} (hw : 0 < w.im) (hqw : q w ≠ 0)
    (hlim : Filter.Tendsto σ (nhdsWithin c (Set.Ico 0 c)) (nhds w)) :
    ∃ σ' : ℝ → ℂ, Set.EqOn σ' σ (Set.Ico 0 c) ∧ σ' c = w ∧
      IsTrajOn q σ' (Set.Icc 0 c) := by
  have hH : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨r, hr, hsubH, Φ, hΦd0, hΦinj0, hΦsq0⟩ :=
    exists_natural_chart (q := fun z => -q z) hH hq.neg hw (neg_ne_zero.mpr hqw)
  have hqc : ContinuousAt q w := hq.continuousOn.continuousAt (hH.mem_nhds hw)
  obtain ⟨r₁, hr₁, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hqc (isOpen_ne.mem_nhds hqw) : q ⁻¹' {x | x ≠ 0} ∈ nhds w)
      (Metric.ball_mem_nhds w hr))
  set S : Set ℂ := Metric.ball w r₁ with hSdef
  have hSr : S ⊆ Metric.ball w r := fun x hx => (hball hx).2
  have hSne : ∀ x ∈ S, q x ≠ 0 := fun x hx => (hball hx).1
  have hSo : IsOpen S := Metric.isOpen_ball
  have hSH : S ⊆ {z : ℂ | 0 < z.im} := hSr.trans hsubH
  have hwS : w ∈ S := Metric.mem_ball_self hr₁
  have hΦd : DifferentiableOn ℂ Φ S := hΦd0.mono hSr
  have hΦinj : Set.InjOn Φ S := hΦinj0.mono hSr
  have hΦsq : ∀ x ∈ S, deriv Φ x ^ 2 = -q x := fun x hx => hΦsq0 x (hSr hx)
  have htail : ∀ᶠ u in nhdsWithin c (Set.Ico 0 c), σ u ∈ S := hlim (hSo.mem_nhds hwS)
  obtain ⟨ε, hε, hgerm⟩ := traj_tail_affine hSo hΦd hΦsq hc hσ hwS hlim htail
  have hε2 : ((ε : ℝ) : ℂ) ^ 2 = 1 := by
    rcases hε with h | h <;> rw [h] <;> norm_num
  have hεne : ((ε : ℝ) : ℂ) ≠ 0 := by
    rcases hε with h | h <;> rw [h] <;> norm_num
  set σ' : ℝ → ℂ := fun t => if t < c then σ t else w with hσ'def
  have hEq : Set.EqOn σ' σ (Set.Ico 0 c) := fun u hu => if_pos hu.2
  have hσ'c : σ' c = w := if_neg (lt_irrefl c)
  have hsplit : ∀ t : ℝ, nhdsWithin t (Set.Icc 0 c)
      = nhdsWithin t (Set.Ico 0 c) ⊔ nhdsWithin t {c} := by
    intro t
    rw [← nhdsWithin_union, Set.Ico_union_right hc.le]
  refine ⟨σ', hEq, hσ'c, ?_, ?_⟩
  · intro t ht
    rcases lt_or_eq_of_le ht.2 with htc | htc
    · change Filter.Tendsto σ' (nhdsWithin t (Set.Icc 0 c)) (nhds (σ' t))
      rw [nhdsWithin_Ico htc, hEq ⟨ht.1, htc⟩]
      exact Filter.Tendsto.congr'
        (eventually_mem_nhdsWithin.mono fun u hu => (hEq hu).symm)
        (hσ.cont t ⟨ht.1, htc⟩)
    · change Filter.Tendsto σ' (nhdsWithin t (Set.Icc 0 c)) (nhds (σ' t))
      rw [htc, hsplit c, Filter.tendsto_sup, hσ'c]
      constructor
      · exact Filter.Tendsto.congr'
          (eventually_mem_nhdsWithin.mono fun u hu => (hEq hu).symm) hlim
      · rw [nhdsWithin_singleton]
        have : Filter.Tendsto σ' (pure c) (nhds (σ' c)) := tendsto_pure_nhds σ' c
        rwa [hσ'c] at this
  · intro t ht
    rcases lt_or_eq_of_le ht.2 with htc | htc
    · obtain ⟨Ut, hUto, hptU, hUtH, hUtne, Φt, hΦtd, hΦtinj, hΦtsq, hevt⟩ :=
        hσ.chart t ⟨ht.1, htc⟩
      refine ⟨Ut, hUto, by rw [hEq ⟨ht.1, htc⟩]; exact hptU, hUtH, hUtne,
        Φt, hΦtd, hΦtinj, hΦtsq, ?_⟩
      rw [nhdsWithin_Ico htc]
      filter_upwards [hevt, eventually_mem_nhdsWithin] with u hu huIco
      rw [hEq huIco, hEq ⟨ht.1, htc⟩]
      exact hu
    · subst htc
      refine ⟨S, hSo, by rw [hσ'c]; exact hwS, hSH, hSne,
        fun z => ((ε : ℝ) : ℂ) * Φ z,
        fun x hx => ((hΦd x hx).const_mul _), ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        exact hΦinj hx hy (mul_left_cancel₀ hεne hxy)
      · intro x hx
        have hdiff : DifferentiableAt ℂ Φ x := hΦd.differentiableAt (hSo.mem_nhds hx)
        have hd : deriv (fun z => ((ε : ℝ) : ℂ) * Φ z) x = ((ε : ℝ) : ℂ) * deriv Φ x :=
          deriv_const_mul _ hdiff
        rw [hd, mul_pow, hε2, one_mul]
        exact hΦsq x hx
      · rw [hsplit t, Filter.eventually_sup]
        constructor
        · filter_upwards [hgerm, htail, eventually_mem_nhdsWithin] with u hg hSu hu
          rw [hEq hu, hσ'c]
          refine ⟨hSu, ?_⟩
          rw [hg]
          linear_combination ((u - t : ℝ) : ℂ) * hε2
        · rw [nhdsWithin_singleton]
          rw [Filter.eventually_pure]
          rw [hσ'c]
          refine ⟨hwS, ?_⟩
          rw [sub_self]
          push_cast
          ring

end RiemannDynamics

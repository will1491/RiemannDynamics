/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.ModuliAction.Interpolate.Chains

/-!
# Interpolation, III: analytic estimates for the development

Bump atoms at hyperbolic centers, local finiteness of the orbit sum, Wirtinger-derivative
bounds, the core Möbius derivative packs, Sobolev membership, openness and ball
surjectivity, composition of hyperbolic balls, matrix denominators, injectivity from
derivative bounds, differentiability of Möbius maps, the corrected vector field,
isometric transport, the weight system, and conjugated regularity of the developed map.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-! ## The development of the corrected tile maps: analytic estimates -/

/-- The bump atom at a hyperbolic center: value, bridge, and differentiability. -/
private lemma zz_atom_bridge (gb : ℝ → ℝ) (w : UpperHalfPlane) (τ : UpperHalfPlane) :
    gb (1 + Complex.normSq ((τ : ℂ) - (w : ℂ)) / (2 * (τ : ℂ).im * (w : ℂ).im))
      = gb (Real.cosh (dist τ w)) := by
  rw [zz_cd_bridge]

/-- Differentiability of the bump atom on the upper half plane. -/
private lemma zz_atom_contDiffAt (gb : ℝ → ℝ) (hgb : ContDiff ℝ 1 gb)
    (w : UpperHalfPlane) (z₀ : ℂ) (hz₀ : 0 < z₀.im) :
    ContDiffAt ℝ 1 (fun z : ℂ =>
      gb (1 + Complex.normSq (z - (w : ℂ)) / (2 * z.im * (w : ℂ).im))) z₀ := by
  have hwim : 0 < (w : ℂ).im := by
    rw [UpperHalfPlane.coe_im]
    exact w.im_pos
  exact hgb.contDiffAt.comp z₀ (zz_cd_contDiffAt (w : ℂ) hwim z₀ hz₀)

/-- Vanishing of the bump atom away from its center, for a profile vanishing above
`cosh (R + 1)`. -/
private lemma zz_atom_vanish (gb : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hgb0 : ∀ t : ℝ, Real.cosh (R + 1) ≤ t → gb t = 0)
    (w τ : UpperHalfPlane) (hfar : R + 1 ≤ dist τ w) :
    gb (1 + Complex.normSq ((τ : ℂ) - (w : ℂ)) / (2 * (τ : ℂ).im * (w : ℂ).im)) = 0 := by
  rw [zz_atom_bridge gb w τ]
  refine hgb0 _ ?_
  have h1 : |R + 1| ≤ |dist τ w| := by
    rw [abs_of_nonneg dist_nonneg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ R + 1)]
    exact hfar
  exact Real.cosh_le_cosh.mpr h1

/-- **Local finiteness of the bump family**: around each point of the upper half plane there
is a Euclidean ball on which all but finitely many atoms vanish identically. -/
private lemma zz_locfin {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ) (τ₀ : UpperHalfPlane) (R : ℝ)
    (z₀ : ℂ) (hz₀ : 0 < z₀.im) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : Set ↥Γ, F.Finite ∧
      (∀ z ∈ Metric.ball z₀ r, 0 < z.im) ∧
      ∀ z ∈ Metric.ball z₀ r, ∀ hz : 0 < z.im, ∀ γ : ↥Γ, γ ∉ F →
        R + 1 ≤ dist (⟨z, hz⟩ : UpperHalfPlane) (γ • τ₀) := by
  classical
  -- the hyperbolic unit ball about `z₀` is an open Euclidean ball containing `z₀`
  obtain ⟨τz, hτz⟩ : ∃ τz : UpperHalfPlane, (τz : ℂ) = z₀ := ⟨⟨z₀, hz₀⟩, rfl⟩
  have hz₀mem : z₀ ∈ Metric.ball ((((τz : ℂ).re : ℝ) : ℂ)
      + ((τz.im * Real.cosh 1 : ℝ) : ℂ) * Complex.I) (τz.im * Real.sinh 1) := by
    rw [zz_ball τz 1 one_pos z₀]
    refine ⟨hz₀, ?_⟩
    have : (⟨z₀, hz₀⟩ : UpperHalfPlane) = τz := by
      ext
      rw [hτz]
    rw [this]
    rw [dist_self]
    norm_num
  obtain ⟨r, hrpos, hrsub⟩ : ∃ r > 0, Metric.ball z₀ r ⊆ Metric.ball ((((τz : ℂ).re : ℝ) : ℂ)
      + ((τz.im * Real.cosh 1 : ℝ) : ℂ) * Complex.I) (τz.im * Real.sinh 1) :=
    Metric.mem_nhds_iff.mp (Metric.isOpen_ball.mem_nhds hz₀mem)
  refine ⟨r, hrpos, {γ : ↥Γ | dist τz (γ • τ₀) ≤ R + 2}, zz_fin hΓ τz τ₀ (R + 2), ?_, ?_⟩
  · intro z hz
    have hzE := hrsub hz
    rw [zz_ball τz 1 one_pos z] at hzE
    obtain ⟨hzim, _⟩ := hzE
    exact hzim
  · intro z hz hzim γ hγF
    by_contra hcon
    push Not at hcon
    have hzE := hrsub hz
    rw [zz_ball τz 1 one_pos z] at hzE
    obtain ⟨hzim', hzd⟩ := hzE
    apply hγF
    have htri : dist τz (γ • τ₀) ≤ dist τz (⟨z, hzim'⟩ : UpperHalfPlane)
        + dist (⟨z, hzim'⟩ : UpperHalfPlane) (γ • τ₀) := dist_triangle _ _ _
    have heq : dist (⟨z, hzim'⟩ : UpperHalfPlane) (γ • τ₀)
        = dist (⟨z, hzim⟩ : UpperHalfPlane) (γ • τ₀) := rfl
    have hd1 : dist τz (⟨z, hzim'⟩ : UpperHalfPlane) < 1 := by
      rw [dist_comm]
      exact hzd
    simp only [Set.mem_ofPred_eq]
    rw [heq] at htri
    linarith

/-- Wirtinger bounds from a split of the derivative into a near-identity complex-linear part
and small error values in the two coordinate directions. -/
private lemma zz_wirt (F : ℂ → ℂ) (z : ℂ) (Sw e1 eI : ℂ) (Cb : ℝ)
    (hα : fderiv ℝ F z 1 = Sw + e1) (hβ : fderiv ℝ F z Complex.I = Sw * Complex.I + eI)
    (hSw1 : ‖Sw - 1‖ ≤ Cb) (he1 : ‖e1‖ ≤ Cb) (heI : ‖eI‖ ≤ Cb) (hCb : 0 ≤ Cb)
    (hsm : Cb ≤ 1 / 6) :
    ‖dzbar F z‖ ≤ Cb ∧ (1 : ℝ) / 2 ≤ ‖dz F z‖ ∧ 0 < (fderiv ℝ F z).det := by
  have hdzbar_eq : dzbar F z = (1 / 2 : ℂ) * (e1 + Complex.I * eI) := by
    rw [dzbar, hα, hβ]
    linear_combination (Sw / 2) * Complex.I_mul_I
  have hdz_eq : dz F z = Sw + (1 / 2 : ℂ) * (e1 - Complex.I * eI) := by
    rw [dz, hα, hβ]
    linear_combination (-(Sw / 2)) * Complex.I_mul_I
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
    rw [norm_div, norm_one, Complex.norm_ofNat]
  have hIeI : ‖Complex.I * eI‖ = ‖eI‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  have hbar : ‖dzbar F z‖ ≤ Cb := by
    rw [hdzbar_eq, norm_mul, hhalf]
    have h1 := norm_add_le e1 (Complex.I * eI)
    rw [hIeI] at h1
    have h2 : ‖e1 + Complex.I * eI‖ ≤ 2 * Cb := by linarith only [h1, he1, heI]
    linarith only [h2, norm_nonneg (e1 + Complex.I * eI), hCb]
  have hSlb : 1 - Cb ≤ ‖Sw‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) Sw
    rw [norm_one, norm_sub_rev] at h1
    linarith only [h1, hSw1]
  have hzlb : (1 : ℝ) / 2 ≤ ‖dz F z‖ := by
    rw [hdz_eq]
    have h1 := norm_sub_norm_le Sw (-((1 / 2 : ℂ) * (e1 - Complex.I * eI)))
    rw [sub_neg_eq_add, norm_neg, norm_mul, hhalf] at h1
    have h2 := norm_sub_le e1 (Complex.I * eI)
    rw [hIeI] at h2
    have h3 : ‖e1 - Complex.I * eI‖ ≤ 2 * Cb := by linarith only [h2, he1, heI]
    have h4 : 1 / 2 * ‖e1 - Complex.I * eI‖ ≤ Cb := by
      linarith only [h3, norm_nonneg (e1 - Complex.I * eI), hCb]
    have h5 : Cb + Cb ≤ 1 / 3 := by linarith only [hsm]
    linarith only [h1, h4, hSlb, h5]
  refine ⟨hbar, hzlb, ?_⟩
  rw [det_fderiv_eq_wirtinger]
  have h6 : ‖dzbar F z‖ ^ 2 ≤ Cb ^ 2 := by
    have := mul_le_mul hbar hbar (norm_nonneg _) hCb
    nlinarith [this]
  have h7 : (1 : ℝ) / 4 ≤ ‖dz F z‖ ^ 2 := by
    have := mul_le_mul hzlb hzlb (by norm_num) (le_trans (by norm_num) hzlb)
    nlinarith [this]
  have h8 : Cb ^ 2 ≤ 1 / 36 := by nlinarith [hsm, hCb]
  nlinarith [h6, h7, h8]

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The derivative chain of the coefficient Möbius quotient elaborates one large product and
-- inverse rule; the default heartbeat budget does not cover it.
/-- Fréchet differentiability and the derivative formula for a Möbius quotient with `C¹`
real coefficient fields, off the zero set of the denominator. -/
private lemma zz_moeb_core
    (b00 b01 b10 b11 : ℂ → ℝ) (D00 D01 D10 D11 : ℂ →L[ℝ] ℝ) (z : ℂ)
    (hD00 : HasFDerivAt b00 D00 z) (hD01 : HasFDerivAt b01 D01 z)
    (hD10 : HasFDerivAt b10 D10 z) (hD11 : HasFDerivAt b11 D11 z)
    (hdenne' : ((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ) ≠ 0) :
    DifferentiableAt ℝ
        (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
          / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z ∧
      ∀ v : ℂ, fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
          / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z v
        = ((b00 z * b11 z - b01 z * b10 z : ℝ) : ℂ)
            / (((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ)) ^ 2 * v
          + ((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ))
                * (((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ))
              - (((b00 z : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ))
                * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ)))
            / (((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ)) ^ 2 := by
  have hCSRC : ContinuousSMul ℝ ℂ := ⟨by
    have h : (fun p : ℝ × ℂ => p.1 • p.2) = fun p : ℝ × ℂ => (p.1 : ℂ) * p.2 := by
      funext p
      exact Complex.real_smul
    rw [h]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd⟩
  -- the derivative chain, following the collar-estimate pattern
  have h00 : HasFDerivAt (fun w : ℂ => ((b00 w : ℝ) : ℂ)) (Complex.ofRealCLM.comp D00) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hD00
  have h01 : HasFDerivAt (fun w : ℂ => ((b01 w : ℝ) : ℂ)) (Complex.ofRealCLM.comp D01) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hD01
  have h10 : HasFDerivAt (fun w : ℂ => ((b10 w : ℝ) : ℂ)) (Complex.ofRealCLM.comp D10) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hD10
  have h11 : HasFDerivAt (fun w : ℂ => ((b11 w : ℝ) : ℂ)) (Complex.ofRealCLM.comp D11) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hD11
  have hchain := ((h00.mul (hasFDerivAt_id z)).add h01).mul
    ((hasDerivAt_inv hdenne').comp_hasFDerivAt z ((h10.mul (hasFDerivAt_id z)).add h11))
  have hfeq : (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
      / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ)))
      = fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
        * ((((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))⁻¹) := by
    funext w
    rw [div_eq_mul_inv]
  have hφex : HasFDerivAt (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
        * ((((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))⁻¹))
      ((((b00 z : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ)) •
          ((-((((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ)) ^ 2)⁻¹) •
            (((b10 z : ℝ) : ℂ) • ContinuousLinearMap.id ℝ ℂ
              + z • Complex.ofRealCLM.comp D10 + Complex.ofRealCLM.comp D11))
        + (((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ))⁻¹ •
            (((b00 z : ℝ) : ℂ) • ContinuousLinearMap.id ℝ ℂ
              + z • Complex.ofRealCLM.comp D00 + Complex.ofRealCLM.comp D01)) z := hchain
  have hdiff : DifferentiableAt ℝ
      (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
        / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z := by
    rw [hfeq]
    exact hφex.differentiableAt
  have hfd0 : fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
      / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z
      = fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
        * ((((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))⁻¹)) z := by
    rw [hfeq]
  have hfd1 := hφex.differentiableAt.hasFDerivAt.unique hφex
  -- the linear-map value of the derivative
  have hLv : ∀ v : ℂ, fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
      / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z v
      = ((b00 z * b11 z - b01 z * b10 z : ℝ) : ℂ)
          / (((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ)) ^ 2 * v
        + ((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ))
              * (((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ))
            - (((b00 z : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ))
              * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ)))
          / (((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ)) ^ 2 := by
    intro v
    rw [hfd0, hfd1]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      Complex.ofRealCLM_apply, smul_eq_mul]
    field_simp
    push_cast
    ring
  exact ⟨hdiff, hLv⟩

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The per-point value and operator-norm package elaborates one large derivative chain;
-- the default heartbeat budget does not cover it.
/-- **Value and derivative closeness to the identity for a Möbius map with near-identity
`C¹` coefficient field**, with explicit polynomial constants. -/
lemma zz_moeb_packA
    (b00 b01 b10 b11 : ℂ → ℝ) (D00 D01 D10 D11 : ℂ →L[ℝ] ℝ) (z : ℂ)
    (Rz ε : ℝ) (hRz : 1 ≤ Rz) (hzR : ‖z‖ ≤ Rz)
    (hD00 : HasFDerivAt b00 D00 z) (hD01 : HasFDerivAt b01 D01 z)
    (hD10 : HasFDerivAt b10 D10 z) (hD11 : HasFDerivAt b11 D11 z)
    (hε : 0 ≤ ε)
    (hb00 : |b00 z - 1| ≤ ε) (hb01 : |b01 z| ≤ ε)
    (hb10 : |b10 z| ≤ ε) (hb11 : |b11 z - 1| ≤ ε)
    (hn00 : ‖D00‖ ≤ ε) (hn01 : ‖D01‖ ≤ ε) (hn10 : ‖D10‖ ≤ ε) (hn11 : ‖D11‖ ≤ ε)
    (hsmall : ε * Rz ^ 2 ≤ 1 / 1000) :
    DifferentiableAt ℝ
        (fun wq => (((b00 wq : ℝ) : ℂ) * wq + ((b01 wq : ℝ) : ℂ))
          / (((b10 wq : ℝ) : ℂ) * wq + ((b11 wq : ℝ) : ℂ))) z ∧
      ‖(((b00 z : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ))
          / (((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ)) - z‖ ≤ 8 * Rz ^ 2 * ε ∧
      ‖fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
          / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z
        - ContinuousLinearMap.id ℝ ℂ‖ ≤ 64 * Rz ^ 2 * ε := by
  have hCSRC : ContinuousSMul ℝ ℂ := ⟨by
    have h : (fun p : ℝ × ℂ => p.1 • p.2) = fun p : ℝ × ℂ => (p.1 : ℂ) * p.2 := by
      funext p
      exact Complex.real_smul
    rw [h]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd⟩
  have hεRz : ε * Rz ≤ 1 / 128 := by
    nlinarith [hsmall, mul_nonneg hε (mul_nonneg
      (by linarith : (0 : ℝ) ≤ Rz - 1) (by linarith : (0 : ℝ) ≤ Rz))]
  have hε1 : ε ≤ 1 / 128 := by
    nlinarith [hsmall, mul_nonneg hε (by nlinarith : (0 : ℝ) ≤ Rz ^ 2 - 1)]
  have hRz0 : (0 : ℝ) < Rz := by linarith
  -- basic denominator and numerator bounds
  obtain ⟨den, hden_def⟩ : ∃ x : ℂ, ((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ) = x := ⟨_, rfl⟩
  obtain ⟨num, hnum_def⟩ : ∃ x : ℂ, ((b00 z : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ) = x := ⟨_, rfl⟩
  have hden1 : ‖den - 1‖ ≤ 2 * ε * Rz := by
    rw [← hden_def]
    have h1 : ((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ) - 1
        = ((b10 z : ℝ) : ℂ) * z + ((b11 z - 1 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1]
    calc ‖((b10 z : ℝ) : ℂ) * z + ((b11 z - 1 : ℝ) : ℂ)‖
        ≤ ‖((b10 z : ℝ) : ℂ) * z‖ + ‖((b11 z - 1 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |b10 z| * ‖z‖ + |b11 z - 1| := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
      _ ≤ ε * Rz + ε * 1 := by
          refine add_le_add (mul_le_mul hb10 hzR (norm_nonneg z) hε) ?_
          calc |b11 z - 1| ≤ ε := hb11
            _ = ε * 1 := (mul_one ε).symm
      _ ≤ 2 * ε * Rz := by nlinarith [mul_le_mul_of_nonneg_left hRz hε]
  have hdenlb : (1 : ℝ) / 2 ≤ ‖den‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) den
    rw [norm_one, norm_sub_rev] at h1
    nlinarith [hden1, hεRz]
  have hdenub : ‖den‖ ≤ 3 / 2 := by
    have h1 := norm_add_le (den - 1) 1
    rw [sub_add_cancel, norm_one] at h1
    nlinarith [hden1, hεRz]
  have hdenne : den ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdenlb
    linarith
  have hdenne' : ((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ) ≠ 0 := by
    rw [hden_def]
    exact hdenne
  have hnumz : ‖num - z‖ ≤ 2 * ε * Rz := by
    rw [← hnum_def]
    have h1 : ((b00 z : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ) - z
        = ((b00 z - 1 : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1]
    calc ‖((b00 z - 1 : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ)‖
        ≤ ‖((b00 z - 1 : ℝ) : ℂ) * z‖ + ‖((b01 z : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |b00 z - 1| * ‖z‖ + |b01 z| := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
      _ ≤ ε * Rz + ε * 1 := by
          refine add_le_add (mul_le_mul hb00 hzR (norm_nonneg z) hε) ?_
          calc |b01 z| ≤ ε := hb01
            _ = ε * 1 := (mul_one ε).symm
      _ ≤ 2 * ε * Rz := by nlinarith [mul_le_mul_of_nonneg_left hRz hε]
  have hnumub : ‖num‖ ≤ 2 * Rz := by
    have h1 := norm_add_le (num - z) z
    rw [sub_add_cancel] at h1
    nlinarith [hnumz, hεRz, hzR]
  obtain ⟨hdiff, hLvraw⟩ := zz_moeb_core b00 b01 b10 b11 D00 D01 D10 D11 z
    hD00 hD01 hD10 hD11 hdenne'
  have hLv : ∀ v : ℂ, fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
      / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z v
      = ((b00 z * b11 z - b01 z * b10 z : ℝ) : ℂ) / den ^ 2 * v
        + ((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
            - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))) / den ^ 2 := by
    intro v
    rw [hLvraw v, hden_def, hnum_def]
  clear hLvraw hD00 hD01 hD10 hD11
  -- bounds for the two parts  -- bounds for the two parts
  obtain ⟨Sw, hSw_def⟩ : ∃ x : ℂ, ((b00 z * b11 z - b01 z * b10 z : ℝ) : ℂ) / den ^ 2 = x :=
    ⟨_, rfl⟩
  have hdet1 : |b00 z * b11 z - b01 z * b10 z - 1| ≤ 4 * ε := by
    have e1 : b00 z * b11 z - b01 z * b10 z - 1
        = (b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1) - b01 z * b10 z := by ring
    rw [e1]
    have h1 : |(b00 z - 1) * (b11 z - 1)| ≤ ε * ε := by
      rw [abs_mul]
      exact mul_le_mul hb00 hb11 (abs_nonneg _) hε
    have h2 : |b01 z * b10 z| ≤ ε * ε := by
      rw [abs_mul]
      exact mul_le_mul hb01 hb10 (abs_nonneg _) hε
    have h3 := abs_add_le ((b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1))
      (-(b01 z * b10 z))
    rw [abs_neg] at h3
    have h4 := abs_add_le ((b00 z - 1) * (b11 z - 1) + (b00 z - 1)) (b11 z - 1)
    have h5 := abs_add_le ((b00 z - 1) * (b11 z - 1)) (b00 z - 1)
    have hee : ε * ε ≤ ε := by
      have h := mul_le_mul_of_nonneg_left (by linarith only [hε1] : ε ≤ 1) hε
      linarith only [h]
    have hgoal : (b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1) - b01 z * b10 z
        = (b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1) + -(b01 z * b10 z) := by
      ring
    rw [hgoal]
    calc |(b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1) + -(b01 z * b10 z)|
        ≤ |(b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1)| + |b01 z * b10 z| := h3
      _ ≤ |(b00 z - 1) * (b11 z - 1) + (b00 z - 1)| + |b11 z - 1| + |b01 z * b10 z| := by
          linarith [h4]
      _ ≤ |(b00 z - 1) * (b11 z - 1)| + |b00 z - 1| + |b11 z - 1| + |b01 z * b10 z| := by
          linarith [h5]
      _ ≤ ε * ε + ε + ε + ε * ε := by linarith [h1, h2, hb00, hb11]
      _ ≤ 4 * ε := by linarith [hee]
  have hden2lb : (1 : ℝ) / 4 ≤ ‖den ^ 2‖ := by
    rw [norm_pow]
    nlinarith [hdenlb, norm_nonneg den]
  have hden2ne : den ^ 2 ≠ 0 := pow_ne_zero 2 hdenne
  have hSw1 : ‖Sw - 1‖ ≤ 36 * ε * Rz := by
    rw [← hSw_def]
    have e1 : ((b00 z * b11 z - b01 z * b10 z : ℝ) : ℂ) / den ^ 2 - 1
        = (((b00 z * b11 z - b01 z * b10 z - 1 : ℝ) : ℂ) - (den ^ 2 - 1)) / den ^ 2 := by
      field_simp
      push_cast
      ring
    rw [e1, norm_div]
    have h1 : ‖((b00 z * b11 z - b01 z * b10 z - 1 : ℝ) : ℂ) - (den ^ 2 - 1)‖
        ≤ 4 * ε + 5 * ε * Rz := by
      have h2 : ‖den ^ 2 - 1‖ ≤ 5 * ε * Rz := by
        have e2 : den ^ 2 - 1 = (den - 1) * (den + 1) := by ring
        rw [e2, norm_mul]
        have h3 : ‖den + 1‖ ≤ 5 / 2 := by
          have := norm_add_le den (1 : ℂ)
          rw [norm_one] at this
          linarith [hdenub]
        calc ‖den - 1‖ * ‖den + 1‖ ≤ (2 * ε * Rz) * (5 / 2) :=
              mul_le_mul hden1 h3 (norm_nonneg _) (by positivity)
          _ = 5 * ε * Rz := by ring
      calc ‖((b00 z * b11 z - b01 z * b10 z - 1 : ℝ) : ℂ) - (den ^ 2 - 1)‖
          ≤ ‖((b00 z * b11 z - b01 z * b10 z - 1 : ℝ) : ℂ)‖ + ‖den ^ 2 - 1‖ :=
            norm_sub_le _ _
        _ ≤ 4 * ε + 5 * ε * Rz := by
            rw [Complex.norm_real, Real.norm_eq_abs]
            linarith [hdet1, h2]
    rw [div_le_iff₀ (by linarith [hden2lb] : (0 : ℝ) < ‖den ^ 2‖)]
    have h4 : 36 * ε * Rz * (1 / 4) ≤ 36 * ε * Rz * ‖den ^ 2‖ := by
      refine mul_le_mul_of_nonneg_left hden2lb ?_
      positivity
    have h5 : 4 * ε + 5 * ε * Rz ≤ 9 * ε * Rz := by nlinarith
    linarith
  -- the error part of the derivative
  have hEbound : ∀ v : ℂ, ‖((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
      - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))) / den ^ 2‖
      ≤ 28 * Rz ^ 2 * ε * ‖v‖ := by
    intro v
    have hDnum : ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ))‖ ≤ 2 * ε * Rz * ‖v‖ := by
      calc ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ))‖
          ≤ ‖((D00 v : ℝ) : ℂ) * z‖ + ‖((D01 v : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = |D00 v| * ‖z‖ + |D01 v| := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
        _ ≤ ε * ‖v‖ * Rz + ε * ‖v‖ := by
            refine add_le_add ?_ ?_
            · refine mul_le_mul ?_ hzR (norm_nonneg z) (by positivity)
              calc |D00 v| ≤ ‖D00‖ * ‖v‖ := D00.le_opNorm v
                _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hn00 (norm_nonneg v)
            · calc |D01 v| ≤ ‖D01‖ * ‖v‖ := D01.le_opNorm v
                _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hn01 (norm_nonneg v)
        _ ≤ 2 * ε * Rz * ‖v‖ := by
          nlinarith [norm_nonneg v, hε,
            mul_nonneg (mul_nonneg hε (by nlinarith [hRz] : (0 : ℝ) ≤ Rz - 1))
              (norm_nonneg v)]
    have hDden : ‖(((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖ ≤ 2 * ε * Rz * ‖v‖ := by
      calc ‖(((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖
          ≤ ‖((D10 v : ℝ) : ℂ) * z‖ + ‖((D11 v : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = |D10 v| * ‖z‖ + |D11 v| := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
        _ ≤ ε * ‖v‖ * Rz + ε * ‖v‖ := by
            refine add_le_add ?_ ?_
            · refine mul_le_mul ?_ hzR (norm_nonneg z) (by positivity)
              calc |D10 v| ≤ ‖D10‖ * ‖v‖ := D10.le_opNorm v
                _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hn10 (norm_nonneg v)
            · calc |D11 v| ≤ ‖D11‖ * ‖v‖ := D11.le_opNorm v
                _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hn11 (norm_nonneg v)
        _ ≤ 2 * ε * Rz * ‖v‖ := by
          nlinarith [norm_nonneg v, hε,
            mul_nonneg (mul_nonneg hε (by nlinarith [hRz] : (0 : ℝ) ≤ Rz - 1))
              (norm_nonneg v)]
    rw [norm_div]
    rw [div_le_iff₀ (by linarith [hden2lb] : (0 : ℝ) < ‖den ^ 2‖)]
    have h1 : ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
        - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖
        ≤ 2 * ε * Rz * ‖v‖ * (3 / 2) + 2 * Rz * (2 * ε * Rz * ‖v‖) := by
      calc ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
          - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖
          ≤ ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den‖
            + ‖num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖ := norm_sub_le _ _
        _ ≤ 2 * ε * Rz * ‖v‖ * (3 / 2) + 2 * Rz * (2 * ε * Rz * ‖v‖) := by
            rw [norm_mul, norm_mul]
            refine add_le_add ?_ ?_
            · exact mul_le_mul hDnum hdenub (norm_nonneg _) (by positivity)
            · exact mul_le_mul hnumub hDden (norm_nonneg _) (by positivity)
    have h2 : 2 * ε * Rz * ‖v‖ * (3 / 2) + 2 * Rz * (2 * ε * Rz * ‖v‖)
        ≤ 7 * ε * Rz ^ 2 * ‖v‖ := by
      nlinarith [norm_nonneg v, hε, hRz0,
        mul_nonneg (mul_nonneg hε (by nlinarith [hRz] : (0 : ℝ) ≤ Rz ^ 2 - Rz))
          (norm_nonneg v)]
    have h3 : 28 * Rz ^ 2 * ε * ‖v‖ * (1 / 4) ≤ 28 * Rz ^ 2 * ε * ‖v‖ * ‖den ^ 2‖ := by
      refine mul_le_mul_of_nonneg_left hden2lb ?_
      positivity
    obtain ⟨X, hX⟩ : ∃ x : ℝ, ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
        - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖ = x := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ x : ℝ, ‖v‖ = x := ⟨_, rfl⟩
    obtain ⟨Dq, hDq⟩ : ∃ x : ℝ, ‖den ^ 2‖ = x := ⟨_, rfl⟩
    rw [hX] at h1 ⊢
    rw [hY] at h1 h2 h3 ⊢
    rw [hDq] at h3 ⊢
    linarith [h1, h2, h3]
  -- rewrite the scalar part
  have hLv' : ∀ v : ℂ, fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
      / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z v
      = Sw * v + ((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
          - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))) / den ^ 2 := by
    intro v
    rw [hLv v, ← hSw_def]
  -- value bound
  have hval : ‖(((b00 z : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ))
      / (((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ)) - z‖ ≤ 8 * Rz ^ 2 * ε := by
    rw [hnum_def, hden_def]
    have e1 : num / den - z = (num - z * den) / den := by
      field_simp
    rw [e1, norm_div]
    have h1 : ‖num - z * den‖ ≤ 4 * ε * Rz ^ 2 := by
      have e2 : num - z * den = (num - z) - z * (den - 1) := by ring
      rw [e2]
      calc ‖(num - z) - z * (den - 1)‖ ≤ ‖num - z‖ + ‖z * (den - 1)‖ := norm_sub_le _ _
        _ ≤ 2 * ε * Rz + Rz * (2 * ε * Rz) := by
            rw [norm_mul]
            exact add_le_add hnumz (mul_le_mul hzR hden1 (norm_nonneg _) (by positivity))
        _ ≤ 4 * ε * Rz ^ 2 := by
            nlinarith [mul_nonneg hε (mul_nonneg
              (by linarith : (0 : ℝ) ≤ Rz - 1) (by linarith : (0 : ℝ) ≤ Rz))]
    rw [div_le_iff₀ (by linarith [hdenlb] : (0 : ℝ) < ‖den‖)]
    have h2 : 8 * Rz ^ 2 * ε * (1 / 2) ≤ 8 * Rz ^ 2 * ε * ‖den‖ := by
      refine mul_le_mul_of_nonneg_left hdenlb ?_
      positivity
    linarith [h1, h2]
  -- operator-norm bound for the difference to the identity
  have hopn : ‖fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
      / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z
      - ContinuousLinearMap.id ℝ ℂ‖ ≤ 64 * Rz ^ 2 * ε := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
    intro v
    rw [sub_apply, ContinuousLinearMap.id_apply, hLv' v]
    have e1 : Sw * v + ((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
        - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))) / den ^ 2 - v
        = (Sw - 1) * v + ((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
          - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))) / den ^ 2 := by
      ring
    rw [e1]
    calc ‖(Sw - 1) * v + ((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
        - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))) / den ^ 2‖
        ≤ ‖(Sw - 1) * v‖ + ‖((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
          - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))) / den ^ 2‖ := norm_add_le _ _
      _ ≤ 36 * ε * Rz * ‖v‖ + 28 * Rz ^ 2 * ε * ‖v‖ := by
          rw [norm_mul]
          exact add_le_add (mul_le_mul_of_nonneg_right hSw1 (norm_nonneg v)) (hEbound v)
      _ ≤ 64 * Rz ^ 2 * ε * ‖v‖ := by
          obtain ⟨Y, hY⟩ : ∃ x : ℝ, ‖v‖ = x := ⟨_, rfl⟩
          have hY0 : 0 ≤ Y := hY ▸ norm_nonneg v
          rw [hY]
          have hRz2 : (0 : ℝ) ≤ Rz ^ 2 - Rz := by
            have h := mul_nonneg (by linarith only [hRz] : (0 : ℝ) ≤ Rz - 1)
              (by linarith only [hRz] : (0 : ℝ) ≤ Rz)
            nlinarith [h]
          have hprod : 0 ≤ ε * (Rz ^ 2 - Rz) * Y := mul_nonneg (mul_nonneg hε hRz2) hY0
          nlinarith [hprod]
  exact ⟨hdiff, hval, hopn⟩

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The per-point Wirtinger bounds elaborate one large derivative chain; the default
-- heartbeat budget does not cover it.
/-- **Wirtinger bounds for a Möbius map with near-identity `C¹` coefficient field**: an
upper bound for the conjugate-linear part, a lower bound for the complex-linear part, and
positivity of the Jacobian, with explicit polynomial constants. -/
lemma zz_moeb_packB
    (b00 b01 b10 b11 : ℂ → ℝ) (D00 D01 D10 D11 : ℂ →L[ℝ] ℝ) (z : ℂ)
    (Rz ε : ℝ) (hRz : 1 ≤ Rz) (hzR : ‖z‖ ≤ Rz)
    (hD00 : HasFDerivAt b00 D00 z) (hD01 : HasFDerivAt b01 D01 z)
    (hD10 : HasFDerivAt b10 D10 z) (hD11 : HasFDerivAt b11 D11 z)
    (hε : 0 ≤ ε)
    (hb00 : |b00 z - 1| ≤ ε) (hb01 : |b01 z| ≤ ε)
    (hb10 : |b10 z| ≤ ε) (hb11 : |b11 z - 1| ≤ ε)
    (hn00 : ‖D00‖ ≤ ε) (hn01 : ‖D01‖ ≤ ε) (hn10 : ‖D10‖ ≤ ε) (hn11 : ‖D11‖ ≤ ε)
    (hsmall : ε * Rz ^ 2 ≤ 1 / 1000) :
    ‖dzbar (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
          / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z‖ ≤ 64 * Rz ^ 2 * ε ∧
      (1 : ℝ) / 2 ≤ ‖dz (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
          / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z‖ ∧
      0 < (fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
          / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z).det := by
  have hCSRC : ContinuousSMul ℝ ℂ := ⟨by
    have h : (fun p : ℝ × ℂ => p.1 • p.2) = fun p : ℝ × ℂ => (p.1 : ℂ) * p.2 := by
      funext p
      exact Complex.real_smul
    rw [h]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd⟩
  have hεRz : ε * Rz ≤ 1 / 128 := by
    nlinarith [hsmall, mul_nonneg hε (mul_nonneg
      (by linarith : (0 : ℝ) ≤ Rz - 1) (by linarith : (0 : ℝ) ≤ Rz))]
  have hε1 : ε ≤ 1 / 128 := by
    nlinarith [hsmall, mul_nonneg hε (by nlinarith : (0 : ℝ) ≤ Rz ^ 2 - 1)]
  have hRz0 : (0 : ℝ) < Rz := by linarith
  -- basic denominator and numerator bounds
  obtain ⟨den, hden_def⟩ : ∃ x : ℂ, ((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ) = x := ⟨_, rfl⟩
  obtain ⟨num, hnum_def⟩ : ∃ x : ℂ, ((b00 z : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ) = x := ⟨_, rfl⟩
  have hden1 : ‖den - 1‖ ≤ 2 * ε * Rz := by
    rw [← hden_def]
    have h1 : ((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ) - 1
        = ((b10 z : ℝ) : ℂ) * z + ((b11 z - 1 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1]
    calc ‖((b10 z : ℝ) : ℂ) * z + ((b11 z - 1 : ℝ) : ℂ)‖
        ≤ ‖((b10 z : ℝ) : ℂ) * z‖ + ‖((b11 z - 1 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |b10 z| * ‖z‖ + |b11 z - 1| := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
      _ ≤ ε * Rz + ε * 1 := by
          refine add_le_add (mul_le_mul hb10 hzR (norm_nonneg z) hε) ?_
          calc |b11 z - 1| ≤ ε := hb11
            _ = ε * 1 := (mul_one ε).symm
      _ ≤ 2 * ε * Rz := by nlinarith [mul_le_mul_of_nonneg_left hRz hε]
  have hdenlb : (1 : ℝ) / 2 ≤ ‖den‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) den
    rw [norm_one, norm_sub_rev] at h1
    nlinarith [hden1, hεRz]
  have hdenub : ‖den‖ ≤ 3 / 2 := by
    have h1 := norm_add_le (den - 1) 1
    rw [sub_add_cancel, norm_one] at h1
    nlinarith [hden1, hεRz]
  have hdenne : den ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdenlb
    linarith
  have hdenne' : ((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ) ≠ 0 := by
    rw [hden_def]
    exact hdenne
  have hnumz : ‖num - z‖ ≤ 2 * ε * Rz := by
    rw [← hnum_def]
    have h1 : ((b00 z : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ) - z
        = ((b00 z - 1 : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1]
    calc ‖((b00 z - 1 : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ)‖
        ≤ ‖((b00 z - 1 : ℝ) : ℂ) * z‖ + ‖((b01 z : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |b00 z - 1| * ‖z‖ + |b01 z| := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
      _ ≤ ε * Rz + ε * 1 := by
          refine add_le_add (mul_le_mul hb00 hzR (norm_nonneg z) hε) ?_
          calc |b01 z| ≤ ε := hb01
            _ = ε * 1 := (mul_one ε).symm
      _ ≤ 2 * ε * Rz := by nlinarith [mul_le_mul_of_nonneg_left hRz hε]
  have hnumub : ‖num‖ ≤ 2 * Rz := by
    have h1 := norm_add_le (num - z) z
    rw [sub_add_cancel] at h1
    nlinarith [hnumz, hεRz, hzR]
  obtain ⟨hdiff, hLvraw⟩ := zz_moeb_core b00 b01 b10 b11 D00 D01 D10 D11 z
    hD00 hD01 hD10 hD11 hdenne'
  have hLv : ∀ v : ℂ, fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
      / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z v
      = ((b00 z * b11 z - b01 z * b10 z : ℝ) : ℂ) / den ^ 2 * v
        + ((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
            - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))) / den ^ 2 := by
    intro v
    rw [hLvraw v, hden_def, hnum_def]
  clear hLvraw hD00 hD01 hD10 hD11
  -- bounds for the two parts  -- bounds for the two parts
  obtain ⟨Sw, hSw_def⟩ : ∃ x : ℂ, ((b00 z * b11 z - b01 z * b10 z : ℝ) : ℂ) / den ^ 2 = x :=
    ⟨_, rfl⟩
  have hdet1 : |b00 z * b11 z - b01 z * b10 z - 1| ≤ 4 * ε := by
    have e1 : b00 z * b11 z - b01 z * b10 z - 1
        = (b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1) - b01 z * b10 z := by ring
    rw [e1]
    have h1 : |(b00 z - 1) * (b11 z - 1)| ≤ ε * ε := by
      rw [abs_mul]
      exact mul_le_mul hb00 hb11 (abs_nonneg _) hε
    have h2 : |b01 z * b10 z| ≤ ε * ε := by
      rw [abs_mul]
      exact mul_le_mul hb01 hb10 (abs_nonneg _) hε
    have h3 := abs_add_le ((b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1))
      (-(b01 z * b10 z))
    rw [abs_neg] at h3
    have h4 := abs_add_le ((b00 z - 1) * (b11 z - 1) + (b00 z - 1)) (b11 z - 1)
    have h5 := abs_add_le ((b00 z - 1) * (b11 z - 1)) (b00 z - 1)
    have hee : ε * ε ≤ ε := by
      have h := mul_le_mul_of_nonneg_left (by linarith only [hε1] : ε ≤ 1) hε
      linarith only [h]
    have hgoal : (b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1) - b01 z * b10 z
        = (b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1) + -(b01 z * b10 z) := by
      ring
    rw [hgoal]
    calc |(b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1) + -(b01 z * b10 z)|
        ≤ |(b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1)| + |b01 z * b10 z| := h3
      _ ≤ |(b00 z - 1) * (b11 z - 1) + (b00 z - 1)| + |b11 z - 1| + |b01 z * b10 z| := by
          linarith [h4]
      _ ≤ |(b00 z - 1) * (b11 z - 1)| + |b00 z - 1| + |b11 z - 1| + |b01 z * b10 z| := by
          linarith [h5]
      _ ≤ ε * ε + ε + ε + ε * ε := by linarith [h1, h2, hb00, hb11]
      _ ≤ 4 * ε := by linarith [hee]
  have hden2lb : (1 : ℝ) / 4 ≤ ‖den ^ 2‖ := by
    rw [norm_pow]
    nlinarith [hdenlb, norm_nonneg den]
  have hden2ne : den ^ 2 ≠ 0 := pow_ne_zero 2 hdenne
  have hSw1 : ‖Sw - 1‖ ≤ 36 * ε * Rz := by
    rw [← hSw_def]
    have e1 : ((b00 z * b11 z - b01 z * b10 z : ℝ) : ℂ) / den ^ 2 - 1
        = (((b00 z * b11 z - b01 z * b10 z - 1 : ℝ) : ℂ) - (den ^ 2 - 1)) / den ^ 2 := by
      field_simp
      push_cast
      ring
    rw [e1, norm_div]
    have h1 : ‖((b00 z * b11 z - b01 z * b10 z - 1 : ℝ) : ℂ) - (den ^ 2 - 1)‖
        ≤ 4 * ε + 5 * ε * Rz := by
      have h2 : ‖den ^ 2 - 1‖ ≤ 5 * ε * Rz := by
        have e2 : den ^ 2 - 1 = (den - 1) * (den + 1) := by ring
        rw [e2, norm_mul]
        have h3 : ‖den + 1‖ ≤ 5 / 2 := by
          have := norm_add_le den (1 : ℂ)
          rw [norm_one] at this
          linarith [hdenub]
        calc ‖den - 1‖ * ‖den + 1‖ ≤ (2 * ε * Rz) * (5 / 2) :=
              mul_le_mul hden1 h3 (norm_nonneg _) (by positivity)
          _ = 5 * ε * Rz := by ring
      calc ‖((b00 z * b11 z - b01 z * b10 z - 1 : ℝ) : ℂ) - (den ^ 2 - 1)‖
          ≤ ‖((b00 z * b11 z - b01 z * b10 z - 1 : ℝ) : ℂ)‖ + ‖den ^ 2 - 1‖ :=
            norm_sub_le _ _
        _ ≤ 4 * ε + 5 * ε * Rz := by
            rw [Complex.norm_real, Real.norm_eq_abs]
            linarith [hdet1, h2]
    rw [div_le_iff₀ (by linarith [hden2lb] : (0 : ℝ) < ‖den ^ 2‖)]
    have h4 : 36 * ε * Rz * (1 / 4) ≤ 36 * ε * Rz * ‖den ^ 2‖ := by
      refine mul_le_mul_of_nonneg_left hden2lb ?_
      positivity
    have h5 : 4 * ε + 5 * ε * Rz ≤ 9 * ε * Rz := by nlinarith
    linarith
  -- the error part of the derivative
  have hEbound : ∀ v : ℂ, ‖((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
      - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))) / den ^ 2‖
      ≤ 28 * Rz ^ 2 * ε * ‖v‖ := by
    intro v
    have hDnum : ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ))‖ ≤ 2 * ε * Rz * ‖v‖ := by
      calc ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ))‖
          ≤ ‖((D00 v : ℝ) : ℂ) * z‖ + ‖((D01 v : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = |D00 v| * ‖z‖ + |D01 v| := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
        _ ≤ ε * ‖v‖ * Rz + ε * ‖v‖ := by
            refine add_le_add ?_ ?_
            · refine mul_le_mul ?_ hzR (norm_nonneg z) (by positivity)
              calc |D00 v| ≤ ‖D00‖ * ‖v‖ := D00.le_opNorm v
                _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hn00 (norm_nonneg v)
            · calc |D01 v| ≤ ‖D01‖ * ‖v‖ := D01.le_opNorm v
                _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hn01 (norm_nonneg v)
        _ ≤ 2 * ε * Rz * ‖v‖ := by
          nlinarith [norm_nonneg v, hε,
            mul_nonneg (mul_nonneg hε (by nlinarith [hRz] : (0 : ℝ) ≤ Rz - 1))
              (norm_nonneg v)]
    have hDden : ‖(((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖ ≤ 2 * ε * Rz * ‖v‖ := by
      calc ‖(((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖
          ≤ ‖((D10 v : ℝ) : ℂ) * z‖ + ‖((D11 v : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = |D10 v| * ‖z‖ + |D11 v| := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
        _ ≤ ε * ‖v‖ * Rz + ε * ‖v‖ := by
            refine add_le_add ?_ ?_
            · refine mul_le_mul ?_ hzR (norm_nonneg z) (by positivity)
              calc |D10 v| ≤ ‖D10‖ * ‖v‖ := D10.le_opNorm v
                _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hn10 (norm_nonneg v)
            · calc |D11 v| ≤ ‖D11‖ * ‖v‖ := D11.le_opNorm v
                _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hn11 (norm_nonneg v)
        _ ≤ 2 * ε * Rz * ‖v‖ := by
          nlinarith [norm_nonneg v, hε,
            mul_nonneg (mul_nonneg hε (by nlinarith [hRz] : (0 : ℝ) ≤ Rz - 1))
              (norm_nonneg v)]
    rw [norm_div]
    rw [div_le_iff₀ (by linarith [hden2lb] : (0 : ℝ) < ‖den ^ 2‖)]
    have h1 : ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
        - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖
        ≤ 2 * ε * Rz * ‖v‖ * (3 / 2) + 2 * Rz * (2 * ε * Rz * ‖v‖) := by
      calc ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
          - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖
          ≤ ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den‖
            + ‖num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖ := norm_sub_le _ _
        _ ≤ 2 * ε * Rz * ‖v‖ * (3 / 2) + 2 * Rz * (2 * ε * Rz * ‖v‖) := by
            rw [norm_mul, norm_mul]
            refine add_le_add ?_ ?_
            · exact mul_le_mul hDnum hdenub (norm_nonneg _) (by positivity)
            · exact mul_le_mul hnumub hDden (norm_nonneg _) (by positivity)
    have h2 : 2 * ε * Rz * ‖v‖ * (3 / 2) + 2 * Rz * (2 * ε * Rz * ‖v‖)
        ≤ 7 * ε * Rz ^ 2 * ‖v‖ := by
      nlinarith [norm_nonneg v, hε, hRz0,
        mul_nonneg (mul_nonneg hε (by nlinarith [hRz] : (0 : ℝ) ≤ Rz ^ 2 - Rz))
          (norm_nonneg v)]
    have h3 : 28 * Rz ^ 2 * ε * ‖v‖ * (1 / 4) ≤ 28 * Rz ^ 2 * ε * ‖v‖ * ‖den ^ 2‖ := by
      refine mul_le_mul_of_nonneg_left hden2lb ?_
      positivity
    obtain ⟨X, hX⟩ : ∃ x : ℝ, ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
        - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖ = x := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ x : ℝ, ‖v‖ = x := ⟨_, rfl⟩
    obtain ⟨Dq, hDq⟩ : ∃ x : ℝ, ‖den ^ 2‖ = x := ⟨_, rfl⟩
    rw [hX] at h1 ⊢
    rw [hY] at h1 h2 h3 ⊢
    rw [hDq] at h3 ⊢
    linarith [h1, h2, h3]
  -- Wirtinger parts via the split of the derivative
  have hα : fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
      / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z 1
      = Sw + ((((D00 1 : ℝ) : ℂ) * z + ((D01 1 : ℝ) : ℂ)) * den
          - num * (((D10 1 : ℝ) : ℂ) * z + ((D11 1 : ℝ) : ℂ))) / den ^ 2 := by
    rw [hLv 1, ← hSw_def, mul_one]
  have hβ : fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
      / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z Complex.I
      = Sw * Complex.I + ((((D00 Complex.I : ℝ) : ℂ) * z + ((D01 Complex.I : ℝ) : ℂ)) * den
          - num * (((D10 Complex.I : ℝ) : ℂ) * z
            + ((D11 Complex.I : ℝ) : ℂ))) / den ^ 2 := by
    rw [hLv Complex.I, ← hSw_def]
  have hE1 := hEbound 1
  have hEI := hEbound Complex.I
  rw [norm_one, mul_one] at hE1
  rw [Complex.norm_I, mul_one] at hEI
  have hCb0 : (0 : ℝ) ≤ 64 * Rz ^ 2 * ε := by positivity
  have hSw64 : ‖Sw - 1‖ ≤ 64 * Rz ^ 2 * ε := by
    refine le_trans hSw1 ?_
    have hRz2 : (0 : ℝ) ≤ Rz ^ 2 - Rz := by
      have h := mul_nonneg (by linarith only [hRz] : (0 : ℝ) ≤ Rz - 1)
        (by linarith only [hRz] : (0 : ℝ) ≤ Rz)
      nlinarith [h]
    nlinarith [mul_nonneg hε hRz2]
  have hE164 : ‖((((D00 1 : ℝ) : ℂ) * z + ((D01 1 : ℝ) : ℂ)) * den
      - num * (((D10 1 : ℝ) : ℂ) * z + ((D11 1 : ℝ) : ℂ))) / den ^ 2‖
      ≤ 64 * Rz ^ 2 * ε := by
    refine le_trans hE1 ?_
    nlinarith [mul_nonneg (mul_nonneg hε (sq_nonneg Rz)) (by norm_num : (0:ℝ) ≤ 36)]
  have hEI64 : ‖((((D00 Complex.I : ℝ) : ℂ) * z + ((D01 Complex.I : ℝ) : ℂ)) * den
      - num * (((D10 Complex.I : ℝ) : ℂ) * z + ((D11 Complex.I : ℝ) : ℂ))) / den ^ 2‖
      ≤ 64 * Rz ^ 2 * ε := by
    refine le_trans hEI ?_
    nlinarith [mul_nonneg (mul_nonneg hε (sq_nonneg Rz)) (by norm_num : (0:ℝ) ≤ 36)]
  have hsm6 : 64 * Rz ^ 2 * ε ≤ 1 / 6 := by nlinarith [hsmall]
  obtain ⟨hbar, hzlb, hdet⟩ := zz_wirt _ z Sw _ _ (64 * Rz ^ 2 * ε) hα hβ hSw64 hE164 hEI64
    hCb0 hsm6
  exact ⟨hbar, hzlb, hdet⟩

/-- Continuous functions are locally `Lᵖ`. -/
private lemma zz_memlp (f : ℂ → ℂ) (p : ℝ≥0∞) (Ω : Set ℂ) (hf : ContinuousOn f Ω) :
    MemLpLocOn f p Ω := by
  intro K hKΩ hK
  have : Fact (volume K < ⊤) := ⟨hK.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hf.mono hKΩ)
  refine MemLp.of_bound ((hf.mono hKΩ).aestronglyMeasurable hK.measurableSet) C ?_
  rw [MeasureTheory.ae_restrict_iff' hK.measurableSet]
  exact Filter.Eventually.of_forall hC

/-- A `C¹` function on an open set lies in `W^{1,2}_loc` there. -/
lemma zz_sobolev (f : ℂ → ℂ) (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ 1 f Ω) : MemWklocP f 1 2 Ω := by
  have hfc : ContinuousOn f Ω := hf.continuousOn
  have hgc : ContinuousOn (fderiv ℝ f) Ω := hf.continuousOn_fderiv_of_isOpen hΩ le_rfl
  refine ⟨zz_memlp f 2 Ω hfc, fun z => (fderiv ℝ f z) 1, fun z => (fderiv ℝ f z) Complex.I,
    ⟨HasWeakDirDeriv.of_contDiffOn hΩ hf, HasWeakDirDeriv.of_contDiffOn hΩ hf⟩, ?_, ?_⟩
  · exact zz_memlp _ 2 Ω (hgc.clm_apply continuousOn_const)
  · exact zz_memlp _ 2 Ω (hgc.clm_apply continuousOn_const)

/-- **Quantitative inverse mapping on a ball**: a map whose derivative stays within `1/2`
of the identity on a closed ball is injective there and covers the quarter-radius ball
around the image of the center. -/
lemma zz_surj (F : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hd : ∀ x ∈ Metric.closedBall c r, DifferentiableAt ℝ F x)
    (hb : ∀ x ∈ Metric.closedBall c r,
      ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2) :
    Set.InjOn F (Metric.closedBall c r) ∧
      ∀ y ∈ Metric.closedBall (F c) (r / 4), ∃ x ∈ Metric.closedBall c r, F x = y := by
  have hconv : Convex ℝ (Metric.closedBall c r) := convex_closedBall c r
  have hlip : ∀ a ∈ Metric.closedBall c r, ∀ b ∈ Metric.closedBall c r,
      ‖(F b - b) - (F a - a)‖ ≤ 1 / 2 * ‖b - a‖ := by
    intro a ha b hb'
    refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun w => F w - w)
      (f' := fun x => fderiv ℝ F x - ContinuousLinearMap.id ℝ ℂ)
      (fun x hx => (((hd x hx).hasFDerivAt).sub (hasFDerivAt_id x)).hasFDerivWithinAt)
      (fun x hx => hb x hx) hconv ha hb'
  constructor
  · intro a ha b hb' hab
    have h1 := hlip a ha b hb'
    have h2 : (F b - b) - (F a - a) = a - b := by
      rw [hab]
      ring
    rw [h2] at h1
    have h3 : ‖a - b‖ = ‖b - a‖ := by
      rw [← neg_sub b a, norm_neg]
    rw [h3] at h1
    have h4 : ‖b - a‖ ≤ 0 := by linarith [h1]
    have h5 : b - a = 0 := norm_le_zero_iff.mp h4
    have h6 : b = a := by
      have := sub_eq_zero.mp h5
      exact this
    exact h6.symm
  · intro y hy
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm] at hy
    -- the update map is a contraction of the closed ball
    have : Nonempty (Metric.closedBall c r) := ⟨⟨c, Metric.mem_closedBall_self hr.le⟩⟩
    have hmaps : ∀ x ∈ Metric.closedBall c r, x - F x + y ∈ Metric.closedBall c r := by
      intro x hx
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h1 : x - F x + y - c = ((F c - c) - (F x - x)) + (y - F c) := by ring
      rw [h1]
      have h2 := hlip x hx c (Metric.mem_closedBall_self hr.le)
      have h3 : ‖x - c‖ ≤ r := by
        rw [← dist_eq_norm]
        exact Metric.mem_closedBall.mp hx
      have h4 := norm_add_le ((F c - c) - (F x - x)) (y - F c)
      have h5 : ‖c - x‖ = ‖x - c‖ := by
        rw [← neg_sub x c, norm_neg]
      rw [h5] at h2
      have h6 : ‖y - F c‖ = ‖F c - y‖ := by
        rw [← neg_sub (F c) y, norm_neg]
      linarith [h2, h3, h4, hy, h6]
    obtain ⟨T, hTdef⟩ : ∃ T : Metric.closedBall c r → Metric.closedBall c r,
        T = fun x => ⟨(x : ℂ) - F x + y, hmaps x x.2⟩ := ⟨_, rfl⟩
    have hLip : LipschitzWith (1 / 2 : NNReal) T := by
      refine LipschitzWith.of_dist_le_mul ?_
      intro a b
      rw [hTdef]
      have hab := hlip a a.2 b b.2
      rw [Subtype.dist_eq, Subtype.dist_eq]
      simp only [dist_eq_norm]
      have he : ((a : ℂ) - F a + y) - ((b : ℂ) - F b + y)
          = (F b - b) - (F a - a) := by ring
      rw [he]
      have hcoe : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
      rw [hcoe]
      have h3 : ‖(a : ℂ) - b‖ = ‖(b : ℂ) - a‖ := by
        rw [← neg_sub (b : ℂ) a, norm_neg]
      rw [h3]
      exact hab
    have hcontract : ContractingWith (1 / 2 : NNReal) T := ⟨by norm_num, hLip⟩
    have : CompleteSpace (Metric.closedBall c r) :=
      (Metric.isClosed_closedBall (x := c) (ε := r)).completeSpace_coe
    obtain ⟨x, hxfix⟩ : ∃ x : Metric.closedBall c r, T x = x :=
      ⟨ContractingWith.fixedPoint T hcontract, hcontract.fixedPoint_isFixedPt⟩
    refine ⟨x, x.2, ?_⟩
    have h1 : (T x : ℂ) = x := by
      rw [hxfix]
    rw [hTdef] at h1
    simp only at h1
    have h2 : (x : ℂ) - F x + y = x := h1
    have h3 : F (x : ℂ) = y := by linear_combination -h2
    exact h3

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The nested square estimates for the hyperbolic-Euclidean ball comparison exceed the
-- default heartbeat budget.
/-- **Euclidean sandwich for small hyperbolic balls**: for radius `s ≤ 1/2` the hyperbolic
ball nests between the Euclidean balls of radii `im · s / 2` and `2 · im · s` about the
center. -/
lemma zz_ballcomp (w : UpperHalfPlane) (s : ℝ) (hs : 0 < s) (hs2 : s ≤ 1 / 2) :
    (∀ z : ℂ, z ∈ Metric.ball (w : ℂ) (w.im * s / 2) →
      ∃ hz : 0 < z.im, dist (⟨z, hz⟩ : UpperHalfPlane) w < s) ∧
    (∀ z : ℂ, ∀ hz : 0 < z.im, dist (⟨z, hz⟩ : UpperHalfPlane) w < s →
      z ∈ Metric.ball (w : ℂ) (2 * w.im * s)) := by
  have hwim : 0 < w.im := w.im_pos
  have hsinh : 0 < Real.sinh s := by positivity
  have hcosh1 : 1 ≤ Real.cosh s := Real.one_le_cosh s
  have hcs : Real.cosh s - Real.sinh s = Real.exp (-s) := Real.cosh_sub_sinh s
  have hca : Real.cosh s + Real.sinh s = Real.exp s := Real.cosh_add_sinh s
  -- the two elementary exponential estimates
  have hlow : s / 2 ≤ Real.sinh s - (Real.cosh s - 1) := by
    have h1 : (-s) + 1 ≤ Real.exp (-s) := Real.add_one_le_exp (-s)
    have h2 : s + 1 ≤ Real.exp s := Real.add_one_le_exp s
    have h3 : Real.exp (-s) * Real.exp s = 1 := by
      rw [← Real.exp_add]
      simp
    have h4 : Real.exp (-s) ≤ 1 / (1 + s) := by
      rw [div_eq_inv_mul, mul_one, le_inv_comm₀ (Real.exp_pos _) (by linarith)]
      calc (1 + s : ℝ) = s + 1 := by ring
        _ ≤ Real.exp s := h2
        _ = (Real.exp (-s))⁻¹ := by
            rw [← Real.exp_neg, neg_neg]
    have h5 : 1 / (1 + s) ≤ 1 - s / 2 := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + s)]
      nlinarith [hs, hs2]
    have h6 : Real.exp (-s) ≤ 1 - s / 2 := le_trans h4 h5
    linarith [hcs, h6]
  have hhigh : Real.sinh s + (Real.cosh s - 1) ≤ 2 * s := by
    have h1 : 1 - s ≤ Real.exp (-s) := by
      have := Real.add_one_le_exp (-s)
      linarith
    have h2 : Real.exp s ≤ 1 / (1 - s) := by
      rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - s)]
      calc Real.exp s * (1 - s) ≤ Real.exp s * Real.exp (-s) := by
            refine mul_le_mul_of_nonneg_left h1 (Real.exp_pos s).le
        _ = 1 := by
            rw [← Real.exp_add]
            simp
    have h3 : 1 / (1 - s) ≤ 1 + 2 * s := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - s)]
      nlinarith [hs, hs2]
    have h4 : Real.exp s ≤ 1 + 2 * s := le_trans h2 h3
    linarith [hca, h4]
  have hcen : ∀ z : ℂ, dist z ((((w : ℂ).re : ℝ) : ℂ)
      + ((w.im * Real.cosh s : ℝ) : ℂ) * Complex.I) ^ 2
      = (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im * Real.cosh s) ^ 2 := by
    intro z
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  have hchar : ∀ (z : ℂ) (hz : 0 < z.im), dist (⟨z, hz⟩ : UpperHalfPlane) w < s ↔
      (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im * Real.cosh s) ^ 2
        < (w.im * Real.sinh s) ^ 2 := by
    intro z hz
    constructor
    · intro h
      have hm := (zz_ball w s hs z).mpr ⟨hz, h⟩
      rw [Metric.mem_ball] at hm
      have h2 := mul_self_lt_mul_self dist_nonneg hm
      rw [← hcen z]
      nlinarith [h2]
    · intro h
      have h0 : dist z ((((w : ℂ).re : ℝ) : ℂ)
          + ((w.im * Real.cosh s : ℝ) : ℂ) * Complex.I) ^ 2
          < (w.im * Real.sinh s) ^ 2 := by
        rw [hcen z]
        exact h
      have hlt : dist z ((((w : ℂ).re : ℝ) : ℂ)
          + ((w.im * Real.cosh s : ℝ) : ℂ) * Complex.I) < w.im * Real.sinh s := by
        by_contra hcon
        push Not at hcon
        have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ w.im * Real.sinh s) hcon
        nlinarith [h0, hsq]
      obtain ⟨hz', hdd⟩ := (zz_ball w s hs z).mp (Metric.mem_ball.mpr hlt)
      exact hdd
  constructor
  · -- inner inclusion
    intro z hzball
    rw [Metric.mem_ball, dist_eq_norm] at hzball
    have hnormsq : ‖z - (w : ℂ)‖ ^ 2 = (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_im]
      ring
    have hE2 : (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im) ^ 2 < (w.im * s / 2) ^ 2 := by
      rw [← hnormsq]
      have h := mul_self_lt_mul_self (norm_nonneg (z - (w : ℂ))) hzball
      nlinarith [h]
    have hzim : 0 < z.im := by
      have hb2 : (z.im - w.im) ^ 2 < (w.im * s / 2) ^ 2 := by
        nlinarith [hE2, sq_nonneg (z.re - (w : ℂ).re)]
      have hr : 0 < w.im * s / 2 := by positivity
      have habs : |z.im - w.im| < w.im * s / 2 := by
        by_contra hcon
        push Not at hcon
        have hsq := mul_self_le_mul_self hr.le hcon
        nlinarith [sq_abs (z.im - w.im), hb2, hsq]
      have h1 : -(w.im * s / 2) < z.im - w.im := (abs_lt.mp habs).1
      have h2 : 0 < w.im * (1 - s / 2) := mul_pos hwim (by linarith)
      nlinarith [h1, h2]
    refine ⟨hzim, ?_⟩
    rw [hchar z hzim]
    have hK0 : 0 ≤ w.im * (Real.cosh s - 1) :=
      mul_nonneg hwim.le (by linarith [hcosh1])
    have hkey : w.im * s / 2 + w.im * (Real.cosh s - 1) ≤ w.im * Real.sinh s := by
      have h := mul_le_mul_of_nonneg_left hlow hwim.le
      nlinarith [h]
    have hb2 : (z.im - w.im) ^ 2 < (w.im * s / 2) ^ 2 := by
      nlinarith [hE2, sq_nonneg (z.re - (w : ℂ).re)]
    have hbabs : |z.im - w.im| < w.im * s / 2 := by
      by_contra hcon
      push Not at hcon
      have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ w.im * s / 2) hcon
      nlinarith [sq_abs (z.im - w.im), hb2, hsq]
    have hsplit : z.im - w.im * Real.cosh s = (z.im - w.im) - w.im * (Real.cosh s - 1) := by
      ring
    rw [hsplit]
    nlinarith [hE2, hbabs, hK0, hkey, sq_abs (z.im - w.im), abs_nonneg (z.im - w.im),
      neg_abs_le (z.im - w.im), le_abs_self (z.im - w.im),
      mul_pos hwim hsinh]
  · -- outer inclusion
    intro z hz hlt
    rw [hchar z hz] at hlt
    rw [Metric.mem_ball, dist_eq_norm]
    have hnormsq : ‖z - (w : ℂ)‖ ^ 2 = (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_im]
      ring
    have hK0 : 0 ≤ w.im * (Real.cosh s - 1) :=
      mul_nonneg hwim.le (by linarith [hcosh1])
    have hSp : 0 < w.im * Real.sinh s := by positivity
    have hbabs : |z.im - w.im * Real.cosh s| < w.im * Real.sinh s := by
      by_contra hcon
      push Not at hcon
      have hsq := mul_self_le_mul_self hSp.le hcon
      nlinarith [sq_abs (z.im - w.im * Real.cosh s), hlt, hsq,
        sq_nonneg (z.re - (w : ℂ).re)]
    have hkey : w.im * Real.sinh s + w.im * (Real.cosh s - 1) ≤ 2 * w.im * s := by
      have h := mul_le_mul_of_nonneg_left hhigh hwim.le
      nlinarith [h]
    have hfin : ‖z - (w : ℂ)‖ ^ 2 < (2 * w.im * s) ^ 2 := by
      rw [hnormsq]
      have hsplit : z.im - w.im = (z.im - w.im * Real.cosh s) + w.im * (Real.cosh s - 1) := by
        ring
      rw [hsplit]
      nlinarith [hlt, hbabs, hK0, hkey, sq_abs (z.im - w.im * Real.cosh s),
        le_abs_self (z.im - w.im * Real.cosh s), neg_abs_le (z.im - w.im * Real.cosh s),
        hSp]
    nlinarith [hfin, norm_nonneg (z - (w : ℂ)), mul_pos (mul_pos two_pos hwim) hs]

/-- Multiplicativity of the Möbius denominator of a matrix product. -/
private lemma zz_matden (M N : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ)
    (hN : (N 1 0 : ℂ) * z + (N 1 1 : ℂ) ≠ 0) :
    ((M * N) 1 0 : ℂ) * z + ((M * N) 1 1 : ℂ)
      = ((M 1 0 : ℂ) * matMoebius N z + (M 1 1 : ℂ))
        * ((N 1 0 : ℂ) * z + (N 1 1 : ℂ)) := by
  have h0 : (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have hu : matMoebius N z * ((N 1 0 : ℂ) * z + (N 1 1 : ℂ))
      = (N 0 0 : ℂ) * z + (N 0 1 : ℂ) := by
    rw [matMoebius, div_mul_cancel₀ _ hN]
  rw [h0, h1, add_mul, mul_assoc, hu]
  push_cast
  ring

/-- Injectivity of a near-identity `C¹` map on a convex set. -/
lemma zz_inj (F : ℂ → ℂ) (S : Set ℂ) (hconv : Convex ℝ S)
    (hd : ∀ x ∈ S, DifferentiableAt ℝ F x)
    (hb : ∀ x ∈ S, ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2) :
    Set.InjOn F S := by
  have hlip : ∀ a ∈ S, ∀ b ∈ S, ‖(F b - b) - (F a - a)‖ ≤ 1 / 2 * ‖b - a‖ := by
    intro a ha b hb'
    refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun w => F w - w)
      (f' := fun x => fderiv ℝ F x - ContinuousLinearMap.id ℝ ℂ)
      (fun x hx => (((hd x hx).hasFDerivAt).sub (hasFDerivAt_id x)).hasFDerivWithinAt)
      (fun x hx => hb x hx) hconv ha hb'
  intro a ha b hb' hab
  have h1 := hlip a ha b hb'
  have h2 : (F b - b) - (F a - a) = a - b := by
    rw [hab]
    ring
  rw [h2] at h1
  have h3 : ‖a - b‖ = ‖b - a‖ := by
    rw [← neg_sub b a, norm_neg]
  rw [h3] at h1
  have h4 : ‖b - a‖ ≤ 0 := by linarith [h1]
  have h5 : b - a = 0 := norm_le_zero_iff.mp h4
  exact (sub_eq_zero.mp h5).symm

/-- Möbius maps of `SL(2, ℝ)` are `C¹` off the real axis. -/
private lemma zz_moeb_cdiff (gm : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ)
    (hz : 0 < z.im) : ContDiffAt ℝ 1 (moebiusMap gm) z := by
  have hden : (gm 1 0 : ℂ) * z + (gm 1 1 : ℂ) ≠ 0 :=
    moebiusDenom_ne_zero_of_im_ne_zero gm (ne_of_gt hz)
  have hfeq : moebiusMap gm = fun w => ((gm 0 0 : ℂ) * w + (gm 0 1 : ℂ))
      * (((gm 1 0 : ℂ) * w + (gm 1 1 : ℂ))⁻¹) := by
    funext w
    rw [moebiusMap, div_eq_mul_inv]
    rfl
  rw [hfeq]
  have hnum : ContDiffAt ℝ 1 (fun w : ℂ => (gm 0 0 : ℂ) * w + (gm 0 1 : ℂ)) z :=
    ((contDiff_const.mul contDiff_id).add contDiff_const).contDiffAt
  have hde : ContDiffAt ℝ 1 (fun w : ℂ => (gm 1 0 : ℂ) * w + (gm 1 1 : ℂ)) z :=
    ((contDiff_const.mul contDiff_id).add contDiff_const).contDiffAt
  exact hnum.mul (hde.inv hden)

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The averaged-field bounds sum convex combinations of near-identity matrices and their
-- derivatives; the default heartbeat budget does not cover the elaboration.
/-- **Bounds for a convex matrix average**: a field given on an open set by a finite convex
combination of near-identity constant matrices with `C¹` weights has entries `ε`-close to
the identity, differentiable entries with controlled derivative, and nonvanishing Möbius
denominator. -/
lemma zz_field {ι' : Type} (U : Set ℂ) (hUopen : IsOpen U)
    (K : Set ℂ) (_hKU : K ⊆ U)
    (F : Finset ι') (u : ι' → ℂ → ℝ) (c : ι' → Matrix (Fin 2) (Fin 2) ℝ)
    (Rz ε₂ Mu : ℝ) (hε₂0 : 0 < ε₂)
    (hRzU : ∀ z ∈ U, ‖z‖ ≤ Rz)
    (hu01 : ∀ (γ : ι') (z : ℂ), z ∈ U → 0 ≤ u γ z ∧ u γ z ≤ 1)
    (husm : ∀ γ : ι', ContDiffOn ℝ 1 (u γ) U)
    (huD : ∀ γ ∈ F, ∀ z ∈ K, ‖fderiv ℝ (u γ) z‖ ≤ Mu)
    (hsum1 : ∀ z ∈ U, ∑ γ ∈ F, u γ z = 1)
    (hcclose : ∀ γ ∈ F, ∀ i j : Fin 2,
      |c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ ε₂)
    (B : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (hBrep : ∀ z ∈ U, B z = ∑ γ ∈ F, u γ z • c γ)
    (hsmall : ε₂ * Rz + ε₂ ≤ 1 / 2) :
    (∀ z ∈ U, ∀ i j : Fin 2, |B z i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ ε₂) ∧
    (∀ z ∈ U, ∀ i j : Fin 2, HasFDerivAt (fun w => B w i j)
      (∑ γ ∈ F, (c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) • fderiv ℝ (u γ) z) z) ∧
    (∀ z ∈ K, ∀ i j : Fin 2, ‖∑ γ ∈ F, (c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
      • fderiv ℝ (u γ) z‖ ≤ (F.card : ℝ) * Mu * ε₂) ∧
    (∀ z ∈ U, ((B z 1 0 : ℝ) : ℂ) * z + ((B z 1 1 : ℝ) : ℂ) ≠ 0) := by
  have hBfun : ∀ i j : Fin 2, ∀ z ∈ U, B z i j
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j
        + ∑ γ ∈ F, u γ z * (c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
    intro i j z hz
    rw [hBrep z hz, Matrix.sum_apply]
    have he : ∀ γ ∈ F, (u γ z • c γ) i j = u γ z * c γ i j := by
      intro γ _
      rw [Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl he]
    have hsub : ∑ γ ∈ F, u γ z * (c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
        = (∑ γ ∈ F, u γ z * c γ i j)
          - (∑ γ ∈ F, u γ z) * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro γ _
      ring
    rw [hsub, hsum1 z hz, one_mul]
    ring
  have hBentry : ∀ z ∈ U, ∀ i j : Fin 2,
      |B z i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ ε₂ := by
    intro z hz i j
    rw [hBfun i j z hz, add_sub_cancel_left]
    calc |∑ γ ∈ F, u γ z * (c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)|
        ≤ ∑ γ ∈ F, |u γ z * (c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ γ ∈ F, u γ z * ε₂ := by
          refine Finset.sum_le_sum ?_
          intro γ hγ
          rw [abs_mul, abs_of_nonneg (hu01 γ z hz).1]
          exact mul_le_mul_of_nonneg_left (hcclose γ hγ i j) (hu01 γ z hz).1
      _ = ε₂ := by
          rw [← Finset.sum_mul, hsum1 z hz, one_mul]
  have hBD : ∀ z ∈ U, ∀ i j : Fin 2,
      HasFDerivAt (fun w => B w i j)
        (∑ γ ∈ F, (c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
          • fderiv ℝ (u γ) z) z := by
    intro z hz i j
    have hUnhds : U ∈ nhds z := hUopen.mem_nhds hz
    have hDγ : ∀ γ ∈ F, HasFDerivAt (fun w => u γ w
        * (c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j))
        ((c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) • fderiv ℝ (u γ) z) z := by
      intro γ _
      have hdiff : DifferentiableAt ℝ (u γ) z :=
        (((husm γ) z hz).contDiffAt hUnhds).differentiableAt one_ne_zero
      exact hdiff.hasFDerivAt.mul_const _
    have hsum0 := (HasFDerivAt.sum hDγ).const_add ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
    refine hsum0.congr_of_eventuallyEq ?_
    filter_upwards [hUnhds] with w hw
    rw [hBfun i j w hw, Finset.sum_apply]
  refine ⟨hBentry, hBD, ?_, ?_⟩
  · intro z hz i j
    calc ‖∑ γ ∈ F, (c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
        • fderiv ℝ (u γ) z‖
        ≤ ∑ γ ∈ F, ‖(c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
          • fderiv ℝ (u γ) z‖ := norm_sum_le _ _
      _ ≤ ∑ _γ ∈ F, ε₂ * Mu := by
          refine Finset.sum_le_sum ?_
          intro γ hγ
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul (hcclose γ hγ i j) (huD γ hγ z hz) (norm_nonneg _) hε₂0.le
      _ = (F.card : ℝ) * (ε₂ * Mu) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (F.card : ℝ) * Mu * ε₂ := by ring
  · intro z hz
    have h10 := hBentry z hz 1 0
    have h11 := hBentry z hz 1 1
    rw [Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at h10
    rw [Matrix.one_apply_eq] at h11
    intro h0
    have he : ((B z 1 0 : ℝ) : ℂ) * z + ((B z 1 1 : ℝ) : ℂ) - 1
        = ((B z 1 0 : ℝ) : ℂ) * z + ((B z 1 1 - 1 : ℝ) : ℂ) := by
      push_cast
      ring
    have hb : ‖((B z 1 0 : ℝ) : ℂ) * z + ((B z 1 1 - 1 : ℝ) : ℂ)‖ ≤ ε₂ * Rz + ε₂ := by
      calc ‖((B z 1 0 : ℝ) : ℂ) * z + ((B z 1 1 - 1 : ℝ) : ℂ)‖
          ≤ ‖((B z 1 0 : ℝ) : ℂ) * z‖ + ‖((B z 1 1 - 1 : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = |B z 1 0| * ‖z‖ + |B z 1 1 - 1| := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
        _ ≤ ε₂ * Rz + ε₂ := by
            refine add_le_add (mul_le_mul h10 (hRzU z hz) (norm_nonneg z) hε₂0.le) h11
    have h1 : ‖((B z 1 0 : ℝ) : ℂ) * z + ((B z 1 1 : ℝ) : ℂ) - 1‖ = 1 := by
      rw [h0]
      simp
    rw [he] at h1
    linarith [hb, h1.symm.le, hsmall]

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The transport computation chains three Wirtinger factorizations; the default heartbeat
-- budget does not cover the elaboration.
/-- **Möbius transport of Wirtinger data**: if `F` agrees on the upper half plane with a
conjugate `𝔪A ∘ F ∘ 𝔪G`, then differentiability, upper-half-plane values and the two
Wirtinger derivatives at `z` are carried by a single nonzero complex factor from those at
the transported point. -/
private lemma zz_transport (A G : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (F : ℂ → ℂ) (z w : ℂ) (hz : 0 < z.im) (_hw : 0 < w.im)
    (hwz : w = moebiusMap G z)
    (hEE : ∀ x : ℂ, 0 < x.im → F x = moebiusMap A (F (moebiusMap G x)))
    (hFd : DifferentiableAt ℝ F w) (hFim : 0 < (F w).im) :
    DifferentiableAt ℝ F z ∧ 0 < (F z).im ∧
      ∃ q₁ q₂ : ℂ, q₁ ≠ 0 ∧ ‖q₁‖ = ‖q₂‖ ∧ dz F z = q₁ * dz F w
        ∧ dzbar F z = q₂ * dzbar F w := by
  have hopen : IsOpen {x : ℂ | 0 < x.im} := isOpen_lt continuous_const Complex.continuous_im
  have hdenG : moebiusDenom G z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero G (ne_of_gt hz)
  have hGd : DifferentiableAt ℂ (moebiusMap G) z :=
    (hasDerivAt_moebiusMap G hdenG).differentiableAt
  have hGderiv : deriv (moebiusMap G) z = ((moebiusDenom G z) ^ 2)⁻¹ :=
    (hasDerivAt_moebiusMap G hdenG).deriv
  have hFdw : DifferentiableAt ℝ F (moebiusMap G z) := by
    rw [← hwz]
    exact hFd
  -- the inner composite
  have hinner_dz : dz (F ∘ moebiusMap G) z = dz F w * deriv (moebiusMap G) z := by
    rw [dz_comp_of_holomorphicAt hGd hFdw, ← hwz]
  have hinner_dzbar : dzbar (F ∘ moebiusMap G) z
      = dzbar F w * starRingEnd ℂ (deriv (moebiusMap G) z) := by
    rw [dzbar_comp_of_holomorphicAt hGd hFdw, ← hwz]
  have hinner_d : DifferentiableAt ℝ (F ∘ moebiusMap G) z :=
    hFdw.comp z (differentiableAt_complex_iff_differentiableAt_real.mp hGd).1
  -- the outer Möbius factor
  have hFGim : 0 < (F (moebiusMap G z)).im := by
    rw [← hwz]
    exact hFim
  have hdenA : moebiusDenom A (F (moebiusMap G z)) ≠ 0 :=
    moebiusDenom_ne_zero_of_im_ne_zero A (ne_of_gt hFGim)
  have hAd : DifferentiableAt ℂ (moebiusMap A) (F (moebiusMap G z)) :=
    (hasDerivAt_moebiusMap A hdenA).differentiableAt
  have hAderiv : deriv (moebiusMap A) (F (moebiusMap G z))
      = ((moebiusDenom A (F (moebiusMap G z))) ^ 2)⁻¹ :=
    (hasDerivAt_moebiusMap A hdenA).deriv
  have hAdr : DifferentiableAt ℝ (moebiusMap A) ((F ∘ moebiusMap G) z) :=
    (differentiableAt_complex_iff_differentiableAt_real.mp hAd).1
  -- the composite and its Wirtinger data
  have hcomp_dz : dz (fun x => moebiusMap A ((F ∘ moebiusMap G) x)) z
      = deriv (moebiusMap A) (F (moebiusMap G z)) * dz (F ∘ moebiusMap G) z := by
    rw [dz_comp hinner_d hAdr]
    rw [show (F ∘ moebiusMap G) z = F (moebiusMap G z) from rfl]
    rw [dzbar_eq_zero_of_differentiableAt hAd, dz_eq_deriv_of_differentiableAt hAd]
    ring
  have hcomp_dzbar : dzbar (fun x => moebiusMap A ((F ∘ moebiusMap G) x)) z
      = deriv (moebiusMap A) (F (moebiusMap G z)) * dzbar (F ∘ moebiusMap G) z := by
    rw [dzbar_comp hinner_d hAdr]
    rw [show (F ∘ moebiusMap G) z = F (moebiusMap G z) from rfl]
    rw [dzbar_eq_zero_of_differentiableAt hAd, dz_eq_deriv_of_differentiableAt hAd]
    ring
  have hcomp_d : DifferentiableAt ℝ (fun x => moebiusMap A ((F ∘ moebiusMap G) x)) z :=
    hAdr.comp z hinner_d
  -- transfer along the eventual identity
  have hEEq : F =ᶠ[nhds z] fun x => moebiusMap A ((F ∘ moebiusMap G) x) := by
    filter_upwards [hopen.mem_nhds hz] with x hx
    exact hEE x hx
  have hFdz : DifferentiableAt ℝ F z := hcomp_d.congr_of_eventuallyEq hEEq
  have hfdeq : fderiv ℝ F z = fderiv ℝ (fun x => moebiusMap A ((F ∘ moebiusMap G) x)) z :=
    hEEq.fderiv_eq
  have hdz_eq : dz F z = dz (fun x => moebiusMap A ((F ∘ moebiusMap G) x)) z := by
    rw [dz, dz, hfdeq]
  have hdzbar_eq : dzbar F z = dzbar (fun x => moebiusMap A ((F ∘ moebiusMap G) x)) z := by
    rw [dzbar, dzbar, hfdeq]
  refine ⟨hFdz, ?_, ?_⟩
  · rw [hEE z hz]
    exact moebiusMap_im_pos A hFGim
  · refine ⟨deriv (moebiusMap A) (F (moebiusMap G z)) * deriv (moebiusMap G) z,
      deriv (moebiusMap A) (F (moebiusMap G z))
        * starRingEnd ℂ (deriv (moebiusMap G) z), ?_, ?_, ?_, ?_⟩
    · refine mul_ne_zero ?_ ?_
      · rw [hAderiv]
        exact inv_ne_zero (pow_ne_zero 2 hdenA)
      · rw [hGderiv]
        exact inv_ne_zero (pow_ne_zero 2 hdenG)
    · rw [norm_mul, norm_mul, Complex.norm_conj]
    · rw [hdz_eq, hcomp_dz, hinner_dz]
      ring
    · rw [hdzbar_eq, hcomp_dzbar, hinner_dzbar]
      ring

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The weight-field construction sums bump atoms over the group with compactness bounds;
-- the default heartbeat budget does not cover the elaboration.
/-- **The equivariant partition of unity subordinate to the orbit**: from an orbit-density
radius, a family of `C¹` weights on a euclidean-ball neighborhood of the base orbit ball,
summing to one over a finite active set, vanishing off it, with uniform derivative bounds
on an inner ball, and exactly equivariant under the Möbius action. -/
lemma zz_weights {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ'fuchs : IsFuchsianGroup Γ') (τ₀ : UpperHalfPlane) (R : ℝ) (hRpos : 0 < R)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit (↥Γ') τ₀) ≤ R) :
    ∃ (UK UKb : Set ℂ) (SACT : Finset ↥Γ') (uψ : ↥Γ' → ℂ → ℝ) (Mψ Rz imK : ℝ),
      IsOpen UK ∧ UK ⊆ {z : ℂ | 0 < z.im} ∧ IsOpen UKb ∧ Convex ℝ UKb ∧ UKb ⊆ UK ∧
      (∀ (z : ℂ) (hz : 0 < z.im),
        dist (⟨z, hz⟩ : UpperHalfPlane) τ₀ < R + 3 / 2 → z ∈ UKb) ∧
      1 ≤ Rz ∧ (∀ z ∈ UK, ‖z‖ ≤ Rz) ∧ 0 ≤ Mψ ∧ 0 < imK ∧ (∀ z ∈ UK, imK < z.im) ∧
      (∀ (γ : ↥Γ') (z : ℂ), z ∈ UK → 0 ≤ uψ γ z ∧ uψ γ z ≤ 1) ∧
      (∀ γ : ↥Γ', ContDiffOn ℝ 1 (uψ γ) UK) ∧
      (∀ γ ∈ SACT, ∀ z ∈ UKb, ‖fderiv ℝ (uψ γ) z‖ ≤ Mψ) ∧
      (∀ z ∈ UK, ∑ γ ∈ SACT, uψ γ z = 1) ∧
      (∀ z ∈ UK, ∀ γ : ↥Γ', γ ∉ SACT → uψ γ z = 0) ∧
      (∀ γ ∈ SACT, dist τ₀ (γ • τ₀) ≤ 2 * R + 4) ∧
      (∀ (β γ : ↥Γ') (z : ℂ), 0 < z.im →
        uψ (β * γ) (moebiusMap (↑β) z) = uψ γ z) ∧
      (∀ z : ℂ, 0 < z.im → ∃ Fz : Finset ↥Γ', ∀ γ : ↥Γ', γ ∉ Fz → uψ γ z = 0) := by
  classical
  have : IsIsometricSMul (↥Γ') UpperHalfPlane :=
    ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
  have hτ₀im : 0 < τ₀.im := τ₀.im_pos
  have hSfin : ∀ r : ℝ, {γ : ↥Γ' | dist τ₀ (γ • τ₀) ≤ r}.Finite :=
    fun r => zz_fin hΓ'fuchs τ₀ τ₀ r
  -- the bump profile
  obtain ⟨gb, hgbdef⟩ : ∃ g : ℝ → ℝ, g = fun t =>
      Real.smoothTransition ((Real.cosh (R + 1) - t)
        / (Real.cosh (R + 1) - Real.cosh (R + 1 / 2))) := ⟨_, rfl⟩
  have hcoshRlt : Real.cosh (R + 1 / 2) < Real.cosh (R + 1) := by
    rw [Real.cosh_lt_cosh]
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ R + 1 / 2),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ R + 1)]
    linarith
  have hgbsm : ContDiff ℝ 1 gb := by
    rw [hgbdef]
    refine Real.smoothTransition.contDiff.comp ?_
    refine ContDiff.div_const ?_ _
    exact contDiff_const.sub contDiff_id
  have hgb01 : ∀ t : ℝ, 0 ≤ gb t ∧ gb t ≤ 1 := by
    intro t
    rw [hgbdef]
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hgb1 : ∀ t : ℝ, t ≤ Real.cosh (R + 1 / 2) → gb t = 1 := by
    intro t ht
    rw [hgbdef]
    refine Real.smoothTransition.one_of_one_le ?_
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hgb0 : ∀ t : ℝ, Real.cosh (R + 1) ≤ t → gb t = 0 := by
    intro t ht
    rw [hgbdef]
    refine Real.smoothTransition.zero_of_nonpos ?_
    have h1 : Real.cosh (R + 1) - t ≤ 0 := by linarith
    exact div_nonpos_of_nonpos_of_nonneg h1 (by linarith)
  -- the atoms
  obtain ⟨aψ, haψdef⟩ : ∃ a : ↥Γ' → ℂ → ℝ, a = fun γ z =>
      gb (1 + Complex.normSq (z - ((γ • τ₀ : UpperHalfPlane) : ℂ))
        / (2 * z.im * ((γ • τ₀ : UpperHalfPlane) : ℂ).im)) := ⟨_, rfl⟩
  have haψbridge : ∀ (γ : ↥Γ') (τ : UpperHalfPlane),
      aψ γ (τ : ℂ) = gb (Real.cosh (dist τ (γ • τ₀))) := by
    intro γ τ
    rw [haψdef]
    exact zz_atom_bridge gb (γ • τ₀) τ
  have haψ01 : ∀ (γ : ↥Γ') (z : ℂ), 0 ≤ aψ γ z ∧ aψ γ z ≤ 1 := by
    intro γ z
    rw [haψdef]
    exact hgb01 _
  have haψvanish : ∀ (γ : ↥Γ') (τ : UpperHalfPlane), R + 1 ≤ dist τ (γ • τ₀) →
      aψ γ (τ : ℂ) = 0 := by
    intro γ τ hfar
    rw [haψdef]
    exact zz_atom_vanish gb R hRpos.le hgb0 (γ • τ₀) τ hfar
  have haψplateau : ∀ (γ : ↥Γ') (τ : UpperHalfPlane), dist τ (γ • τ₀) ≤ R + 1 / 2 →
      aψ γ (τ : ℂ) = 1 := by
    intro γ τ hnear
    rw [haψbridge]
    refine hgb1 _ ?_
    have h1 : |dist τ (γ • τ₀)| ≤ |R + 1 / 2| := by
      rw [abs_of_nonneg dist_nonneg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ R + 1 / 2)]
      exact hnear
    exact Real.cosh_le_cosh.mpr h1
  have haψsm : ∀ (γ : ↥Γ') (z₀ : ℂ), 0 < z₀.im → ContDiffAt ℝ 1 (aψ γ) z₀ := by
    intro γ z₀ hz₀
    rw [haψdef]
    exact zz_atom_contDiffAt gb hgbsm (γ • τ₀) z₀ hz₀
  obtain ⟨Ψs, hΨdef⟩ : ∃ P : ℂ → ℝ, P = fun z => ∑' γ : ↥Γ', aψ γ z := ⟨_, rfl⟩
  have hrep : ∀ z₀ : ℂ, 0 < z₀.im → ∃ r : ℝ, 0 < r ∧ ∃ F : Finset ↥Γ',
      (∀ z ∈ Metric.ball z₀ r, 0 < z.im) ∧
      (∀ z ∈ Metric.ball z₀ r, ∀ γ : ↥Γ', γ ∉ F → aψ γ z = 0) := by
    intro z₀ hz₀
    obtain ⟨r, hr, F, hFfin, hball, hvan⟩ := zz_locfin hΓ'fuchs τ₀ R z₀ hz₀
    refine ⟨r, hr, hFfin.toFinset, hball, ?_⟩
    intro z hz γ hγ
    have hzim := hball z hz
    have hfar := hvan z hz hzim γ (by
      intro hmem'
      exact hγ (hFfin.mem_toFinset.mpr hmem'))
    exact haψvanish γ ⟨z, hzim⟩ hfar
  have hΨrep : ∀ z₀ : ℂ, 0 < z₀.im → ∃ r : ℝ, 0 < r ∧ ∃ F : Finset ↥Γ',
      (∀ z ∈ Metric.ball z₀ r, 0 < z.im) ∧
      (∀ z ∈ Metric.ball z₀ r, ∀ γ : ↥Γ', γ ∉ F → aψ γ z = 0) ∧
      ∀ z ∈ Metric.ball z₀ r, Ψs z = ∑ γ ∈ F, aψ γ z := by
    intro z₀ hz₀
    obtain ⟨r, hr, F, hball, hvan⟩ := hrep z₀ hz₀
    refine ⟨r, hr, F, hball, hvan, ?_⟩
    intro z hz
    rw [hΨdef]
    exact tsum_eq_sum (fun γ hγ => hvan z hz γ hγ)
  have hΨge1 : ∀ z : ℂ, 0 < z.im → 1 ≤ Ψs z := by
    intro z hz
    obtain ⟨r, hr, F, hball, hvan, hsum⟩ := hΨrep z hz
    have hzmem : z ∈ Metric.ball z r := Metric.mem_ball_self hr
    rw [hsum z hzmem]
    have h1 : Metric.infDist (⟨z, hz⟩ : UpperHalfPlane) (MulAction.orbit (↥Γ') τ₀) ≤ R :=
      hdense _
    have hne : (MulAction.orbit (↥Γ') τ₀).Nonempty := ⟨τ₀, MulAction.mem_orbit_self τ₀⟩
    obtain ⟨y, hymem, hylt⟩ := (Metric.infDist_lt_iff hne).mp
      (lt_of_le_of_lt h1 (by linarith : R < R + 1 / 2))
    obtain ⟨γd, rfl⟩ := MulAction.mem_orbit_iff.mp hymem
    have hone : aψ γd z = 1 := haψplateau γd ⟨z, hz⟩ hylt.le
    have hγdF : γd ∈ F := by
      by_contra hγd
      have h0 := hvan z hzmem γd hγd
      rw [h0] at hone
      norm_num at hone
    calc (1 : ℝ) = aψ γd z := hone.symm
      _ ≤ ∑ γ ∈ F, aψ γ z :=
          Finset.single_le_sum (fun γ _ => (haψ01 γ z).1) hγdF
  -- the regions
  obtain ⟨UK, hUKdef⟩ : ∃ U : Set ℂ, U = Metric.ball ((((τ₀ : ℂ).re : ℝ) : ℂ)
      + ((τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ) * Complex.I)
      (τ₀.im * Real.sinh (R + 2)) := ⟨_, rfl⟩
  have hUKchar : ∀ z : ℂ, z ∈ UK ↔
      ∃ hz : 0 < z.im, dist (⟨z, hz⟩ : UpperHalfPlane) τ₀ < R + 2 := by
    intro z
    rw [hUKdef]
    exact zz_ball τ₀ (R + 2) (by linarith) z
  have hUKopen : IsOpen UK := by
    rw [hUKdef]
    exact Metric.isOpen_ball
  have hUKsub : UK ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    obtain ⟨hzim, _⟩ := (hUKchar z).mp hz
    exact hzim
  obtain ⟨UKb, hUKbdef⟩ : ∃ U : Set ℂ, U = Metric.ball ((((τ₀ : ℂ).re : ℝ) : ℂ)
      + ((τ₀.im * Real.cosh (R + 3 / 2) : ℝ) : ℂ) * Complex.I)
      (τ₀.im * Real.sinh (R + 3 / 2)) := ⟨_, rfl⟩
  have hUKbchar : ∀ z : ℂ, z ∈ UKb ↔
      ∃ hz : 0 < z.im, dist (⟨z, hz⟩ : UpperHalfPlane) τ₀ < R + 3 / 2 := by
    intro z
    rw [hUKbdef]
    exact zz_ball τ₀ (R + 3 / 2) (by linarith) z
  have hUKbopen : IsOpen UKb := by
    rw [hUKbdef]
    exact Metric.isOpen_ball
  have hUKbconv : Convex ℝ UKb := by
    rw [hUKbdef]
    exact convex_ball _ _
  have hUKbUK : UKb ⊆ UK := by
    intro z hz
    obtain ⟨hzim, hd⟩ := (hUKbchar z).mp hz
    exact (hUKchar z).mpr ⟨hzim, by linarith⟩
  -- the closed inner region for the compactness bound
  obtain ⟨K1c, hK1cdef⟩ : ∃ K : Set ℂ, K = Metric.closedBall ((((τ₀ : ℂ).re : ℝ) : ℂ)
      + ((τ₀.im * Real.cosh (R + 3 / 2) : ℝ) : ℂ) * Complex.I)
      (τ₀.im * Real.sinh (R + 3 / 2)) := ⟨_, rfl⟩
  have hK1ccomp : IsCompact K1c := by
    rw [hK1cdef]
    exact isCompact_closedBall _ _
  have hUKbK1c : UKb ⊆ K1c := by
    rw [hUKbdef, hK1cdef]
    exact Metric.ball_subset_closedBall
  have hK1cUK : K1c ⊆ UK := by
    rw [hK1cdef, hUKdef]
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    have hcd : dist ((((τ₀ : ℂ).re : ℝ) : ℂ)
        + ((τ₀.im * Real.cosh (R + 3 / 2) : ℝ) : ℂ) * Complex.I)
        ((((τ₀ : ℂ).re : ℝ) : ℂ)
        + ((τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ) * Complex.I)
        = τ₀.im * Real.cosh (R + 2) - τ₀.im * Real.cosh (R + 3 / 2) := by
      rw [dist_eq_norm]
      have he : ((((τ₀ : ℂ).re : ℝ) : ℂ)
          + ((τ₀.im * Real.cosh (R + 3 / 2) : ℝ) : ℂ) * Complex.I)
          - ((((τ₀ : ℂ).re : ℝ) : ℂ)
          + ((τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ) * Complex.I)
          = ((τ₀.im * Real.cosh (R + 3 / 2) - τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ)
            * Complex.I := by
        push_cast
        ring
      rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonpos ?_]
      · ring
      · have hmn : Real.cosh (R + 3 / 2) ≤ Real.cosh (R + 2) := by
          rw [Real.cosh_le_cosh, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          linarith
        nlinarith [hmn, hτ₀im]
    have htri := dist_triangle z ((((τ₀ : ℂ).re : ℝ) : ℂ)
        + ((τ₀.im * Real.cosh (R + 3 / 2) : ℝ) : ℂ) * Complex.I)
        ((((τ₀ : ℂ).re : ℝ) : ℂ) + ((τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ) * Complex.I)
    rw [hcd] at htri
    have hkey : τ₀.im * Real.sinh (R + 3 / 2) + τ₀.im * Real.cosh (R + 2)
        - τ₀.im * Real.cosh (R + 3 / 2) < τ₀.im * Real.sinh (R + 2) := by
      have h1 : Real.cosh (R + 2) - Real.sinh (R + 2)
          < Real.cosh (R + 3 / 2) - Real.sinh (R + 3 / 2) := by
        rw [Real.cosh_sub_sinh, Real.cosh_sub_sinh]
        refine Real.exp_lt_exp.mpr ?_
        linarith
      nlinarith [h1, hτ₀im]
    linarith
  -- the active set
  obtain ⟨SACT, hSACTdef⟩ : ∃ S : Finset ↥Γ',
      S = (hSfin (2 * R + 4)).toFinset := ⟨_, rfl⟩
  have hSACTmem : ∀ γ : ↥Γ', γ ∈ SACT ↔ dist τ₀ (γ • τ₀) ≤ 2 * R + 4 := by
    intro γ
    rw [hSACTdef, Set.Finite.mem_toFinset]
    rfl
  have hSACTvan : ∀ z ∈ UK, ∀ γ : ↥Γ', γ ∉ SACT → aψ γ z = 0 := by
    intro z hz γ hγ
    obtain ⟨hzim, hzd⟩ := (hUKchar z).mp hz
    rw [hSACTmem] at hγ
    push Not at hγ
    refine haψvanish γ ⟨z, hzim⟩ ?_
    have htri := dist_triangle τ₀ (⟨z, hzim⟩ : UpperHalfPlane) (γ • τ₀)
    have hcomm : dist τ₀ (⟨z, hzim⟩ : UpperHalfPlane)
        = dist (⟨z, hzim⟩ : UpperHalfPlane) τ₀ := dist_comm _ _
    linarith
  have hΨrepUK : ∀ z ∈ UK, Ψs z = ∑ γ ∈ SACT, aψ γ z := by
    intro z hz
    rw [hΨdef]
    exact tsum_eq_sum (fun γ hγ => hSACTvan z hz γ hγ)
  have hΨsmUK : ContDiffOn ℝ 1 Ψs UK := by
    intro z hz
    have hsumsm : ContDiffWithinAt ℝ 1 (fun w => ∑ γ ∈ SACT, aψ γ w) UK z := by
      refine ContDiffWithinAt.sum ?_
      intro γ _
      exact ((haψsm γ z (hUKsub hz)).contDiffWithinAt)
    refine hsumsm.congr_of_eventuallyEq ?_ (hΨrepUK z hz)
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hΨrepUK w hw
  obtain ⟨uψ, huψdef⟩ : ∃ u : ↥Γ' → ℂ → ℝ, u = fun γ z => aψ γ z / Ψs z := ⟨_, rfl⟩
  have hΨne : ∀ z ∈ UK, Ψs z ≠ 0 := by
    intro z hz
    have := hΨge1 z (hUKsub hz)
    linarith
  have huψsm : ∀ γ : ↥Γ', ContDiffOn ℝ 1 (uψ γ) UK := by
    intro γ
    rw [huψdef]
    refine ContDiffOn.div ?_ hΨsmUK hΨne
    intro z hz
    exact (haψsm γ z (hUKsub hz)).contDiffWithinAt
  have hsum1 : ∀ z ∈ UK, ∑ γ ∈ SACT, uψ γ z = 1 := by
    intro z hz
    rw [huψdef]
    simp only
    rw [← Finset.sum_div, ← hΨrepUK z hz, div_self (hΨne z hz)]
  have huψ01 : ∀ (γ : ↥Γ') (z : ℂ), z ∈ UK → 0 ≤ uψ γ z ∧ uψ γ z ≤ 1 := by
    intro γ z hz
    rw [huψdef]
    have h1 := hΨge1 z (hUKsub hz)
    have h2 := haψ01 γ z
    constructor
    · exact div_nonneg h2.1 (by linarith)
    · rw [div_le_one (by linarith)]
      calc aψ γ z ≤ 1 := h2.2
        _ ≤ Ψs z := h1
  -- derivative bounds on the inner ball, from compactness of its closure
  have hBg : ∀ γ : ↥Γ', ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K1c, ‖fderiv ℝ (uψ γ) z‖ ≤ C := by
    intro γ
    have hcont : ContinuousOn (fun z => ‖fderiv ℝ (uψ γ) z‖) K1c := by
      refine ContinuousOn.norm ?_
      refine ((huψsm γ).continuousOn_fderiv_of_isOpen hUKopen le_rfl).mono hK1cUK
    obtain ⟨C, hC⟩ := hK1ccomp.exists_bound_of_continuousOn hcont
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro z hz
    have := hC z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at this
    exact le_trans this (le_max_left _ _)
  choose CB hCB0 hCBle using hBg
  have hSACTne : (SACT : Finset ↥Γ').Nonempty := by
    refine ⟨1, ?_⟩
    rw [hSACTmem]
    rw [show ((1 : ↥Γ') • τ₀) = τ₀ from one_smul _ _, dist_self]
    linarith
  obtain ⟨Mψ, hMψdef⟩ : ∃ M : ℝ, M = SACT.sup' hSACTne CB := ⟨_, rfl⟩
  have hMψle : ∀ γ ∈ SACT, CB γ ≤ Mψ := by
    intro γ hγ
    rw [hMψdef]
    exact Finset.le_sup' CB hγ
  have hMψ0 : 0 ≤ Mψ := by
    obtain ⟨γ0, hγ0⟩ := hSACTne
    exact le_trans (hCB0 γ0) (hMψle γ0 hγ0)
  -- the euclidean size and the imaginary-part floor
  obtain ⟨Rz, hRzdef⟩ : ∃ x : ℝ, x = max (‖(((τ₀ : ℂ).re : ℝ) : ℂ)
      + ((τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ) * Complex.I‖
      + τ₀.im * Real.sinh (R + 2)) 1 := ⟨_, rfl⟩
  have hRz1 : 1 ≤ Rz := by
    rw [hRzdef]
    exact le_max_right _ _
  have hRzUK : ∀ z ∈ UK, ‖z‖ ≤ Rz := by
    intro z hz
    rw [hUKdef, Metric.mem_ball] at hz
    have h1 := norm_sub_norm_le z ((((τ₀ : ℂ).re : ℝ) : ℂ)
        + ((τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ) * Complex.I)
    rw [← dist_eq_norm] at h1
    rw [hRzdef]
    refine le_trans ?_ (le_max_left _ _)
    linarith
  obtain ⟨imK, himKdef⟩ : ∃ x : ℝ, x = τ₀.im * Real.exp (-(R + 2)) := ⟨_, rfl⟩
  have himK0 : 0 < imK := by
    rw [himKdef]
    positivity
  have himUK : ∀ z ∈ UK, imK < z.im := by
    intro z hz
    rw [hUKdef, Metric.mem_ball] at hz
    have hcim : ((((τ₀ : ℂ).re : ℝ) : ℂ)
        + ((τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ) * Complex.I).im
        = τ₀.im * Real.cosh (R + 2) := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_zero, mul_one, add_zero, zero_add]
    have h1 : |(z - ((((τ₀ : ℂ).re : ℝ) : ℂ)
        + ((τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ) * Complex.I)).im|
        ≤ ‖z - ((((τ₀ : ℂ).re : ℝ) : ℂ)
        + ((τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ) * Complex.I)‖ :=
      Complex.abs_im_le_norm _
    rw [Complex.sub_im, hcim, ← dist_eq_norm] at h1
    have h2 := (abs_le.mp h1).1
    have h3 : Real.cosh (R + 2) - Real.sinh (R + 2) = Real.exp (-(R + 2)) :=
      Real.cosh_sub_sinh (R + 2)
    rw [himKdef]
    nlinarith [hz, hτ₀im, h3]
  -- equivariance of the weights
  have hcoesmul : ∀ (β : ↥Γ') (τ : UpperHalfPlane),
      ((β • τ : UpperHalfPlane) : ℂ) = moebiusMap (↑β) (τ : ℂ) :=
    fun β τ => coe_smul_eq_moebiusMap (↑β) τ
  have haψequi : ∀ (β γ : ↥Γ') (z : ℂ), 0 < z.im →
      aψ (β * γ) (moebiusMap (↑β) z) = aψ γ z := by
    intro β γ z hz
    have him : 0 < (moebiusMap (↑β) z).im := moebiusMap_im_pos _ hz
    have hpt : (⟨moebiusMap (↑β) z, him⟩ : UpperHalfPlane) = β • ⟨z, hz⟩ := by
      ext
      rw [hcoesmul β ⟨z, hz⟩]
    have h1 := haψbridge (β * γ) (⟨moebiusMap (↑β) z, him⟩ : UpperHalfPlane)
    have h2 := haψbridge γ (⟨z, hz⟩ : UpperHalfPlane)
    have hd : dist (⟨moebiusMap (↑β) z, him⟩ : UpperHalfPlane) ((β * γ) • τ₀)
        = dist (⟨z, hz⟩ : UpperHalfPlane) (γ • τ₀) := by
      rw [hpt, mul_smul]
      exact dist_smul β _ _
    have hcoe1 : ((⟨moebiusMap (↑β) z, him⟩ : UpperHalfPlane) : ℂ)
        = moebiusMap (↑β) z := rfl
    have hcoe2 : ((⟨z, hz⟩ : UpperHalfPlane) : ℂ) = z := rfl
    rw [hcoe1] at h1
    rw [hcoe2] at h2
    rw [h1, h2, hd]
  have hΨequi : ∀ (β : ↥Γ') (z : ℂ), 0 < z.im →
      Ψs (moebiusMap (↑β) z) = Ψs z := by
    intro β z hz
    rw [hΨdef]
    simp only
    rw [← Equiv.tsum_eq (Equiv.mulLeft β) (fun γ => aψ γ (moebiusMap (↑β) z))]
    refine tsum_congr ?_
    intro δ
    simp only [Equiv.coe_mulLeft]
    exact haψequi β δ z hz
  refine ⟨UK, UKb, SACT, uψ, Mψ, Rz, imK, hUKopen, hUKsub, hUKbopen, hUKbconv, hUKbUK,
    ?_, hRz1, hRzUK, hMψ0, himK0, himUK, huψ01, huψsm, ?_, hsum1, ?_, ?_, ?_, ?_⟩
  · intro z hz hd
    exact (hUKbchar z).mpr ⟨hz, hd⟩
  · intro γ hγ z hz
    exact le_trans (hCBle γ z (hUKbK1c hz)) (hMψle γ hγ)
  · intro z hz γ hγ
    rw [huψdef]
    simp only
    rw [hSACTvan z hz γ hγ, zero_div]
  · intro γ hγ
    rw [← hSACTmem]
    exact hγ
  · intro β γ z hz
    rw [huψdef]
    simp only
    rw [haψequi β γ z hz, hΨequi β z hz]
  · intro z hz
    obtain ⟨r, hr, F, hball, hvan⟩ := hrep z hz
    refine ⟨F, ?_⟩
    intro γ hγ
    rw [huψdef]
    simp only
    rw [hvan z (Metric.mem_ball_self hr) γ hγ, zero_div]

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The conjugation-and-regularity package chains matrix Möbius factorizations at every
-- point; the default heartbeat budget does not cover the elaboration.
/-- **Globalization of the developed map**: from the twisted equivariance of the
coefficient field, transport of base points into the analyzed region and the pointwise
package there, the map `z ↦ 𝔪(B z) z` has nonvanishing denominator, upper-half-plane
values, exact `θ`-equivariance, `C¹` regularity, positive Jacobian and Beltrami quotient
at most `κ` on the whole upper half plane. -/
lemma zz_conjreg {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (θ : ↥Γ' → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (Bf : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (UK UKb : Set ℂ)
    (hUKopen : IsOpen UK) (hUKbUK : UKb ⊆ UK)
    (κ Cb : ℝ) (hκ : 0 < κ) (hCbκ : 2 * Cb ≤ κ)
    (htransport : ∀ z : ℂ, 0 < z.im → ∃ (γ : ↥Γ') (w : ℂ), 0 < w.im ∧ w ∈ UKb ∧
      w = moebiusMap (↑(γ⁻¹ : ↥Γ')) z ∧ z = moebiusMap (↑γ) w)
    (hBequi : ∀ (β : ↥Γ') (z : ℂ), 0 < z.im → Bf (moebiusMap (↑β) z)
      = ((θ β : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        * Bf z * ((((↑β : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹
          : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
    (hdenUK : ∀ z ∈ UK, ((Bf z 1 0 : ℝ) : ℂ) * z + ((Bf z 1 1 : ℝ) : ℂ) ≠ 0)
    (hsmUK : ContDiffOn ℝ 1 (fun z => matMoebius (Bf z) z) UK)
    (hpk : ∀ w ∈ UKb, DifferentiableAt ℝ (fun z => matMoebius (Bf z) z) w ∧
      0 < ((fun z => matMoebius (Bf z) z) w).im ∧
      ‖dzbar (fun z => matMoebius (Bf z) z) w‖ ≤ Cb ∧
      (1 : ℝ) / 2 ≤ ‖dz (fun z => matMoebius (Bf z) z) w‖ ∧
      0 < (fderiv ℝ (fun z => matMoebius (Bf z) z) w).det) :
    (∀ z : ℂ, 0 < z.im →
      ((Bf z 1 0 : ℝ) : ℂ) * z + ((Bf z 1 1 : ℝ) : ℂ) ≠ 0) ∧
    (∀ z : ℂ, 0 < z.im → 0 < ((fun z => matMoebius (Bf z) z) z).im) ∧
    (∀ (β : ↥Γ') (z : ℂ), 0 < z.im →
      (fun z => matMoebius (Bf z) z) (moebiusMap (↑β) z)
        = moebiusMap (θ β) ((fun z => matMoebius (Bf z) z) z)) ∧
    (∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 1 (fun z => matMoebius (Bf z) z) z) ∧
    (∀ z : ℂ, 0 < z.im → 0 < (fderiv ℝ (fun z => matMoebius (Bf z) z) z).det ∧
      ‖dzbar (fun z => matMoebius (Bf z) z) z‖
        ≤ κ * ‖dz (fun z => matMoebius (Bf z) z) z‖) := by
  obtain ⟨hm, hhdef⟩ : ∃ h : ℂ → ℂ, h = fun z => matMoebius (Bf z) z := ⟨_, rfl⟩
  have hopenH : IsOpen {x : ℂ | 0 < x.im} := isOpen_lt continuous_const Complex.continuous_im
  have himhm : ∀ w ∈ UKb, 0 < (hm w).im := by
    intro w hw
    have h := (hpk w hw).2.1
    rw [hhdef]
    exact h
  have hdUKb : ∀ w ∈ UKb, DifferentiableAt ℝ hm w := by
    intro w hw
    have h := (hpk w hw).1
    rw [hhdef]
    exact h
  have hmsmUK : ContDiffOn ℝ 1 hm UK := by
    rw [hhdef]
    exact hsmUK
  have hglob : ∀ z : ℂ, 0 < z.im →
      (((Bf z 1 0 : ℝ) : ℂ) * z + ((Bf z 1 1 : ℝ) : ℂ) ≠ 0) ∧ 0 < (hm z).im := by
    intro z hz
    obtain ⟨γ, w, hwim, hwUKb, hwdef, hzw⟩ := htransport z hz
    obtain ⟨Am, hAm⟩ : ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
        X = ((θ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) :=
      ⟨_, rfl⟩
    obtain ⟨Cm, hCm⟩ : ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
        X = ((((↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹
          : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := ⟨_, rfl⟩
    have hBz : Bf z = Am * (Bf w * Cm) := by
      conv_lhs => rw [hzw]
      rw [hBequi γ w hwim, Matrix.mul_assoc, hAm, hCm]
    have hdenCm : ((Cm 1 0 : ℝ) : ℂ) * z + ((Cm 1 1 : ℝ) : ℂ) ≠ 0 := by
      rw [hCm]
      exact moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt hz)
    have hmCz : matMoebius Cm z = w := by
      rw [hCm, matMoebius_coe, hwdef]
      rfl
    have hdenBC : (((Bf w * Cm) 1 0 : ℝ) : ℂ) * z + (((Bf w * Cm) 1 1 : ℝ) : ℂ) ≠ 0 := by
      rw [zz_matden (Bf w) Cm z hdenCm]
      refine mul_ne_zero ?_ hdenCm
      rw [hmCz]
      exact hdenUK w (hUKbUK hwUKb)
    have hmBCz : matMoebius (Bf w * Cm) z = matMoebius (Bf w) w := by
      rw [zz_matmul (Bf w) Cm z hdenCm hdenBC, hmCz]
    have hdenθ : moebiusDenom (θ γ) (hm w) ≠ 0 :=
      moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt (himhm w hwUKb))
    have hdenθ' : ((Am 1 0 : ℝ) : ℂ) * matMoebius (Bf w * Cm) z
        + ((Am 1 1 : ℝ) : ℂ) ≠ 0 := by
      rw [hmBCz, hAm]
      have hh : matMoebius (Bf w) w = hm w := by
        rw [hhdef]
      rw [hh]
      exact hdenθ
    have hdenABC : (((Am * (Bf w * Cm)) 1 0 : ℝ) : ℂ) * z
        + (((Am * (Bf w * Cm)) 1 1 : ℝ) : ℂ) ≠ 0 := by
      rw [zz_matden Am (Bf w * Cm) z hdenBC]
      exact mul_ne_zero hdenθ' hdenBC
    constructor
    · rw [hBz]
      exact hdenABC
    · have hval : matMoebius (Bf z) z = moebiusMap (θ γ) (matMoebius (Bf w) w) := by
        rw [hBz, zz_matmul Am (Bf w * Cm) z hdenBC hdenABC, hmBCz, hAm, matMoebius_coe]
      have hgoal : hm z = moebiusMap (θ γ) (hm w) := by
        rw [hhdef]
        exact hval
      rw [hgoal]
      exact moebiusMap_im_pos _ (himhm w hwUKb)
  have hdenglobal : ∀ z : ℂ, 0 < z.im →
      ((Bf z 1 0 : ℝ) : ℂ) * z + ((Bf z 1 1 : ℝ) : ℂ) ≠ 0 := fun z hz => (hglob z hz).1
  have himglobal : ∀ z : ℂ, 0 < z.im → 0 < (hm z).im := fun z hz => (hglob z hz).2
  have hequi : ∀ (β : ↥Γ') (z : ℂ), 0 < z.im →
      hm (moebiusMap (↑β) z) = moebiusMap (θ β) (hm z) := by
    intro β z hz
    have hzim' : 0 < (moebiusMap (↑β) z).im := moebiusMap_im_pos _ hz
    obtain ⟨Am, hAm⟩ : ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
        X = ((θ β : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) :=
      ⟨_, rfl⟩
    obtain ⟨Cm, hCm⟩ : ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
        X = ((((↑β : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹
          : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := ⟨_, rfl⟩
    have hBz : Bf (moebiusMap (↑β) z) = Am * (Bf z * Cm) := by
      rw [hBequi β z hz, Matrix.mul_assoc, hAm, hCm]
    have hdenCm : ((Cm 1 0 : ℝ) : ℂ) * (moebiusMap (↑β) z) + ((Cm 1 1 : ℝ) : ℂ) ≠ 0 := by
      rw [hCm]
      exact moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt hzim')
    have hmCz : matMoebius Cm (moebiusMap (↑β) z) = z := by
      rw [hCm, matMoebius_coe]
      rw [moebiusMap_mul ((↑β : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ (↑β) z
        (moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt hz))]
      rw [inv_mul_cancel, moebiusMap_one]
    have hdenBC : (((Bf z * Cm) 1 0 : ℝ) : ℂ) * (moebiusMap (↑β) z)
        + (((Bf z * Cm) 1 1 : ℝ) : ℂ) ≠ 0 := by
      rw [zz_matden (Bf z) Cm _ hdenCm]
      refine mul_ne_zero ?_ hdenCm
      rw [hmCz]
      exact hdenglobal z hz
    have hmBC : matMoebius (Bf z * Cm) (moebiusMap (↑β) z) = matMoebius (Bf z) z := by
      rw [zz_matmul (Bf z) Cm _ hdenCm hdenBC, hmCz]
    have hdenABC : (((Am * (Bf z * Cm)) 1 0 : ℝ) : ℂ) * (moebiusMap (↑β) z)
        + (((Am * (Bf z * Cm)) 1 1 : ℝ) : ℂ) ≠ 0 := by
      rw [zz_matden Am (Bf z * Cm) _ hdenBC]
      refine mul_ne_zero ?_ hdenBC
      rw [hmBC, hAm]
      have hh : matMoebius (Bf z) z = hm z := by
        rw [hhdef]
      rw [hh]
      exact moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt (himglobal z hz))
    have hval : matMoebius (Bf (moebiusMap (↑β) z)) (moebiusMap (↑β) z)
        = moebiusMap (θ β) (matMoebius (Bf z) z) := by
      rw [hBz, zz_matmul Am (Bf z * Cm) _ hdenBC hdenABC, hmBC, hAm, matMoebius_coe]
    rw [hhdef]
    exact hval
  have hEEglob : ∀ (γ : ↥Γ') (x : ℂ), 0 < x.im →
      hm x = moebiusMap (θ γ) (hm (moebiusMap (↑(γ⁻¹ : ↥Γ')) x)) := by
    intro γ x hx
    have hxin : 0 < (moebiusMap (↑(γ⁻¹ : ↥Γ')) x).im := moebiusMap_im_pos _ hx
    have h := hequi γ (moebiusMap (↑(γ⁻¹ : ↥Γ')) x) hxin
    have hcancel : moebiusMap (↑γ) (moebiusMap (↑(γ⁻¹ : ↥Γ')) x) = x := by
      rw [moebiusMap_mul (↑γ) (↑(γ⁻¹ : ↥Γ')) x
        (moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt hx))]
      have hone : (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) * (↑(γ⁻¹ : ↥Γ')) = 1 := by
        rw [← Subgroup.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
      rw [hone, moebiusMap_one]
    rwa [hcancel] at h
  have hmC1 : ∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 1 hm z := by
    intro z hz
    obtain ⟨γ, w, hwim, hwUKb, hwdef, hzw⟩ := htransport z hz
    have hinner : ContDiffAt ℝ 1 (moebiusMap (↑(γ⁻¹ : ↥Γ'))) z :=
      zz_moeb_cdiff _ z hz
    have hmid : ContDiffAt ℝ 1 hm (moebiusMap (↑(γ⁻¹ : ↥Γ')) z) := by
      rw [← hwdef]
      exact (hmsmUK w (hUKbUK hwUKb)).contDiffAt (hUKopen.mem_nhds (hUKbUK hwUKb))
    have houter : ContDiffAt ℝ 1 (moebiusMap (θ γ))
        (hm (moebiusMap (↑(γ⁻¹ : ↥Γ')) z)) := by
      refine zz_moeb_cdiff _ _ ?_
      rw [← hwdef]
      exact himhm w hwUKb
    refine ((ContDiffAt.comp z houter (ContDiffAt.comp z hmid hinner)).congr_of_eventuallyEq
      ?_)
    filter_upwards [hopenH.mem_nhds hz] with x hx
    exact hEEglob γ x hx
  have hjb : ∀ z : ℂ, 0 < z.im →
      0 < (fderiv ℝ hm z).det ∧ ‖dzbar hm z‖ ≤ κ * ‖dz hm z‖ := by
    intro z hz
    obtain ⟨γ, w, hwim, hwUKb, hwdef, hzw⟩ := htransport z hz
    obtain ⟨hdw0, _, hbarw0, hdzw0, hdetw0⟩ := hpk w hwUKb
    have hdw : DifferentiableAt ℝ hm w := by
      rw [hhdef]
      exact hdw0
    have hbarw : ‖dzbar hm w‖ ≤ Cb := by
      rw [hhdef]
      exact hbarw0
    have hdzw : (1 : ℝ) / 2 ≤ ‖dz hm w‖ := by
      rw [hhdef]
      exact hdzw0
    have hdetw : 0 < (fderiv ℝ hm w).det := by
      rw [hhdef]
      exact hdetw0
    obtain ⟨hdz', him', q₁, q₂, hq1ne, hqeq, hdzq, hdzbarq⟩ :=
      zz_transport (θ γ) (↑(γ⁻¹ : ↥Γ')) hm z w hz hwim hwdef (hEEglob γ) hdw
        (himhm w hwUKb)
    have hq1pos : 0 < ‖q₁‖ := norm_pos_iff.mpr hq1ne
    have hbase : ‖dzbar hm w‖ ≤ κ * ‖dz hm w‖ := by
      have h2 : κ / 2 ≤ κ * ‖dz hm w‖ := by
        have h3 := mul_le_mul_of_nonneg_left hdzw hκ.le
        linarith [h3]
      linarith [hbarw, hCbκ, h2]
    constructor
    · rw [det_fderiv_eq_wirtinger, hdzq, hdzbarq, norm_mul, norm_mul, ← hqeq]
      have hdet2 : 0 < ‖dz hm w‖ ^ 2 - ‖dzbar hm w‖ ^ 2 := by
        rw [← det_fderiv_eq_wirtinger]
        exact hdetw
      have h4 : 0 < ‖q₁‖ ^ 2 * (‖dz hm w‖ ^ 2 - ‖dzbar hm w‖ ^ 2) :=
        mul_pos (pow_pos hq1pos 2) hdet2
      nlinarith [h4]
    · rw [hdzq, hdzbarq, norm_mul, norm_mul, ← hqeq]
      calc ‖q₁‖ * ‖dzbar hm w‖ ≤ ‖q₁‖ * (κ * ‖dz hm w‖) :=
            mul_le_mul_of_nonneg_left hbase hq1pos.le
        _ = κ * (‖q₁‖ * ‖dz hm w‖) := by ring
  refine ⟨hdenglobal, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have h := himglobal z hz
    rwa [hhdef] at h
  · intro β z hz
    have h := hequi β z hz
    rwa [hhdef] at h
  · intro z hz
    have h := hmC1 z hz
    rwa [hhdef] at h
  · intro z hz
    have h := hjb z hz
    rwa [hhdef] at h

end RiemannDynamics

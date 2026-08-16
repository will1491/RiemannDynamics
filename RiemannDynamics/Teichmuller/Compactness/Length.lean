/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.Foundations.Metric
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Translation length, systole and the thick part

The translation length of `A ∈ SL(2, ℝ)` on the upper half plane is
`2 arcosh (max 1 (|tr A| / 2))`: it vanishes for elliptic, parabolic and central elements and
equals the infimum of the displacement `dist τ (A • τ)` for hyperbolic ones, computed by
diagonalizing `A` and minimizing the displacement of `τ ↦ λ² τ` along the imaginary axis. The
clamp `max 1` absorbs the junk negative values of `arcosh` below `1`, making the length
total. The systole of a Teichmüller representative is the infimal translation length of the
nontrivially-acting elements of its Fuchsian group; it descends to Teichmüller space, whose
`ε`-thick part it defines. The hyperbolic area of balls in the upper half plane and its
`SL(2, ℝ)`-invariance provide the volume data for the packing arguments.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-! ## Translation length -/

/-- The **translation length** of `A ∈ SL(2, ℝ)` acting on the upper half plane:
`2 arcosh (max 1 (|tr A| / 2))`. The clamp `max 1` makes the value `0` for `|tr A| ≤ 2`
(elliptic, parabolic and central elements) and positive exactly for hyperbolic ones. -/
noncomputable def translationLength (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) : ℝ :=
  2 * Real.arcosh (max 1 (|Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ)| / 2))

/-- Translation length is nonnegative. -/
theorem translationLength_nonneg (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    0 ≤ translationLength A := by
  have h := Real.arcosh_nonneg
    (le_max_left 1 (|Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ)| / 2))
  unfold translationLength
  linarith

/-- Translation length is positive exactly for hyperbolic matrices: `|tr| > 2` is
`tr² − 4 > 0`, the sign of the discriminant. -/
theorem translationLength_pos_iff (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    0 < translationLength A ↔ (A : Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic := by
  have hdet : ((A : Matrix (Fin 2) (Fin 2) ℝ)).det = 1 := Matrix.SpecialLinearGroup.det_coe A
  have hhyp : (A : Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic ↔
      4 < Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 := by
    unfold Matrix.IsHyperbolic
    rw [Matrix.discr_fin_two, hdet]
    constructor <;> intro h <;> linarith
  rw [hhyp]
  unfold translationLength
  constructor
  · intro h
    by_contra hle
    rw [not_lt] at hle
    have h2 : |Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ)| / 2 ≤ 1 := by
      nlinarith [sq_abs (Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ)),
        abs_nonneg (Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ))]
    rw [max_eq_left h2, Real.arcosh_zero] at h
    norm_num at h
  · intro h
    have h2 : 1 < |Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ)| / 2 := by
      nlinarith [sq_abs (Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ)),
        abs_nonneg (Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ))]
    rw [max_eq_right h2.le]
    have h3 := Real.arcosh_pos h2
    linarith

/-- The diagonal element `!![λ, 0; 0, λ⁻¹]` of `SL(2, ℝ)`. -/
noncomputable def diagSL2 (lam : ℝ) (hlam : lam ≠ 0) :
    Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![lam, 0; 0, lam⁻¹], by rw [Matrix.det_fin_two_of]; simp [mul_inv_cancel₀ hlam]⟩

/-- Diagonalization of hyperbolic elements of `SL(2, ℝ)`: a matrix with `tr² > 4` has real
distinct eigenvalues `λ, λ⁻¹` and is conjugate within `SL(2, ℝ)` to `!![λ, 0; 0, λ⁻¹]`. -/
theorem sl2_hyperbolic_diagonalization (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : (A : Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic) :
    ∃ (P : Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam : ℝ) (hlam : lam ≠ 0),
      1 < lam ^ 2 ∧ P * A * P⁻¹ = diagSL2 lam hlam := by
  have hA4 : 4 < Matrix.trace ((A : Matrix (Fin 2) (Fin 2) ℝ)) ^ 2 := by
    unfold Matrix.IsHyperbolic at hA
    rw [Matrix.discr_fin_two, Matrix.SpecialLinearGroup.det_coe] at hA
    linarith
  -- the b ≠ 0 core: an eigenvector matrix conjugating B into diagonal form
  have main : ∀ B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      4 < Matrix.trace ((B : Matrix (Fin 2) (Fin 2) ℝ)) ^ 2 →
      (B : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ≠ 0 →
      ∃ (R : Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam : ℝ) (hlam : lam ≠ 0),
        1 < lam ^ 2 ∧ B * R = R * diagSL2 lam hlam := by
    intro B htB hb01
    obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d, (B : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d] :=
      ⟨_, _, _, _, Matrix.eta_fin_two _⟩
    rw [hM, Matrix.trace_fin_two_of] at htB
    rw [hM] at hb01
    have hb : b ≠ 0 := by simpa using hb01
    have hdet : a * d - b * c = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe B
      rwa [hM, Matrix.det_fin_two_of] at h
    have hs4 : (0:ℝ) < (a + d) ^ 2 - 4 := by linarith
    obtain ⟨s, hs, hs2⟩ : ∃ s : ℝ, 0 < s ∧ s ^ 2 = (a + d) ^ 2 - 4 :=
      ⟨Real.sqrt ((a + d) ^ 2 - 4), Real.sqrt_pos.mpr hs4, Real.sq_sqrt hs4.le⟩
    -- eigenvalue-pair core
    have core : ∀ lam mu : ℝ, lam + mu = a + d → lam * mu = 1 → mu - lam ≠ 0 → 1 < lam ^ 2 →
        ∃ (R : Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam' : ℝ) (hlam' : lam' ≠ 0),
          1 < lam' ^ 2 ∧ B * R = R * diagSL2 lam' hlam' := by
      intro lam mu hsum hprod hne h1
      have hlam : lam ≠ 0 := left_ne_zero_of_mul_eq_one hprod
      have hmu : lam⁻¹ = mu := (eq_inv_of_mul_eq_one_right hprod).symm
      have hql : lam ^ 2 - (a + d) * lam + 1 = 0 := by linear_combination lam * hsum - hprod
      have hqm : mu ^ 2 - (a + d) * mu + 1 = 0 := by linear_combination mu * hsum - hprod
      have hδ : b * (mu - lam) ≠ 0 := mul_ne_zero hb hne
      have hRdet : Matrix.det !![b / (b * (mu - lam)), b;
          (lam - a) / (b * (mu - lam)), mu - a] = 1 := by
        rw [Matrix.det_fin_two_of]
        field_simp
        ring
      -- bind the eigenvector matrix at the group type so that `coe_mul` matches the products
      obtain ⟨R, hR⟩ : ∃ R : Matrix.SpecialLinearGroup (Fin 2) ℝ,
          (R : Matrix (Fin 2) (Fin 2) ℝ) =
            !![b / (b * (mu - lam)), b; (lam - a) / (b * (mu - lam)), mu - a] :=
        ⟨⟨_, hRdet⟩, rfl⟩
      refine ⟨R, lam, hlam, h1, ?_⟩
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hM, hR,
        show ((diagSL2 lam hlam : Matrix (Fin 2) (Fin 2) ℝ)) = !![lam, 0; 0, lam⁻¹] from rfl,
        hmu]
      ext i j
      fin_cases i <;> fin_cases j
      · -- entry (0,0)
        simp only [Matrix.mul_apply, Fin.sum_univ_two]
        simp
        field_simp
        ring
      · -- entry (0,1)
        simp only [Matrix.mul_apply, Fin.sum_univ_two]
        simp
        ring
      · -- entry (1,0)
        simp only [Matrix.mul_apply, Fin.sum_univ_two]
        simp
        field_simp
        linear_combination -hql - hdet
      · -- entry (1,1)
        simp only [Matrix.mul_apply, Fin.sum_univ_two]
        simp
        linear_combination -hqm - hdet
    rcases le_or_gt 0 (a + d) with ht | ht
    · -- 0 ≤ a + d: the larger root (a + d + s)/2 exceeds 1
      have ht2 : 2 < a + d := by nlinarith
      refine core ((a + d + s) / 2) ((a + d - s) / 2) (by ring) ?_ ?_ ?_
      · linear_combination (-(1:ℝ)/4) * hs2
      · intro h0
        have hs0 : s = 0 := by linarith
        exact hs.ne' hs0
      · nlinarith [mul_pos (by linarith : (0:ℝ) < a + d + s - 2)
          (by linarith : (0:ℝ) < a + d + s + 2)]
    · -- a + d < 0: the smaller root (a + d - s)/2 is below -1
      have ht2 : a + d < -2 := by nlinarith
      refine core ((a + d - s) / 2) ((a + d + s) / 2) (by ring) ?_ ?_ ?_
      · linear_combination (-(1:ℝ)/4) * hs2
      · intro h0
        have hs0 : s = 0 := by linarith
        exact hs.ne' hs0
      · nlinarith [mul_pos (by linarith : (0:ℝ) < -(a + d - s) - 2)
          (by linarith : (0:ℝ) < -(a + d - s) + 2)]
  -- transfer through an explicit conjugation
  have transfer : ∀ S Sinv : Matrix.SpecialLinearGroup (Fin 2) ℝ, S * Sinv = 1 →
      4 < Matrix.trace (((S * A * Sinv : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ)) ^ 2 →
      ((S * A * Sinv : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) 0 1 ≠ 0 →
      ∃ (P : Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam : ℝ) (hlam : lam ≠ 0),
        1 < lam ^ 2 ∧ P * A * P⁻¹ = diagSL2 lam hlam := by
    intro S Sinv hSS htrB hB01
    obtain ⟨R, lam, hlam, h1, hBR⟩ := main (S * A * Sinv) htrB hB01
    have hSinv : Sinv = S⁻¹ := eq_inv_of_mul_eq_one_right hSS
    refine ⟨R⁻¹ * S, lam, hlam, h1, ?_⟩
    have hgrp : R⁻¹ * S * A * (R⁻¹ * S)⁻¹ = R⁻¹ * (S * A * Sinv) * R := by
      rw [hSinv]
      group
    rw [hgrp, mul_assoc, hBR, inv_mul_cancel_left]
  by_cases hb : (A : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0
  · by_cases hc : (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0
    · -- diagonal matrix: conjugate by the shear !![1, 1; 0, 1]
      have hT1 : Matrix.det !![(1:ℝ), 1; 0, 1] = 1 := by
        rw [Matrix.det_fin_two_of]
        norm_num
      have hT2 : Matrix.det !![(1:ℝ), -1; 0, 1] = 1 := by
        rw [Matrix.det_fin_two_of]
        norm_num
      obtain ⟨T, hTc⟩ : ∃ T : Matrix.SpecialLinearGroup (Fin 2) ℝ,
          (T : Matrix (Fin 2) (Fin 2) ℝ) = !![(1:ℝ), 1; 0, 1] := ⟨⟨_, hT1⟩, rfl⟩
      obtain ⟨Tinv, hTc2⟩ : ∃ Tinv : Matrix.SpecialLinearGroup (Fin 2) ℝ,
          (Tinv : Matrix (Fin 2) (Fin 2) ℝ) = !![(1:ℝ), -1; 0, 1] := ⟨⟨_, hT2⟩, rfl⟩
      have hTT : T * Tinv = 1 := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul, hTc, hTc2, Matrix.SpecialLinearGroup.coe_one,
          Matrix.mul_fin_two, Matrix.one_fin_two]
        norm_num
      have hTAT : ((T * A * Tinv : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) =
          !![(A : Matrix (Fin 2) (Fin 2) ℝ) 0 0,
            (A : Matrix (Fin 2) (Fin 2) ℝ) 1 1 - (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0;
            0, (A : Matrix (Fin 2) (Fin 2) ℝ) 1 1] := by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hTc, hTc2,
          Matrix.eta_fin_two ((A : Matrix (Fin 2) (Fin 2) ℝ)), hb, hc, Matrix.mul_fin_two,
          Matrix.mul_fin_two]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
            Matrix.cons_val_fin_one, Matrix.cons_val_one] <;>
          ring_nf
      refine transfer T Tinv hTT ?_ ?_
      · rw [hTAT, Matrix.trace_fin_two_of]
        rw [Matrix.trace_fin_two] at hA4
        nlinarith [hA4]
      · rw [hTAT]
        have hd : (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (A : Matrix (Fin 2) (Fin 2) ℝ) 1 1
            = 1 := by
          have h := Matrix.SpecialLinearGroup.det_coe A
          rw [Matrix.det_fin_two, hb, hc] at h
          simpa using h
        rw [Matrix.trace_fin_two] at hA4
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.cons_val_one]
        intro h0
        have h11 : (A : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by
          linarith
        rw [h11] at hA4 hd
        nlinarith [hA4, hd]
    · -- lower-left entry nonzero: conjugate by the rotation !![0, -1; 1, 0]
      have hS1 : Matrix.det !![(0:ℝ), -1; 1, 0] = 1 := by
        rw [Matrix.det_fin_two_of]
        norm_num
      have hS2 : Matrix.det !![(0:ℝ), 1; -1, 0] = 1 := by
        rw [Matrix.det_fin_two_of]
        norm_num
      obtain ⟨S, hSc⟩ : ∃ S : Matrix.SpecialLinearGroup (Fin 2) ℝ,
          (S : Matrix (Fin 2) (Fin 2) ℝ) = !![(0:ℝ), -1; 1, 0] := ⟨⟨_, hS1⟩, rfl⟩
      obtain ⟨Sinv, hSc2⟩ : ∃ Sinv : Matrix.SpecialLinearGroup (Fin 2) ℝ,
          (Sinv : Matrix (Fin 2) (Fin 2) ℝ) = !![(0:ℝ), 1; -1, 0] := ⟨⟨_, hS2⟩, rfl⟩
      have hSS : S * Sinv = 1 := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul, hSc, hSc2, Matrix.SpecialLinearGroup.coe_one,
          Matrix.mul_fin_two, Matrix.one_fin_two]
        norm_num
      have hSAS : ((S * A * Sinv : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) =
          !![(A : Matrix (Fin 2) (Fin 2) ℝ) 1 1, -(A : Matrix (Fin 2) (Fin 2) ℝ) 1 0;
            -(A : Matrix (Fin 2) (Fin 2) ℝ) 0 1, (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0] := by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hSc, hSc2,
          Matrix.eta_fin_two ((A : Matrix (Fin 2) (Fin 2) ℝ)), Matrix.mul_fin_two,
          Matrix.mul_fin_two]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
            Matrix.cons_val_fin_one, Matrix.cons_val_one] <;>
          ring_nf
      refine transfer S Sinv hSS ?_ ?_
      · rw [hSAS, Matrix.trace_fin_two_of]
        rw [Matrix.trace_fin_two] at hA4
        nlinarith [hA4]
      · rw [hSAS]
        simpa using hc
  · -- upper-right entry nonzero: apply the core directly
    obtain ⟨R, lam, hlam, h1, hBR⟩ := main A hA4 hb
    refine ⟨R⁻¹, lam, hlam, h1, ?_⟩
    rw [inv_inv, mul_assoc, hBR, inv_mul_cancel_left]

/-- The diagonal element acts on the upper half plane as scaling by `λ²`. -/
theorem diagSL2_smul_coe {lam : ℝ} (hlam : lam ≠ 0) (τ : UpperHalfPlane) :
    ((diagSL2 lam hlam • τ : UpperHalfPlane) : ℂ) = (lam : ℂ) ^ 2 * (τ : ℂ) := by
  have hl : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam
  rw [UpperHalfPlane.coe_specialLinearGroup_apply,
    show ((diagSL2 lam hlam : Matrix (Fin 2) (Fin 2) ℝ)) = !![lam, 0; 0, lam⁻¹] from rfl]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_one]
  simp only [map_zero, Complex.ofReal_zero, zero_mul, add_zero, zero_add,
    show (algebraMap ℝ ℝ) lam = lam from rfl, show (algebraMap ℝ ℝ) lam⁻¹ = lam⁻¹ from rfl,
    Complex.ofReal_inv]
  rw [div_eq_mul_inv, inv_inv]
  ring

/-- The displacement of the diagonal element at `i` realizes the translation length:
`cosh (dist i (λ² i)) = (λ² + λ⁻²)/2 = cosh (2 arcosh (|tr|/2))`. -/
theorem dist_I_diagSL2 {lam : ℝ} (hlam : lam ≠ 0) (h1 : 1 < lam ^ 2) :
    dist UpperHalfPlane.I (diagSL2 lam hlam • UpperHalfPlane.I)
      = translationLength (diagSL2 lam hlam) := by
  have hlam2 : (0:ℝ) < lam ^ 2 := zero_lt_one.trans h1
  -- the coordinates of the moved point
  have hdI : dist ((UpperHalfPlane.I : UpperHalfPlane) : ℂ)
      ((diagSL2 lam hlam • UpperHalfPlane.I : UpperHalfPlane) : ℂ) ^ 2 = (1 - lam ^ 2) ^ 2 := by
    rw [diagSL2_smul_coe hlam, dist_eq_norm, UpperHalfPlane.coe_I]
    have hsub : Complex.I - (lam : ℂ) ^ 2 * Complex.I
        = ((1 - lam ^ 2 : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have himI : (diagSL2 lam hlam • UpperHalfPlane.I).im = lam ^ 2 := by
    rw [← UpperHalfPlane.coe_im, diagSL2_smul_coe hlam, UpperHalfPlane.coe_I,
      ← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re]
    ring
  have hcoshd : Real.cosh (dist UpperHalfPlane.I (diagSL2 lam hlam • UpperHalfPlane.I))
      = 1 + (1 - lam ^ 2) ^ 2 / (2 * lam ^ 2) := by
    rw [UpperHalfPlane.cosh_dist, hdI, himI, UpperHalfPlane.I_im]
    norm_num
  -- the translation-length side
  have htr : Matrix.trace ((diagSL2 lam hlam : Matrix (Fin 2) (Fin 2) ℝ)) = lam + lam⁻¹ := by
    rw [show ((diagSL2 lam hlam : Matrix (Fin 2) (Fin 2) ℝ)) = !![lam, 0; 0, lam⁻¹] from rfl,
      Matrix.trace_fin_two_of]
  have habs : 2 ≤ |lam + lam⁻¹| := by
    nlinarith [sq_abs (lam + lam⁻¹), abs_nonneg (lam + lam⁻¹), sq_nonneg (lam - lam⁻¹),
      mul_inv_cancel₀ hlam]
  have h1m : 1 ≤ |lam + lam⁻¹| / 2 := by linarith
  have hcosht : Real.cosh (translationLength (diagSL2 lam hlam))
      = 1 + (1 - lam ^ 2) ^ 2 / (2 * lam ^ 2) := by
    unfold translationLength
    rw [htr, max_eq_right h1m, Real.cosh_two_mul, Real.cosh_arcosh h1m, Real.sinh_arcosh h1m,
      Real.sq_sqrt (by nlinarith : (0:ℝ) ≤ (|lam + lam⁻¹| / 2) ^ 2 - 1), div_pow, sq_abs]
    field_simp
    ring_nf
  have h := hcoshd.trans hcosht.symm
  have h2 := congrArg Real.arcosh h
  rwa [Real.arcosh_cosh dist_nonneg, Real.arcosh_cosh (translationLength_nonneg _)] at h2

/-- The displacement of the diagonal element is minimized on the imaginary axis:
`cosh (dist τ (λ² τ)) = 1 + (1 − λ²)² |τ|² / (2 λ² (im τ)²) ≥ (λ² + λ⁻²)/2`. -/
theorem translationLength_le_dist_diagSL2 {lam : ℝ} (hlam : lam ≠ 0) (h1 : 1 < lam ^ 2)
    (τ : UpperHalfPlane) :
    translationLength (diagSL2 lam hlam) ≤ dist τ (diagSL2 lam hlam • τ) := by
  have hlam2 : (0:ℝ) < lam ^ 2 := zero_lt_one.trans h1
  have him0 : 0 < τ.im := τ.im_pos
  have hd : dist ((τ : UpperHalfPlane) : ℂ)
      ((diagSL2 lam hlam • τ : UpperHalfPlane) : ℂ) ^ 2
      = (1 - lam ^ 2) ^ 2 * ((τ : ℂ).re ^ 2 + (τ : ℂ).im ^ 2) := by
    rw [diagSL2_smul_coe hlam, dist_eq_norm]
    have hsub : (τ : ℂ) - (lam : ℂ) ^ 2 * (τ : ℂ) = ((1 - lam ^ 2 : ℝ) : ℂ) * (τ : ℂ) := by
      push_cast
      ring
    rw [hsub, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Complex.sq_norm, Complex.normSq_apply]
    ring
  have him : (diagSL2 lam hlam • τ).im = lam ^ 2 * τ.im := by
    rw [← UpperHalfPlane.coe_im, diagSL2_smul_coe hlam, ← Complex.ofReal_pow,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_im]
    ring
  have hcoshd : Real.cosh (dist τ (diagSL2 lam hlam • τ))
      = 1 + (1 - lam ^ 2) ^ 2 * ((τ : ℂ).re ^ 2 + (τ : ℂ).im ^ 2)
        / (2 * τ.im * (lam ^ 2 * τ.im)) := by
    rw [UpperHalfPlane.cosh_dist, hd, him]
  -- the translation-length side
  have htr : Matrix.trace ((diagSL2 lam hlam : Matrix (Fin 2) (Fin 2) ℝ)) = lam + lam⁻¹ := by
    rw [show ((diagSL2 lam hlam : Matrix (Fin 2) (Fin 2) ℝ)) = !![lam, 0; 0, lam⁻¹] from rfl,
      Matrix.trace_fin_two_of]
  have habs : 2 ≤ |lam + lam⁻¹| := by
    nlinarith [sq_abs (lam + lam⁻¹), abs_nonneg (lam + lam⁻¹), sq_nonneg (lam - lam⁻¹),
      mul_inv_cancel₀ hlam]
  have h1m : 1 ≤ |lam + lam⁻¹| / 2 := by linarith
  have hcosht : Real.cosh (translationLength (diagSL2 lam hlam))
      = 1 + (1 - lam ^ 2) ^ 2 / (2 * lam ^ 2) := by
    unfold translationLength
    rw [htr, max_eq_right h1m, Real.cosh_two_mul, Real.cosh_arcosh h1m, Real.sinh_arcosh h1m,
      Real.sq_sqrt (by nlinarith : (0:ℝ) ≤ (|lam + lam⁻¹| / 2) ^ 2 - 1), div_pow, sq_abs]
    field_simp
    ring_nf
  have hcim : (τ : ℂ).im = τ.im := UpperHalfPlane.coe_im τ
  have hle : Real.cosh (translationLength (diagSL2 lam hlam))
      ≤ Real.cosh (dist τ (diagSL2 lam hlam • τ)) := by
    rw [hcoshd, hcosht]
    have key : (1 - lam ^ 2) ^ 2 / (2 * lam ^ 2)
        ≤ (1 - lam ^ 2) ^ 2 * ((τ : ℂ).re ^ 2 + (τ : ℂ).im ^ 2)
          / (2 * τ.im * (lam ^ 2 * τ.im)) := by
      rw [div_le_div_iff₀ (by linarith) (by positivity), hcim]
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (1 - lam ^ 2))
        (sq_nonneg ((τ : ℂ).re))) hlam2.le, him0, hlam2]
    linarith
  calc translationLength (diagSL2 lam hlam)
      = Real.arcosh (Real.cosh (translationLength (diagSL2 lam hlam))) :=
        (Real.arcosh_cosh (translationLength_nonneg _)).symm
    _ ≤ Real.arcosh (Real.cosh (dist τ (diagSL2 lam hlam • τ))) :=
        (Real.arcosh_le_arcosh (Real.cosh_pos _) (Real.cosh_pos _)).mpr hle
    _ = dist τ (diagSL2 lam hlam • τ) := Real.arcosh_cosh dist_nonneg

/-- The infimal displacement of the diagonal element is its translation length. -/
theorem iInf_dist_diagSL2 {lam : ℝ} (hlam : lam ≠ 0) (h1 : 1 < lam ^ 2) :
    (⨅ τ : UpperHalfPlane, dist τ (diagSL2 lam hlam • τ))
      = translationLength (diagSL2 lam hlam) := by
  refine le_antisymm ?_ (le_ciInf fun τ => translationLength_le_dist_diagSL2 hlam h1 τ)
  have hbdd : BddBelow (Set.range fun τ : UpperHalfPlane => dist τ (diagSL2 lam hlam • τ)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨τ, rfl⟩
    exact dist_nonneg
  calc (⨅ τ : UpperHalfPlane, dist τ (diagSL2 lam hlam • τ))
      ≤ dist UpperHalfPlane.I (diagSL2 lam hlam • UpperHalfPlane.I) :=
        ciInf_le hbdd UpperHalfPlane.I
    _ = translationLength (diagSL2 lam hlam) := dist_I_diagSL2 hlam h1

/-- Translation length is a conjugation invariant: the trace is. -/
theorem translationLength_conj (P A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    translationLength (P * A * P⁻¹) = translationLength A := by
  have htr : Matrix.trace ((P * A * P⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_left]
  unfold translationLength
  rw [htr]

/-- The infimal displacement of a hyperbolic element is its translation length. -/
theorem iInf_dist_smul_eq_translationLength (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : (A : Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic) :
    (⨅ τ : UpperHalfPlane, dist τ (A • τ)) = translationLength A := by
  obtain ⟨P, lam, hlam, h1, hPA⟩ := sl2_hyperbolic_diagonalization A hA
  have hsurj : Function.Surjective fun τ : UpperHalfPlane => P • τ := (MulAction.bijective P).2
  have hfun : (fun τ : UpperHalfPlane => dist τ (A • τ)) =
      (fun σ : UpperHalfPlane => dist σ (diagSL2 lam hlam • σ)) ∘
        fun τ : UpperHalfPlane => P • τ := by
    funext τ
    change dist τ (A • τ) = dist (P • τ) (diagSL2 lam hlam • (P • τ))
    rw [← hPA, ← mul_smul, inv_mul_cancel_right, mul_smul, dist_smul]
  calc (⨅ τ : UpperHalfPlane, dist τ (A • τ))
      = ⨅ σ : UpperHalfPlane, dist σ (diagSL2 lam hlam • σ) := by
        rw [← sInf_range, ← sInf_range, hfun, Function.Surjective.range_comp hsurj]
    _ = translationLength (diagSL2 lam hlam) := iInf_dist_diagSL2 hlam h1
    _ = translationLength A := by
        rw [← hPA]
        exact translationLength_conj P A

/-- The infimal displacement of a hyperbolic element is attained, on the image of the
imaginary axis under the diagonalizing conjugation. -/
theorem exists_dist_smul_eq_translationLength (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : (A : Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic) :
    ∃ τ₀ : UpperHalfPlane, dist τ₀ (A • τ₀) = translationLength A := by
  obtain ⟨P, lam, hlam, h1, hPA⟩ := sl2_hyperbolic_diagonalization A hA
  have hgen : ∀ σ : UpperHalfPlane,
      dist (P • σ) (diagSL2 lam hlam • (P • σ)) = dist σ (A • σ) := by
    intro σ
    rw [← hPA, ← mul_smul, inv_mul_cancel_right, mul_smul, dist_smul]
  refine ⟨P⁻¹ • UpperHalfPlane.I, ?_⟩
  rw [← hgen (P⁻¹ • UpperHalfPlane.I), smul_inv_smul, dist_I_diagSL2 hlam h1, ← hPA]
  exact translationLength_conj P A

/-- Displacement lower bound: a hyperbolic element moves every point at least its
translation length. -/
theorem translationLength_le_dist_smul (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : (A : Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic) (τ : UpperHalfPlane) :
    translationLength A ≤ dist τ (A • τ) := by
  obtain ⟨P, lam, hlam, h1, hPA⟩ := sl2_hyperbolic_diagonalization A hA
  have hgen : dist (P • τ) (diagSL2 lam hlam • (P • τ)) = dist τ (A • τ) := by
    rw [← hPA, ← mul_smul, inv_mul_cancel_right, mul_smul, dist_smul]
  have h := translationLength_le_dist_diagSL2 hlam h1 (P • τ)
  rw [hgen] at h
  have hc : translationLength (diagSL2 lam hlam) = translationLength A := by
    rw [← hPA]
    exact translationLength_conj P A
  calc translationLength A = translationLength (diagSL2 lam hlam) := hc.symm
    _ ≤ dist τ (A • τ) := h

/-- The central elements `±1` act trivially and have zero translation length. -/
theorem smul_eq_self_of_pm_one (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h : (A : Matrix (Fin 2) (Fin 2) ℝ) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) ℝ) = -1) :
    (∀ τ : UpperHalfPlane, A • τ = τ) ∧ translationLength A = 0 := by
  constructor
  · intro τ
    rcases h with h | h
    · have hA1 : A = 1 := Subtype.ext (by rw [h, Matrix.SpecialLinearGroup.coe_one])
      rw [hA1, one_smul]
    · apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_specialLinearGroup_apply, h]
      simp [Matrix.neg_apply]
  · have h2 : |Matrix.trace ((A : Matrix (Fin 2) (Fin 2) ℝ))| = 2 := by
      rcases h with h | h <;> rw [h]
      · rw [Matrix.trace_one]
        norm_num [Fintype.card_fin]
      · rw [Matrix.trace_neg, Matrix.trace_one]
        norm_num [Fintype.card_fin]
    unfold translationLength
    rw [h2]
    norm_num [Real.arcosh_zero]

/-! ## Systole -/

/-- An element of `SL(2, ℝ)` **acts nontrivially** when it moves some point of the upper
half plane; the trivially-acting elements are exactly `±1`. -/
def actsNontrivially (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Prop :=
  ∃ τ : UpperHalfPlane, A • τ ≠ τ

/-- The **systole** of a Teichmüller representative: the infimal translation length of the
nontrivially-acting elements of its Fuchsian group (`0` over an empty index). -/
noncomputable def systoleRep (x : TeichRep Γ₀) : ℝ :=
  ⨅ γ : {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ // γ ∈ x.group ∧ actsNontrivially γ},
    translationLength γ.1

/-- The systole is nonnegative: translation lengths are. -/
theorem systoleRep_nonneg (x : TeichRep Γ₀) : 0 ≤ systoleRep x := by
  unfold systoleRep
  exact Real.iInf_nonneg fun γ => translationLength_nonneg γ.1

/-- The systole bounds the translation length of every nontrivially-acting group element
from below. -/
theorem systoleRep_le (x : TeichRep Γ₀) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : γ ∈ x.group) (hnt : actsNontrivially γ) :
    systoleRep x ≤ translationLength γ := by
  unfold systoleRep
  have hbdd : BddBelow (Set.range fun γ : {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ //
      γ ∈ x.group ∧ actsNontrivially γ} => translationLength γ.1) := by
    refine ⟨0, ?_⟩
    rintro v ⟨δ, rfl⟩
    exact translationLength_nonneg δ.1
  exact ciInf_le hbdd ⟨γ, hγ, hnt⟩

/-- A uniform lower bound on the translation lengths of nontrivially-acting group elements
bounds the systole from below, provided some group element acts nontrivially. -/
theorem le_systoleRep (x : TeichRep Γ₀) {ε : ℝ}
    (hne : ∃ γ ∈ x.group, actsNontrivially γ)
    (h : ∀ γ ∈ x.group, actsNontrivially γ → ε ≤ translationLength γ) :
    ε ≤ systoleRep x := by
  obtain ⟨γ₀, hγ₀, hnt₀⟩ := hne
  have : Nonempty {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ //
      γ ∈ x.group ∧ actsNontrivially γ} := ⟨⟨γ₀, hγ₀, hnt₀⟩⟩
  unfold systoleRep
  exact le_ciInf fun γ => h γ.1 γ.2.1 γ.2.2

/-- **Trace gap**: in a group of systole at least `ε > 0`, every nontrivially-acting element
is hyperbolic with `|tr| ≥ 2 cosh (ε/2)`. -/
theorem trace_gap_of_systole {x : TeichRep Γ₀} {ε : ℝ} (hε : 0 < ε)
    (hsys : ε ≤ systoleRep x) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : γ ∈ x.group) (hnt : actsNontrivially γ) :
    2 * Real.cosh (ε / 2) ≤ |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)| ∧
      (γ : Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic := by
  have hlen : ε ≤ translationLength γ := hsys.trans (systoleRep_le x hγ hnt)
  unfold translationLength at hlen
  set M := max 1 (|Matrix.trace ((γ : Matrix (Fin 2) (Fin 2) ℝ))| / 2) with hM
  have hM1 : (1:ℝ) ≤ M := le_max_left _ _
  have harc : ε / 2 ≤ Real.arcosh M := by linarith
  have hcosh : Real.cosh (ε / 2) ≤ M := by
    have h : Real.cosh (ε / 2) ≤ Real.cosh (Real.arcosh M) := by
      rw [Real.cosh_le_cosh, abs_of_nonneg (by linarith : (0:ℝ) ≤ ε / 2),
        abs_of_nonneg (Real.arcosh_nonneg hM1)]
      exact harc
    rwa [Real.cosh_arcosh hM1] at h
  have h1c : (1:ℝ) < Real.cosh (ε / 2) :=
    Real.one_lt_cosh.mpr (by positivity : (0:ℝ) < ε / 2).ne'
  have htr2 : 1 < |Matrix.trace ((γ : Matrix (Fin 2) (Fin 2) ℝ))| / 2 := by
    rcases le_or_gt (|Matrix.trace ((γ : Matrix (Fin 2) (Fin 2) ℝ))| / 2) 1 with hle | hlt
    · exfalso
      rw [hM, max_eq_left hle] at hcosh
      linarith
    · exact hlt
  rw [hM, max_eq_right htr2.le] at hcosh
  refine ⟨by linarith, ?_⟩
  have hdet : ((γ : Matrix (Fin 2) (Fin 2) ℝ)).det = 1 := Matrix.SpecialLinearGroup.det_coe γ
  unfold Matrix.IsHyperbolic
  rw [Matrix.discr_fin_two, hdet]
  have h2 : 2 < |Matrix.trace ((γ : Matrix (Fin 2) (Fin 2) ℝ))| := by linarith
  nlinarith [sq_abs (Matrix.trace ((γ : Matrix (Fin 2) (Fin 2) ℝ))),
    abs_nonneg (Matrix.trace ((γ : Matrix (Fin 2) (Fin 2) ℝ))),
    mul_pos (by linarith : (0:ℝ) < |Matrix.trace ((γ : Matrix (Fin 2) (Fin 2) ℝ))| - 2)
      (by linarith : (0:ℝ) < |Matrix.trace ((γ : Matrix (Fin 2) (Fin 2) ℝ))| + 2)]

/-! ## Hyperbolic area of balls -/

/-- Balls of the upper half plane have positive hyperbolic volume: the density `(im)⁻²` of
the hyperbolic measure is positive on the open embedding into the plane. -/
theorem volume_ball_pos (τ : UpperHalfPlane) {r : ℝ} (hr : 0 < r) :
    0 < volume (Metric.ball τ r) := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  set S : Set ℂ := UpperHalfPlane.coe '' Metric.ball τ r with hS
  set T : Set ℂ := S ∩ {z : ℂ | z.im < τ.im + 1} with hT
  have hSopen : IsOpen S :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ Metric.isOpen_ball
  have hTopen : IsOpen T :=
    hSopen.inter (isOpen_lt Complex.continuous_im continuous_const)
  have hτS : ((τ : ℂ)) ∈ S := ⟨τ, Metric.mem_ball_self hr, rfl⟩
  have hτT : ((τ : ℂ)) ∈ T := by
    refine ⟨hτS, ?_⟩
    simp only [Set.mem_ofPred_eq, UpperHalfPlane.coe_im]
    linarith
  have hSim : ∀ z ∈ S, 0 < z.im := by
    rintro z ⟨σ, -, rfl⟩
    rw [UpperHalfPlane.coe_im]
    exact σ.im_pos
  set c : NNReal := ‖τ.im + 1‖₊ with hc
  have him : (0:ℝ) < τ.im := τ.im_pos
  have hcpos : 0 < c := nnnorm_pos.mpr (by positivity : (0:ℝ) < τ.im + 1).ne'
  have hbound : ∀ z ∈ T, (((1 / c) ^ 2 : NNReal) : ℝ≥0∞) ≤ ((1 / ‖z.im‖₊) ^ 2 : NNReal) := by
    intro z hz
    obtain ⟨hzS, hzc⟩ := hz
    have h0 : 0 < z.im := hSim z hzS
    have hzc' : z.im < τ.im + 1 := hzc
    rw [ENNReal.coe_le_coe]
    have h1 : ‖z.im‖₊ ≤ c := by
      rw [← NNReal.coe_le_coe]
      simp only [hc, coe_nnnorm, Real.norm_eq_abs]
      rw [abs_of_pos h0, abs_of_pos (by positivity : (0:ℝ) < τ.im + 1)]
      exact hzc'.le
    exact pow_le_pow_left₀ (zero_le)
      (one_div_le_one_div_of_le (nnnorm_pos.mpr h0.ne') h1) 2
  have hmeasN : Measurable fun z : ℂ => ((1 / ‖z.im‖₊) ^ 2 : NNReal) := by
    simp only [one_div]
    exact (Complex.measurable_im.nnnorm.inv).pow_const 2
  have hmeas : Measurable fun z : ℂ => (((1 / ‖z.im‖₊) ^ 2 : NNReal) : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp hmeasN
  have hchain : ((((1 / c) ^ 2 : NNReal)) : ℝ≥0∞) * volume T
      ≤ ∫⁻ z in S, (((1 / ‖z.im‖₊) ^ 2 : NNReal) : ℝ≥0∞) := by
    calc ((((1 / c) ^ 2 : NNReal)) : ℝ≥0∞) * volume T
        = ∫⁻ _ in T, ((((1 / c) ^ 2 : NNReal)) : ℝ≥0∞) := (setLIntegral_const T _).symm
      _ ≤ ∫⁻ z in T, (((1 / ‖z.im‖₊) ^ 2 : NNReal) : ℝ≥0∞) := setLIntegral_mono hmeas hbound
      _ ≤ ∫⁻ z in S, (((1 / ‖z.im‖₊) ^ 2 : NNReal) : ℝ≥0∞) :=
          lintegral_mono_set Set.inter_subset_left
  refine lt_of_lt_of_le ?_ hchain
  refine ENNReal.mul_pos ?_ ?_
  · exact (ENNReal.coe_ne_zero.mpr (pow_ne_zero 2 (one_div_ne_zero hcpos.ne')))
  · exact (hTopen.measure_pos volume ⟨(τ : ℂ), hτT⟩).ne'

/-- The hyperbolic volume of balls is `SL(2, ℝ)`-invariant: the action is isometric and
measure preserving. -/
theorem volume_ball_smul (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane)
    (r : ℝ) : volume (Metric.ball (g • τ) r) = volume (Metric.ball τ r) := by
  have himg : (fun σ : UpperHalfPlane => (Matrix.SpecialLinearGroup.mapGL ℝ g) • σ) ''
      Metric.ball τ r = Metric.ball (g • τ) r := (IsometryEquiv.constSMul g).image_ball τ r
  rw [← himg]
  exact measure_smul volume (Matrix.SpecialLinearGroup.mapGL ℝ g) (Metric.ball τ r)

/-- Transitivity of the `SL(2, ℝ)`-action on the upper half plane: `x + i y` is the image of
`i` under `!![√y, x/√y; 0, 1/√y]`. -/
theorem exists_smul_I_eq (τ : UpperHalfPlane) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℝ, g • UpperHalfPlane.I = τ := by
  refine ⟨affineSL2 τ.im τ.re τ.im_pos, ?_⟩
  apply UpperHalfPlane.ext
  rw [coe_smul_eq_moebiusMap, UpperHalfPlane.coe_I, moebiusMap_affineSL2]
  rw [← Complex.re_add_im (τ : ℂ), UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- The hyperbolic volume of a ball of radius `r` about `i`, hence about any point. -/
noncomputable def upperBallVolume (r : ℝ) : ℝ≥0∞ :=
  volume (Metric.ball UpperHalfPlane.I r)

/-- Balls of positive radius have positive hyperbolic volume. -/
theorem upperBallVolume_pos {r : ℝ} (hr : 0 < r) : 0 < upperBallVolume r := by
  unfold upperBallVolume
  exact volume_ball_pos UpperHalfPlane.I hr

/-- All balls of radius `r` in the upper half plane have volume `upperBallVolume r`. -/
theorem volume_ball_eq_upperBallVolume (τ : UpperHalfPlane) (r : ℝ) :
    volume (Metric.ball τ r) = upperBallVolume r := by
  obtain ⟨g, hg⟩ := exists_smul_I_eq τ
  unfold upperBallVolume
  rw [← hg, volume_ball_smul]

/-! ## Descent to Teichmüller space and the thick part -/

/-- Inseparable representatives have equal boundary maps, hence equal Fuchsian groups and
equal systoles. -/
theorem systoleRep_congr :
    ∀ x y : TeichRep Γ₀, Inseparable x y → systoleRep x = systoleRep y := by
  intro x y hxy
  have hw : ∀ t : ℝ, x.w t = y.w t := inseparable_iff_boundary_eq.mp hxy
  have hb : x.boundary = y.boundary := funext fun t => by
    simp only [TeichRep.boundary]
    rw [hw t]
  have hg : x.group = y.group := TeichRep.group_eq_of_boundary_eq hb
  unfold systoleRep
  rw [hg]

/-- The systole as a function on Teichmüller space. -/
noncomputable def systole : Teich Γ₀ → ℝ :=
  SeparationQuotient.lift systoleRep systoleRep_congr

/-- The systole of a class is the systole of any representative. -/
@[simp]
theorem systole_mk (x : TeichRep Γ₀) : systole (Teich.mk x) = systoleRep x := rfl

/-- The `ε`-**thick part** of Teichmüller space: classes of systole at least `ε`. -/
def ThickPart (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (ε : ℝ) :
    Set (Teich Γ₀) :=
  {ξ | ε ≤ systole ξ}

end RiemannDynamics

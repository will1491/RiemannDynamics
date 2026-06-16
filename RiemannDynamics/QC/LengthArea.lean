/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Geometric
import RiemannDynamics.QC.Analytic
import RiemannDynamics.Analysis.Sobolev.SobolevToACL
import RiemannDynamics.Analysis.SingularIntegral.Beurling.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Length–area infrastructure for the quasiconformal equivalence

The equivalence of the analytic and geometric definitions of quasiconformality
rests on the **length–area method**, which relates the modulus distortion of a
quasiconformal map to its differential. This file collects the infrastructure
lemmas that the two directions of `qc_analytic_iff_geometric` consume — the pieces
that go beyond the absolute-continuity-on-lines theory and the change-of-variables
formula already in hand.

Four ingredients:

* **Wirtinger singular values** (`det_fderiv_eq_wirtinger`, `opNorm_fderiv_eq_wirtinger`)
  — the real Jacobian determinant and operator norm of the real differential of a
  map `ℂ → ℂ`, expressed through the Wirtinger derivatives `∂f`, `∂̄f`:
  `det (Df) = ‖∂f‖² − ‖∂̄f‖²` and `‖Df‖ = ‖∂f‖ + ‖∂̄f‖`. These are the singular-value
  identities of a real-linear self-map of `ℂ`; the dilatation bound
  `‖(Df)⁻¹‖² · det (Df) ≤ K` follows algebraically from them and the Beltrami bound
  `‖∂̄f‖ ≤ ((K−1)/(K+1)) ‖∂f‖`. Self-contained linear algebra.

* **Gehring–Lehto a.e. differentiability** (`IsQCAnalytic.ae_differentiableAt`) — a
  quasiconformal map is differentiable almost everywhere. A genuine classical
  theorem (absent from Mathlib, which has a.e. differentiability only for Lipschitz
  and one-dimensional monotone maps).

* **Fuglede's theorem** (`curveModulus_sdiff_modulus_zero`,
  `IsQCAnalytic.image_nonAC_modulus_zero`) — a curve subfamily of zero modulus does
  not affect the modulus, and the curves whose image under a quasiconformal map
  fails to be absolutely continuous form a family of zero modulus. This is what
  lets the length–area transfer of densities ignore the exceptional curves.

The Wirtinger singular-value identities are proved here; Gehring–Lehto and Fuglede
are the deep classical inputs the equivalence reduces to.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RiemannDynamics

/-- **Wirtinger Jacobian identity.** The real Jacobian determinant of `f : ℂ → ℂ`
at `z` is `‖∂f‖² − ‖∂̄f‖²`. (Singular-value identity: the determinant of the real
differential equals the product of singular values `(‖∂f‖ + ‖∂̄f‖)(‖∂f‖ − ‖∂̄f‖)`.) -/
theorem det_fderiv_eq_wirtinger (f : ℂ → ℂ) (z : ℂ) :
    (fderiv ℝ f z).det = ‖dz f z‖ ^ 2 - ‖dzbar f z‖ ^ 2 := by
  -- Work with a general real-linear self-map `A` of `ℂ`.
  set A : ℂ →L[ℝ] ℂ := fderiv ℝ f z with hA
  -- The entries of the matrix of `A` in the basis `(1, I)`.
  set a : ℝ := (A 1).re with ha
  set b : ℝ := (A 1).im with hb
  set c : ℝ := (A Complex.I).re with hc
  set d : ℝ := (A Complex.I).im with hd
  -- `dz f z` and `dzbar f z` in terms of `a, b, c, d`.
  have hpval : dz f z = (1/2 : ℂ) * ((A 1) - Complex.I * (A Complex.I)) := rfl
  have hqval : dzbar f z = (1/2 : ℂ) * ((A 1) + Complex.I * (A Complex.I)) := rfl
  -- Determinant of `A` via the matrix in `Complex.basisOneI`.
  have hdet : A.det = a * d - b * c := by
    have key : ∀ M : ℂ →ₗ[ℝ] ℂ, LinearMap.det M
        = (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI M).det := fun M =>
      (LinearMap.det_toMatrix Complex.basisOneI M).symm
    rw [ContinuousLinearMap.det, key]
    have hb0 : (Complex.basisOneI : Module.Basis (Fin 2) ℝ ℂ) 0 = (1 : ℂ) := by
      simp [Complex.coe_basisOneI]
    have hb1 : (Complex.basisOneI : Module.Basis (Fin 2) ℝ ℂ) 1 = Complex.I := by
      simp [Complex.coe_basisOneI]
    have c00 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 0 0 = a := by
      rw [LinearMap.toMatrix_apply, hb0, Complex.coe_basisOneI_repr]
      rfl
    have c10 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 1 0 = b := by
      rw [LinearMap.toMatrix_apply, hb0, Complex.coe_basisOneI_repr]
      rfl
    have c01 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 0 1 = c := by
      rw [LinearMap.toMatrix_apply, hb1, Complex.coe_basisOneI_repr]
      rfl
    have c11 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 1 1 = d := by
      rw [LinearMap.toMatrix_apply, hb1, Complex.coe_basisOneI_repr]
      rfl
    have h0 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) = !![a, c; b, d] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
          Matrix.cons_val_fin_one] <;>
        first | exact c00 | exact c01 | exact c10 | exact c11
    rw [h0, Matrix.det_fin_two_of]; ring
  -- Compute the two norms-squared.
  have hp2 : ‖dz f z‖ ^ 2 = ((a + d) ^ 2 + (b - c) ^ 2) / 4 := by
    rw [← Complex.normSq_eq_norm_sq, hpval, Complex.normSq_apply]
    have h12re : (1/2 : ℂ).re = 1/2 := by norm_num [Complex.div_re]
    have h12im : (1/2 : ℂ).im = 0 := by norm_num [Complex.div_im]
    have hre : ((1/2 : ℂ) * ((A 1) - Complex.I * (A Complex.I))).re = (a + d) / 2 := by
      rw [ha, hd]
      simp only [Complex.mul_re, Complex.sub_re, Complex.mul_im, Complex.sub_im,
        Complex.I_re, Complex.I_im, h12re, h12im]
      ring
    have him : ((1/2 : ℂ) * ((A 1) - Complex.I * (A Complex.I))).im = (b - c) / 2 := by
      rw [hb, hc]
      simp only [Complex.mul_im, Complex.sub_re, Complex.mul_re, Complex.sub_im,
        Complex.I_re, Complex.I_im, h12re, h12im]
      ring
    rw [hre, him]; ring
  have hq2 : ‖dzbar f z‖ ^ 2 = ((a - d) ^ 2 + (b + c) ^ 2) / 4 := by
    rw [← Complex.normSq_eq_norm_sq, hqval, Complex.normSq_apply]
    have h12re : (1/2 : ℂ).re = 1/2 := by norm_num [Complex.div_re]
    have h12im : (1/2 : ℂ).im = 0 := by norm_num [Complex.div_im]
    have hre : ((1/2 : ℂ) * ((A 1) + Complex.I * (A Complex.I))).re = (a - d) / 2 := by
      rw [ha, hd]
      simp only [Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.add_im,
        Complex.I_re, Complex.I_im, h12re, h12im]
      ring
    have him : ((1/2 : ℂ) * ((A 1) + Complex.I * (A Complex.I))).im = (b + c) / 2 := by
      rw [hb, hc]
      simp only [Complex.mul_im, Complex.add_re, Complex.mul_re, Complex.add_im,
        Complex.I_re, Complex.I_im, h12re, h12im]
      ring
    rw [hre, him]; ring
  rw [hdet, hp2, hq2]; ring

/-- **Wirtinger operator-norm identity.** The operator norm of the real differential
of `f : ℂ → ℂ` at `z` is `‖∂f‖ + ‖∂̄f‖`, the larger singular value of the real-linear
self-map of `ℂ`. -/
theorem opNorm_fderiv_eq_wirtinger (f : ℂ → ℂ) (z : ℂ) :
    ‖fderiv ℝ f z‖ = ‖dz f z‖ + ‖dzbar f z‖ := by
  set A : ℂ →L[ℝ] ℂ := fderiv ℝ f z with hA
  set p : ℂ := dz f z with hp
  set q : ℂ := dzbar f z with hq
  -- `A` is the real-linear map `w ↦ p w + q conj w`.
  have hrepr : ∀ w : ℂ, A w = p * w + q * (starRingEnd ℂ) w := by
    intro w
    rw [hp, hq, dz, dzbar]
    have hLw : A w = (↑w.re : ℂ) * A 1 + (↑w.im : ℂ) * A Complex.I := by
      conv_lhs => rw [show w = w.re • (1 : ℂ) + w.im • Complex.I by
        rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
      rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    have hcw : (starRingEnd ℂ) w = (↑w.re : ℂ) - ↑w.im * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im w]
      simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have hw : w = (↑w.re : ℂ) + ↑w.im * Complex.I := (Complex.re_add_im w).symm
    rw [hLw, hcw]
    set sa : ℂ := (↑w.re : ℂ) with hsa
    set sb : ℂ := (↑w.im : ℂ) with hsb
    rw [hw]
    linear_combination (sb * A Complex.I) * Complex.I_mul_I
  -- Upper bound: `‖A w‖ ≤ (‖p‖ + ‖q‖) ‖w‖`.
  have hub : ‖A‖ ≤ ‖p‖ + ‖q‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
    rw [hrepr w]
    calc ‖p * w + q * (starRingEnd ℂ) w‖
        ≤ ‖p * w‖ + ‖q * (starRingEnd ℂ) w‖ := norm_add_le _ _
      _ = ‖p‖ * ‖w‖ + ‖q‖ * ‖w‖ := by
            rw [norm_mul, norm_mul, Complex.norm_conj]
      _ = (‖p‖ + ‖q‖) * ‖w‖ := by ring
  -- Lower bound: exhibit a unit `w₀` with `‖A w₀‖ = ‖p‖ + ‖q‖`.
  have hlb : ‖p‖ + ‖q‖ ≤ ‖A‖ := by
    -- The target unit vector squares to `t / ‖t‖`, where `t = conj p * q`.
    obtain ⟨w₀, hw₀norm, hcross⟩ :
        ∃ w₀ : ℂ, ‖w₀‖ = 1 ∧ (p * (starRingEnd ℂ) q * (w₀ * w₀)).re = ‖p‖ * ‖q‖ := by
      by_cases ht : (starRingEnd ℂ) p * q = 0
      · -- Then `p = 0` or `q = 0`; the vector `1` works.
        refine ⟨1, by simp, ?_⟩
        rcases mul_eq_zero.mp ht with h | h
        · have hp0 : p = 0 := (map_eq_zero _).mp h
          simp [hp0]
        · have hq0 : q = 0 := h
          simp [hq0]
      · -- `t ≠ 0`: take a square root of the unit `t / ‖t‖`.
        set t : ℂ := (starRingEnd ℂ) p * q with htdef
        have htnorm : (‖t‖ : ℝ) ≠ 0 := by
          simpa [norm_eq_zero] using ht
        obtain ⟨s, hs⟩ := Complex.isSquare (t / (‖t‖ : ℂ))
        have hsnorm : ‖s‖ = 1 := by
          have h1 : ‖s * s‖ = 1 := by
            rw [← hs, norm_div]
            simp [Complex.norm_real, htnorm]
          rw [norm_mul] at h1
          nlinarith [norm_nonneg s, h1]
        refine ⟨s, hsnorm, ?_⟩
        -- `p * conj q * (s * s) = conj t * (t / ‖t‖) = ‖t‖`, a positive real.
        have hpcq : p * (starRingEnd ℂ) q = (starRingEnd ℂ) t := by
          rw [htdef, map_mul, Complex.conj_conj, mul_comm]
        have htt : (starRingEnd ℂ) t * t = ((‖t‖ ^ 2 : ℝ) : ℂ) := by
          rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        have hval : p * (starRingEnd ℂ) q * (s * s) = (‖t‖ : ℂ) := by
          rw [hpcq, ← hs, ← mul_div_assoc, htt]
          rw [div_eq_iff (by exact_mod_cast htnorm)]
          push_cast; ring
        rw [hval]
        have hnormt : ‖t‖ = ‖p‖ * ‖q‖ := by
          rw [htdef, Complex.norm_mul, Complex.norm_conj]
        rw [Complex.ofReal_re, hnormt]
    -- Use the maximizer.
    have key : ‖A w₀‖ = ‖p‖ + ‖q‖ := by
      have hw₀ns : Complex.normSq w₀ = 1 := by
        rw [Complex.normSq_eq_norm_sq, hw₀norm]; norm_num
      have hcrossterm : (p * w₀ * (starRingEnd ℂ) (q * (starRingEnd ℂ) w₀)).re
          = ‖p‖ * ‖q‖ := by
        rw [map_mul, Complex.conj_conj]
        have hr : p * w₀ * ((starRingEnd ℂ) q * w₀) = p * (starRingEnd ℂ) q * (w₀ * w₀) := by
          ring
        rw [hr, hcross]
      have hpns : Complex.normSq p = ‖p‖ ^ 2 := Complex.normSq_eq_norm_sq p
      have hqns : Complex.normSq q = ‖q‖ ^ 2 := Complex.normSq_eq_norm_sq q
      have hnsq : ‖A w₀‖ ^ 2 = (‖p‖ + ‖q‖) ^ 2 := by
        rw [hrepr w₀, ← Complex.normSq_eq_norm_sq, Complex.normSq_add,
          Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_conj,
          hw₀ns, hcrossterm, hpns, hqns]
        ring
      have hnn : (0 : ℝ) ≤ ‖p‖ + ‖q‖ := by positivity
      nlinarith [norm_nonneg (A w₀), hnsq, hnn]
    calc ‖p‖ + ‖q‖ = ‖A w₀‖ := key.symm
      _ ≤ ‖A‖ * ‖w₀‖ := A.le_opNorm w₀
      _ = ‖A‖ := by rw [hw₀norm, mul_one]
  exact le_antisymm hub hlb

/-- **Wirtinger operator-norm of the inverse differential.** When the real Jacobian
determinant of `f` at `z` is positive (so the differential is invertible), the
operator norm of the inverse differential is the reciprocal of the smaller singular
value, `‖A⁻¹‖ = (‖∂f‖ + ‖∂̄f‖) / det (A)`. Combined with `det = ‖∂f‖² − ‖∂̄f‖²`, this
gives `‖A⁻¹‖ = (‖∂f‖ − ‖∂̄f‖)⁻¹`, and the dilatation bound
`‖A⁻¹‖² · det = (‖∂f‖ + ‖∂̄f‖)/(‖∂f‖ − ‖∂̄f‖)` that the length–area estimate consumes. -/
theorem opNorm_inverse_eq_wirtinger (f : ℂ → ℂ) (z : ℂ)
    (hdet : 0 < (fderiv ℝ f z).det) :
    ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖
      = (‖dz f z‖ + ‖dzbar f z‖) / (fderiv ℝ f z).det := by
  classical
  set A : ℂ →L[ℝ] ℂ := fderiv ℝ f z with hA
  set p : ℂ := dz f z with hp
  set q : ℂ := dzbar f z with hq
  set d : ℝ := A.det with hd
  -- The differential is `w ↦ p w + q conj w` (extracted from `opNorm_fderiv_eq_wirtinger`).
  have hAval : ∀ w : ℂ, A w = p * w + q * (starRingEnd ℂ) w := by
    intro w
    rw [hp, hq, dz, dzbar]
    have hLw : A w = (↑w.re : ℂ) * A 1 + (↑w.im : ℂ) * A Complex.I := by
      conv_lhs => rw [show w = w.re • (1 : ℂ) + w.im • Complex.I by
        rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
      rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    have hcw : (starRingEnd ℂ) w = (↑w.re : ℂ) - ↑w.im * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im w]
      simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have hw : w = (↑w.re : ℂ) + ↑w.im * Complex.I := (Complex.re_add_im w).symm
    rw [hLw, hcw]
    set sa : ℂ := (↑w.re : ℂ) with hsa
    set sb : ℂ := (↑w.im : ℂ) with hsb
    rw [hw]
    linear_combination (sb * A Complex.I) * Complex.I_mul_I
  -- `det A = ‖p‖² − ‖q‖²` via the already-proven identity.
  have hddef : d = ‖p‖ ^ 2 - ‖q‖ ^ 2 := by
    rw [hd, hA, hp, hq]; exact det_fderiv_eq_wirtinger f z
  -- Positivity facts: `‖p‖ > ‖q‖ ≥ 0`, hence `d > 0` and the relevant norms are nonzero.
  have hdpos : 0 < d := hdet
  have hqlt : ‖q‖ ^ 2 < ‖p‖ ^ 2 := by nlinarith [hddef, hdpos]
  have hppos : 0 < ‖p‖ := by nlinarith [norm_nonneg q, norm_nonneg p, hqlt]
  -- ***Reusable op-norm fact***: for any `p' q' : ℂ`, the real-linear map
  -- `Lpq p' q' : w ↦ p' w + q' conj w` has operator norm `‖p'‖ + ‖q'‖`.
  set Lpq : ℂ → ℂ → (ℂ →L[ℝ] ℂ) := fun p' q' =>
    (ContinuousLinearMap.mul ℝ ℂ p') +
      (ContinuousLinearMap.mul ℝ ℂ q').comp (Complex.conjCLE : ℂ →L[ℝ] ℂ) with hLpqdef
  have hLpqapp : ∀ (p' q' w : ℂ), Lpq p' q' w = p' * w + q' * (starRingEnd ℂ) w := by
    intro p' q' w
    simp [hLpqdef, ContinuousLinearMap.mul_apply', Complex.conjCLE_apply]
  have opNormLpq : ∀ p' q' : ℂ, ‖Lpq p' q'‖ = ‖p'‖ + ‖q'‖ := by
    intro p' q'
    -- Upper bound.
    have hub : ‖Lpq p' q'‖ ≤ ‖p'‖ + ‖q'‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
      rw [hLpqapp p' q' w]
      calc ‖p' * w + q' * (starRingEnd ℂ) w‖
          ≤ ‖p' * w‖ + ‖q' * (starRingEnd ℂ) w‖ := norm_add_le _ _
        _ = ‖p'‖ * ‖w‖ + ‖q'‖ * ‖w‖ := by
              rw [norm_mul, norm_mul, Complex.norm_conj]
        _ = (‖p'‖ + ‖q'‖) * ‖w‖ := by ring
    -- Lower bound: exhibit a unit `w₀` with `‖Lpq p' q' w₀‖ = ‖p'‖ + ‖q'‖`.
    have hlb : ‖p'‖ + ‖q'‖ ≤ ‖Lpq p' q'‖ := by
      obtain ⟨w₀, hw₀norm, hcross⟩ :
          ∃ w₀ : ℂ, ‖w₀‖ = 1 ∧ (p' * (starRingEnd ℂ) q' * (w₀ * w₀)).re = ‖p'‖ * ‖q'‖ := by
        by_cases ht : (starRingEnd ℂ) p' * q' = 0
        · refine ⟨1, by simp, ?_⟩
          rcases mul_eq_zero.mp ht with h | h
          · have hp0 : p' = 0 := (map_eq_zero _).mp h
            simp [hp0]
          · have hq0 : q' = 0 := h
            simp [hq0]
        · set t : ℂ := (starRingEnd ℂ) p' * q' with htdef
          have htnorm : (‖t‖ : ℝ) ≠ 0 := by
            simpa [norm_eq_zero] using ht
          obtain ⟨s, hs⟩ := Complex.isSquare (t / (‖t‖ : ℂ))
          have hsnorm : ‖s‖ = 1 := by
            have h1 : ‖s * s‖ = 1 := by
              rw [← hs, norm_div]
              simp [Complex.norm_real, htnorm]
            rw [norm_mul] at h1
            nlinarith [norm_nonneg s, h1]
          refine ⟨s, hsnorm, ?_⟩
          have hpcq : p' * (starRingEnd ℂ) q' = (starRingEnd ℂ) t := by
            rw [htdef, map_mul, Complex.conj_conj, mul_comm]
          have htt : (starRingEnd ℂ) t * t = ((‖t‖ ^ 2 : ℝ) : ℂ) := by
            rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          have hval : p' * (starRingEnd ℂ) q' * (s * s) = (‖t‖ : ℂ) := by
            rw [hpcq, ← hs, ← mul_div_assoc, htt]
            rw [div_eq_iff (by exact_mod_cast htnorm)]
            push_cast; ring
          rw [hval]
          have hnormt : ‖t‖ = ‖p'‖ * ‖q'‖ := by
            rw [htdef, Complex.norm_mul, Complex.norm_conj]
          rw [Complex.ofReal_re, hnormt]
      have key : ‖Lpq p' q' w₀‖ = ‖p'‖ + ‖q'‖ := by
        have hw₀ns : Complex.normSq w₀ = 1 := by
          rw [Complex.normSq_eq_norm_sq, hw₀norm]; norm_num
        have hcrossterm : (p' * w₀ * (starRingEnd ℂ) (q' * (starRingEnd ℂ) w₀)).re
            = ‖p'‖ * ‖q'‖ := by
          rw [map_mul, Complex.conj_conj]
          have hr : p' * w₀ * ((starRingEnd ℂ) q' * w₀)
              = p' * (starRingEnd ℂ) q' * (w₀ * w₀) := by ring
          rw [hr, hcross]
        have hpns : Complex.normSq p' = ‖p'‖ ^ 2 := Complex.normSq_eq_norm_sq p'
        have hqns : Complex.normSq q' = ‖q'‖ ^ 2 := Complex.normSq_eq_norm_sq q'
        have hnsq : ‖Lpq p' q' w₀‖ ^ 2 = (‖p'‖ + ‖q'‖) ^ 2 := by
          rw [hLpqapp p' q' w₀, ← Complex.normSq_eq_norm_sq, Complex.normSq_add,
            Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_conj,
            hw₀ns, hcrossterm, hpns, hqns]
          ring
        have hnn : (0 : ℝ) ≤ ‖p'‖ + ‖q'‖ := by positivity
        nlinarith [norm_nonneg (Lpq p' q' w₀), hnsq, hnn]
      calc ‖p'‖ + ‖q'‖ = ‖Lpq p' q' w₀‖ := key.symm
        _ ≤ ‖Lpq p' q'‖ * ‖w₀‖ := (Lpq p' q').le_opNorm w₀
        _ = ‖Lpq p' q'‖ := by rw [hw₀norm, mul_one]
    exact le_antisymm hub hlb
  -- `A = Lpq p q`.
  have hALpq : A = Lpq p q := by
    ext w; rw [hAval w, hLpqapp p q w]
  -- The inverse map: `B := Lpq (conj p / d) (-q / d)`.
  set p' : ℂ := (starRingEnd ℂ) p / (d : ℂ) with hp'def
  set q' : ℂ := -q / (d : ℂ) with hq'def
  set B : ℂ →L[ℝ] ℂ := Lpq p' q' with hBdef
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  -- `‖p‖² − ‖q‖² = d` as complex numbers via `mul_conj`.
  have hppc : p * (starRingEnd ℂ) p = ((‖p‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hqqc : q * (starRingEnd ℂ) q = ((‖q‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hdC2 : ((‖p‖ ^ 2 : ℝ) : ℂ) - ((‖q‖ ^ 2 : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_sub]; exact_mod_cast (hddef.symm)
  -- The cancellation identity, in `ℂ`: `conj p * p - q * conj q = d`.
  have hcancel : (starRingEnd ℂ) p * p - q * (starRingEnd ℂ) q = (d : ℂ) := by
    rw [mul_comm ((starRingEnd ℂ) p) p, hppc, hqqc, hdC2]
  -- Two-sided inverse: `B ∘ A = id`.
  have hBA : B.comp A = ContinuousLinearMap.id ℝ ℂ := by
    ext w
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.coe_id', id_eq]
    rw [hBdef, hLpqapp p' q' (A w), hAval w, hp'def, hq'def]
    have hconjdist : (starRingEnd ℂ) (p * w + q * (starRingEnd ℂ) w)
        = (starRingEnd ℂ) p * (starRingEnd ℂ) w + (starRingEnd ℂ) q * w := by
      simp [map_add, map_mul]
    rw [hconjdist]
    field_simp
    linear_combination w * hcancel
  -- Two-sided inverse: `A ∘ B = id`.
  have hAB : A.comp B = ContinuousLinearMap.id ℝ ℂ := by
    ext v
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.coe_id', id_eq]
    rw [hAval (B v), hBdef, hLpqapp p' q' v, hp'def, hq'def]
    have hconjdist : (starRingEnd ℂ) ((starRingEnd ℂ) p / (d : ℂ) * v
          + -q / (d : ℂ) * (starRingEnd ℂ) v)
        = p / (d : ℂ) * (starRingEnd ℂ) v + -(starRingEnd ℂ) q / (d : ℂ) * v := by
      simp [map_add, map_mul, map_div₀, Complex.conj_ofReal]
    rw [hconjdist]
    field_simp
    linear_combination v * hcancel
  -- Identify the inverse with `B`.
  have hinv : ContinuousLinearMap.inverse A = B :=
    ContinuousLinearMap.inverse_eq hAB hBA
  -- Compute `‖B‖ = ‖p'‖ + ‖q'‖ = (‖p‖ + ‖q‖) / d`.
  have hnormp' : ‖p'‖ = ‖p‖ / d := by
    rw [hp'def, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hdpos.le]
  have hnormq' : ‖q'‖ = ‖q‖ / d := by
    rw [hq'def, norm_div, norm_neg, Complex.norm_real, Real.norm_of_nonneg hdpos.le]
  rw [hA, hinv, hBdef, opNormLpq p' q', hnormp', hnormq', hp, hq, hd, hA]
  rw [← add_div]

/-- **A.e. differentiability of the analytic quasiconformal definition.** A map
satisfying `IsQCAnalytic` is differentiable almost everywhere. This is immediate
from the orientation-preserving condition `∀ᵐ z, 0 < det (fderiv ℝ f z)`: where `f`
fails to be differentiable, `fderiv ℝ f z = 0` has determinant `0`, so the
strict positivity forces differentiability. (The substantive Gehring–Lehto content
— that a *geometrically* quasiconformal map is a.e. differentiable — is discharged
inside the geometric ⇒ analytic direction of the equivalence, where this condition
must be produced rather than assumed.) -/
theorem IsQCAnalytic.ae_differentiableAt {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    ∀ᵐ z, DifferentiableAt ℝ f z := by
  filter_upwards [hf.1.2] with z hz
  by_contra hnd
  rw [fderiv_zero_of_not_differentiableAt hnd] at hz
  simp [ContinuousLinearMap.det] at hz

/-- **A zero-modulus subfamily is negligible.** Removing a curve subfamily of zero
modulus from a family does not change its modulus. -/
theorem curveModulus_sdiff_modulus_zero {Γ Γ' : Set (ℝ → ℂ)} (h : Γ' ⊆ Γ)
    (hΓ' : curveModulus Γ' = 0) :
    curveModulus (Γ \ Γ') = curveModulus Γ := by
  -- `Γ \ Γ' ⊆ Γ`, so one inequality is monotonicity.
  refine le_antisymm (curveModulus_mono Set.diff_subset) ?_
  -- For the substantive direction, bound `curveModulus Γ` by the energy of every
  -- density admissible for `Γ \ Γ'`, then take the infimum.
  refine le_iInf₂ ?_
  rintro ρ ⟨hρmeas, hρadm⟩
  -- Abbreviation: the "root energy" of a density.
  set Eρ : ℝ≥0∞ := (∫⁻ z, (ρ z) ^ 2) ^ ((1 : ℝ) / 2) with hEρ
  -- Algebraic facts about the square-root exponent.
  have hsqrt_sq : ∀ x : ℝ≥0∞, (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast (x ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
    norm_num
  -- It suffices to prove `(curveModulus Γ) ^ (1/2) ≤ Eρ`; then square both sides.
  have hroot : (curveModulus Γ) ^ ((1 : ℝ) / 2) ≤ Eρ := by
    -- We show `M^(1/2) ≤ Eρ + ε` for every positive real `ε`, then use the
    -- `ENNReal` Archimedean lemma.
    refine ENNReal.le_of_forall_pos_le_add (fun ε hεpos _ => ?_)
    -- From `curveModulus Γ' = 0 < ε²`, extract `σ` admissible for `Γ'` with small energy.
    have hlt : curveModulus Γ' < (ε : ℝ≥0∞) ^ 2 := by
      rw [hΓ']; positivity
    rw [curveModulus, iInf_lt_iff] at hlt
    obtain ⟨σ, hlt2⟩ := hlt
    rw [iInf_lt_iff] at hlt2
    obtain ⟨⟨hσmeas, hσadm⟩, hσenergy⟩ := hlt2
    -- `ρ + σ` is admissible for `Γ`.
    have hsum_meas : Measurable (fun z => ρ z + σ z) := hρmeas.add hσmeas
    have hsum_adm : IsAdmissibleDensity (fun z => ρ z + σ z) Γ := by
      refine ⟨hsum_meas, fun γ hγ => ?_⟩
      -- `Γ = (Γ \ Γ') ∪ Γ'`, since `Γ' ⊆ Γ`; case on which piece `γ` lies in.
      rw [← Set.diff_union_of_subset h] at hγ
      rcases hγ with hγΓdiff | hγΓ'
      · -- `γ ∈ Γ \ Γ'`; use `ρ`-admissibility.
        refine le_trans (hρadm γ hγΓdiff) ?_
        unfold arcLengthLineIntegral
        refine lintegral_mono fun t => ?_
        gcongr
        exact le_self_add
      · -- `γ ∈ Γ'`; use `σ`-admissibility.
        refine le_trans (hσadm γ hγΓ') ?_
        unfold arcLengthLineIntegral
        refine lintegral_mono fun t => ?_
        gcongr
        exact le_add_self
    -- Energy bound via Minkowski (`p = 2`).
    have hMink : (∫⁻ z, (ρ z + σ z) ^ 2) ^ ((1 : ℝ) / 2)
        ≤ Eρ + (∫⁻ z, (σ z) ^ 2) ^ ((1 : ℝ) / 2) := by
      have := ENNReal.lintegral_Lp_add_le (μ := volume) (p := 2)
        hρmeas.aemeasurable hσmeas.aemeasurable (by norm_num)
      simpa only [Pi.add_apply, ENNReal.rpow_two, hEρ] using this
    -- `(∫⁻ σ²)^(1/2) ≤ ε` from `∫⁻ σ² < ε²`.
    have hσroot : (∫⁻ z, (σ z) ^ 2) ^ ((1 : ℝ) / 2) ≤ (ε : ℝ≥0∞) := by
      calc (∫⁻ z, (σ z) ^ 2) ^ ((1 : ℝ) / 2)
          ≤ ((ε : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2) := by
            have : (∫⁻ z, (σ z) ^ 2) ≤ (ε : ℝ≥0∞) ^ 2 := hσenergy.le
            gcongr
        _ = (ε : ℝ≥0∞) := by
            rw [← ENNReal.rpow_natCast (ε : ℝ≥0∞) 2, ← ENNReal.rpow_mul]
            norm_num
    -- Chain: `M ≤ ∫⁻ (ρ+σ)²`, then take roots and combine.
    have hM_le : curveModulus Γ ≤ ∫⁻ z, (ρ z + σ z) ^ 2 :=
      iInf₂_le (fun z => ρ z + σ z) hsum_adm
    calc (curveModulus Γ) ^ ((1 : ℝ) / 2)
        ≤ (∫⁻ z, (ρ z + σ z) ^ 2) ^ ((1 : ℝ) / 2) := by gcongr
      _ ≤ Eρ + (∫⁻ z, (σ z) ^ 2) ^ ((1 : ℝ) / 2) := hMink
      _ ≤ Eρ + (ε : ℝ≥0∞) := by gcongr
  -- Square the root inequality to conclude.
  calc curveModulus Γ
      = ((curveModulus Γ) ^ ((1 : ℝ) / 2)) ^ 2 := (hsqrt_sq _).symm
    _ ≤ Eρ ^ 2 := by gcongr
    _ = ∫⁻ z, (ρ z) ^ 2 := hsqrt_sq _

/-- **Subadditivity for null families.** The union of two zero-modulus curve
families is again a zero-modulus family. (Special case of countable subadditivity
of the modulus; the only instance the length–area transfer consumes.) -/
theorem curveModulus_union_zero {Γ₁ Γ₂ : Set (ℝ → ℂ)}
    (h₁ : curveModulus Γ₁ = 0) (h₂ : curveModulus Γ₂ = 0) :
    curveModulus (Γ₁ ∪ Γ₂) = 0 := by
  -- The square-root exponent and its inverse on `ℝ≥0∞`.
  have hsqrt_sq : ∀ x : ℝ≥0∞, (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast (x ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
    norm_num
  -- It suffices to show the *root energy* `M^(1/2) = 0`; then square.
  suffices hroot0 : (curveModulus (Γ₁ ∪ Γ₂)) ^ ((1 : ℝ) / 2) = 0 by
    have := hsqrt_sq (curveModulus (Γ₁ ∪ Γ₂))
    rw [hroot0] at this; simpa using this.symm
  -- Show `M^(1/2) ≤ ε` for every positive real `ε`, hence `= 0`.
  refine le_antisymm ?_ (zero_le _)
  refine ENNReal.le_of_forall_pos_le_add (fun ε hεpos _ => ?_)
  rw [zero_add]
  -- Extract, from `curveModulus Γᵢ = 0 < (ε/2)²`, densities `ρᵢ` admissible for `Γᵢ`
  -- with root energy `≤ ε/2`.  Work with the half `η := (ε : ℝ≥0∞)/2 > 0`.
  set η : ℝ≥0∞ := (ε : ℝ≥0∞) / 2 with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]; exact ENNReal.div_pos (by exact_mod_cast hεpos.ne') (by norm_num)
  have hηsum : η + η = (ε : ℝ≥0∞) := by
    rw [hηdef, ENNReal.add_halves]
  have extract : ∀ {Γ : Set (ℝ → ℂ)}, curveModulus Γ = 0 →
      ∃ ρ : ℂ → ℝ≥0∞, IsAdmissibleDensity ρ Γ ∧
        (∫⁻ z, (ρ z) ^ 2) ^ ((1 : ℝ) / 2) ≤ η := by
    intro Γ hΓ
    have hlt : curveModulus Γ < η ^ 2 := by
      rw [hΓ]; positivity
    rw [curveModulus, iInf_lt_iff] at hlt
    obtain ⟨ρ, hlt2⟩ := hlt
    rw [iInf_lt_iff] at hlt2
    obtain ⟨hρadm, hρenergy⟩ := hlt2
    refine ⟨ρ, hρadm, ?_⟩
    calc (∫⁻ z, (ρ z) ^ 2) ^ ((1 : ℝ) / 2)
        ≤ (η ^ 2) ^ ((1 : ℝ) / 2) := by gcongr
      _ = η := by
          rw [← ENNReal.rpow_natCast η 2, ← ENNReal.rpow_mul]
          norm_num
  obtain ⟨ρ, ⟨hρmeas, hρadm⟩, hρroot⟩ := extract h₁
  obtain ⟨σ, ⟨hσmeas, hσadm⟩, hσroot⟩ := extract h₂
  -- `ρ + σ` is admissible for `Γ₁ ∪ Γ₂`.
  have hsum_meas : Measurable (fun z => ρ z + σ z) := hρmeas.add hσmeas
  have hsum_adm : IsAdmissibleDensity (fun z => ρ z + σ z) (Γ₁ ∪ Γ₂) := by
    refine ⟨hsum_meas, fun γ hγ => ?_⟩
    rcases hγ with hγ1 | hγ2
    · refine le_trans (hρadm γ hγ1) ?_
      unfold arcLengthLineIntegral
      exact lintegral_mono fun t => by gcongr; exact le_self_add
    · refine le_trans (hσadm γ hγ2) ?_
      unfold arcLengthLineIntegral
      exact lintegral_mono fun t => by gcongr; exact le_add_self
  -- Minkowski (`p = 2`) bounds the root energy of `ρ + σ`.
  have hMink : (∫⁻ z, (ρ z + σ z) ^ 2) ^ ((1 : ℝ) / 2)
      ≤ (∫⁻ z, (ρ z) ^ 2) ^ ((1 : ℝ) / 2) + (∫⁻ z, (σ z) ^ 2) ^ ((1 : ℝ) / 2) := by
    have := ENNReal.lintegral_Lp_add_le (μ := volume) (p := 2)
      hρmeas.aemeasurable hσmeas.aemeasurable (by norm_num)
    simpa only [Pi.add_apply, ENNReal.rpow_two] using this
  -- Chain: `curveModulus (Γ₁ ∪ Γ₂) ≤ ∫⁻ (ρ+σ)²`, take roots, combine.
  have hM_le : curveModulus (Γ₁ ∪ Γ₂) ≤ ∫⁻ z, (ρ z + σ z) ^ 2 :=
    iInf₂_le (fun z => ρ z + σ z) hsum_adm
  calc (curveModulus (Γ₁ ∪ Γ₂)) ^ ((1 : ℝ) / 2)
      ≤ (∫⁻ z, (ρ z + σ z) ^ 2) ^ ((1 : ℝ) / 2) := by gcongr
    _ ≤ (∫⁻ z, (ρ z) ^ 2) ^ ((1 : ℝ) / 2) + (∫⁻ z, (σ z) ^ 2) ^ ((1 : ℝ) / 2) := hMink
    _ ≤ η + η := by gcongr
    _ = (ε : ℝ≥0∞) := hηsum

/-- **Curves meeting a null set have zero modulus (weighted form).** If `N ⊆ ℂ`
is Lebesgue-null and measurable, then the family of curves whose *arc-length*
measure of the contact set `{t | γ t ∈ N}` is positive — equivalently, those `γ`
with `1 ≤ ∫₀¹ (∞ · 𝟙_N)(γ t) ‖γ' t‖ dt` — has zero modulus. The witnessing density
is `∞ · 𝟙_N`: it is admissible by hypothesis and has zero energy because
`∫⁻ (∞ · 𝟙_N)² = ∞ · volume N = 0`. -/
theorem curveModulus_meetsNullSet_zero {N : Set ℂ} (hNmeas : MeasurableSet N)
    (hNnull : volume N = 0) (Γ : Set (ℝ → ℂ)) :
    curveModulus {γ ∈ Γ | 1 ≤ arcLengthLineIntegral (N.indicator (fun _ => ∞)) γ} = 0 := by
  -- The density `ρ_N := ∞ · 𝟙_N`.
  set ρN : ℂ → ℝ≥0∞ := N.indicator (fun _ => ∞) with hρN
  -- Measurability of `ρ_N`.
  have hρNmeas : Measurable ρN := by
    rw [hρN]; exact (measurable_const).indicator hNmeas
  -- `ρ_N` is admissible for the exceptional family (admissibility is the very
  -- defining condition of the family).
  have hadm : IsAdmissibleDensity ρN
      {γ ∈ Γ | 1 ≤ arcLengthLineIntegral ρN γ} := by
    refine ⟨hρNmeas, fun γ hγ => hγ.2⟩
  -- The energy of `ρ_N` is zero: `∫⁻ (∞ · 𝟙_N)² = ∫⁻_N ∞ = ∞ · volume N = 0`.
  have henergy : ∫⁻ z, (ρN z) ^ 2 = 0 := by
    have hpt : (fun z => (ρN z) ^ 2) = N.indicator (fun _ => ∞) := by
      funext z; rw [hρN]
      by_cases hz : z ∈ N
      · simp only [Set.indicator_of_mem hz]
        exact ENNReal.top_pow (by norm_num)
      · simp only [Set.indicator_of_notMem hz]
        norm_num
    rw [hpt, lintegral_indicator hNmeas, setLIntegral_measure_zero _ _ hNnull]
  -- The modulus is bounded by this zero energy.
  refine le_antisymm ?_ (zero_le _)
  calc curveModulus {γ ∈ Γ | 1 ≤ arcLengthLineIntegral ρN γ}
      ≤ ∫⁻ z, (ρN z) ^ 2 := iInf₂_le ρN hadm
    _ = 0 := henergy

/-- **Finite-energy density with infinite line integral ⇒ zero modulus.** If a
measurable density `ρ₀` has *finite* energy `∫⁻ ρ₀² < ∞` and its arc-length line
integral is infinite along every curve of a family `Δ`, then `Δ` has zero modulus.

For each `k ≥ 1` the truncated density `ρ₀/k` is admissible for `Δ`: its line
integral is `(1/k)·∞ = ∞ ≥ 1`. Its energy is `∫⁻ (ρ₀/k)² = (1/k²)·∫⁻ ρ₀²`, so
`curveModulus Δ ≤ (∫⁻ ρ₀²)·(1/k²)` for every `k`; the right-hand side tends to `0`
as `k → ∞` (finiteness of `∫⁻ ρ₀²` is what makes the limit `0`), giving the claim.
This is the elementary `ℝ≥0∞` core of Fuglede's modulus estimate. -/
theorem curveModulus_zero_of_lintegralSq_finite {ρ₀ : ℂ → ℝ≥0∞}
    (hρ₀meas : Measurable ρ₀) (hρ₀fin : ∫⁻ z, (ρ₀ z) ^ 2 ≠ ∞)
    {Δ : Set (ℝ → ℂ)} (hΔ : ∀ γ ∈ Δ, arcLengthLineIntegral ρ₀ γ = ∞) :
    curveModulus Δ = 0 := by
  -- The energy of `ρ₀`.
  set C : ℝ≥0∞ := ∫⁻ z, (ρ₀ z) ^ 2 with hC
  -- For each natural `k ≥ 1`, the truncated density `ρ₀/k` is admissible and has
  -- energy `C·(k⁻¹)²`.  Hence `curveModulus Δ ≤ C·(k⁻¹)²` eventually.
  have hbound : ∀ k : ℕ, 1 ≤ k → curveModulus Δ ≤ C * ((k : ℝ≥0∞))⁻¹ ^ 2 := by
    intro k hkpos
    -- The truncated density `ρ_k := ρ₀/k`.
    set ρk : ℂ → ℝ≥0∞ := fun z => ρ₀ z / (k : ℝ≥0∞) with hρk
    have hkne : (k : ℝ≥0∞) ≠ 0 := by
      simp only [Ne, Nat.cast_eq_zero]; omega
    have hρkmeas : Measurable ρk := by
      rw [hρk]; exact hρ₀meas.div_const _
    -- Admissibility: `ALI (ρ₀/k) γ = (1/k)·ALI ρ₀ γ = (1/k)·∞ = ∞ ≥ 1`.
    have hadm : IsAdmissibleDensity ρk Δ := by
      refine ⟨hρkmeas, fun γ hγ => ?_⟩
      have hALI : arcLengthLineIntegral ρk γ = ∞ := by
        unfold arcLengthLineIntegral
        have hpt : (fun t => ρk (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞))
            = fun t => ((k : ℝ≥0∞))⁻¹ * (ρ₀ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞)) := by
          funext t; simp only [hρk, ENNReal.div_eq_inv_mul]; ring
        rw [hpt, lintegral_const_mul' _ _ (by simp [hkne])]
        have hinf : (∫⁻ t in Set.Icc (0 : ℝ) 1, ρ₀ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞)) = ∞ :=
          hΔ γ hγ
        rw [hinf, ENNReal.mul_top (by simp)]
      rw [hALI]; exact le_top
    -- Energy: `∫⁻ (ρ₀/k)² = (k⁻¹)²·C`.
    have henergy : ∫⁻ z, (ρk z) ^ 2 = C * ((k : ℝ≥0∞))⁻¹ ^ 2 := by
      have hpt : (fun z => (ρk z) ^ 2)
          = fun z => ((k : ℝ≥0∞))⁻¹ ^ 2 * (ρ₀ z) ^ 2 := by
        funext z; simp only [hρk, ENNReal.div_eq_inv_mul, mul_pow]
      rw [hpt, lintegral_const_mul' _ _ (by simp [hkne]), mul_comm, hC]
    calc curveModulus Δ
        ≤ ∫⁻ z, (ρk z) ^ 2 := iInf₂_le ρk hadm
      _ = C * ((k : ℝ≥0∞))⁻¹ ^ 2 := henergy
  -- The bound `C·(k⁻¹)² → C·0 = 0` as `k → ∞`, so `curveModulus Δ ≤ 0`.
  refine le_antisymm ?_ (zero_le _)
  have htend : Filter.Tendsto (fun k : ℕ => C * ((k : ℝ≥0∞))⁻¹ ^ 2) Filter.atTop
      (nhds (C * 0)) :=
    ENNReal.Tendsto.const_mul
      (by simpa using ENNReal.Tendsto.pow (n := 2) ENNReal.tendsto_inv_nat_nhds_zero)
      (Or.inr hρ₀fin)
  rw [mul_zero] at htend
  refine ge_of_tendsto htend ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk using hbound k hk

/-- **Fuglede line-integral convergence (the modulus-a.e. core).** Let `G n` be a
sequence of nonnegative measurable densities whose `L²` norms have summable roots,
`∑ₙ (∫⁻ (G n)²)^{1/2} < ∞`. Then, along every family `Γ` of continuous curves, the
subfamily on which the arc-length line integrals `∫_γ (G n) ds` fail to tend to `0`
has zero modulus.

This is the elementary form of Fuglede's theorem on the plane, and it is the bridge
that turns the mollification `L²`-convergence of a Sobolev gradient into
*modulus-a.e.* convergence of its trace along curves — sidestepping the coarea
formula entirely. The proof is the classical finite-energy-density argument: set
`ρ₀ := ∑ₙ G n`. By the countable Minkowski inequality for `∫⁻ ρ₀²`
(monotone limit of the finite `eLpNorm_sum_le`) the summable-roots hypothesis makes
`∫⁻ ρ₀² < ∞`. For a continuous curve `γ`, additivity of the line integral
(`lintegral_tsum`, using continuity of `γ` for measurability of `G n ∘ γ`) gives
`arcLengthLineIntegral ρ₀ γ = ∑ₙ arcLengthLineIntegral (G n) γ`; hence whenever the
summands fail to tend to `0`, the sum is `∞`. So the bad subfamily is contained in
`{γ | arcLengthLineIntegral ρ₀ γ = ∞}`, which has zero modulus by
`curveModulus_zero_of_lintegralSq_finite`; conclude by `curveModulus_mono`. -/
theorem curveModulus_lineIntegral_not_tendsto_zero {G : ℕ → ℂ → ℝ≥0∞}
    (hGmeas : ∀ n, Measurable (G n))
    (hsum : ∑' n, (∫⁻ z, (G n z) ^ 2) ^ (1 / 2 : ℝ) ≠ ∞)
    {Γ : Set (ℝ → ℂ)} (hΓcont : ∀ γ ∈ Γ, Continuous γ) :
    curveModulus {γ ∈ Γ | ¬ Filter.Tendsto
        (fun n => arcLengthLineIntegral (G n) γ) Filter.atTop (nhds 0)} = 0 := by
  classical
  -- The square-root exponent inverts squaring (both directions on `ℝ≥0∞`).
  have hsqrt_sq : ∀ x : ℝ≥0∞, (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast (x ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
    norm_num
  have hsq_sqrt : ∀ x : ℝ≥0∞, (x ^ 2) ^ ((1 : ℝ) / 2) = x := by
    intro x
    rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
    norm_num
  -- The "root energy" of a density.
  set rootE : (ℂ → ℝ≥0∞) → ℝ≥0∞ := fun ρ => (∫⁻ z, (ρ z) ^ 2) ^ ((1 : ℝ) / 2) with hrootE
  -- ===================================================================
  -- Step 2: countable Minkowski for `L²` of `ℝ≥0∞`-valued functions.
  -- Built from the binary `lintegral_Lp_add_le` by a `Finset` induction
  -- and monotone convergence (`tsum = ⨆ finite sums`).
  -- ===================================================================
  -- Finite Minkowski: `rootE (∑_{n∈s} ρₙ) ≤ ∑_{n∈s} rootE ρₙ`.
  have finMink : ∀ {ρ : ℕ → ℂ → ℝ≥0∞}, (∀ n, Measurable (ρ n)) →
      ∀ s : Finset ℕ, rootE (fun z => ∑ n ∈ s, ρ n z) ≤ ∑ n ∈ s, rootE (ρ n) := by
    intro ρ hρmeas s
    classical
    induction s using Finset.induction with
    | empty => simp only [Finset.sum_empty, hrootE]; simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        have hbin : rootE (fun z => ρ a z + ∑ n ∈ s, ρ n z)
            ≤ rootE (ρ a) + rootE (fun z => ∑ n ∈ s, ρ n z) := by
          have hsummeas : Measurable (fun z => ∑ n ∈ s, ρ n z) :=
            Finset.measurable_sum s (fun n _ => hρmeas n)
          have := ENNReal.lintegral_Lp_add_le (μ := volume) (p := 2)
            (hρmeas a).aemeasurable hsummeas.aemeasurable (by norm_num)
          simpa only [Pi.add_apply, ENNReal.rpow_two, hrootE] using this
        calc rootE (fun z => ∑ n ∈ insert a s, ρ n z)
            = rootE (fun z => ρ a z + ∑ n ∈ s, ρ n z) := by
              refine congrArg rootE ?_
              funext z; rw [Finset.sum_insert ha]
          _ ≤ rootE (ρ a) + rootE (fun z => ∑ n ∈ s, ρ n z) := hbin
          _ ≤ rootE (ρ a) + ∑ n ∈ s, rootE (ρ n) := by gcongr
  -- Countable Minkowski: `rootE (∑' n, ρₙ) ≤ ∑' n, rootE ρₙ`.
  have tsumMink : ∀ {ρ : ℕ → ℂ → ℝ≥0∞}, (∀ n, Measurable (ρ n)) →
      rootE (fun z => ∑' n, ρ n z) ≤ ∑' n, rootE (ρ n) := by
    intro ρ hρmeas
    have hsq_cont : Continuous (fun x : ℝ≥0∞ => x ^ 2) := by continuity
    have hsq_mono : Monotone (fun x : ℝ≥0∞ => x ^ 2) := fun a b hab => by
      simpa using pow_le_pow_left' hab 2
    have hpartialsup : (∫⁻ z, (∑' n, ρ n z) ^ 2)
        = ⨆ N : ℕ, ∫⁻ z, (∑ n ∈ Finset.range N, ρ n z) ^ 2 := by
      have hsq_eq : (fun z => (∑' n, ρ n z) ^ 2)
          = fun z => ⨆ N : ℕ, (∑ n ∈ Finset.range N, ρ n z) ^ 2 := by
        funext z
        rw [ENNReal.tsum_eq_iSup_nat]
        exact hsq_mono.map_iSup_of_continuousAt hsq_cont.continuousAt (by simp)
      rw [hsq_eq]
      rw [lintegral_iSup
        (fun N => (Finset.measurable_sum (Finset.range N) (fun n _ => hρmeas n)).pow_const 2) ?_]
      intro N M hNM z
      exact hsq_mono (Finset.sum_le_sum_of_subset (Finset.range_mono hNM))
    have henergy_le : (∫⁻ z, (∑' n, ρ n z) ^ 2) ≤ (∑' n, rootE (ρ n)) ^ 2 := by
      rw [hpartialsup]
      refine iSup_le (fun N => ?_)
      calc ∫⁻ z, (∑ n ∈ Finset.range N, ρ n z) ^ 2
          = (rootE (fun z => ∑ n ∈ Finset.range N, ρ n z)) ^ 2 := by
            rw [hrootE]; rw [hsqrt_sq]
        _ ≤ (∑ n ∈ Finset.range N, rootE (ρ n)) ^ 2 := by
            gcongr; exact finMink hρmeas (Finset.range N)
        _ ≤ (∑' n, rootE (ρ n)) ^ 2 := by gcongr; exact ENNReal.sum_le_tsum (Finset.range N)
    calc rootE (fun z => ∑' n, ρ n z)
        = (∫⁻ z, (∑' n, ρ n z) ^ 2) ^ ((1 : ℝ) / 2) := rfl
      _ ≤ ((∑' n, rootE (ρ n)) ^ 2) ^ ((1 : ℝ) / 2) := by gcongr
      _ = ∑' n, rootE (ρ n) := hsq_sqrt _
  -- ===================================================================
  -- Step 1 & 2 instantiated: `ρ₀ := ∑' n, G n` has finite energy.
  -- ===================================================================
  set ρ₀ : ℂ → ℝ≥0∞ := fun z => ∑' n, G n z with hρ₀
  have hρ₀meas : Measurable ρ₀ := Measurable.ennreal_tsum hGmeas
  -- `rootE (G n) = (∫⁻ (G n)²)^{1/2}`, so `hsum` says `∑' n, rootE (G n) ≠ ∞`.
  have hsum' : ∑' n, rootE (G n) ≠ ∞ := hsum
  -- Countable Minkowski: `rootE ρ₀ ≤ ∑' n, rootE (G n) < ∞`.
  have hrootE_fin : rootE ρ₀ ≠ ∞ := by
    have hle : rootE ρ₀ ≤ ∑' n, rootE (G n) := tsumMink hGmeas
    exact ne_top_of_le_ne_top hsum' hle
  -- Hence the energy `∫⁻ ρ₀² < ∞`.
  have hρ₀fin : ∫⁻ z, (ρ₀ z) ^ 2 ≠ ∞ := by
    intro hcontra
    apply hrootE_fin
    rw [hrootE]
    simp only [hcontra]
    rw [ENNReal.top_rpow_of_pos (by norm_num)]
  -- ===================================================================
  -- Step 3: line-integral additivity along a continuous curve.
  -- ===================================================================
  have hadditive : ∀ γ : ℝ → ℂ, Continuous γ →
      arcLengthLineIntegral ρ₀ γ = ∑' n, arcLengthLineIntegral (G n) γ := by
    intro γ hγcont
    unfold arcLengthLineIntegral
    -- AEMeasurability of each summand on the restricted measure.
    have hmeas_summand : ∀ n, AEMeasurable
        (fun t => G n (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞))
        (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      intro n
      have h1 : Measurable (fun t => G n (γ t)) := (hGmeas n).comp hγcont.measurable
      have h2 : Measurable (fun t : ℝ => (‖deriv γ t‖₊ : ℝ≥0∞)) :=
        (measurable_deriv γ).nnnorm.coe_nnreal_ennreal
      exact (h1.mul h2).aemeasurable
    -- Pull the tsum out of the integrand and swap with the integral.
    have hpt : (fun t => ρ₀ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞))
        = fun t => ∑' n, G n (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
      funext t
      rw [hρ₀]
      simp only
      rw [ENNReal.tsum_mul_right]
    rw [hpt, lintegral_tsum hmeas_summand]
  -- ===================================================================
  -- Step 4: the bad family lies in `{γ | arcLengthLineIntegral ρ₀ γ = ∞}`.
  -- ===================================================================
  refine curveModulus_zero_of_lintegralSq_finite hρ₀meas hρ₀fin ?_
  intro γ hγ
  obtain ⟨hγΓ, hγbad⟩ := hγ
  have hγcont : Continuous γ := hΓcont γ hγΓ
  rw [hadditive γ hγcont]
  -- If the sum were finite, its terms would tend to `0`, contradicting `hγbad`.
  by_contra hne
  apply hγbad
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hne

/-- **Countable subadditivity for null families.** A countable union of
zero-modulus curve families is again a zero-modulus family. (This is the standard
countable subadditivity of the conformal modulus, specialised to the case where
every piece is null. The binary case `curveModulus_union_zero` is proved above by
the `ρ + σ` density and finite Minkowski; the countable case replaces the finite
sum by `∑'ₖ εₖ⁻¹-weighted` densities `ρₖ` with `∑ₖ (root energy of ρₖ) ≤ ε`, using
the countable Minkowski inequality for `∫⁻ (∑ₖ ρₖ)²` — the only missing analytic
input, hence isolated here as a helper.) -/
theorem curveModulus_iUnion_zero {Γ : ℕ → Set (ℝ → ℂ)}
    (h : ∀ n, curveModulus (Γ n) = 0) :
    curveModulus (⋃ n, Γ n) = 0 := by
  classical
  -- The square-root exponent and its inverse on `ℝ≥0∞`.
  have hsqrt_sq : ∀ x : ℝ≥0∞, (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast (x ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
    norm_num
  -- ===================================================================
  -- Countable Minkowski for `L²` of `ℝ≥0∞`-valued functions: the only
  -- analytic input.  Built from the binary case `lintegral_Lp_add_le`
  -- by a `Finset` induction and monotone convergence (`tsum = ⨆ sums`).
  -- ===================================================================
  -- Abbreviation for the "root energy" of a density.
  set rootE : (ℂ → ℝ≥0∞) → ℝ≥0∞ := fun ρ => (∫⁻ z, (ρ z) ^ 2) ^ ((1 : ℝ) / 2) with hrootE
  -- Finite Minkowski: `rootE (∑_{n∈s} ρₙ) ≤ ∑_{n∈s} rootE ρₙ`.
  have finMink : ∀ {ρ : ℕ → ℂ → ℝ≥0∞}, (∀ n, Measurable (ρ n)) →
      ∀ s : Finset ℕ, rootE (fun z => ∑ n ∈ s, ρ n z) ≤ ∑ n ∈ s, rootE (ρ n) := by
    intro ρ hρmeas s
    classical
    induction s using Finset.induction with
    | empty => simp only [Finset.sum_empty, hrootE]; simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        -- `rootE (ρ a + ∑_{s} ρ) ≤ rootE (ρ a) + rootE (∑_{s} ρ)` by binary Minkowski.
        have hbin : rootE (fun z => ρ a z + ∑ n ∈ s, ρ n z)
            ≤ rootE (ρ a) + rootE (fun z => ∑ n ∈ s, ρ n z) := by
          have hsummeas : Measurable (fun z => ∑ n ∈ s, ρ n z) :=
            Finset.measurable_sum s (fun n _ => hρmeas n)
          have := ENNReal.lintegral_Lp_add_le (μ := volume) (p := 2)
            (hρmeas a).aemeasurable hsummeas.aemeasurable (by norm_num)
          simpa only [Pi.add_apply, ENNReal.rpow_two, hrootE] using this
        calc rootE (fun z => ∑ n ∈ insert a s, ρ n z)
            = rootE (fun z => ρ a z + ∑ n ∈ s, ρ n z) := by
              refine congrArg rootE ?_
              funext z; rw [Finset.sum_insert ha]
          _ ≤ rootE (ρ a) + rootE (fun z => ∑ n ∈ s, ρ n z) := hbin
          _ ≤ rootE (ρ a) + ∑ n ∈ s, rootE (ρ n) := by gcongr
  -- The square-root exponent inverts squaring (the other direction).
  have hsq_sqrt : ∀ x : ℝ≥0∞, (x ^ 2) ^ ((1 : ℝ) / 2) = x := by
    intro x
    rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
    norm_num
  -- Countable Minkowski: `rootE (∑' n, ρₙ) ≤ ∑' n, rootE ρₙ`.  Proved by bounding
  -- the *energy* `∫⁻ (∑' ρ)² ≤ (∑' rootE ρ)²` and then taking square roots.
  have tsumMink : ∀ {ρ : ℕ → ℂ → ℝ≥0∞}, (∀ n, Measurable (ρ n)) →
      rootE (fun z => ∑' n, ρ n z) ≤ ∑' n, rootE (ρ n) := by
    intro ρ hρmeas
    -- Squaring on `ℝ≥0∞` is continuous and monotone, hence commutes with directed sups.
    have hsq_cont : Continuous (fun x : ℝ≥0∞ => x ^ 2) := by continuity
    have hsq_mono : Monotone (fun x : ℝ≥0∞ => x ^ 2) := fun a b hab => by
      simpa using pow_le_pow_left' hab 2
    -- Energy of the tsum equals the sup of energies of finite partial sums over
    -- `range N` (monotone convergence applied to `(∑_{range N} ρ)²`, monotone in `N`).
    have hpartialsup : (∫⁻ z, (∑' n, ρ n z) ^ 2)
        = ⨆ N : ℕ, ∫⁻ z, (∑ n ∈ Finset.range N, ρ n z) ^ 2 := by
      have hsq_eq : (fun z => (∑' n, ρ n z) ^ 2)
          = fun z => ⨆ N : ℕ, (∑ n ∈ Finset.range N, ρ n z) ^ 2 := by
        funext z
        rw [ENNReal.tsum_eq_iSup_nat]
        exact hsq_mono.map_iSup_of_continuousAt hsq_cont.continuousAt (by simp)
      rw [hsq_eq]
      rw [lintegral_iSup
        (fun N => (Finset.measurable_sum (Finset.range N) (fun n _ => hρmeas n)).pow_const 2) ?_]
      intro N M hNM z
      exact hsq_mono (Finset.sum_le_sum_of_subset (Finset.range_mono hNM))
    -- Bound the energy of the tsum by `(∑' rootE ρ)²`.
    have henergy_le : (∫⁻ z, (∑' n, ρ n z) ^ 2) ≤ (∑' n, rootE (ρ n)) ^ 2 := by
      rw [hpartialsup]
      refine iSup_le (fun N => ?_)
      -- `(∫⁻ (∑_range ρ)²) = (rootE (∑_range ρ))² ≤ (∑_range rootE ρ)² ≤ (∑' rootE ρ)²`.
      calc ∫⁻ z, (∑ n ∈ Finset.range N, ρ n z) ^ 2
          = (rootE (fun z => ∑ n ∈ Finset.range N, ρ n z)) ^ 2 := by
            rw [hrootE]; rw [hsqrt_sq]
        _ ≤ (∑ n ∈ Finset.range N, rootE (ρ n)) ^ 2 := by
            gcongr; exact finMink hρmeas (Finset.range N)
        _ ≤ (∑' n, rootE (ρ n)) ^ 2 := by gcongr; exact ENNReal.sum_le_tsum (Finset.range N)
    -- Take square roots.
    calc rootE (fun z => ∑' n, ρ n z)
        = (∫⁻ z, (∑' n, ρ n z) ^ 2) ^ ((1 : ℝ) / 2) := rfl
      _ ≤ ((∑' n, rootE (ρ n)) ^ 2) ^ ((1 : ℝ) / 2) := by gcongr
      _ = ∑' n, rootE (ρ n) := hsq_sqrt _
  -- ===================================================================
  -- Main argument: assemble admissible densities `ρₙ` with `rootE ρₙ ≤ ε/2^{n+1}`.
  -- ===================================================================
  -- ===================================================================
  -- Main argument: it suffices to show the *root energy*
  -- `(curveModulus (⋃ Γ n))^(1/2) = 0`; then square via `hsqrt_sq`.
  -- ===================================================================
  suffices hroot0 : (curveModulus (⋃ n, Γ n)) ^ ((1 : ℝ) / 2) = 0 by
    have := hsqrt_sq (curveModulus (⋃ n, Γ n))
    rw [hroot0] at this; simpa using this.symm
  refine le_antisymm ?_ (zero_le _)
  refine ENNReal.le_of_forall_pos_le_add (fun ε hεpos _ => ?_)
  rw [zero_add]
  -- For each `n`, extract `ρₙ` admissible for `Γ n` with `rootE ρₙ ≤ ε/2^{n+1}`.
  set η : ℕ → ℝ≥0∞ := fun n => (ε : ℝ≥0∞) / 2 ^ (n + 1) with hη
  have hηpos : ∀ n, 0 < η n := by
    intro n
    rw [hη]
    exact ENNReal.div_pos (by exact_mod_cast hεpos.ne') (by simp)
  have hηsum : ∑' n, η n = (ε : ℝ≥0∞) := by
    have hgeom : ∑' n : ℕ, ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ = 1 := by
      have hrw : (fun n : ℕ => ((2 : ℝ≥0∞) ^ (n + 1))⁻¹)
          = fun n : ℕ => ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) := by
        funext n; rw [ENNReal.inv_pow]
      rw [hrw, ENNReal.tsum_geometric_add_one]
      rw [ENNReal.one_sub_inv_two, inv_inv]
      rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
    calc ∑' n, η n
        = ∑' n : ℕ, ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ * (ε : ℝ≥0∞) := by
          refine tsum_congr (fun n => ?_)
          change (ε : ℝ≥0∞) / 2 ^ (n + 1) = _
          rw [ENNReal.div_eq_inv_mul, mul_comm]
      _ = (∑' n : ℕ, ((2 : ℝ≥0∞) ^ (n + 1))⁻¹) * (ε : ℝ≥0∞) := by rw [ENNReal.tsum_mul_right]
      _ = (ε : ℝ≥0∞) := by rw [hgeom, one_mul]
  have extract : ∀ n, ∃ ρ : ℂ → ℝ≥0∞, IsAdmissibleDensity ρ (Γ n) ∧ rootE ρ ≤ η n := by
    intro n
    have hlt : curveModulus (Γ n) < (η n) ^ 2 := by
      rw [h n]; exact ENNReal.pow_pos (hηpos n) 2
    rw [curveModulus, iInf_lt_iff] at hlt
    obtain ⟨ρ, hlt2⟩ := hlt
    rw [iInf_lt_iff] at hlt2
    obtain ⟨hρadm, hρenergy⟩ := hlt2
    refine ⟨ρ, hρadm, ?_⟩
    rw [hrootE]
    calc (∫⁻ z, (ρ z) ^ 2) ^ ((1 : ℝ) / 2)
        ≤ ((η n) ^ 2) ^ ((1 : ℝ) / 2) := by
            have : (∫⁻ z, (ρ z) ^ 2) ≤ (η n) ^ 2 := hρenergy.le
            gcongr
      _ = η n := by rw [← ENNReal.rpow_natCast (η n) 2, ← ENNReal.rpow_mul]; norm_num
  choose ρ hρadm hρroot using extract
  have hρmeas : ∀ n, Measurable (ρ n) := fun n => (hρadm n).1
  -- The summed density `rhoSum := ∑' n, ρₙ`.
  set rhoSum : ℂ → ℝ≥0∞ := fun z => ∑' n, ρ n z with hrhoSum
  have hrhoSum_meas : Measurable rhoSum := Measurable.ennreal_tsum hρmeas
  -- `rhoSum` is admissible for `⋃ Γ n` (it dominates each `ρₙ`).
  have hrhoSum_adm : IsAdmissibleDensity rhoSum (⋃ n, Γ n) := by
    refine ⟨hrhoSum_meas, fun γ hγ => ?_⟩
    rw [Set.mem_iUnion] at hγ
    obtain ⟨n, hγn⟩ := hγ
    refine le_trans ((hρadm n).2 γ hγn) ?_
    unfold arcLengthLineIntegral
    refine lintegral_mono fun t => ?_
    gcongr
    exact ENNReal.le_tsum n
  -- Energy bound via countable Minkowski: `rootE rhoSum ≤ ∑' n, η n = ε`.
  have hrootbound : rootE rhoSum ≤ (ε : ℝ≥0∞) := by
    calc rootE rhoSum = rootE (fun z => ∑' n, ρ n z) := rfl
      _ ≤ ∑' n, rootE (ρ n) := tsumMink hρmeas
      _ ≤ ∑' n, η n := ENNReal.tsum_le_tsum hρroot
      _ = (ε : ℝ≥0∞) := hηsum
  -- Bound the root of the modulus: `(curveModulus)^(1/2) ≤ rootE rhoSum ≤ ε`.
  calc (curveModulus (⋃ n, Γ n)) ^ ((1 : ℝ) / 2)
      ≤ (∫⁻ z, (rhoSum z) ^ 2) ^ ((1 : ℝ) / 2) := by
        gcongr; exact iInf₂_le rhoSum hrhoSum_adm
    _ = rootE rhoSum := rfl
    _ ≤ (ε : ℝ≥0∞) := hrootbound

set_option maxHeartbeats 400000 in
-- The proof inlines a horizontal core (Fubini transfer to `ℝ × ℝ`, per-line FTC and
-- difference-quotient uniqueness) and the `v = I` reduction through the coordinate
-- swap `σ`, so the elaboration is long and the heartbeat budget is raised.
/-- **Strong ⇄ weak directional derivative, a.e. bridge (`v ∈ {1, I}`).** For an
almost-everywhere-differentiable, locally integrable function `f` with a locally
integrable weak directional derivative `g` in the real direction `v ∈ {1, I}`, the
*classical* directional derivative `z ↦ (fderiv ℝ f z) v` agrees with `g` almost
everywhere.

Proof (converse-ACL route): apply the project's converse-of-ACL representative
theorem (`exists_aclHorizontal_of_hasWeakDirDeriv_one` for `v = 1`,
`exists_aclVertical_of_hasWeakDirDeriv_I` for `v = I`) to obtain a representative
`f' =ᵐ f` that is absolutely continuous on almost every line with line-derivative
`g`. Working in `ℝ × ℝ` coordinates, on almost every line the AC representative
satisfies, by the fundamental theorem of calculus, `f'(x+s) − f'(x) = ∫ₓ^{x+s} g`,
whose difference quotient tends to `g(x)` for a.e. `x` by the Lebesgue
differentiation theorem. Since `f' =ᵐ f`, the difference quotient of `f` agrees
with that of `f'` for a.e. shift `s` (Fubini), so it has the same limit `g(x)`.
But `f` is differentiable at `(x, y)`, so its difference quotient along the line
has the *full* limit `(fderiv ℝ f (x,y)) v`; uniqueness of limits forces
`(fderiv ℝ f (x,y)) v = g (x,y)`. -/
theorem fderiv_ae_eq_weakDirDeriv {f g : ℂ → ℂ} {v : ℂ}
    (hg : HasWeakDirDeriv v g f Set.univ) (hgloc : LocallyIntegrableOn g Set.univ)
    (hdiff : ∀ᵐ z, DifferentiableAt ℝ f z)
    (hv : v = 1 ∨ v = Complex.I) (hfloc : LocallyIntegrable f) :
    ∀ᵐ z, (fderiv ℝ f z) v = g z := by
  classical
  rw [locallyIntegrableOn_univ] at hgloc
  -- ============================================================
  -- A one-dimensional uniqueness fact: an a.e.-zero function with a derivative at a
  -- point where it vanishes has derivative `0` there. The difference quotient is
  -- identically `0` along the co-null (hence dense, punctured) set where the
  -- function vanishes, so the limit is `0`.
  -- ============================================================
  have aux : ∀ {D : ℝ → ℂ} {x : ℝ} {c : ℂ},
      D =ᵐ[volume] 0 → D x = 0 → HasDerivAt D c x → c = 0 := by
    intro D x c hD0 hDx hderiv
    -- The co-null set where `D` vanishes is dense; deleting `x` keeps it dense.
    have hSdense : Dense {b : ℝ | D b = 0} :=
      MeasureTheory.Measure.dense_of_ae (by filter_upwards [hD0] with b hb using hb)
    have hSx : Dense ({b : ℝ | D b = 0} \ {x}) := hSdense.diff_singleton x
    have hxmem : x ∈ closure ({b : ℝ | D b = 0} \ {x}) := hSx.closure_eq ▸ Set.mem_univ x
    have hNeBot : (nhdsWithin x ({b : ℝ | D b = 0} \ {x})).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp hxmem
    -- The slope tends to `c` along `𝓝[≠]x`, hence along the finer dense punctured filter.
    have htend : Filter.Tendsto (slope D x) (nhdsWithin x {x}ᶜ) (nhds c) :=
      hasDerivAt_iff_tendsto_slope.mp hderiv
    have hsub : ({b : ℝ | D b = 0} \ {x}) ⊆ ({x}ᶜ : Set ℝ) := fun b hb => by
      simp only [Set.mem_diff, Set.mem_singleton_iff] at hb
      simp [Set.mem_compl_iff, Set.mem_singleton_iff, hb.2]
    have htend' : Filter.Tendsto (slope D x)
        (nhdsWithin x ({b : ℝ | D b = 0} \ {x})) (nhds c) :=
      htend.mono_left (nhdsWithin_mono x hsub)
    -- On that set the slope is identically `0`.
    have hslope0 : Filter.Tendsto (slope D x)
        (nhdsWithin x ({b : ℝ | D b = 0} \ {x})) (nhds (0 : ℂ)) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with b hb
      simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff] at hb
      rw [slope_def_module, hb.1, hDx, sub_zero, smul_zero]
    exact tendsto_nhds_unique htend' hslope0
  -- ============================================================
  -- THE HORIZONTAL CORE: the statement for the direction `1`.
  -- ============================================================
  have core : ∀ {f g : ℂ → ℂ}, HasWeakDirDeriv 1 g f Set.univ → LocallyIntegrable g →
      (∀ᵐ z, DifferentiableAt ℝ f z) → LocallyIntegrable f →
      ∀ᵐ z, (fderiv ℝ f z) 1 = g z := by
    clear hg hgloc hdiff hv hfloc f g v
    intro f g hg hgL hdiff hfL
    -- The AC representative `f'` of `f` with horizontal line-derivative `g`.
    obtain ⟨f', hf'ae, hacl⟩ := exists_aclHorizontal_of_hasWeakDirDeriv_one hfL hgL hg
    -- Move to `ℝ × ℝ` through the volume-preserving real-coordinate equivalence.
    have hemb := Complex.measurableEquivRealProd.measurableEmbedding
    have hmp := Complex.volume_preserving_equiv_real_prod
    have hmpsymm : MeasurePreserving Complex.measurableEquivRealProd.symm
        (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
      hmp.symm Complex.measurableEquivRealProd
    -- `f' =ᵐ f` on `ℂ`, transferred to `ℝ × ℝ` slices.
    have hf'ae2 : (fun p : ℝ × ℝ => f' ⟨p.1, p.2⟩) =ᵐ[volume.prod volume]
        (fun p : ℝ × ℝ => f ⟨p.1, p.2⟩) := by
      rw [← Measure.volume_eq_prod]
      have := hmpsymm.quasiMeasurePreserving.ae_eq_comp hf'ae
      filter_upwards [this] with p hp
      simpa [Complex.measurableEquivRealProd_symm_apply] using hp
    -- `f` differentiable a.e., transferred to `ℝ × ℝ`.
    have hdiff2 : ∀ᵐ p : ℝ × ℝ, DifferentiableAt ℝ f ⟨p.1, p.2⟩ := by
      have := hmpsymm.quasiMeasurePreserving.ae hdiff
      filter_upwards [this] with p hp
      simpa [Complex.measurableEquivRealProd_symm_apply] using hp
    -- Per-line a.e.-equality of the slices, from `hf'ae2` by Fubini.
    have hslice_eq : ∀ᵐ y : ℝ,
        (fun x : ℝ => f' ⟨x, y⟩) =ᵐ[volume] (fun x : ℝ => f ⟨x, y⟩) := by
      have hswap : (fun p : ℝ × ℝ => f' ⟨p.2, p.1⟩) =ᵐ[volume.prod volume]
          (fun p : ℝ × ℝ => f ⟨p.2, p.1⟩) := by
        have h := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
          (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae_eq hf'ae2
        simpa [Function.comp_def, Prod.swap] using h
      exact Measure.ae_ae_eq_of_ae_eq_uncurry hswap
    -- Per-line a.e.-`DifferentiableAt`, from `hdiff2` by Fubini.
    have hdiff_line : ∀ᵐ y : ℝ,
        ∀ᵐ x : ℝ, DifferentiableAt ℝ f ⟨x, y⟩ := by
      have hswap : ∀ᵐ p : ℝ × ℝ, DifferentiableAt ℝ f ⟨p.2, p.1⟩ := by
        have h := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
          (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae hdiff2
        simpa [Prod.swap] using h
      exact MeasureTheory.Measure.ae_ae_of_ae_prod hswap
    -- The conclusion, assembled at the `ℝ × ℝ` level via the curried per-line facts.
    -- We first prove the per-line statement `∀ᵐ y, ∀ᵐ x, GOAL⟨x,y⟩`, then transfer
    -- back to `ℂ` through the measure-preserving equivalence.
    have hline : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, (fderiv ℝ f ⟨x, y⟩) 1 = g ⟨x, y⟩ := by
      filter_upwards [hacl, hslice_eq, hdiff_line] with y hy_acl hy_eq hy_diff
      obtain ⟨_, hy_deriv⟩ := hy_acl
      -- On this good line, the f'-slice has `HasDerivAt … (g⟨x,y⟩)` a.e.,
      -- `f` is differentiable, and the two slices agree a.e.
      filter_upwards [hy_deriv, hy_diff, hy_eq] with x hx_deriv hx_diff hx_eq
      -- (i) the `f`-slice has `HasDerivAt … ((fderiv ℝ f ⟨x,y⟩) 1)` (line direction 1).
      have hsliceF : HasDerivAt (fun t : ℝ => f ⟨t, y⟩) ((fderiv ℝ f ⟨x, y⟩) 1) x := by
        have haff : HasDerivAt (fun t : ℝ => (⟨t, y⟩ : ℂ)) (1 : ℂ) x := by
          have he : (fun t : ℝ => (⟨t, y⟩ : ℂ)) =
              fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I := by
            funext t; apply Complex.ext <;> simp
          rw [he]
          simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * Complex.I)
        have hfd : HasFDerivAt f (fderiv ℝ f ⟨x, y⟩) ⟨x, y⟩ := hx_diff.hasFDerivAt
        simpa using hfd.comp_hasDerivAt x haff
      -- (ii) the `f'`-slice has `HasDerivAt … (g⟨x,y⟩)`.
      -- (iii) the slices agree a.e. (in the line variable) and at `x`.
      -- The difference `D` is a.e. zero, vanishes at `x`, and has derivative
      -- `(fderiv ℝ f ⟨x,y⟩) 1 - g⟨x,y⟩`; by `aux` that derivative is `0`.
      have hDae : (fun t : ℝ => f ⟨t, y⟩ - f' ⟨t, y⟩) =ᵐ[volume] 0 := by
        filter_upwards [hy_eq] with t ht
        simp only [Pi.zero_apply]
        rw [ht]; ring
      have hDx : (fun t : ℝ => f ⟨t, y⟩ - f' ⟨t, y⟩) x = 0 := by
        change f ⟨x, y⟩ - f' ⟨x, y⟩ = 0; rw [hx_eq]; ring
      have hDderiv : HasDerivAt (fun t : ℝ => f ⟨t, y⟩ - f' ⟨t, y⟩)
          ((fderiv ℝ f ⟨x, y⟩) 1 - g ⟨x, y⟩) x := hsliceF.sub hx_deriv
      exact sub_eq_zero.mp (aux hDae hDx hDderiv)
    -- Transfer `∀ᵐ y, ∀ᵐ x, P⟨x,y⟩` back to `∀ᵐ z:ℂ, P z`.
    -- The predicate set is measurable once `g` is replaced by a strongly-measurable
    -- representative `g₀ =ᵐ g`; we prove the conclusion for `g₀` at the `ℝ × ℝ` level
    -- via `ae_prod_iff_ae_ae`, pull it back along the equivalence, then return to `g`.
    set g₀ : ℂ → ℂ := hgL.aestronglyMeasurable.mk g with hg₀_def
    have hg₀_ae : g =ᵐ[volume] g₀ := hgL.aestronglyMeasurable.ae_eq_mk
    have hg₀_meas : Measurable g₀ := hgL.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    -- The lifted predicate, with `g₀`, has a measurable set.
    have hLHSmeas : Measurable (fun p : ℝ × ℝ => (fderiv ℝ f ⟨p.1, p.2⟩) 1) :=
      (measurable_fderiv_apply_const ℝ f 1).comp Complex.measurableEquivRealProd.symm.measurable
    have hRHSmeas : Measurable (fun p : ℝ × ℝ => g₀ ⟨p.1, p.2⟩) :=
      hg₀_meas.comp Complex.measurableEquivRealProd.symm.measurable
    have hmeasSet : MeasurableSet
        {p : ℝ × ℝ | (fderiv ℝ f ⟨p.1, p.2⟩) 1 = g₀ ⟨p.1, p.2⟩} :=
      measurableSet_eq_fun hLHSmeas hRHSmeas
    -- The per-line statement upgraded from `g` to `g₀` (they agree a.e. per line).
    have hg₀_line : ∀ᵐ y : ℝ,
        (fun x : ℝ => g ⟨x, y⟩) =ᵐ[volume] (fun x : ℝ => g₀ ⟨x, y⟩) := by
      have hg₀2 : (fun p : ℝ × ℝ => g ⟨p.2, p.1⟩) =ᵐ[volume.prod volume]
          (fun p : ℝ × ℝ => g₀ ⟨p.2, p.1⟩) := by
        have hg₀prod : (fun p : ℝ × ℝ => g ⟨p.1, p.2⟩) =ᵐ[volume.prod volume]
            (fun p : ℝ × ℝ => g₀ ⟨p.1, p.2⟩) := by
          rw [← Measure.volume_eq_prod]
          have := hmpsymm.quasiMeasurePreserving.ae_eq_comp hg₀_ae
          filter_upwards [this] with p hp
          simpa [Complex.measurableEquivRealProd_symm_apply] using hp
        have h := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
          (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae_eq hg₀prod
        simpa [Function.comp_def, Prod.swap] using h
      exact Measure.ae_ae_eq_of_ae_eq_uncurry hg₀2
    have hline₀ : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, (fderiv ℝ f ⟨x, y⟩) 1 = g₀ ⟨x, y⟩ := by
      filter_upwards [hline, hg₀_line] with y hy hy₀
      filter_upwards [hy, hy₀] with x hx hx₀
      rw [hx, hx₀]
    have hprod : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
        (fderiv ℝ f ⟨p.1, p.2⟩) 1 = g₀ ⟨p.1, p.2⟩ := by
      rw [Measure.ae_prod_iff_ae_ae hmeasSet,
        Measure.ae_ae_comm (p := fun a b : ℝ => (fderiv ℝ f ⟨a, b⟩) 1 = g₀ ⟨a, b⟩) hmeasSet]
      exact hline₀
    have hprod' : ∀ᵐ p : ℝ × ℝ, (fderiv ℝ f ⟨p.1, p.2⟩) 1 = g₀ ⟨p.1, p.2⟩ := by
      rwa [← Measure.volume_eq_prod] at hprod
    have hcz₀ : ∀ᵐ z : ℂ, (fderiv ℝ f z) 1 = g₀ z := by
      have := hmp.quasiMeasurePreserving.ae hprod'
      filter_upwards [this] with z hz
      simpa [Complex.measurableEquivRealProd_apply] using hz
    filter_upwards [hcz₀, hg₀_ae] with z hz hz₀
    rw [hz, ← hz₀]
  -- ============================================================
  -- DISPATCH on the direction.
  -- ============================================================
  rcases hv with rfl | rfl
  · exact core hg hgloc hdiff hfloc
  · -- Reduce `v = I` to `v = 1` via the real/imaginary coordinate swap
    -- `σ z = I · conj z`, exactly as in `exists_aclVertical_of_hasWeakDirDeriv_I`.
    set σ : ℂ ≃ₗᵢ[ℝ] ℂ :=
      Complex.conjLIE.trans (rotation ⟨Complex.I, by simp [Submonoid.unitSphere, Metric.sphere]⟩)
      with hσ_def
    have hσ_apply : ∀ z : ℂ, σ z = ⟨z.im, z.re⟩ := by
      intro z
      simp only [hσ_def, LinearIsometryEquiv.trans_apply, Complex.conjLIE_apply, rotation_apply]
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    have hσ_invol : ∀ z : ℂ, σ (σ z) = z := by
      intro z; rw [hσ_apply, hσ_apply]
    -- `σ · I = 1` (the only direction needed below): `σ⟨0,1⟩ = ⟨1,0⟩ = 1`.
    have hσ_I : (σ : ℂ →L[ℝ] ℂ) Complex.I = 1 := by
      have : σ Complex.I = 1 := by rw [hσ_apply]; apply Complex.ext <;> simp
      simpa using this
    -- `σ · 1 = I` (used to read off the conclusion at the end).
    have hσ_one : (σ : ℂ →L[ℝ] ℂ) (1 : ℂ) = Complex.I := by
      have : σ (1 : ℂ) = Complex.I := by rw [hσ_apply]; apply Complex.ext <;> simp
      simpa using this
    have hmp : MeasurePreserving σ volume volume := σ.measurePreserving
    have hemb : MeasurableEmbedding σ := σ.toMeasurableEquiv.measurableEmbedding
    -- Transfer the weak directional derivative to the direction `1`.
    have hweak : HasWeakDirDeriv 1 (fun z => g (σ z)) (fun z => f (σ z)) Set.univ := by
      intro ψ hψ_smooth hψ_cpt _
      have hchain : ∀ w : ℂ,
          (fderiv ℝ (fun z => ψ (σ z)) w) Complex.I = (fderiv ℝ ψ (σ w)) 1 := by
        intro w
        have hd1 : DifferentiableAt ℝ ψ (σ w) :=
          (hψ_smooth.differentiable (by norm_num)).differentiableAt
        have hσd : DifferentiableAt ℝ (fun z => σ z) w :=
          σ.toContinuousLinearEquiv.differentiableAt
        have he : (fun z => ψ (σ z)) = ψ ∘ (fun z => σ z) := rfl
        rw [he, fderiv_comp w hd1 hσd]
        have hσfd : fderiv ℝ (fun z => σ z) w = (σ : ℂ →L[ℝ] ℂ) :=
          (σ.toContinuousLinearEquiv.hasFDerivAt).fderiv
        rw [hσfd]
        simp only [ContinuousLinearMap.comp_apply]
        rw [hσ_I]
      have hψσ_smooth := hψ_smooth.comp σ.toContinuousLinearEquiv.contDiff
      have hψσ_cpt : HasCompactSupport (fun z => ψ (σ z)) := by
        have := hψ_cpt.comp_homeomorph σ.toHomeomorph
        simpa using this
      have hH := hg (fun z => ψ (σ z)) hψσ_smooth hψσ_cpt (by simp)
      rw [show (fun z => ((fderiv ℝ (fun z => ψ (σ z)) z) Complex.I) • f z)
            = (fun z => ((fderiv ℝ ψ (σ z)) 1) • f z) from
            funext (fun z => by rw [hchain z])] at hH
      have hLHS : (∫ w, ((fderiv ℝ ψ w) 1) • f (σ w))
          = ∫ z, ((fderiv ℝ ψ (σ z)) 1) • f z := by
        have := MeasureTheory.integral_comp σ (fun w => ((fderiv ℝ ψ w) 1) • f (σ w))
        rw [← this]
        refine integral_congr_ae ?_; filter_upwards with z; rw [hσ_invol]
      have hRHS : (∫ w, ψ w • g (σ w)) = ∫ z, ψ (σ z) • g z := by
        have := MeasureTheory.integral_comp σ (fun w => ψ w • g (σ w))
        rw [← this]
        refine integral_congr_ae ?_; filter_upwards with z; rw [hσ_invol]
      rw [hLHS, hRHS]
      exact hH
    -- Local integrability of `f∘σ` and `g∘σ`, preserved by `σ`.
    have hLIcomp : ∀ {u : ℂ → ℂ}, LocallyIntegrable u volume →
        LocallyIntegrable (fun z => u (σ z)) volume := by
      intro u hu
      rw [MeasureTheory.locallyIntegrable_iff]
      intro K hK
      have hpre : (σ ⁻¹' (σ '' K)) = K := Set.preimage_image_eq _ σ.injective
      have hKimg : IsCompact (σ '' K) := hK.image σ.continuous
      have := (hmp.integrableOn_comp_preimage hemb (f := u) (s := σ '' K)).mpr
        (hu.integrableOn_isCompact hKimg)
      rwa [hpre] at this
    -- `f∘σ` differentiable a.e. (`σ` is a diffeo and measure-preserving).
    have hdiffσ : ∀ᵐ w, DifferentiableAt ℝ (fun z => f (σ z)) w := by
      have hpre := hmp.quasiMeasurePreserving.ae hdiff
      filter_upwards [hpre] with w hw
      exact hw.comp w σ.toContinuousLinearEquiv.differentiableAt
    -- Apply the horizontal core to `F := f∘σ`, `G := g∘σ`.
    have hcore := core hweak (hLIcomp hgloc) hdiffσ (hLIcomp hfloc)
    -- `(fderiv ℝ (f∘σ) w) 1 = (fderiv ℝ f (σ w)) (σ 1) = (fderiv ℝ f (σ w)) I`.
    have hkey : ∀ᵐ w, (fderiv ℝ f (σ w)) Complex.I = g (σ w) := by
      filter_upwards [hcore, hmp.quasiMeasurePreserving.ae hdiff] with w hw hwd
      have hσd : DifferentiableAt ℝ (fun z => σ z) w :=
        σ.toContinuousLinearEquiv.differentiableAt
      have hchainw : (fderiv ℝ (fun z => f (σ z)) w) (1 : ℂ)
          = (fderiv ℝ f (σ w)) Complex.I := by
        have he : (fun z => f (σ z)) = f ∘ (fun z => σ z) := rfl
        rw [he, fderiv_comp w hwd hσd]
        have hσfd : fderiv ℝ (fun z => σ z) w = (σ : ℂ →L[ℝ] ℂ) :=
          (σ.toContinuousLinearEquiv.hasFDerivAt).fderiv
        rw [hσfd]
        simp only [ContinuousLinearMap.comp_apply]
        rw [hσ_one]
      rw [← hchainw]; exact hw
    -- Change variables `w ↦ σ w` (measure-preserving involution) to conclude.
    have := hmp.quasiMeasurePreserving.ae hkey
    filter_upwards [this] with z hz
    rw [hσ_invol] at hz
    exact hz

/-- **`G := ‖Df‖` is square-integrable on every ball.** For a quasiconformal map
`f ∈ W^{1,2}_loc`, the operator norm `G z := ‖fderiv ℝ f z‖₊` of the (strong)
differential has finite `L²`-energy on every Euclidean ball: `∫⁻_{ball 0 R} G² < ∞`.

This is the genuine Sobolev input. It combines (a) the a.e. identification of the
strong differential `fderiv ℝ f` with the weak gradient `(gx, gy)` of
`MemW12loc f` (where `f` is differentiable a.e., the columns of `fderiv ℝ f` are
the weak partials — the converse-of-ACL bridge `fderiv_ae_eq_weakDirDeriv`),
giving the pointwise a.e. bound `‖fderiv ℝ f z‖ ≤ ‖gx z‖ + ‖gy z‖`, with (b) the
`L²_loc` membership of `gx, gy` from `hf.2.1`, which makes `‖gx‖ + ‖gy‖`
square-integrable on the compact closed ball `closedBall 0 R ⊇ ball 0 R`. The
single genuinely-missing analytic input is the strong⇄weak a.e. bridge, isolated
as `fderiv_ae_eq_weakDirDeriv`. -/
theorem IsQCAnalytic.lintegralSq_fderiv_ball_ne_top {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) (R : ℝ) :
    (∫⁻ z in Metric.ball (0 : ℂ) R, (‖fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2) ≠ ∞ := by
  classical
  -- Extract the weak gradient `(gx, gy)` from `MemW12loc f`.
  obtain ⟨_hLp, gx, gy, ⟨hwgx, hwgy⟩, hmgx, hmgy⟩ := hf.2.1
  -- `hmgx : MemWklocP gx 0 2 univ = MemLpLocOn gx 2 univ`; likewise `hmgy`.
  have hLpgx : MemLpLocOn gx 2 Set.univ := hmgx
  have hLpgy : MemLpLocOn gy 2 Set.univ := hmgy
  -- The map `f` is differentiable a.e. (Gehring–Lehto, from orientation preservation).
  have hdiff : ∀ᵐ z, DifferentiableAt ℝ f z := IsQCAnalytic.ae_differentiableAt hf
  -- The compact closed ball `K := closedBall 0 R ⊇ ball 0 R`.
  set K : Set ℂ := Metric.closedBall (0 : ℂ) R with hK
  have hKcompact : IsCompact K := isCompact_closedBall (0 : ℂ) R
  -- `L²_loc` membership of `gx, gy` on the compact `K` ⟹ they are integrable on `K`,
  -- hence locally integrable on `univ` (used for the uniqueness bridge below).
  have hgxK : MemLp gx 2 (volume.restrict K) := hLpgx K (Set.subset_univ _) hKcompact
  have hgyK : MemLp gy 2 (volume.restrict K) := hLpgy K (Set.subset_univ _) hKcompact
  -- `MemLpLocOn _ 2` ⟹ integrable on every compact set ⟹ locally integrable.
  have memLpLoc_to_loc : ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 Set.univ →
      LocallyIntegrableOn g Set.univ := by
    intro g hg
    rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro k hk
    haveI : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    have hmem1 : MemLp g 1 (volume.restrict k) :=
      (hg k (Set.subset_univ _) hk).mono_exponent (by norm_num)
    exact memLp_one_iff_integrable.mp hmem1
  have hgxloc : LocallyIntegrableOn gx Set.univ := memLpLoc_to_loc hLpgx
  have hgyloc : LocallyIntegrableOn gy Set.univ := memLpLoc_to_loc hLpgy
  -- `f` is locally integrable: it is a homeomorphism, hence continuous.
  have hfloc : LocallyIntegrable f := hf.1.1.continuous.locallyIntegrable
  -- The strong⇄weak a.e. bridge: classical partials equal the weak partials a.e.
  have haex : ∀ᵐ z, (fderiv ℝ f z) (1 : ℂ) = gx z :=
    fderiv_ae_eq_weakDirDeriv hwgx hgxloc hdiff (Or.inl rfl) hfloc
  have haey : ∀ᵐ z, (fderiv ℝ f z) Complex.I = gy z :=
    fderiv_ae_eq_weakDirDeriv hwgy hgyloc hdiff (Or.inr rfl) hfloc
  -- Pointwise a.e. bound: `‖fderiv ℝ f z‖ ≤ ‖gx z‖ + ‖gy z‖`.
  have hbound : ∀ᵐ z, (‖fderiv ℝ f z‖₊ : ℝ≥0∞) ≤ (‖gx z‖₊ : ℝ≥0∞) + (‖gy z‖₊ : ℝ≥0∞) := by
    filter_upwards [haex, haey] with z hzx hzy
    -- `‖T‖ ≤ ‖T 1‖ + ‖T I‖` via the basis decomposition `w = w.re • 1 + w.im • I`.
    have hopn : ‖fderiv ℝ f z‖ ≤ ‖(fderiv ℝ f z) (1 : ℂ)‖ + ‖(fderiv ℝ f z) Complex.I‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
      set T := fderiv ℝ f z with hT
      -- `T w = w.re • T 1 + w.im • T I` from `w = w.re • 1 + w.im • I` and linearity.
      have hTw : T w = w.re • T (1 : ℂ) + w.im • T Complex.I := by
        have hdecomp : w = w.re • (1 : ℂ) + w.im • Complex.I := by
          rw [Complex.real_smul, Complex.real_smul, mul_one]
          exact (Complex.re_add_im w).symm
        conv_lhs => rw [hdecomp]
        simp only [map_add, map_smul]
      calc ‖T w‖ = ‖w.re • T (1 : ℂ) + w.im • T Complex.I‖ := by rw [hTw]
        _ ≤ ‖w.re • T (1 : ℂ)‖ + ‖w.im • T Complex.I‖ := norm_add_le _ _
        _ ≤ ‖(w.re : ℝ)‖ * ‖T (1 : ℂ)‖ + ‖(w.im : ℝ)‖ * ‖T Complex.I‖ := by
            gcongr <;> exact norm_smul_le _ _
        _ = |w.re| * ‖T (1 : ℂ)‖ + |w.im| * ‖T Complex.I‖ := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ ‖w‖ * ‖T (1 : ℂ)‖ + ‖w‖ * ‖T Complex.I‖ := by
            gcongr <;> [exact Complex.abs_re_le_norm w; exact Complex.abs_im_le_norm w]
        _ = (‖T (1 : ℂ)‖ + ‖T Complex.I‖) * ‖w‖ := by ring
    rw [hzx, hzy] at hopn
    -- Transfer the real bound to `ℝ≥0∞`.
    have hnn : ‖fderiv ℝ f z‖₊ ≤ ‖gx z‖₊ + ‖gy z‖₊ := by
      rw [← NNReal.coe_le_coe]; push_cast; exact hopn
    calc (‖fderiv ℝ f z‖₊ : ℝ≥0∞) ≤ ((‖gx z‖₊ + ‖gy z‖₊ : ℝ≥0) : ℝ≥0∞) :=
          ENNReal.coe_le_coe.mpr hnn
      _ = (‖gx z‖₊ : ℝ≥0∞) + (‖gy z‖₊ : ℝ≥0∞) := by push_cast; ring
  -- The `L²`-energy of each weak partial on the compact `K` is finite.
  have hsqfin : ∀ {g : ℂ → ℂ}, MemLp g 2 (volume.restrict K) →
      (∫⁻ z in K, (‖g z‖₊ : ℝ≥0∞) ^ 2) ≠ ∞ := by
    intro g hg
    have hlt := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (μ := volume.restrict K)
      (f := g) (p := 2) (by norm_num) (by norm_num) hg.eLpNorm_lt_top
    -- `∫⁻ ‖g‖ₑ^((2:ℝ≥0∞).toReal) < ∞`, and `‖g z‖ₑ^(2:ℝ) = (‖g z‖₊:ℝ≥0∞)^2`.
    rw [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num] at hlt
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hlt)
    refine lintegral_congr (fun z => ?_)
    rw [enorm_eq_nnnorm, ← ENNReal.rpow_natCast (‖g z‖₊ : ℝ≥0∞) 2]
    norm_num
  have hgxsqfin : (∫⁻ z in K, (‖gx z‖₊ : ℝ≥0∞) ^ 2) ≠ ∞ := hsqfin hgxK
  have hgysqfin : (∫⁻ z in K, (‖gy z‖₊ : ℝ≥0∞) ^ 2) ≠ ∞ := hsqfin hgyK
  -- The a.e. bound, restricted to `K`.
  have hbound_K : (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2)
      ≤ᵐ[volume.restrict K]
      fun z => 2 * ((‖gx z‖₊ : ℝ≥0∞) ^ 2 + (‖gy z‖₊ : ℝ≥0∞) ^ 2) := by
    refine (ae_restrict_of_ae ?_)
    filter_upwards [hbound] with z hz
    calc (‖fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2
        ≤ ((‖gx z‖₊ : ℝ≥0∞) + (‖gy z‖₊ : ℝ≥0∞)) ^ 2 := by gcongr
      _ ≤ 2 * ((‖gx z‖₊ : ℝ≥0∞) ^ 2 + (‖gy z‖₊ : ℝ≥0∞) ^ 2) := by
          have hkey := ENNReal.rpow_add_le_mul_rpow_add_rpow
            (‖gx z‖₊ : ℝ≥0∞) (‖gy z‖₊ : ℝ≥0∞) (by norm_num : (1 : ℝ) ≤ 2)
          have htwo : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by
            norm_num
          rw [htwo] at hkey
          rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_natCast (‖gx z‖₊ : ℝ≥0∞) 2,
            ← ENNReal.rpow_natCast (‖gy z‖₊ : ℝ≥0∞) 2]
          push_cast
          exact hkey
  -- Chain: `∫⁻ ball ‖fderiv‖² ≤ ∫⁻ K ‖fderiv‖² ≤ ∫⁻ K 2(‖gx‖²+‖gy‖²) < ∞`.
  have hball_sub_K : Metric.ball (0 : ℂ) R ⊆ K := Metric.ball_subset_closedBall
  -- AE-measurability of `‖gx‖²`, `‖gy‖²` (from `MemLp`'s `AEStronglyMeasurable`).
  have hgxsq_aem : AEMeasurable (fun z => (‖gx z‖₊ : ℝ≥0∞) ^ 2) (volume.restrict K) :=
    (hgxK.aestronglyMeasurable.aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hgysq_aem : AEMeasurable (fun z => (‖gy z‖₊ : ℝ≥0∞) ^ 2) (volume.restrict K) :=
    (hgyK.aestronglyMeasurable.aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hfin : (∫⁻ z in K, (‖fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2) ≠ ∞ := by
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae hbound_K) ?_)
    rw [lintegral_const_mul' 2 _ (by norm_num)]
    rw [lintegral_add_left' hgxsq_aem]
    refine ENNReal.mul_lt_top (by norm_num) ?_
    exact ENNReal.add_lt_top.mpr ⟨lt_of_le_of_ne le_top hgxsqfin, lt_of_le_of_ne le_top hgysqfin⟩
  exact ne_of_lt (lt_of_le_of_lt (lintegral_mono_set hball_sub_K) (lt_of_le_of_ne le_top hfin))

/-- **The unbounded-image exceptional curves have zero modulus.** The curves `γ`
of a family `Γ` along which the gradient line integral `∫₀¹ G(γ t)‖γ' t‖ dt` is
infinite *and whose trace `γ '' [0,1]` is contained in no ball* form a zero-modulus
family.

This is the one piece of the localization argument that the *current* statement of
`curveModulus_lineIntegral_top_zero` cannot supply on its own, because `Γ` is an
**arbitrary** `Set (ℝ → ℂ)`. The localized truncation `G·𝟙_{ball 0 n}` is
admissible only for curves whose trace lies in a fixed ball; for a curve with
genuinely unbounded trace on `[0,1]` there is no such ball, and the construction
breaks. In every intended application the curve family consists of **continuous**
curves on `[0,1]` (e.g. `Quadrilateral.curveFamily`), for which `γ '' [0,1]` is
compact, hence bounded, so this subfamily is *empty* and the modulus is trivially
`0`. The honest fix is to carry a continuity/boundedness hypothesis on `Γ` into the
statement; isolated here so the architect can decide where to add it. -/
theorem curveModulus_lineIntegral_top_unbounded_zero {f : ℂ → ℂ} {b : BeltramiCoeff}
    (_hf : IsQCAnalytic f b) (Γ : Set (ℝ → ℂ)) (hcont : ∀ γ ∈ Γ, Continuous γ) :
    curveModulus {γ ∈ Γ |
      arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ = ∞ ∧
        ∀ n : ℕ, ∃ t ∈ Set.Icc (0 : ℝ) 1, γ t ∉ Metric.ball (0 : ℂ) n} = 0 := by
  -- Under the continuity hypothesis the subfamily is **empty**: a continuous curve
  -- restricted to the compact interval `[0,1]` has a compact, hence bounded, image,
  -- so its trace lies in some ball `ball 0 n` — contradicting unboundedness.
  have hempty : {γ ∈ Γ |
      arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ = ∞ ∧
        ∀ n : ℕ, ∃ t ∈ Set.Icc (0 : ℝ) 1, γ t ∉ Metric.ball (0 : ℂ) n} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro γ ⟨hγΓ, -, hunbdd⟩
    -- The image of the compact interval `[0,1]` under the continuous `γ` is compact.
    have hcompact : IsCompact (γ '' Set.Icc (0 : ℝ) 1) :=
      (isCompact_Icc).image (hcont γ hγΓ)
    -- A compact set is bounded, hence contained in some ball `ball 0 n`.
    obtain ⟨r, hr⟩ := hcompact.isBounded.subset_ball (0 : ℂ)
    obtain ⟨n, hn⟩ := exists_nat_gt r
    -- The unboundedness condition gives a point of the trace outside `ball 0 n`.
    obtain ⟨t, ht, htnotin⟩ := hunbdd n
    have hmem : γ t ∈ γ '' Set.Icc (0 : ℝ) 1 := ⟨t, ht, rfl⟩
    have hin_ball : γ t ∈ Metric.ball (0 : ℂ) r := hr hmem
    apply htnotin
    rw [Metric.mem_ball, dist_zero_right]
    rw [Metric.mem_ball, dist_zero_right] at hin_ball
    calc ‖γ t‖ < r := hin_ball
      _ < n := hn
  rw [hempty]
  -- `curveModulus ∅ = 0`: the zero density is (vacuously) admissible for `∅`.
  refine le_antisymm ?_ (zero_le _)
  have hadm0 : IsAdmissibleDensity (fun _ => (0 : ℝ≥0∞)) (∅ : Set (ℝ → ℂ)) :=
    ⟨measurable_const, fun γ hγ => absurd hγ (Set.notMem_empty γ)⟩
  refine le_trans (iInf₂_le (fun _ => (0 : ℝ≥0∞)) hadm0) ?_
  simp

/-- **(F1) The infinite-gradient-line-integral family has zero modulus.** For a
`W^{1,2}_loc` quasiconformal map `f`, with `G z := ‖fderiv ℝ f z‖₊` the operator
norm of its differential (which lies in `L²_loc` since `f ∈ W^{1,2}_loc`), the
curves `γ` along which the arc-length integral `∫₀¹ G(γ t)‖γ' t‖ dt` of `G` is
infinite form a family of zero modulus.

This is the analytic heart of Fuglede's theorem.  The energy estimate needs the
*global* square-integrability `∫⁻ G² < ∞`, but `MemW12loc f` only gives `G ∈ L²`
on every ball.  The proof localizes:

* For each `n`, the *truncated* density `Gₙ := 𝟙_{ball 0 n}·G` has finite energy
  `∫⁻ Gₙ² = ∫⁻_{ball 0 n} G² < ∞` (`IsQCAnalytic.lintegralSq_fderiv_ball_ne_top`).
  Along a curve `γ` whose trace `γ '' [0,1]` lies in `ball 0 n`, the line integral
  of `Gₙ` equals that of `G`, hence is `∞`.  So
  `curveModulus_zero_of_lintegralSq_finite` gives zero modulus for the subfamily
  `Δₙ := {γ ∈ Γ | line integral of G is ∞, trace ⊆ ball 0 n}`.
* The countable union `⋃ₙ Δₙ` is the bounded-trace part of the exceptional family;
  it has zero modulus by `curveModulus_iUnion_zero`.
* The unbounded-trace part has zero modulus by
  `curveModulus_lineIntegral_top_unbounded_zero` (which for the continuous curve
  families of the applications is empty).

The exceptional family is the union of these two parts, so `curveModulus_mono`
plus `curveModulus_union_zero` finish.  The two genuine analytic inputs are the
ball-energy bound (the strong-`fderiv` ⇄ weak-gradient a.e. bridge) and countable
subadditivity, both isolated as the named helpers above. -/
theorem curveModulus_lineIntegral_top_zero {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) (Γ : Set (ℝ → ℂ)) (hcont : ∀ γ ∈ Γ, Continuous γ) :
    curveModulus {γ ∈ Γ |
      arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ = ∞} = 0 := by
  classical
  -- The gradient density `G`, and its measurability.
  set G : ℂ → ℝ≥0∞ := fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞) with hG
  have hGmeas : Measurable G := by
    rw [hG]
    exact ((measurable_fderiv ℝ f).nnnorm).coe_nnreal_ennreal
  -- The full exceptional family.
  set E : Set (ℝ → ℂ) := {γ ∈ Γ | arcLengthLineIntegral G γ = ∞} with hE
  -- The `n`-th bounded-trace truncated density `Gₙ := 𝟙_{ball 0 n}·G`.
  set Gn : ℕ → ℂ → ℝ≥0∞ :=
    fun n => (Metric.ball (0 : ℂ) n).indicator G with hGn
  have hGnmeas : ∀ n, Measurable (Gn n) := fun n =>
    hGmeas.indicator measurableSet_ball
  -- The `n`-th bounded-trace subfamily.
  set Δ : ℕ → Set (ℝ → ℂ) :=
    fun n => {γ ∈ Γ | arcLengthLineIntegral G γ = ∞ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Metric.ball (0 : ℂ) n} with hΔ
  -- Each `Δ n` has zero modulus, via the finite-energy reduction applied to `Gₙ`.
  have hΔzero : ∀ n, curveModulus (Δ n) = 0 := by
    intro n
    -- `Gₙ` has finite energy: `∫⁻ Gₙ² = ∫⁻_{ball 0 n} G² < ∞`.
    have hGnfin : ∫⁻ z, (Gn n z) ^ 2 ≠ ∞ := by
      have hpt : (fun z => (Gn n z) ^ 2)
          = (Metric.ball (0 : ℂ) n).indicator (fun z => (G z) ^ 2) := by
        funext z
        by_cases hz : z ∈ Metric.ball (0 : ℂ) (n : ℝ)
        · simp only [hGn, Set.indicator_of_mem hz]
        · simp only [hGn, Set.indicator_of_notMem hz]; norm_num
      rw [hpt, lintegral_indicator measurableSet_ball]
      exact hf.lintegralSq_fderiv_ball_ne_top (n : ℝ)
    -- Along every `γ ∈ Δ n`, the line integral of `Gₙ` is `∞` (it equals that of `G`).
    have hΔinf : ∀ γ ∈ Δ n, arcLengthLineIntegral (Gn n) γ = ∞ := by
      rintro γ ⟨-, hγinf, hγtrace⟩
      have heq : arcLengthLineIntegral (Gn n) γ = arcLengthLineIntegral G γ := by
        unfold arcLengthLineIntegral
        refine setLIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
        have : Gn n (γ t) = G (γ t) := by
          simp only [hGn, Set.indicator_of_mem (hγtrace t ht)]
        rw [this]
      rw [heq, hγinf]
    exact curveModulus_zero_of_lintegralSq_finite (hGnmeas n) hGnfin hΔinf
  -- The bounded-trace part `⋃ₙ Δ n` has zero modulus.
  have hUnionZero : curveModulus (⋃ n, Δ n) = 0 := curveModulus_iUnion_zero hΔzero
  -- The unbounded-trace part.
  set U : Set (ℝ → ℂ) := {γ ∈ Γ | arcLengthLineIntegral G γ = ∞ ∧
      ∀ n : ℕ, ∃ t ∈ Set.Icc (0 : ℝ) 1, γ t ∉ Metric.ball (0 : ℂ) n} with hU
  have hUzero : curveModulus U = 0 := curveModulus_lineIntegral_top_unbounded_zero hf Γ hcont
  -- The exceptional family is contained in `(⋃ₙ Δ n) ∪ U`.
  have hsub : E ⊆ (⋃ n, Δ n) ∪ U := by
    rintro γ ⟨hγΓ, hγinf⟩
    by_cases hb : ∀ n : ℕ, ∃ t ∈ Set.Icc (0 : ℝ) 1, γ t ∉ Metric.ball (0 : ℂ) n
    · -- Unbounded trace: `γ ∈ U`.
      exact Or.inr ⟨hγΓ, hγinf, hb⟩
    · -- Bounded trace: some `n` contains the whole trace, so `γ ∈ Δ n`.
      rw [not_forall] at hb
      obtain ⟨n, hn⟩ := hb
      refine Or.inl (Set.mem_iUnion.mpr ⟨n, hγΓ, hγinf, fun t ht => ?_⟩)
      by_contra hnotin
      exact hn ⟨t, ht, hnotin⟩
  -- Conclude by monotonicity and binary subadditivity.
  refine le_antisymm ?_ (zero_le _)
  calc curveModulus E
      ≤ curveModulus ((⋃ n, Δ n) ∪ U) := curveModulus_mono hsub
    _ = 0 := curveModulus_union_zero hUnionZero hUzero

/-- The real arc-length integrand `g t := ‖fderiv ℝ f (γ t)‖ · ‖deriv γ t‖`, the
`ℝ`-valued density whose finiteness drives the Fuglede absolute-continuity
argument. Its `ℝ≥0∞`-coercion is the integrand of `arcLengthLineIntegral`. -/
private noncomputable def fdNormMulDeriv (f : ℂ → ℂ) (γ : ℝ → ℂ) (t : ℝ) : ℝ :=
  ‖fderiv ℝ f (γ t)‖ * ‖deriv γ t‖

/-- **(ℂ-valued fundamental theorem of calculus for absolutely continuous curves.)**
If `h : ℝ → ℂ` is absolutely continuous on `uIcc a c`, has a pointwise a.e. derivative
`h'`, and `h'` is interval-integrable on `a..c`, then `h c - h a = ∫ t in a..c, h' t`.

This is the complex-valued analogue of Mathlib's real
`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`, obtained componentwise: the
real and imaginary parts `Complex.reCLM ∘ h`, `Complex.imCLM ∘ h` are absolutely
continuous (Lipschitz composition) with a.e. derivatives `(h' ·).re`, `(h' ·).im`, so
the real FTC applies to each part and recombines through `Complex.re_add_im`. -/
private theorem complex_ac_ftc {h h' : ℝ → ℂ} {a c : ℝ}
    (hac : AbsolutelyContinuousOnInterval h a c)
    (hderiv : ∀ᵐ t : ℝ, HasDerivAt h (h' t) t)
    (hint : IntervalIntegrable h' MeasureTheory.volume a c) :
    h c - h a = ∫ t in a..c, h' t := by
  -- Lipschitz-composition: real/imaginary parts of an AC curve are AC.
  have hLipComp : ∀ {Y : Type} [PseudoMetricSpace Y] (l : ℂ → Y) (K : NNReal),
      LipschitzWith K l → AbsolutelyContinuousOnInterval (fun t => l (h t)) a c := by
    intro Y _ l K hl
    rw [absolutelyContinuousOnInterval_iff] at hac ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hac (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist (l (h (E.2 i).1)) (l (h (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (h (E.2 i).1) (h (E.2 i).2) :=
          Finset.sum_le_sum (fun i _ => hl.dist_le_mul _ _)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (h (E.2 i).1) (h (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  have hre_ac : AbsolutelyContinuousOnInterval (fun t => (h t).re) a c :=
    hLipComp Complex.reCLM ‖Complex.reCLM‖₊ Complex.reCLM.lipschitz
  have him_ac : AbsolutelyContinuousOnInterval (fun t => (h t).im) a c :=
    hLipComp Complex.imCLM ‖Complex.imCLM‖₊ Complex.imCLM.lipschitz
  -- a.e. derivatives of the real/imaginary parts (compose with the `ℝ`-linear CLMs
  -- `reCLM`, `imCLM`).
  have hre_deriv : ∀ᵐ t : ℝ, HasDerivAt (fun s => (h s).re) (h' t).re t := by
    filter_upwards [hderiv] with t ht
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ht
    simpa using this
  have him_deriv : ∀ᵐ t : ℝ, HasDerivAt (fun s => (h s).im) (h' t).im t := by
    filter_upwards [hderiv] with t ht
    have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t ht
    simpa using this
  -- Identify the a.e. `deriv` of each part with the corresponding component of `h'`.
  have hre_deriv_eq : ∀ᵐ t : ℝ, deriv (fun s => (h s).re) t = (h' t).re := by
    filter_upwards [hre_deriv] with t ht using ht.deriv
  have him_deriv_eq : ∀ᵐ t : ℝ, deriv (fun s => (h s).im) t = (h' t).im := by
    filter_upwards [him_deriv] with t ht using ht.deriv
  -- Real FTC on each part.
  have hre_ftc : ∫ t in a..c, deriv (fun s => (h s).re) t = (h c).re - (h a).re :=
    hre_ac.integral_deriv_eq_sub
  have him_ftc : ∫ t in a..c, deriv (fun s => (h s).im) t = (h c).im - (h a).im :=
    him_ac.integral_deriv_eq_sub
  -- Integrability of the components for the integral-congruence rewrite.
  have hint_re : IntervalIntegrable (fun t => (h' t).re) MeasureTheory.volume a c :=
    ⟨Complex.reCLM.integrable_comp hint.1, Complex.reCLM.integrable_comp hint.2⟩
  have hint_im : IntervalIntegrable (fun t => (h' t).im) MeasureTheory.volume a c :=
    ⟨Complex.imCLM.integrable_comp hint.1, Complex.imCLM.integrable_comp hint.2⟩
  -- Replace the `deriv (… .re)` integrand by `(h' ·).re` under the integral sign.
  have hre_congr : (∫ t in a..c, deriv (fun s => (h s).re) t) = ∫ t in a..c, (h' t).re :=
    intervalIntegral.integral_congr_ae (by
      filter_upwards [hre_deriv_eq] with t ht _ using ht)
  have him_congr : (∫ t in a..c, deriv (fun s => (h s).im) t) = ∫ t in a..c, (h' t).im :=
    intervalIntegral.integral_congr_ae (by
      filter_upwards [him_deriv_eq] with t ht _ using ht)
  have hre_int : ∫ t in a..c, (h' t).re = (h c).re - (h a).re := by
    rw [← hre_congr, hre_ftc]
  have him_int : ∫ t in a..c, (h' t).im = (h c).im - (h a).im := by
    rw [← him_congr, him_ftc]
  -- The real and imaginary parts of `∫ h'` are `∫ (h'·).re`, `∫ (h'·).im`.
  have hintre : (∫ t in a..c, h' t).re = ∫ t in a..c, (h' t).re := by
    have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint
    simpa using this.symm
  have hintim : (∫ t in a..c, h' t).im = ∫ t in a..c, (h' t).im := by
    have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.imCLM hint
    simpa using this.symm
  -- Conclude `h c - h a = ∫ h'` componentwise.
  apply Complex.ext
  · rw [Complex.sub_re, hintre, hre_int]
  · rw [Complex.sub_im, hintim, him_int]

/-- **(Interval-integrability of the derivative of an absolutely continuous curve.)**
If `γ : ℝ → ℂ` is absolutely continuous on every interval, then its derivative `deriv γ`
is interval-integrable on `a..b`.

Componentwise: `Complex.reCLM ∘ γ`, `Complex.imCLM ∘ γ` are real absolutely continuous
(Lipschitz composition), so Mathlib's
`AbsolutelyContinuousOnInterval.intervalIntegrable_deriv` makes their derivatives
interval-integrable; these agree a.e. with `(deriv γ ·).re`, `(deriv γ ·).im`, which
recombine to `deriv γ`. -/
private theorem intervalIntegrable_deriv_of_complex_ac {γ : ℝ → ℂ}
    (hγac : ∀ a c : ℝ, AbsolutelyContinuousOnInterval γ a c) (a b : ℝ) :
    IntervalIntegrable (deriv γ) MeasureTheory.volume a b := by
  -- a.e. differentiability of `γ` on `uIcc a b` (bounded variation ⇒ a.e. differentiable).
  have hγ_diff : ∀ᵐ t : ℝ, t ∈ Set.uIcc a b → DifferentiableAt ℝ γ t :=
    (hγac a b).boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  -- Lipschitz-composition: real/imaginary parts of `γ` are AC.
  have hLipComp : ∀ {Y : Type} [PseudoMetricSpace Y] (l : ℂ → Y) (K : NNReal),
      LipschitzWith K l → AbsolutelyContinuousOnInterval (fun t => l (γ t)) a b := by
    intro Y _ l K hl
    have hγab := hγac a b
    rw [absolutelyContinuousOnInterval_iff] at hγab ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hγab (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist (l (γ (E.2 i).1)) (l (γ (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (γ (E.2 i).1) (γ (E.2 i).2) :=
          Finset.sum_le_sum (fun i _ => hl.dist_le_mul _ _)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (γ (E.2 i).1) (γ (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  have hre_ac : AbsolutelyContinuousOnInterval (fun t => (γ t).re) a b :=
    hLipComp Complex.reCLM ‖Complex.reCLM‖₊ Complex.reCLM.lipschitz
  have him_ac : AbsolutelyContinuousOnInterval (fun t => (γ t).im) a b :=
    hLipComp Complex.imCLM ‖Complex.imCLM‖₊ Complex.imCLM.lipschitz
  -- Real-part / imaginary-part derivatives are interval-integrable.
  have hre_int : IntervalIntegrable (deriv (fun t => (γ t).re)) MeasureTheory.volume a b :=
    hre_ac.intervalIntegrable_deriv
  have him_int : IntervalIntegrable (deriv (fun t => (γ t).im)) MeasureTheory.volume a b :=
    him_ac.intervalIntegrable_deriv
  -- a.e. on `uIcc a b`: `deriv (re∘γ) = (deriv γ).re` and `deriv (im∘γ) = (deriv γ).im`.
  have hre_eq : (deriv (fun t => (γ t).re)) =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)]
      (fun t => (deriv γ t).re) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hγ_diff] with t ht ht'
    have hd : HasDerivAt γ (deriv γ t) t := (ht (Set.uIoc_subset_uIcc ht')).hasDerivAt
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
    simpa using this.deriv
  have him_eq : (deriv (fun t => (γ t).im)) =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)]
      (fun t => (deriv γ t).im) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hγ_diff] with t ht ht'
    have hd : HasDerivAt γ (deriv γ t) t := (ht (Set.uIoc_subset_uIcc ht')).hasDerivAt
    have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hd
    simpa using this.deriv
  -- Transport interval-integrability to the components of `deriv γ`.
  have hre_int' : IntervalIntegrable (fun t => (deriv γ t).re) MeasureTheory.volume a b := by
    rw [intervalIntegrable_iff]
    exact (hre_int.def'.congr hre_eq)
  have him_int' : IntervalIntegrable (fun t => (deriv γ t).im) MeasureTheory.volume a b := by
    rw [intervalIntegrable_iff]
    exact (him_int.def'.congr him_eq)
  -- Push the real components into `ℂ` via `Complex.ofRealCLM`.
  have hre_intℂ : IntervalIntegrable (fun t => (↑(deriv γ t).re : ℂ)) MeasureTheory.volume a b :=
    ⟨Complex.ofRealCLM.integrable_comp hre_int'.1, Complex.ofRealCLM.integrable_comp hre_int'.2⟩
  have him_intℂ : IntervalIntegrable (fun t => (↑(deriv γ t).im : ℂ)) MeasureTheory.volume a b :=
    ⟨Complex.ofRealCLM.integrable_comp him_int'.1, Complex.ofRealCLM.integrable_comp him_int'.2⟩
  -- Recombine: `deriv γ = (re) + (im) * I`.
  have hrecomb : deriv γ = fun t => (↑(deriv γ t).re : ℂ) + (↑(deriv γ t).im : ℂ) * Complex.I := by
    funext t; exact (Complex.re_add_im (deriv γ t)).symm
  rw [hrecomb]
  exact hre_intℂ.add (him_intℂ.mul_const Complex.I)

/-- **(Smooth upper-gradient bound — provable glue.)** For a `C¹` function `g : ℂ → ℂ`
and an absolutely continuous curve `γ`, the distance `g` moves across `uIoc x y` is
bounded by the arc-length integral of `‖fderiv ℝ g‖` along the curve.

This is the per-mollifier elementary bound: `g ∘ γ` is `C¹ ∘ AC`, hence AC, with a.e.
derivative `(fderiv ℝ g (γ t)) (deriv γ t)` (chain rule); the ℂ-valued FTC
(`complex_ac_ftc`) plus `norm_integral_le_integral_norm` and the operator-norm bound
`‖(fderiv ℝ g (γ t)) (deriv γ t)‖ ≤ ‖fderiv ℝ g (γ t)‖ · ‖deriv γ t‖` give the claim. -/
private theorem dist_comp_le_setIntegral_of_contDiff {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    {γ : ℝ → ℂ} (hγac : ∀ a c : ℝ, AbsolutelyContinuousOnInterval γ a c)
    (x y : ℝ) :
    dist (g (γ x)) (g (γ y)) ≤ ∫ t in Set.uIoc x y, ‖fderiv ℝ g (γ t)‖ * ‖deriv γ t‖ := by
  -- `γ` is continuous (AC on every interval ⇒ continuous on every interval).
  have hγcont : Continuous γ := by
    rw [continuous_iff_continuousAt]
    intro z
    have hcon : ContinuousOn γ (Set.uIcc (z - 1) (z + 1)) := (hγac (z - 1) (z + 1)).continuousOn
    have hmem : Set.uIcc (z - 1) (z + 1) ∈ nhds z := by
      rw [Set.uIcc_of_le (by linarith)]; exact Icc_mem_nhds (by linarith) (by linarith)
    exact hcon.continuousAt hmem
  -- `g` is differentiable with continuous derivative, hence `HasFDerivAt g (fderiv) z`.
  have hgdiff : ∀ z : ℂ, HasFDerivAt g (fderiv ℝ g z) z :=
    fun z => (hg.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  -- a.e. derivative of `γ`: AC ⇒ differentiable a.e., and there `deriv` witnesses it.
  have hγ_diff : ∀ᵐ t : ℝ, DifferentiableAt ℝ γ t := by
    -- Build a.e. differentiability on every `[-n, n]`, then take the union.
    have hball : ∀ n : ℕ, ∀ᵐ t : ℝ, t ∈ Set.uIcc (-(n : ℝ)) (n : ℝ) → DifferentiableAt ℝ γ t := by
      intro n
      have hbv : BoundedVariationOn γ (Set.uIcc (-(n : ℝ)) (n : ℝ)) :=
        (hγac (-(n : ℝ)) (n : ℝ)).boundedVariationOn
      exact hbv.ae_differentiableAt_of_mem_uIcc
    rw [← MeasureTheory.ae_all_iff] at hball
    filter_upwards [hball] with t ht
    obtain ⟨n, hn⟩ := exists_nat_gt |t|
    have htmem : t ∈ Set.uIcc (-(n : ℝ)) (n : ℝ) := by
      have h1 : -(n : ℝ) ≤ t := by
        have := (abs_le.mp hn.le).1; linarith
      have h2 : t ≤ (n : ℝ) := (abs_le.mp hn.le).2
      rw [Set.uIcc_of_le (by linarith)]
      exact ⟨h1, h2⟩
    exact ht n htmem
  have hγ_deriv : ∀ᵐ t : ℝ, HasDerivAt γ (deriv γ t) t := by
    filter_upwards [hγ_diff] with t ht using ht.hasDerivAt
  -- The composed curve `g ∘ γ`, its a.e. derivative, integrability of the integrand,
  -- and the ℂ-valued FTC, are assembled below.
  set G : ℝ → ℂ := fun t => g (γ t) with hG
  set G' : ℝ → ℂ := fun t => (fderiv ℝ g (γ t)) (deriv γ t) with hG'
  -- a.e. chain rule: `HasDerivAt (g ∘ γ) ((fderiv g (γ t)) (deriv γ t)) t`.
  have hG_deriv : ∀ᵐ t : ℝ, HasDerivAt G (G' t) t := by
    filter_upwards [hγ_deriv] with t ht
    exact (hgdiff (γ t)).comp_hasDerivAt t ht
  -- `g ∘ γ` is AC on `uIcc x y`: `g` is Lipschitz on a ball containing the compact
  -- trace `γ '' uIcc x y`, and Lipschitz-on-set ∘ AC is AC.
  have hG_ac : AbsolutelyContinuousOnInterval G x y := by
    -- A closed ball `closedBall 0 R` containing the compact trace `γ '' uIcc x y`.
    have htrace_cpt : IsCompact (γ '' Set.uIcc x y) := (isCompact_uIcc).image hγcont
    obtain ⟨R, hRpos, hRsub⟩ : ∃ R > 0, γ '' Set.uIcc x y ⊆ Metric.closedBall (0 : ℂ) R := by
      obtain ⟨R, hRsub⟩ := htrace_cpt.isBounded.subset_closedBall (0 : ℂ)
      exact ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _),
        hRsub.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
    -- `g` is `K`-Lipschitz on the (convex, compact) ball.
    obtain ⟨K, hK⟩ : ∃ K, LipschitzOnWith K g (Metric.closedBall (0 : ℂ) R) :=
      (hg.contDiffOn).exists_lipschitzOnWith (by norm_num) (convex_closedBall _ _)
        (isCompact_closedBall _ _)
    -- Lipschitz-on-trace ∘ AC ⇒ AC, by the ε–δ bound on distances.
    have hγxy := hγac x y
    rw [absolutelyContinuousOnInterval_iff] at hγxy ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hγxy (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    -- Each endpoint of a disjoint subinterval inside `uIcc x y` lands in the ball.
    have hmem : ∀ s : ℝ, s ∈ Set.uIcc x y → γ s ∈ Metric.closedBall (0 : ℂ) R :=
      fun s hs => hRsub ⟨s, hs, rfl⟩
    have hsubmem := hE.1
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist (g (γ (E.2 i).1)) (g (γ (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (γ (E.2 i).1) (γ (E.2 i).2) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          exact hK.dist_le_mul _ (hmem _ (hsubmem i hi).1) _ (hmem _ (hsubmem i hi).2)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (γ (E.2 i).1) (γ (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  -- `fderiv ℝ g` is continuous (`g` is `C¹`), so `t ↦ ‖fderiv ℝ g (γ t)‖` is continuous.
  have hfd_cont : Continuous (fun z => fderiv ℝ g z) := hg.continuous_fderiv (by norm_num)
  have hnormfd_cont : Continuous (fun t => ‖fderiv ℝ g (γ t)‖) :=
    (hfd_cont.comp hγcont).norm
  -- `‖deriv γ ·‖` is interval-integrable (AC ⇒ deriv interval-integrable, then `.norm`).
  have hnormγ'_int : IntervalIntegrable (fun t => ‖deriv γ t‖) MeasureTheory.volume x y :=
    (intervalIntegrable_deriv_of_complex_ac hγac x y).norm
  -- The real density `‖fderiv g (γ ·)‖ · ‖deriv γ ·‖` is interval-integrable on `x..y`.
  have hdens_II : IntervalIntegrable (fun t => ‖fderiv ℝ g (γ t)‖ * ‖deriv γ t‖)
      MeasureTheory.volume x y :=
    hnormγ'_int.continuousOn_mul hnormfd_cont.continuousOn
  -- Measurability of the ℂ-valued derivative `G'`: the bilinear application
  -- `(L, v) ↦ L v` is continuous, `fderiv g ∘ γ` is continuous, `deriv γ` is measurable.
  have hG'_meas : Measurable G' := by
    have happ : Continuous (fun p : (ℂ →L[ℝ] ℂ) × ℂ => p.1 p.2) :=
      isBoundedBilinearMap_apply.continuous
    have hpair : Measurable (fun t => ((fderiv ℝ g (γ t)), deriv γ t)) :=
      (hfd_cont.comp hγcont).measurable.prodMk (measurable_deriv γ)
    exact happ.measurable.comp hpair
  -- Domination: `‖G'‖ ≤ ‖fderiv g (γ)‖ ‖γ'‖`, so `G'` is interval-integrable.
  have hG'_int : IntervalIntegrable G' MeasureTheory.volume x y :=
    hdens_II.mono_fun' hG'_meas.aestronglyMeasurable
      (MeasureTheory.ae_of_all _ (fun t => (fderiv ℝ g (γ t)).le_opNorm (deriv γ t)))
  -- ℂ-valued FTC for `G = g ∘ γ`.
  have hftc : G y - G x = ∫ t in x..y, G' t := complex_ac_ftc hG_ac hG_deriv hG'_int
  -- The pointwise norm bound `‖G' t‖ ≤ ‖fderiv g (γ t)‖ · ‖deriv γ t‖`.
  have hptbd : ∀ t, ‖G' t‖ ≤ ‖fderiv ℝ g (γ t)‖ * ‖deriv γ t‖ :=
    fun t => (fderiv ℝ g (γ t)).le_opNorm (deriv γ t)
  -- `dist (g (γ x)) (g (γ y)) = ‖G y - G x‖ ≤ ∫_{Ι} ‖G'‖ ≤ ∫_{Ι} ‖fderiv g (γ)‖ ‖γ'‖`.
  have hdist : dist (g (γ x)) (g (γ y)) = ‖∫ t in x..y, G' t‖ := by
    rw [dist_comm, dist_eq_norm, ← hftc]
  rw [hdist]
  -- `‖G'‖` is interval-integrable, and the real density is integrable on `uIoc x y`.
  have hnorm_int : IntervalIntegrable (fun t => ‖G' t‖) MeasureTheory.volume x y :=
    hG'_int.norm
  have hdens_int : IntegrableOn (fun t => ‖fderiv ℝ g (γ t)‖ * ‖deriv γ t‖)
      (Set.uIoc x y) MeasureTheory.volume := hdens_II.def'
  calc ‖∫ t in x..y, G' t‖
      ≤ ∫ t in Set.uIoc x y, ‖G' t‖ := intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ t in Set.uIoc x y, ‖fderiv ℝ g (γ t)‖ * ‖deriv γ t‖ :=
        MeasureTheory.setIntegral_mono_on hnorm_int.def' hdens_int measurableSet_uIoc
          (fun t _ => hptbd t)

open scoped Pointwise in
/-- **(L² mollification convergence — scalar core.)** For `g ∈ L²(ℂ)` and a sequence
of normed `ContDiffBump`s on `ℂ` with outer radius tending to `0`, the mollifications
`(φ n).normed volume ⋆ g` converge to `g` in `L²`.

This is the classical `3·ε` argument. Approximate `g` in `L²` by a smooth compactly
supported `h` with `eLpNorm (g - h) 2 ≤ ε` (`MemLp.exist_eLpNorm_sub_le`). For the
smooth compactly supported `h`, the mollifications converge uniformly with support in
a fixed compact set (`ContDiffBump.convolution_tendsto_right_of_continuous` plus the
shrinking support `rOut → 0`), so `eLpNorm (ρ_n ⋆ h - h) 2 → 0`. For the error term,
write the real normed bump as a complex-valued `L¹` function (`r • z = (↑r) * z`, so
the `lsmul ℝ ℝ` convolution equals the `mul ℂ ℂ` convolution of the cast bump) and
apply Young's inequality `eLpNorm_convolution_le`: `eLpNorm (ρ_n ⋆ (g - h)) 2 ≤
eLpNorm (↑ρ_n) 1 · eLpNorm (g - h) 2 = ε`, since the bump has unit `L¹` mass
(`ContDiffBump.integral_normed`). Conclude by the triangle inequality. -/
theorem eLpNorm_convolution_normed_sub_tendsto_zero {g : ℂ → ℂ}
    (hg : MemLp g 2 MeasureTheory.volume) (φ : ℕ → ContDiffBump (0 : ℂ))
    (hφrout : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => eLpNorm
        (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) g
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume - g) 2 MeasureTheory.volume)
      Filter.atTop (nhds 0) := by
  classical
  -- `ρ n := (φ n).normed volume`, and `C n := ρ n ⋆ g`.
  set Cg : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φ n).normed MeasureTheory.volume)
    g (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume with hCg
  -- ********** (P1) Smooth compactly supported approximant. **********
  -- We will repeat the `ε/3` argument for each `ε`; first, the `ε`-independent piece
  -- (P3) below is proved once, as a `Tendsto` statement.
  -- ====================================================================
  -- (P3) `ρ n ⋆ h - h → 0` in `L²` for a fixed smooth compactly supported `h`.
  -- ====================================================================
  have hP3 : ∀ (h : ℂ → ℂ), HasCompactSupport h → ContDiff ℝ (⊤ : ℕ∞) h →
      Filter.Tendsto (fun n => eLpNorm
        (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) h
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume - h) 2 MeasureTheory.volume)
        Filter.atTop (nhds 0) := by
    intro h hh_supp hh_smooth
    obtain ⟨M, hM⟩ := hh_smooth.continuous.bounded_above_of_compact_support hh_supp
    have hM0 : 0 ≤ M := le_trans (norm_nonneg (h 0)) (hM 0)
    -- Fixed compact set `Kset := cthickening 1 (tsupport h)`.
    set Kset : Set ℂ := Metric.cthickening 1 (tsupport h) with hKdef
    have hKcompact : IsCompact Kset := hh_supp.isCompact.cthickening
    have hKmeas : MeasurableSet Kset := hKcompact.measurableSet
    have hKfin : MeasureTheory.volume Kset < ⊤ := hKcompact.measure_lt_top
    have htsupp_sub : tsupport h ⊆ Kset := Metric.self_subset_cthickening _
    set Cn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φ n).normed MeasureTheory.volume)
      h (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume with hCn
    -- continuity of each `Cn n`.
    have hCn_cont : ∀ n, Continuous (Cn n) := fun n =>
      HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
        ((φ n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
    -- pointwise convergence `Cn n x → h x`.
    have hptwise : ∀ x, Filter.Tendsto (fun n => Cn n x) Filter.atTop (nhds (h x)) := fun x =>
      ContDiffBump.convolution_tendsto_right_of_continuous hφrout hh_smooth.continuous x
    -- uniform sup bound `‖Cn n x‖ ≤ M`.
    have hCnbd : ∀ n x, ‖Cn n x‖ ≤ M := by
      intro n x
      set ρ := (φ n).normed MeasureTheory.volume with hρ
      have hρnn : ∀ t, 0 ≤ ρ t := (φ n).nonneg_normed
      rw [hCn]; simp only; rw [MeasureTheory.convolution_def]
      calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t)) ∂MeasureTheory.volume‖
          ≤ ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t))‖ ∂MeasureTheory.volume :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ t, ρ t * M ∂MeasureTheory.volume := by
            have hint : Integrable ρ MeasureTheory.volume :=
              ((φ n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
                ((φ n).hasCompactSupport_normed)
            apply integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun t => norm_nonneg _)) (hint.mul_const M)
            refine Filter.Eventually.of_forall (fun t => ?_)
            simp only [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_of_nonneg (hρnn t)]
            exact mul_le_mul_of_nonneg_left (hM _) (hρnn t)
        _ = (∫ t, ρ t ∂MeasureTheory.volume) * M := by rw [integral_mul_const]
        _ = M := by rw [(φ n).integral_normed]; ring
    have hMh : ∀ y, ‖h y‖ ≤ M := hM
    -- eventual support control: `support (Cn n) ⊆ Kset` once `(φ n).rOut ≤ 1`.
    have hsupp_in_K : ∀ᶠ n in Filter.atTop, Function.support (Cn n) ⊆ Kset := by
      have hev : ∀ᶠ n in Filter.atTop, (φ n).rOut ≤ 1 := by
        have := hφrout.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
        filter_upwards [this] with n hn using hn
      filter_upwards [hev] with n hrout1
      have haddsub : Metric.closedBall (0 : ℂ) (φ n).rOut + tsupport h ⊆ Kset := by
        intro z hz
        obtain ⟨a, ha, b, hb, rfl⟩ := hz
        rw [Metric.mem_closedBall, dist_zero_right] at ha
        refine Metric.mem_cthickening_of_dist_le (a + b) b 1 (tsupport h) hb ?_
        rw [dist_eq_norm]; simp only [add_sub_cancel_right]; exact le_trans ha hrout1
      have hsub := MeasureTheory.support_convolution_subset (μ := MeasureTheory.volume)
        (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ))
        (f := (φ n).normed MeasureTheory.volume) (g := h)
      refine hsub.trans (le_trans ?_ haddsub)
      apply Set.add_subset_add _ (subset_tsupport h)
      intro z hz
      have h1 : z ∈ tsupport ((φ n).normed MeasureTheory.volume) := subset_tsupport _ hz
      rwa [(φ n).tsupport_normed_eq] at h1
    -- finite-measure machinery on `volume.restrict Kset`.
    haveI : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict Kset) := by
      constructor; rw [MeasureTheory.Measure.restrict_apply_univ]; exact hKfin
    set D : ℕ → ℂ → ℂ := fun n => Cn n - h with hD
    -- on the eventual support set, the `L²` norm over `volume` and over `restrict Kset` agree.
    have hrestrict : ∀ᶠ n in Filter.atTop,
        eLpNorm (D n) 2 MeasureTheory.volume
          = eLpNorm (D n) 2 (MeasureTheory.volume.restrict Kset) := by
      filter_upwards [hsupp_in_K] with n hn
      have hDsupp : Function.support (D n) ⊆ Kset := by
        intro x hx
        simp only [hD, Pi.sub_apply, Function.mem_support, ne_eq] at hx
        by_contra hxK
        have h1 : Cn n x = 0 := Function.notMem_support.mp (fun hc => hxK (hn hc))
        have h2 : h x = 0 := Function.notMem_support.mp
          (fun hc => hxK (htsupp_sub (subset_tsupport h hc)))
        rw [h1, h2, sub_zero] at hx; exact hx rfl
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict hKmeas, Set.indicator_eq_self.mpr hDsupp]
    -- `L²` convergence on the finite-measure set via Vitali / a.e. convergence.
    have hgoal : Filter.Tendsto (fun n => eLpNorm (D n) 2 (MeasureTheory.volume.restrict Kset))
        Filter.atTop (nhds 0) := by
      have hui : MeasureTheory.UnifIntegrable Cn 2 (MeasureTheory.volume.restrict Kset) := by
        refine MeasureTheory.unifIntegrable_of (by norm_num) (by norm_num)
          (fun n => (hCn_cont n).aestronglyMeasurable) (fun ε hε => ?_)
        refine ⟨(M.toNNReal + 1), fun n => ?_⟩
        have hempty : {x | (M.toNNReal + 1 : ℝ≥0) ≤ ‖Cn n x‖₊} = (∅ : Set ℂ) := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
          have hb' : ‖Cn n x‖₊ ≤ M.toNNReal := by
            rw [← NNReal.coe_le_coe, Real.coe_toNNReal M hM0]; exact hCnbd n x
          exact lt_of_le_of_lt hb' (by simp)
        rw [hempty, Set.indicator_empty]; simp
      have hhmem : MemLp h 2 (MeasureTheory.volume.restrict Kset) :=
        MemLp.of_bound hh_smooth.continuous.aestronglyMeasurable M
          (Filter.Eventually.of_forall hMh)
      exact MeasureTheory.tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
        (fun n => (hCn_cont n).aestronglyMeasurable) hhmem hui
        (Filter.Eventually.of_forall hptwise)
    exact Filter.Tendsto.congr' (hrestrict.mono (fun n hn => hn.symm)) hgoal
  -- ====================================================================
  -- (P2) Young error bound on `ρ n ⋆ u` for `u ∈ L²`.
  -- ====================================================================
  have hP2 : ∀ (u : ℂ → ℂ), MemLp u 2 MeasureTheory.volume → ∀ (ε : ℝ),
      eLpNorm u 2 MeasureTheory.volume ≤ ENNReal.ofReal ε → ∀ n,
        eLpNorm (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) u
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) 2 MeasureTheory.volume
          ≤ ENNReal.ofReal ε := by
    intro u hu ε hclose n
    set ρc : ℂ → ℂ := fun z => (((φ n).normed MeasureTheory.volume z : ℝ) : ℂ) with hρc
    have hconv_eq : MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) u
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume
        = MeasureTheory.convolution ρc u (ContinuousLinearMap.mul ℂ ℂ) MeasureTheory.volume := by
      funext x
      rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
      simp only [hρc, ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply]
      exact (Complex.real_smul).symm
    rw [hconv_eq]
    have hρc_memLp : MemLp ρc 1 MeasureTheory.volume := by
      have hcont : Continuous ρc :=
        Complex.continuous_ofReal.comp ((φ n).contDiff_normed (n := 0)).continuous
      have hsupp : HasCompactSupport ρc :=
        ((φ n).hasCompactSupport_normed).comp_left (g := (fun r : ℝ => (r : ℂ))) (by simp)
      exact hcont.memLp_of_hasCompactSupport hsupp
    have hρc_norm : eLpNorm ρc 1 MeasureTheory.volume = 1 := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      have hint : Integrable ((φ n).normed MeasureTheory.volume) MeasureTheory.volume :=
        ((φ n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
          ((φ n).hasCompactSupport_normed)
      have hnn : 0 ≤ᵐ[MeasureTheory.volume] (φ n).normed MeasureTheory.volume :=
        Filter.Eventually.of_forall (fun z => (φ n).nonneg_normed z)
      calc ∫⁻ z, ‖ρc z‖ₑ ∂MeasureTheory.volume
          = ∫⁻ z, ENNReal.ofReal ((φ n).normed MeasureTheory.volume z) ∂MeasureTheory.volume := by
            refine lintegral_congr (fun z => ?_)
            rw [hρc,
              show ‖(((φ n).normed MeasureTheory.volume z : ℝ) : ℂ)‖ₑ
                  = ‖(φ n).normed MeasureTheory.volume z‖ₑ from by
                rw [← enorm_norm, Complex.norm_real, enorm_norm],
              Real.enorm_of_nonneg ((φ n).nonneg_normed z)]
        _ = ENNReal.ofReal (∫ z, (φ n).normed MeasureTheory.volume z ∂MeasureTheory.volume) :=
            (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
        _ = 1 := by rw [(φ n).integral_normed]; simp
    calc eLpNorm (MeasureTheory.convolution ρc u (ContinuousLinearMap.mul ℂ ℂ)
            MeasureTheory.volume) 2 MeasureTheory.volume
        ≤ eLpNorm ρc 1 MeasureTheory.volume * eLpNorm u 2 MeasureTheory.volume :=
          eLpNorm_convolution_le hρc_memLp hu
      _ = eLpNorm u 2 MeasureTheory.volume := by rw [hρc_norm, one_mul]
      _ ≤ ENNReal.ofReal ε := hclose
  -- ====================================================================
  -- Main: `∀ ε > 0, ∀ᶠ n, eLpNorm (Cg n - g) 2 ≤ ε`.
  -- ====================================================================
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  -- pull out a positive real `δ` with `ENNReal.ofReal δ = ε` (use `δ := ε.toReal`).
  by_cases htop : ε = ⊤
  · refine Filter.Eventually.of_forall (fun n => ?_)
    rw [htop]; exact le_top
  set δ : ℝ := ε.toReal with hδ
  have hδpos : 0 < δ := ENNReal.toReal_pos hε.ne' htop
  have hδle : ENNReal.ofReal δ = ε := ENNReal.ofReal_toReal htop
  -- (P1) the smooth approximant `h` with `eLpNorm (g - h) 2 ≤ ofReal (δ/3)`.
  obtain ⟨h, hh_supp, hh_smooth, hh_close⟩ := hg.exist_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (ε := δ / 3) (by positivity)
  -- `MemLp h 2` and `MemLp (g - h) 2`.
  have hh_memLp : MemLp h 2 MeasureTheory.volume :=
    hh_smooth.continuous.memLp_of_hasCompactSupport hh_supp
  have hgh_memLp : MemLp (g - h) 2 MeasureTheory.volume := hg.sub hh_memLp
  -- `eLpNorm (g - h) 2 ≤ ofReal (δ/3)`.
  -- (P2) applied to `u := g - h`.
  have hP2gh : ∀ n, eLpNorm (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume)
        (g - h) (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) 2 MeasureTheory.volume
        ≤ ENNReal.ofReal (δ / 3) :=
    hP2 (g - h) hgh_memLp (δ / 3) hh_close
  -- (P3) eventual bound.
  have hP3ev : ∀ᶠ n in Filter.atTop,
      eLpNorm (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) h
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume - h) 2 MeasureTheory.volume
        ≤ ENNReal.ofReal (δ / 3) :=
    (ENNReal.tendsto_nhds_zero.mp (hP3 h hh_supp hh_smooth) (ENNReal.ofReal (δ / 3))
      (ENNReal.ofReal_pos.mpr (by positivity)))
  -- the convolution decomposition `Cg n = ρ n ⋆ (g - h) + ρ n ⋆ h`.
  have hdecomp : ∀ n, Cg n - g = MeasureTheory.convolution ((φ n).normed MeasureTheory.volume)
        (g - h) (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume
      + (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) h
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume - h) + (h - g) := by
    intro n
    have hce1 : MeasureTheory.ConvolutionExists ((φ n).normed MeasureTheory.volume) (g - h)
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume := by
      refine HasCompactSupport.convolutionExists_left _ ((φ n).hasCompactSupport_normed)
        ((φ n).contDiff_normed (n := 0)).continuous ?_
      exact (hg.locallyIntegrable (by norm_num)).sub hh_smooth.continuous.locallyIntegrable
    have hce2 : MeasureTheory.ConvolutionExists ((φ n).normed MeasureTheory.volume) h
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume :=
      HasCompactSupport.convolutionExists_left _ ((φ n).hasCompactSupport_normed)
        ((φ n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
    have hsplit : Cg n = MeasureTheory.convolution ((φ n).normed MeasureTheory.volume)
          (g - h) (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume
        + MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) h
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume := by
      rw [hCg]; simp only
      rw [← MeasureTheory.ConvolutionExists.distrib_add hce1 hce2]
      congr 1; abel
    rw [hsplit]; abel
  -- combine: triangle inequality.
  filter_upwards [hP3ev] with n hn3
  rw [hdecomp n]
  -- measurabilities for `eLpNorm_add_le`.
  have hm1 : AEStronglyMeasurable (MeasureTheory.convolution
      ((φ n).normed MeasureTheory.volume) (g - h) (ContinuousLinearMap.lsmul ℝ ℝ)
      MeasureTheory.volume) MeasureTheory.volume :=
    (HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
      ((φ n).contDiff_normed (n := 0)).continuous
      ((hg.locallyIntegrable (by norm_num)).sub
        hh_smooth.continuous.locallyIntegrable)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (MeasureTheory.convolution
      ((φ n).normed MeasureTheory.volume) h (ContinuousLinearMap.lsmul ℝ ℝ)
      MeasureTheory.volume - h) MeasureTheory.volume :=
    ((HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
      ((φ n).contDiff_normed (n := 0)).continuous
      hh_smooth.continuous.locallyIntegrable).sub hh_smooth.continuous).aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (h - g) MeasureTheory.volume :=
    (hh_memLp.sub hg).1
  have hkey : eLpNorm (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume)
        (g - h) (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume
      + (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) h
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume - h) + (h - g)) 2
        MeasureTheory.volume
      ≤ ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) := by
    refine le_trans (eLpNorm_add_le (hm1.add hm2) hm3 (by norm_num)) ?_
    refine add_le_add (le_trans (eLpNorm_add_le hm1 hm2 (by norm_num)) ?_) ?_
    · exact add_le_add (hP2gh n) hn3
    · -- `eLpNorm (h - g) 2 = eLpNorm (g - h) 2 ≤ ofReal (δ/3)`.
      rw [eLpNorm_sub_comm]; exact hh_close
  refine le_trans hkey ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← hδle]
  apply le_of_eq; congr 1; ring

/-- **(A1: mollification commutes with the weak directional derivative.)** If `gv`
is a weak directional derivative of `f` in the real direction `v` (on all of `ℂ`),
then for a smooth compactly supported real mollifier `ρ` the genuine directional
derivative of the (smooth) mollification `ρ ⋆ f` equals the mollification of `gv`:
`(fderiv ℝ (ρ ⋆ f) z) v = (ρ ⋆ gv) z`.

The mollification `ρ ⋆ f` is differentiated by moving the derivative onto the
smooth factor (`HasCompactSupport.hasFDerivAt_convolution_left`):
`(fderiv ℝ (ρ ⋆ f) z) v = ∫ ((fderiv ℝ ρ t) v) • f (z - t) dt`. Substituting
`u = z - t` and setting the test function `φ z (u) := ρ (z - u)` — which is smooth,
compactly supported, and satisfies `(fderiv ℝ (φ z) u) v = -(fderiv ℝ ρ (z - u)) v`
by the chain rule for the affine map `u ↦ z - u` — turns this into
`-∫ ((fderiv ℝ (φ z) u) v) • f u du`. The weak-derivative integration-by-parts
identity `HasWeakDirDeriv` applied to `φ z` rewrites it as `∫ (φ z u) • gv u du =
∫ ρ (z - u) • gv u du`, which is `(ρ ⋆ gv) z` after substituting back. -/
theorem fderiv_convolution_normed_apply_eq {f gv : ℂ → ℂ} {v : ℂ}
    (hv : HasWeakDirDeriv v gv f Set.univ)
    (hf : MeasureTheory.LocallyIntegrable f) (hgv : MeasureTheory.LocallyIntegrable gv)
    {ρ : ℂ → ℝ} (hρ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hρ_supp : HasCompactSupport ρ) (z : ℂ) :
    (fderiv ℝ (MeasureTheory.convolution ρ f
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) z) v
      = MeasureTheory.convolution ρ gv
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume z := by
  classical
  -- `gv` is not needed beyond the statement's typing role.
  have _hgv := hgv
  -- Abbreviation for the scalar-multiplication bilinear map.
  set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hL
  -- `ρ` is `C^1` and continuous (specializations of the `C^∞` hypothesis).
  have hρ_one : ContDiff ℝ ((1 : ℕ∞) : WithTop ℕ∞) ρ := hρ_smooth.of_le (by exact_mod_cast le_top)
  have hρ_diff : Differentiable ℝ ρ :=
    hρ_one.differentiable (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))
  have hρ_cont : Continuous ρ := hρ_smooth.continuous
  -- `fderiv ℝ ρ` has compact support.
  have hdρ_supp : HasCompactSupport (fderiv ℝ ρ) := hρ_supp.fderiv ℝ
  -- (1) Differentiate the mollification onto the smooth factor.
  have hderiv :
      HasFDerivAt (MeasureTheory.convolution ρ f L MeasureTheory.volume)
        (MeasureTheory.convolution (fderiv ℝ ρ) f (L.precompL ℂ) MeasureTheory.volume z) z :=
    HasCompactSupport.hasFDerivAt_convolution_left L hρ_supp hρ_one hf z
  rw [hderiv.fderiv]
  -- (2) Evaluate the vector-valued convolution at `v` and move it inside the integral.
  have hconvexists :
      MeasureTheory.ConvolutionExistsAt (fderiv ℝ ρ) f z (L.precompL ℂ) MeasureTheory.volume :=
    (hdρ_supp.convolutionExists_left (L.precompL ℂ)
      (hρ_one.continuous_fderiv (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))) hf) z
  rw [MeasureTheory.convolution_def,
      ContinuousLinearMap.integral_apply hconvexists.integrable]
  simp only [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.lsmul_apply]
  -- Now goal: `∫ t, ((fderiv ℝ ρ t) v) • f (z - t) = (ρ ⋆ gv) z`.
  -- (3) Change variables `t ↦ z - t`.
  have hcv :
      (∫ t, ((fderiv ℝ ρ t) v) • f (z - t) ∂MeasureTheory.volume)
        = ∫ u, ((fderiv ℝ ρ (z - u)) v) • f u ∂MeasureTheory.volume := by
    have hself := MeasureTheory.integral_sub_left_eq_self
      (fun t => ((fderiv ℝ ρ t) v) • f (z - t)) MeasureTheory.volume z
    simp only [sub_sub_cancel] at hself
    exact hself.symm
  refine hcv.trans ?_
  -- (4) Chain rule for the test function `φz u := ρ (z - u)`.
  set φz : ℂ → ℝ := fun u => ρ (z - u) with hφz
  have hφz_fderiv : ∀ u, (fderiv ℝ φz u) v = -((fderiv ℝ ρ (z - u)) v) := by
    intro u
    have hsub : HasFDerivAt (fun u : ℂ => z - u) (-ContinuousLinearMap.id ℝ ℂ) u := by
      simpa using (hasFDerivAt_id u).const_sub z
    have hcomp : HasFDerivAt φz
        ((fderiv ℝ ρ (z - u)).comp (-ContinuousLinearMap.id ℝ ℂ)) u :=
      (hρ_diff (z - u)).hasFDerivAt.comp u hsub
    rw [hcomp.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply, map_neg]
  have hint_eq :
      (∫ u, ((fderiv ℝ ρ (z - u)) v) • f u ∂MeasureTheory.volume)
        = -∫ u, ((fderiv ℝ φz u) v) • f u ∂MeasureTheory.volume := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    change ((fderiv ℝ ρ (z - u)) v) • f u = -(((fderiv ℝ φz u) v) • f u)
    rw [hφz_fderiv u]
    rw [show (-(fderiv ℝ ρ (z - u)) v) • f u = -(((fderiv ℝ ρ (z - u)) v) • f u)
      from neg_smul _ _, neg_neg]
  rw [hint_eq]
  -- (5) Apply the weak-derivative identity to `φz`.
  have hφz_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φz :=
    hρ_smooth.comp (contDiff_const.sub contDiff_id)
  have hφz_supp : HasCompactSupport φz :=
    hρ_supp.comp_homeomorph (Homeomorph.subLeft z)
  have hwd := hv φz hφz_smooth hφz_supp (Set.subset_univ _)
  rw [hwd, neg_neg]
  -- (6) Recognize the convolution `∫ ρ (z - u) • gv u = (ρ ⋆ gv) z`.
  rw [MeasureTheory.convolution_def, ← MeasureTheory.integral_sub_left_eq_self
      (fun t => (L (ρ t)) (gv (z - t))) MeasureTheory.volume z]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  simp only [hφz, sub_sub_cancel, hL, ContinuousLinearMap.lsmul_apply]
  rfl

/-- **(A: mollified-gradient `L²` energy decay on a ball.)** For a quasiconformal
`f` and a sequence of normed `ContDiffBump` mollifiers with outer radius tending to
`0`, the `L²` energy of the difference between the (genuine) differential of the
mollification `ρ_n ⋆ f` and the differential of `f`, measured over any ball, tends
to `0`.

This assembles the two convolution facts with the weak-to-strong bridge. The weak
gradient of `f ∈ W^{1,2}_loc` provides partials `gx` (direction `1`) and `gy`
(direction `I`), both `L²_loc`. By `fderiv_convolution_normed_apply_eq` the
directional derivatives of `ρ_n ⋆ f` are the mollifications `ρ_n ⋆ gx` and
`ρ_n ⋆ gy`; by `fderiv_ae_eq_weakDirDeriv` the directional derivatives of `f` agree
a.e. with `gx`, `gy`. Truncating `gx`, `gy` to a slightly larger ball makes them
globally `L²`, and on the given ball the mollified truncations agree with the
mollified partials once `rOut < 1`; so the operator-norm bound
`‖T‖ ≤ ‖T 1‖ + ‖T I‖` reduces the energy to the two scalar pieces
`∫ ‖ρ_n ⋆ gx_R - gx_R‖²` and `∫ ‖ρ_n ⋆ gy_R - gy_R‖²`, each tending to `0` by the
scalar `L²` mollification convergence `eLpNorm_convolution_normed_sub_tendsto_zero`. -/
theorem mollified_fderiv_ball_energy_tendsto_zero {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) (R : ℝ) (φ : ℕ → ContDiffBump (0 : ℂ))
    (hφrout : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫⁻ z in Metric.ball (0 : ℂ) R,
        (‖fderiv ℝ (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) f
            (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) z
          - fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2)
      Filter.atTop (nhds 0) := by
  classical
  -- Abbreviations: `ρ n := (φ n).normed volume`, `fn n := ρ n ⋆ f`.
  set ρ : ℕ → ℂ → ℝ := fun n => (φ n).normed MeasureTheory.volume with hρ
  set fn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution (ρ n) f
    (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume with hfn
  -- ===== (0) Extract the weak gradient `(gx, gy)` from `MemW12loc f`. =====
  obtain ⟨_hLp, gx, gy, ⟨hwgx, hwgy⟩, hmgx, hmgy⟩ := hf.2.1
  have hLpgx : MemLpLocOn gx 2 Set.univ := hmgx
  have hLpgy : MemLpLocOn gy 2 Set.univ := hmgy
  have hdiff : ∀ᵐ z, DifferentiableAt ℝ f z := IsQCAnalytic.ae_differentiableAt hf
  have hfloc : MeasureTheory.LocallyIntegrable f := hf.1.1.continuous.locallyIntegrable
  -- `L²_loc ⟹ L¹_loc ⟹ LocallyIntegrable`.
  have memLpLoc_to_loc : ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 Set.univ →
      MeasureTheory.LocallyIntegrable g := by
    intro g hg
    rw [← locallyIntegrableOn_univ, locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro k hk
    haveI : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict k) :=
      ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    have hmem1 : MeasureTheory.MemLp g 1 (MeasureTheory.volume.restrict k) :=
      (hg k (Set.subset_univ _) hk).mono_exponent (by norm_num)
    exact MeasureTheory.memLp_one_iff_integrable.mp hmem1
  have hgxLI : MeasureTheory.LocallyIntegrable gx := memLpLoc_to_loc hLpgx
  have hgyLI : MeasureTheory.LocallyIntegrable gy := memLpLoc_to_loc hLpgy
  have hgxloc : MeasureTheory.LocallyIntegrableOn gx Set.univ :=
    locallyIntegrableOn_univ.mpr hgxLI
  have hgyloc : MeasureTheory.LocallyIntegrableOn gy Set.univ :=
    locallyIntegrableOn_univ.mpr hgyLI
  -- ===== (1) Smoothness / compact support of the mollifier. =====
  have hρsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
    (φ n).contDiff_normed (n := ⊤)
  have hρsupp : ∀ n, HasCompactSupport (ρ n) := fun n => (φ n).hasCompactSupport_normed
  -- ===== (2) The two directional derivatives of `fn n` and of `f`. =====
  -- A1: `(fderiv (fn n) z) 1 = ρ n ⋆ gx z`, `(fderiv (fn n) z) I = ρ n ⋆ gy z` (every `z`).
  have hA1x : ∀ n z, (fderiv ℝ (fn n) z) (1 : ℂ)
      = MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ)
          MeasureTheory.volume z := fun n z =>
    fderiv_convolution_normed_apply_eq hwgx hfloc hgxLI (hρsm n) (hρsupp n) z
  have hA1y : ∀ n z, (fderiv ℝ (fn n) z) Complex.I
      = MeasureTheory.convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ)
          MeasureTheory.volume z := fun n z =>
    fderiv_convolution_normed_apply_eq hwgy hfloc hgyLI (hρsm n) (hρsupp n) z
  -- a.e.: `(fderiv f z) 1 = gx z`, `(fderiv f z) I = gy z`.
  have haex : ∀ᵐ z, (fderiv ℝ f z) (1 : ℂ) = gx z :=
    fderiv_ae_eq_weakDirDeriv hwgx hgxloc hdiff (Or.inl rfl) hfloc
  have haey : ∀ᵐ z, (fderiv ℝ f z) Complex.I = gy z :=
    fderiv_ae_eq_weakDirDeriv hwgy hgyloc hdiff (Or.inr rfl) hfloc
  -- ===== (4) Truncate the partials to a global `L²` function on `ball 0 (R+1)`. =====
  set gxR : ℂ → ℂ := (Metric.ball (0 : ℂ) (R + 1)).indicator gx with hgxR
  set gyR : ℂ → ℂ := (Metric.ball (0 : ℂ) (R + 1)).indicator gy with hgyR
  have hmemLp_trunc : ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 Set.univ →
      MeasureTheory.MemLp ((Metric.ball (0 : ℂ) (R + 1)).indicator g) 2
        MeasureTheory.volume := by
    intro g hg
    rw [MeasureTheory.memLp_indicator_iff_restrict measurableSet_ball]
    have hcb : MeasureTheory.MemLp g 2 (MeasureTheory.volume.restrict
        (Metric.closedBall (0 : ℂ) (R + 1))) :=
      hg (Metric.closedBall (0 : ℂ) (R + 1)) (Set.subset_univ _)
        (isCompact_closedBall _ _)
    exact hcb.mono_measure (MeasureTheory.Measure.restrict_mono
      Metric.ball_subset_closedBall le_rfl)
  have hgxR_memLp : MeasureTheory.MemLp gxR 2 MeasureTheory.volume := hmemLp_trunc hLpgx
  have hgyR_memLp : MeasureTheory.MemLp gyR 2 MeasureTheory.volume := hmemLp_trunc hLpgy
  -- ===== The two scalar `L²` errors and their convergence (A2). =====
  set Ex : ℕ → ℝ≥0∞ := fun n => eLpNorm
    (MeasureTheory.convolution (ρ n) gxR (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume
      - gxR) 2 MeasureTheory.volume with hEx
  set Ey : ℕ → ℝ≥0∞ := fun n => eLpNorm
    (MeasureTheory.convolution (ρ n) gyR (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume
      - gyR) 2 MeasureTheory.volume with hEy
  have hExto : Filter.Tendsto Ex Filter.atTop (nhds 0) :=
    eLpNorm_convolution_normed_sub_tendsto_zero hgxR_memLp φ hφrout
  have hEyto : Filter.Tendsto Ey Filter.atTop (nhds 0) :=
    eLpNorm_convolution_normed_sub_tendsto_zero hgyR_memLp φ hφrout
  -- The dominating sequence `D n := 2 * (Ex n ^ 2 + Ey n ^ 2) → 0`.
  set D : ℕ → ℝ≥0∞ := fun n => 2 * (Ex n ^ 2 + Ey n ^ 2) with hD
  have hDto : Filter.Tendsto D Filter.atTop (nhds 0) := by
    have hsq : Filter.Tendsto (fun n => Ex n ^ 2 + Ey n ^ 2) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n => Ex n ^ 2) Filter.atTop (nhds 0) := by
        have := (ENNReal.continuous_pow 2).continuousAt.tendsto.comp hExto
        simpa using this
      have h2 : Filter.Tendsto (fun n => Ey n ^ 2) Filter.atTop (nhds 0) := by
        have := (ENNReal.continuous_pow 2).continuousAt.tendsto.comp hEyto
        simpa using this
      simpa using h1.add h2
    have hconst : Filter.Tendsto (fun n => (2 : ℝ≥0∞) * (Ex n ^ 2 + Ey n ^ 2))
        Filter.atTop (nhds ((2 : ℝ≥0∞) * 0)) :=
      ENNReal.Tendsto.const_mul hsq (Or.inr (ENNReal.ofNat_ne_top))
    simpa using hconst
  -- ===== (3)+(5)+(6) The eventual pointwise+integral domination. =====
  -- For `(φ n).rOut ≤ 1`, on a.e. `z ∈ ball 0 R`, the squared energy is `≤` the integrand
  -- of `D n`; integrating over `ball 0 R` and extending to the whole space gives the bound.
  have hev_rout : ∀ᶠ n in Filter.atTop, (φ n).rOut ≤ 1 := by
    have := hφrout.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [this] with n hn using hn
  have hdom : ∀ᶠ n in Filter.atTop,
      (∫⁻ z in Metric.ball (0 : ℂ) R,
        (‖fderiv ℝ (fn n) z - fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2) ≤ D n := by
    filter_upwards [hev_rout] with n hrout1
    -- (5) On `ball 0 R`, the mollified partial = mollified truncation.
    have hconv_eq : ∀ {g : ℂ → ℂ}, ∀ z ∈ Metric.ball (0 : ℂ) R,
        MeasureTheory.convolution (ρ n) g (ContinuousLinearMap.lsmul ℝ ℝ)
            MeasureTheory.volume z
          = MeasureTheory.convolution (ρ n) ((Metric.ball (0 : ℂ) (R + 1)).indicator g)
            (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume z := by
      intro g z hz
      rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
      simp only
      by_cases ht : ρ n t = 0
      · simp only [ht, map_zero, ContinuousLinearMap.zero_apply]
      · -- `ρ n t ≠ 0 ⟹ t ∈ support (ρ n) = ball 0 rOut`, so `‖t‖ < rOut ≤ 1`.
        have htsupp : t ∈ Function.support (ρ n) := ht
        rw [hρ, (φ n).support_normed_eq] at htsupp
        rw [Metric.mem_ball, dist_zero_right] at htsupp
        have hzlt : ‖z‖ < R := by
          rw [Metric.mem_ball, dist_zero_right] at hz; exact hz
        have hztmem : z - t ∈ Metric.ball (0 : ℂ) (R + 1) := by
          rw [Metric.mem_ball, dist_zero_right]
          calc ‖z - t‖ ≤ ‖z‖ + ‖t‖ := norm_sub_le _ _
            _ < R + 1 := by
              have : ‖t‖ < 1 := lt_of_lt_of_le htsupp hrout1
              linarith
        rw [Set.indicator_of_mem hztmem]
    -- (3) Operator-norm bound: `‖T‖₊^2 ≤ 2*(‖T 1‖₊^2 + ‖T I‖₊^2)` for a.e. `z ∈ ball R`.
    have hball_sub : Metric.ball (0 : ℂ) R ⊆ Metric.ball (0 : ℂ) (R + 1) :=
      Metric.ball_subset_ball (by linarith)
    have hptbd : ∀ᵐ z, z ∈ Metric.ball (0 : ℂ) R →
        (‖fderiv ℝ (fn n) z - fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2 ≤
        2 * ((‖MeasureTheory.convolution (ρ n) gxR (ContinuousLinearMap.lsmul ℝ ℝ)
                MeasureTheory.volume z - gxR z‖₊ : ℝ≥0∞) ^ 2
            + (‖MeasureTheory.convolution (ρ n) gyR (ContinuousLinearMap.lsmul ℝ ℝ)
                MeasureTheory.volume z - gyR z‖₊ : ℝ≥0∞) ^ 2) := by
      filter_upwards [haex, haey] with z hzx hzy hzball
      set T := fderiv ℝ (fn n) z - fderiv ℝ f z with hT
      -- Identify the two basis components of `T`.
      have hTx : T (1 : ℂ) = MeasureTheory.convolution (ρ n) gxR
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume z - gxR z := by
        rw [hT, ContinuousLinearMap.sub_apply, hA1x n z, hzx, hconv_eq z hzball,
          hgxR, Set.indicator_of_mem (hball_sub hzball)]
      have hTy : T Complex.I = MeasureTheory.convolution (ρ n) gyR
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume z - gyR z := by
        rw [hT, ContinuousLinearMap.sub_apply, hA1y n z, hzy, hconv_eq z hzball,
          hgyR, Set.indicator_of_mem (hball_sub hzball)]
      -- `‖T‖ ≤ ‖T 1‖ + ‖T I‖`.
      have hopn : ‖T‖ ≤ ‖T (1 : ℂ)‖ + ‖T Complex.I‖ := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
        have hTw : T w = w.re • T (1 : ℂ) + w.im • T Complex.I := by
          have hdecomp : w = w.re • (1 : ℂ) + w.im • Complex.I := by
            rw [Complex.real_smul, Complex.real_smul, mul_one]
            exact (Complex.re_add_im w).symm
          conv_lhs => rw [hdecomp]
          simp only [map_add, map_smul]
        calc ‖T w‖ = ‖w.re • T (1 : ℂ) + w.im • T Complex.I‖ := by rw [hTw]
          _ ≤ ‖w.re • T (1 : ℂ)‖ + ‖w.im • T Complex.I‖ := norm_add_le _ _
          _ ≤ ‖(w.re : ℝ)‖ * ‖T (1 : ℂ)‖ + ‖(w.im : ℝ)‖ * ‖T Complex.I‖ := by
              gcongr <;> exact norm_smul_le _ _
          _ = |w.re| * ‖T (1 : ℂ)‖ + |w.im| * ‖T Complex.I‖ := by
              rw [Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ ‖w‖ * ‖T (1 : ℂ)‖ + ‖w‖ * ‖T Complex.I‖ := by
              gcongr <;> [exact Complex.abs_re_le_norm w; exact Complex.abs_im_le_norm w]
          _ = (‖T (1 : ℂ)‖ + ‖T Complex.I‖) * ‖w‖ := by ring
      -- Transfer to `ℝ≥0`, square, and bound `(a+b)^2 ≤ 2(a^2+b^2)` in `ℝ≥0∞`.
      have hnn : ‖T‖₊ ≤ ‖T (1 : ℂ)‖₊ + ‖T Complex.I‖₊ := by
        rw [← NNReal.coe_le_coe]; push_cast; exact hopn
      have hle1 : (‖T‖₊ : ℝ≥0∞) ≤ (‖T (1 : ℂ)‖₊ : ℝ≥0∞) + (‖T Complex.I‖₊ : ℝ≥0∞) := by
        calc (‖T‖₊ : ℝ≥0∞) ≤ ((‖T (1 : ℂ)‖₊ + ‖T Complex.I‖₊ : ℝ≥0) : ℝ≥0∞) :=
              ENNReal.coe_le_coe.mpr hnn
          _ = (‖T (1 : ℂ)‖₊ : ℝ≥0∞) + (‖T Complex.I‖₊ : ℝ≥0∞) := by push_cast; ring
      calc (‖T‖₊ : ℝ≥0∞) ^ 2
          ≤ ((‖T (1 : ℂ)‖₊ : ℝ≥0∞) + (‖T Complex.I‖₊ : ℝ≥0∞)) ^ 2 := by gcongr
        _ ≤ 2 * ((‖T (1 : ℂ)‖₊ : ℝ≥0∞) ^ 2 + (‖T Complex.I‖₊ : ℝ≥0∞) ^ 2) := by
            have hkey := ENNReal.rpow_add_le_mul_rpow_add_rpow
              (‖T (1 : ℂ)‖₊ : ℝ≥0∞) (‖T Complex.I‖₊ : ℝ≥0∞) (by norm_num : (1 : ℝ) ≤ 2)
            have htwo : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by norm_num
            rw [htwo] at hkey
            rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_natCast (‖T (1 : ℂ)‖₊ : ℝ≥0∞) 2,
              ← ENNReal.rpow_natCast (‖T Complex.I‖₊ : ℝ≥0∞) 2]
            push_cast
            exact hkey
        _ = 2 * ((‖MeasureTheory.convolution (ρ n) gxR (ContinuousLinearMap.lsmul ℝ ℝ)
                MeasureTheory.volume z - gxR z‖₊ : ℝ≥0∞) ^ 2
              + (‖MeasureTheory.convolution (ρ n) gyR (ContinuousLinearMap.lsmul ℝ ℝ)
                MeasureTheory.volume z - gyR z‖₊ : ℝ≥0∞) ^ 2) := by rw [hTx, hTy]
    -- Integrate over `ball 0 R` and bound by the full-space `eLpNorm`s.
    have hint_bd : (∫⁻ z in Metric.ball (0 : ℂ) R,
          (‖fderiv ℝ (fn n) z - fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2)
        ≤ ∫⁻ z in Metric.ball (0 : ℂ) R,
          2 * ((‖MeasureTheory.convolution (ρ n) gxR (ContinuousLinearMap.lsmul ℝ ℝ)
                MeasureTheory.volume z - gxR z‖₊ : ℝ≥0∞) ^ 2
            + (‖MeasureTheory.convolution (ρ n) gyR (ContinuousLinearMap.lsmul ℝ ℝ)
                MeasureTheory.volume z - gyR z‖₊ : ℝ≥0∞) ^ 2) := by
      refine MeasureTheory.lintegral_mono_ae ?_
      rw [MeasureTheory.ae_restrict_iff' measurableSet_ball]
      filter_upwards [hptbd] with z hz using hz
    -- Compute the RHS as `D n` via `(eLpNorm · 2)^2 = ∫⁻ ‖·‖ₑ^2`.
    have heLpSq : ∀ (h : ℂ → ℂ), (eLpNorm h 2 MeasureTheory.volume) ^ 2
        = ∫⁻ z, (‖h z‖₊ : ℝ≥0∞) ^ 2 := by
      intro h
      rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      rw [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num]
      have hlint_eq : (∫⁻ z, ‖h z‖ₑ ^ (2 : ℝ)) = ∫⁻ z, (‖h z‖₊ : ℝ≥0∞) ^ 2 := by
        refine lintegral_congr (fun z => ?_)
        rw [enorm_eq_nnnorm, ← ENNReal.rpow_natCast (‖h z‖₊ : ℝ≥0∞) 2]
        norm_num
      rw [hlint_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
      norm_num
    -- Local integrability of the truncated partials (for convolution continuity).
    have hgxR_LI : MeasureTheory.LocallyIntegrable gxR :=
      hgxR_memLp.locallyIntegrable (by norm_num)
    have hgyR_LI : MeasureTheory.LocallyIntegrable gyR :=
      hgyR_memLp.locallyIntegrable (by norm_num)
    -- The two convolutions are continuous (`ρ n` smooth, compact support).
    have hconvx_cont : Continuous (MeasureTheory.convolution (ρ n) gxR
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) :=
      HasCompactSupport.continuous_convolution_left _ (hρsupp n)
        (hρsm n).continuous hgxR_LI
    -- AEMeasurability of the `x`-integrand `‖conv - gxR‖₊²`.
    have hmeasx : AEMeasurable (fun z =>
        (‖MeasureTheory.convolution (ρ n) gxR (ContinuousLinearMap.lsmul ℝ ℝ)
            MeasureTheory.volume z - gxR z‖₊ : ℝ≥0∞) ^ 2) MeasureTheory.volume :=
      ((hconvx_cont.aestronglyMeasurable.sub
          hgxR_memLp.aestronglyMeasurable).aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2
    calc (∫⁻ z in Metric.ball (0 : ℂ) R,
          (‖fderiv ℝ (fn n) z - fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2)
        ≤ ∫⁻ z in Metric.ball (0 : ℂ) R,
            2 * ((‖MeasureTheory.convolution (ρ n) gxR (ContinuousLinearMap.lsmul ℝ ℝ)
                  MeasureTheory.volume z - gxR z‖₊ : ℝ≥0∞) ^ 2
              + (‖MeasureTheory.convolution (ρ n) gyR (ContinuousLinearMap.lsmul ℝ ℝ)
                  MeasureTheory.volume z - gyR z‖₊ : ℝ≥0∞) ^ 2) := hint_bd
      _ ≤ ∫⁻ z,
            2 * ((‖MeasureTheory.convolution (ρ n) gxR (ContinuousLinearMap.lsmul ℝ ℝ)
                  MeasureTheory.volume z - gxR z‖₊ : ℝ≥0∞) ^ 2
              + (‖MeasureTheory.convolution (ρ n) gyR (ContinuousLinearMap.lsmul ℝ ℝ)
                  MeasureTheory.volume z - gyR z‖₊ : ℝ≥0∞) ^ 2) :=
            MeasureTheory.setLIntegral_le_lintegral _ _
      _ = 2 * ((∫⁻ z, (‖MeasureTheory.convolution (ρ n) gxR (ContinuousLinearMap.lsmul ℝ ℝ)
                  MeasureTheory.volume z - gxR z‖₊ : ℝ≥0∞) ^ 2)
              + ∫⁻ z, (‖MeasureTheory.convolution (ρ n) gyR (ContinuousLinearMap.lsmul ℝ ℝ)
                  MeasureTheory.volume z - gyR z‖₊ : ℝ≥0∞) ^ 2) := by
            rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
              MeasureTheory.lintegral_add_left' hmeasx]
      _ = D n := by
            rw [hD, hEx, hEy]
            simp only [heLpSq, Pi.sub_apply]
  -- ===== Squeeze: `0 ≤ (·) ≤ D n` eventually, both bounds `→ 0`. =====
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hDto
    (Filter.Eventually.of_forall (fun n => zero_le _)) hdom

/-- A curve `γ` is **good** for `f` when some sequence of normed `ContDiffBump`
mollifiers with outer radius tending to `0` makes the arc-length line integral along
`γ` of the difference between the differential of the mollification and the
differential of `f` tend to `0`. By the quasiconformal Fuglede theorem
(`IsQCAnalytic.curveModulus_notGoodCurve_zero`) the non-good curves of any family form
a zero-modulus subfamily, so the upper-gradient inequality (which holds for good
curves) holds modulus-almost-everywhere. -/
def GoodCurve (f : ℂ → ℂ) (γ : ℝ → ℂ) : Prop :=
  ∃ φ : ℕ → ContDiffBump (0 : ℂ),
    Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => arcLengthLineIntegral
      (fun z => (‖fderiv ℝ (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) f
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) z - fderiv ℝ f z‖₊ : ℝ≥0∞)) γ)
      Filter.atTop (nhds 0)

/-- **(Mollified-differential trace convergence along a good curve.)**
For a curve `γ` along which the mollified differential converges in arc-length to the
differential of `f` (`hgood_φ`), the mollified arc-length density integral is
eventually within `ε` of the target `∫ fdNormMulDeriv f γ`:
`∫_{uIoc x y} ‖fderiv ℝ f_n (γ t)‖ ‖deriv γ t‖ ≤ ∫ fdNormMulDeriv f γ + ε` eventually.

Proof: the reverse triangle inequality bounds the excess by the arc-length integral of
the differential difference `‖fderiv ℝ f_n − fderiv ℝ f‖`, which tends to `0` by
`hgood_φ`. -/
theorem fderiv_mollified_lineIntegral_le {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) {γ : ℝ → ℂ}
    (hγac : ∀ a c : ℝ, AbsolutelyContinuousOnInterval γ a c)
    (hfin : arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ ≠ ∞)
    (x y : ℝ) (hxy : Set.uIcc x y ⊆ Set.Icc (0 : ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) (φ : ℕ → ContDiffBump (0 : ℂ))
    (_hφrout : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0))
    (hgood_φ : Filter.Tendsto (fun n => arcLengthLineIntegral
      (fun z => (‖fderiv ℝ (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) f
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) z - fderiv ℝ f z‖₊ : ℝ≥0∞)) γ)
      Filter.atTop (nhds 0)) :
    ∀ᶠ n in Filter.atTop,
      (∫ t in Set.uIoc x y,
          ‖fderiv ℝ (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) f
            (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) (γ t)‖ * ‖deriv γ t‖) ≤
        (∫ t in Set.uIoc x y, fdNormMulDeriv f γ t) + ε := by
  -- Abbreviations: `fn n := ρ_n ⋆ f` the mollifications,
  -- `dn n t := fderiv (fn n) (γ t) − fderiv f (γ t)`.
  set fn : ℕ → ℂ → ℂ :=
    fun n => MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) f
      (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume with hfndef
  have hfcont : Continuous f := hf.1.1.continuous
  have hfloc : MeasureTheory.LocallyIntegrable f := hfcont.locallyIntegrable
  -- `γ` is continuous (AC on every interval ⇒ continuous).
  have hγcont : Continuous γ := by
    rw [continuous_iff_continuousAt]
    intro x
    have hcon : ContinuousOn γ (Set.uIcc (x - 1) (x + 1)) :=
      (hγac (x - 1) (x + 1)).continuousOn
    have hmem : Set.uIcc (x - 1) (x + 1) ∈ nhds x := by
      rw [Set.uIcc_of_le (by linarith)]
      exact Icc_mem_nhds (by linarith) (by linarith)
    exact hcon.continuousAt hmem
  -- Each `fn n` is `C¹`, hence `fderiv ℝ (fn n)` is continuous.
  have hfn_contDiff : ∀ n, ContDiff ℝ 1 (fn n) := fun n =>
    ((φ n).hasCompactSupport_normed).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (n := 1) (φ n).contDiff_normed hfloc
  have hfn_fderiv_cont : ∀ n, Continuous (fun z => fderiv ℝ (fn n) z) := fun n =>
    (hfn_contDiff n).continuous_fderiv (by norm_num)
  -- Abbreviation: the `ℝ≥0∞` arc-length integral of the differential difference along `γ`.
  set A : ℕ → ℝ≥0∞ := fun n => arcLengthLineIntegral
      (fun z => (‖fderiv ℝ (fn n) z - fderiv ℝ f z‖₊ : ℝ≥0∞)) γ with hA
  -- The `.toReal` of these tend to `0`, since they tend to `0` in `ℝ≥0∞`.
  have hA_to_zero : Filter.Tendsto (fun n => (A n).toReal) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto A Filter.atTop (nhds 0) := hgood_φ
    simpa using (ENNReal.tendsto_toReal (by simp)).comp this
  -- Eventually `(A n).toReal ≤ ε`.
  have hAev : ∀ᶠ n in Filter.atTop, (A n).toReal ≤ ε :=
    hA_to_zero.eventually (ge_mem_nhds hε)
  -- Eventually `A n ≠ ∞` (since `A → 0` in `ℝ≥0∞`, `A n` is eventually `< 1`).
  have hAne : ∀ᶠ n in Filter.atTop, A n ≠ ∞ := by
    have hlt : ∀ᶠ n in Filter.atTop, A n < 1 :=
      (hgood_φ : Filter.Tendsto A Filter.atTop (nhds 0)).eventually
        (eventually_lt_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
    filter_upwards [hlt] with n hn using ne_top_of_lt (hn.trans_le le_top)
  filter_upwards [hAev, hAne] with n hAn hAnetop
  -- `g t := ‖fderiv (fn n) (γ t)‖ * ‖deriv γ t‖` and `h t := fdNormMulDeriv f γ t`.
  -- `deriv γ` is measurable; `‖deriv γ ·‖` measurable.
  have hderiv_meas : Measurable (fun t => ‖deriv γ t‖) := (measurable_deriv γ).norm
  -- The `fderiv f` piece is integrable on `uIcc x y ⊇ uIoc x y`. (Inlined here, since
  -- `integrableOn_fderiv_norm_mul_deriv_uIcc` is defined later in the file.)
  have hh_int_uIcc : IntegrableOn (fdNormMulDeriv f γ) (Set.uIcc x y) := by
    have hmeas : Measurable (fdNormMulDeriv f γ) := by
      have h1 : Measurable (fun t => ‖fderiv ℝ f (γ t)‖) :=
        ((measurable_fderiv ℝ f).norm).comp hγcont.measurable
      simpa only [fdNormMulDeriv] using h1.mul hderiv_meas
    refine IntegrableOn.mono_set ?_ hxy
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lt_top_iff_ne_top]
    have hptf : ∀ t, ‖fdNormMulDeriv f γ t‖ₑ
        = (‖fderiv ℝ f (γ t)‖₊ : ℝ≥0∞) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
      intro t
      simp only [fdNormMulDeriv, enorm_eq_nnnorm, nnnorm_mul, nnnorm_norm, ENNReal.coe_mul]
    calc ∫⁻ t in Set.Icc (0:ℝ) 1, ‖fdNormMulDeriv f γ t‖ₑ
        = ∫⁻ t in Set.Icc (0:ℝ) 1,
            (‖fderiv ℝ f (γ t)‖₊ : ℝ≥0∞) * (‖deriv γ t‖₊ : ℝ≥0∞) := by simp_rw [hptf]
      _ = arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ := by
            rw [arcLengthLineIntegral]
      _ ≠ ∞ := hfin
  have hh_int : IntegrableOn (fdNormMulDeriv f γ) (Set.uIoc x y) :=
    hh_int_uIcc.mono_set Set.Ioc_subset_Icc_self
  -- The mollified piece is continuous, hence measurable.
  have hfn_density_meas : Measurable
      (fun t => ‖fderiv ℝ (fn n) (γ t)‖ * ‖deriv γ t‖) :=
    (((hfn_fderiv_cont n).comp hγcont).norm.measurable).mul hderiv_meas
  -- The differential-difference density `dterm t := ‖dn t‖ * ‖γ' t‖`.
  have hdmeas : Measurable
      (fun t => ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖) := by
    have hfn_meas : Measurable (fun t => fderiv ℝ (fn n) (γ t)) :=
      ((hfn_fderiv_cont n).measurable).comp hγcont.measurable
    have hf_meas : Measurable (fun t => fderiv ℝ f (γ t)) :=
      (measurable_fderiv ℝ f).comp hγcont.measurable
    have h1 : Measurable (fun t => ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖) :=
      (hfn_meas.sub hf_meas).norm
    exact h1.mul hderiv_meas
  -- Its enorm at `t` equals the `ℝ≥0∞`-density factor.
  have hpt : ∀ t,
      ‖‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖‖ₑ
        = (‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖₊ : ℝ≥0∞) *
          (‖deriv γ t‖₊ : ℝ≥0∞) := by
    intro t
    rw [enorm_eq_nnnorm, nnnorm_mul, ENNReal.coe_mul, nnnorm_norm, nnnorm_norm]
  -- The lower integral of its enorm over `uIoc x y` is `≤ A n`.
  have hAeq : A n = ∫⁻ t in Set.Icc (0:ℝ) 1,
      (‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖₊ : ℝ≥0∞) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
    simp only [hA, arcLengthLineIntegral]
  have hle : (∫⁻ t in Set.uIoc x y,
      ‖‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖‖ₑ) ≤ A n := by
    simp_rw [hpt]
    rw [hAeq]
    exact MeasureTheory.lintegral_mono_set (Set.Ioc_subset_Icc_self.trans hxy)
  -- The excess density is integrable on `uIoc x y` (finite enorm integral `≤ A n < ∞`).
  have hdterm_int : IntegrableOn
      (fun t => ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖)
      (Set.uIoc x y) := by
    refine ⟨hdmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lt_top_iff_ne_top]
    exact ne_top_of_le_ne_top hAnetop hle
  -- The reverse-triangle pointwise bound `g ≤ h + dterm`.
  have hbound : ∀ t, ‖fderiv ℝ (fn n) (γ t)‖ * ‖deriv γ t‖ ≤
      fdNormMulDeriv f γ t +
        ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖ := by
    intro t
    have htri : ‖fderiv ℝ (fn n) (γ t)‖ ≤
        ‖fderiv ℝ f (γ t)‖ + ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ := by
      have := norm_le_norm_add_norm_sub' (fderiv ℝ (fn n) (γ t)) (fderiv ℝ f (γ t))
      simpa [norm_sub_rev] using this
    have hnn : (0 : ℝ) ≤ ‖deriv γ t‖ := norm_nonneg _
    calc ‖fderiv ℝ (fn n) (γ t)‖ * ‖deriv γ t‖
        ≤ (‖fderiv ℝ f (γ t)‖ +
            ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖) * ‖deriv γ t‖ :=
          mul_le_mul_of_nonneg_right htri hnn
      _ = fdNormMulDeriv f γ t +
            ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖ := by
          rw [fdNormMulDeriv, add_mul]
  -- The mollified density is integrable, dominated by `h + dterm`.
  have hg_int : IntegrableOn
      (fun t => ‖fderiv ℝ (fn n) (γ t)‖ * ‖deriv γ t‖) (Set.uIoc x y) := by
    refine Integrable.mono' (hh_int.add hdterm_int) hfn_density_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun t => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hbound t
  -- The arc-length excess term `Rₙ := ∫ ‖dn‖‖γ'‖`.
  set R : ℝ := ∫ t in Set.uIoc x y,
      ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖ with hR
  -- Bound `R ≤ (A n).toReal`.
  have hR_le : R ≤ (A n).toReal := by
    rw [hR]
    -- For nonneg integrand, `∫ ≤ (∫⁻ ‖·‖ₑ).toReal`.
    have hnn : 0 ≤ᵐ[volume.restrict (Set.uIoc x y)]
        (fun t => ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖) :=
      Filter.Eventually.of_forall (fun t => by positivity)
    have hstep : (∫ t in Set.uIoc x y,
        ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖) ≤
        (∫⁻ t in Set.uIoc x y,
          ‖‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖‖ₑ).toReal := by
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn
        hdterm_int.aestronglyMeasurable]
      apply ENNReal.toReal_mono (by
        rw [← lt_top_iff_ne_top]; exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hAnetop))
      refine MeasureTheory.lintegral_mono (fun t => ?_)
      rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (by positivity)]
    refine hstep.trans ?_
    exact ENNReal.toReal_mono hAnetop hle
  -- Finally: `∫ ‖fderiv (fn n)(γ)‖‖γ'‖ ≤ ∫ fdNormMulDeriv f γ + R ≤ ∫ fdNormMulDeriv f γ + ε`.
  have hmain : (∫ t in Set.uIoc x y, ‖fderiv ℝ (fn n) (γ t)‖ * ‖deriv γ t‖) ≤
      (∫ t in Set.uIoc x y, fdNormMulDeriv f γ t) + R := by
    rw [hR, ← MeasureTheory.integral_add hh_int hdterm_int]
    refine MeasureTheory.integral_mono hg_int (hh_int.add hdterm_int) (fun t => ?_)
    have htri : ‖fderiv ℝ (fn n) (γ t)‖ ≤
        ‖fderiv ℝ f (γ t)‖ + ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ := by
      have := norm_le_norm_add_norm_sub' (fderiv ℝ (fn n) (γ t)) (fderiv ℝ f (γ t))
      simpa [norm_sub_rev] using this
    have hnn : (0 : ℝ) ≤ ‖deriv γ t‖ := norm_nonneg _
    calc ‖fderiv ℝ (fn n) (γ t)‖ * ‖deriv γ t‖
        ≤ (‖fderiv ℝ f (γ t)‖ +
            ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖) * ‖deriv γ t‖ :=
          mul_le_mul_of_nonneg_right htri hnn
      _ = fdNormMulDeriv f γ t +
            ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖ := by
          rw [fdNormMulDeriv, add_mul]
  calc (∫ t in Set.uIoc x y, ‖fderiv ℝ (fn n) (γ t)‖ * ‖deriv γ t‖)
      ≤ (∫ t in Set.uIoc x y, fdNormMulDeriv f γ t) + R := hmain
    _ ≤ (∫ t in Set.uIoc x y, fdNormMulDeriv f γ t) + ε := by
        have := hR_le.trans hAn
        linarith

/-- **(Smooth approximant along the curve.)** For a quasiconformal `f`, an absolutely
continuous curve `γ` with finite gradient line integral, and any tolerance `ε > 0`,
there is a `C¹` function `g` that (i) approximates `f` at the two endpoints `γ x`,
`γ y` to within `ε`, and (ii) whose arc-length density integral along `γ` over
`uIoc x y` is within `ε` of the target `∫ fdNormMulDeriv f γ`.

Fully proven from the mollification glue and the single isolated residual
`fderiv_mollified_lineIntegral_le`: take `g = f_n = ρ_n ⋆ f` (`ρ_n` a normed
`ContDiffBump` with `rOut → 0`); `f_n` is `C¹` (`HasCompactSupport.contDiff_convolution_left`),
part (i) is the pointwise convergence `f_n (z) → f (z)`
(`ContDiffBump.convolution_tendsto_right_of_continuous`, `f` continuous), and part (ii)
is exactly the isolated residual. -/
theorem exists_contDiff_approx_along_curve {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) {γ : ℝ → ℂ}
    (hγac : ∀ a c : ℝ, AbsolutelyContinuousOnInterval γ a c)
    (hfin : arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ ≠ ∞)
    (x y : ℝ) (hxy : Set.uIcc x y ⊆ Set.Icc (0 : ℝ) 1) (hgood : GoodCurve f γ) :
    ∀ ε > (0 : ℝ), ∃ g : ℂ → ℂ, ContDiff ℝ 1 g ∧
      dist (f (γ x)) (g (γ x)) ≤ ε ∧ dist (f (γ y)) (g (γ y)) ≤ ε ∧
      (∫ t in Set.uIoc x y, ‖fderiv ℝ g (γ t)‖ * ‖deriv γ t‖) ≤
        (∫ t in Set.uIoc x y, fdNormMulDeriv f γ t) + ε := by
  intro ε hε
  -- `f` is continuous and locally integrable (from `IsQCAnalytic`).
  have hfcont : Continuous f := hf.1.1.continuous
  have hfloc : MeasureTheory.LocallyIntegrable f := hfcont.locallyIntegrable
  -- The good-curve mollifier sequence `φ n` of normed bumps with `rOut → 0`.
  obtain ⟨φ, hφrout, hgood_φ⟩ := hgood
  -- The mollified functions `f_n := (φ n).normed volume ⋆ f`, each `C^∞` hence `C¹`.
  set fn : ℕ → ℂ → ℂ :=
    fun n => MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) f
      (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume with hfndef
  have hfn_contDiff : ∀ n, ContDiff ℝ 1 (fn n) := fun n =>
    ((φ n).hasCompactSupport_normed).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (n := 1) (φ n).contDiff_normed hfloc
  -- (i) Pointwise convergence `f_n (z) → f (z)` at any point, from continuity of `f`.
  have hfn_tendsto : ∀ z : ℂ, Filter.Tendsto (fun n => fn n z) Filter.atTop (nhds (f z)) :=
    fun z => ContDiffBump.convolution_tendsto_right_of_continuous hφrout hfcont z
  -- Pick `N` large enough that `f_N` is within `ε` of `f` at both endpoints, AND the
  -- density-integral bound (the trace residual) holds within `ε`.  The density bound is
  -- the genuine Fuglede core, isolated below.
  have hfn_density : ∀ᶠ n in Filter.atTop,
      (∫ t in Set.uIoc x y, ‖fderiv ℝ (fn n) (γ t)‖ * ‖deriv γ t‖) ≤
        (∫ t in Set.uIoc x y, fdNormMulDeriv f γ t) + ε :=
    fderiv_mollified_lineIntegral_le hf hγac hfin x y hxy hε φ hφrout hgood_φ
  -- The endpoint convergences give eventual `ε`-closeness.
  have hev_close : ∀ z : ℂ, ∀ᶠ n in Filter.atTop, dist (f z) (fn n z) ≤ ε := by
    intro z
    have hd : Filter.Tendsto (fun n => dist (f z) (fn n z)) Filter.atTop (nhds 0) := by
      have := (tendsto_const_nhds (x := f z)).dist (hfn_tendsto z)
      simpa using this
    have := (hd.eventually (ge_mem_nhds (show (0 : ℝ) < ε from hε)))
    filter_upwards [this] with n hn using hn
  have hxev := hev_close (γ x)
  have hyev := hev_close (γ y)
  -- Combine the three eventual conditions and extract a witness `N`.
  obtain ⟨N, hN⟩ := (hfn_density.and (hxev.and hyev)).exists
  exact ⟨fn N, hfn_contDiff N, hN.2.1, hN.2.2, hN.1⟩

/-- **(Fuglede upper-gradient inequality.)** For a quasiconformal `f` and an absolutely
continuous curve `γ` whose gradient line integral over `[0,1]` is finite, the distance
moved by `f ∘ γ` across a subinterval `uIoc x y ⊆ [0,1]` is bounded by the arc-length
integral of `‖fderiv ℝ f‖` over that subinterval.

The proof is the elementary `ε`-limit glue over the smooth approximant residual
`exists_contDiff_approx_along_curve`: applying the proven smooth upper-gradient bound
`dist_comp_le_setIntegral_of_contDiff` to the `C¹` approximant `g` and inserting it via
the triangle inequality
`dist (f (γ x)) (f (γ y)) ≤ dist (f (γ x)) (g (γ x)) + dist (g (γ x)) (g (γ y))
  + dist (g (γ y)) (f (γ y))`
bounds the LHS by `∫ fdNormMulDeriv f γ + 3ε` for every `ε > 0`; letting `ε → 0`
closes the inequality. All the mollification setup, smooth chain-rule/FTC bound, and
ℂ-valued density integrability are discharged in the helpers above; only the
trace-convergence core remains, isolated in `exists_contDiff_approx_along_curve`. -/
theorem fugledeUpperGradient {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) {γ : ℝ → ℂ}
    (hγac : ∀ a c : ℝ, AbsolutelyContinuousOnInterval γ a c)
    (hfin : arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ ≠ ∞)
    (x y : ℝ) (hxy : Set.uIcc x y ⊆ Set.Icc (0 : ℝ) 1) (hgood : GoodCurve f γ) :
    dist ((f ∘ γ) x) ((f ∘ γ) y) ≤ ∫ t in Set.uIoc x y, fdNormMulDeriv f γ t := by
  -- It suffices to show `dist ≤ target + 3ε` for every `ε > 0`.
  rw [show (f ∘ γ) x = f (γ x) from rfl, show (f ∘ γ) y = f (γ y) from rfl]
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  -- Obtain the `C¹` approximant `g` for tolerance `ε / 3`.
  obtain ⟨g, hg_smooth, hgx, hgy, hg_int⟩ :=
    exists_contDiff_approx_along_curve hf hγac hfin x y hxy hgood (ε / 3) (by positivity)
  -- The proven smooth upper-gradient bound for `g`.
  have hsmooth := dist_comp_le_setIntegral_of_contDiff hg_smooth hγac x y
  -- Triangle inequality: insert `g (γ x)`, `g (γ y)` between the `f`-endpoints.
  have htri : dist (f (γ x)) (f (γ y)) ≤
      dist (f (γ x)) (g (γ x)) + dist (g (γ x)) (g (γ y)) + dist (g (γ y)) (f (γ y)) := by
    have h1 : dist (f (γ x)) (f (γ y))
        ≤ dist (f (γ x)) (g (γ y)) + dist (g (γ y)) (f (γ y)) := dist_triangle _ _ _
    have h2 : dist (f (γ x)) (g (γ y))
        ≤ dist (f (γ x)) (g (γ x)) + dist (g (γ x)) (g (γ y)) := dist_triangle _ _ _
    linarith
  -- Chain the bounds: `dist (g (γ x)) (g (γ y)) ≤ ∫ density g`, then `hg_int`.
  have hgy' : dist (g (γ y)) (f (γ y)) ≤ ε / 3 := by rw [dist_comm]; exact hgy
  -- Combine all bounds linearly.
  have : (∫ t in Set.uIoc x y, ‖fderiv ℝ g (γ t)‖ * ‖deriv γ t‖) ≤
      (∫ t in Set.uIoc x y, fdNormMulDeriv f γ t) + ε / 3 := hg_int
  linarith [htri, hgx, hgy', hsmooth, this]

/-- **(Fuglede upper-gradient inequality, statement-fixed `[0,1]`-restricted form.)**
The distance moved by `f ∘ γ` across a subinterval `uIoc x y ⊆ [0,1]` is bounded by
the arc-length integral of `‖fderiv ℝ f‖` over that subinterval. The `[0,1]` guard
`hxy : uIcc x y ⊆ Icc 0 1` is essential and consumable: `hfin` only controls the
gradient line integral over `[0,1]`, and the downstream length–area assembly only
ever integrates along `[0,1]`. A thin wrapper over the isolated residual
`fugledeUpperGradient`. -/
theorem dist_le_setIntegral_fderiv_norm_mul_deriv {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) {γ : ℝ → ℂ}
    (hγac : ∀ a c : ℝ, AbsolutelyContinuousOnInterval γ a c)
    (hfin : arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ ≠ ∞)
    (x y : ℝ) (hxy : Set.uIcc x y ⊆ Set.Icc (0 : ℝ) 1) (hgood : GoodCurve f γ) :
    dist ((f ∘ γ) x) ((f ∘ γ) y) ≤ ∫ t in Set.uIoc x y, fdNormMulDeriv f γ t :=
  fugledeUpperGradient hf hγac hfin x y hxy hgood

/-- **(Interval integrability of the density, helper 2 of 2.)** The real
arc-length integrand `g t := ‖fderiv ℝ f (γ t)‖ · ‖deriv γ t‖` is integrable on
every compact interval `uIcc a c ⊆ [0,1]`.

With the `[0,1]` guard this is exactly the `ℝ`-valued content of `hfin`: `γ` is
continuous (it is AC on every interval), so `g` is measurable, and the lower
integral of its enorm over `[0,1]` equals
`arcLengthLineIntegral ‖fderiv ℝ f‖ γ`, which is finite by `hfin`. A nonnegative
measurable function with finite lower integral is integrable, and
`IntegrableOn.mono_set` restricts from `[0,1]` to `uIcc a c`. -/
theorem integrableOn_fderiv_norm_mul_deriv_uIcc {f : ℂ → ℂ} {b : BeltramiCoeff}
    (_hf : IsQCAnalytic f b) {γ : ℝ → ℂ}
    (hγac : ∀ a c : ℝ, AbsolutelyContinuousOnInterval γ a c)
    (hfin : arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ ≠ ∞)
    (a c : ℝ) (huIcc : Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1) :
    IntegrableOn (fdNormMulDeriv f γ) (Set.uIcc a c) := by
  -- `γ` is continuous (AC on every interval ⇒ continuous).
  have hγcont : Continuous γ := by
    rw [continuous_iff_continuousAt]
    intro x
    have hcon : ContinuousOn γ (Set.uIcc (x - 1) (x + 1)) :=
      (hγac (x - 1) (x + 1)).continuousOn
    have hmem : Set.uIcc (x - 1) (x + 1) ∈ nhds x := by
      rw [Set.uIcc_of_le (by linarith)]
      exact Icc_mem_nhds (by linarith) (by linarith)
    exact hcon.continuousAt hmem
  -- Measurability of the integrand.
  have hmeas : Measurable (fdNormMulDeriv f γ) := by
    have h1 : Measurable (fun t => ‖fderiv ℝ f (γ t)‖) :=
      ((measurable_fderiv ℝ f).norm).comp hγcont.measurable
    have h2 : Measurable (fun t => ‖deriv γ t‖) := (measurable_deriv γ).norm
    simpa only [fdNormMulDeriv] using h1.mul h2
  -- Reduce `uIcc a c` to `Icc 0 1`.
  refine IntegrableOn.mono_set ?_ huIcc
  -- Build `Integrable` from AEStronglyMeasurable + HasFiniteIntegral.
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lt_top_iff_ne_top]
  -- The lintegral of the enorm equals the arc-length line integral of `hfin`.
  have hpt : ∀ t, ‖fdNormMulDeriv f γ t‖ₑ
      = (‖fderiv ℝ f (γ t)‖₊ : ℝ≥0∞) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
    intro t
    simp only [fdNormMulDeriv, enorm_eq_nnnorm, nnnorm_mul, nnnorm_norm,
      ENNReal.coe_mul]
  calc ∫⁻ t in Set.Icc (0:ℝ) 1, ‖fdNormMulDeriv f γ t‖ₑ
      = ∫⁻ t in Set.Icc (0:ℝ) 1,
          (‖fderiv ℝ f (γ t)‖₊ : ℝ≥0∞) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
        simp_rw [hpt]
    _ = arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ := by
        rw [arcLengthLineIntegral]
    _ ≠ ∞ := hfin

/-- **(Fuglede length–area content.)** Absolute continuity of `f ∘ γ` on every
interval, given that the gradient line integral
`∫₀¹ ‖fderiv ℝ f (γ t)‖ ‖γ' t‖ dt` is finite and the curve `γ` is itself
absolutely continuous.

The genuine analytic core is fully reduced to two precise named helpers:
`dist_le_setIntegral_fderiv_norm_mul_deriv` (the upper-gradient inequality along
the curve — the mollification / `L¹`-trace step) and
`integrableOn_fderiv_norm_mul_deriv_uIcc` (interval integrability of the density).
Granting those, this proof is the elementary `ε`-`δ` glue: it mirrors Mathlib's
`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`, bounding the
distance-sum over a disjoint interval family by the set-integral of the density
over their union and using that the integral over a small-measure set is small
(`Integrable.tendsto_setIntegral_nhds_zero`). -/
theorem absolutelyContinuous_comp_of_finite_lineIntegral {f : ℂ → ℂ}
    {b : BeltramiCoeff} (hf : IsQCAnalytic f b) {γ : ℝ → ℂ}
    (hγac : ∀ a c : ℝ, AbsolutelyContinuousOnInterval γ a c)
    (hfin : arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ ≠ ∞)
    (hgood : GoodCurve f γ) :
    ∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
      AbsolutelyContinuousOnInterval (f ∘ γ) a c := by
  intro a c huIcc
  -- The density `g` and its integrability on `uIcc a c`.
  set g : ℝ → ℝ := fdNormMulDeriv f γ with hg
  have hgint : IntegrableOn g (Set.uIcc a c) :=
    integrableOn_fderiv_norm_mul_deriv_uIcc hf hγac hfin a c huIcc
  -- `g` is nonnegative.
  have hgnonneg : ∀ t, 0 ≤ g t := fun t => by
    rw [hg, fdNormMulDeriv]; positivity
  -- Abbreviation for the union of the disjoint subintervals of a family `E`.
  set s : ℕ × (ℕ → ℝ × ℝ) → Set ℝ :=
    fun E => ⋃ i ∈ Finset.range E.1, Set.uIoc (E.2 i).1 (E.2 i).2 with hs
  -- The set-integrals of `g` over `s E`, restricted to `uIoc a c`, tend to `0`
  -- as the total length of `E` tends to `0` along `disjWithin a c`.
  have hgint' : Integrable g (volume.restrict (Set.uIoc a c)) := by
    have : IntegrableOn g (Set.uIoc a c) :=
      hgint.mono_set Set.Ioc_subset_Icc_self
    exact this
  have htend : Filter.Tendsto
      (fun E => ∫ t in s E, g t ∂(volume.restrict (Set.uIoc a c)))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        Filter.principal (AbsolutelyContinuousOnInterval.disjWithin a c)) (nhds 0) :=
    hgint'.tendsto_setIntegral_nhds_zero
      (AbsolutelyContinuousOnInterval.tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero
        a c)
  -- Reduce to the `ε`-`δ` form via the `disjWithin` filter, mirroring Mathlib's
  -- `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`.
  rw [AbsolutelyContinuousOnInterval]
  refine squeeze_zero' (g := fun E =>
      ∫ t in s E, g t ∂(volume.restrict (Set.uIoc a c))) ?_ ?_ htend
  · -- The distance-sum is nonnegative.
    filter_upwards with E
    exact Finset.sum_nonneg (fun _ _ => dist_nonneg)
  · -- The distance-sum is bounded by the set-integral of `g`.
    have hmem : ∀ᶠ (E : ℕ × (ℕ → ℝ × ℝ)) in
        (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
          Filter.principal (AbsolutelyContinuousOnInterval.disjWithin a c)),
        E ∈ AbsolutelyContinuousOnInterval.disjWithin a c :=
      Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall fun _ h => h)
    filter_upwards [hmem] with E hE
    obtain ⟨n, I⟩ := E
    -- Each subinterval `uIoc (I i).1 (I i).2 ⊆ uIoc a c`.
    have hsub : ∀ i ∈ Finset.range n,
        Set.uIoc (I i).1 (I i).2 ⊆ Set.uIoc a c :=
      fun i hi => AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hE
        (Finset.mem_range.mp hi)
    -- Each subinterval's *closed* hull `uIcc (I i).1 (I i).2 ⊆ Icc 0 1`: its endpoints
    -- lie in `uIcc a c ⊆ Icc 0 1` (from `disjWithin a c` membership and `huIcc`).
    have hsub01 : ∀ i ∈ Finset.range n,
        Set.uIcc (I i).1 (I i).2 ⊆ Set.Icc (0 : ℝ) 1 := by
      intro i hi
      obtain ⟨hp1, hp2⟩ := hE.1 i hi
      exact Set.uIcc_subset_Icc (huIcc hp1) (huIcc hp2)
    -- `g` is integrable on each subinterval (restricted to `uIoc a c`).
    have hgint_i : ∀ i ∈ Finset.range n,
        IntegrableOn g (Set.uIoc (I i).1 (I i).2) (volume.restrict (Set.uIoc a c)) := by
      intro i hi
      rw [IntegrableOn, Measure.restrict_restrict_of_subset (hsub i hi)]
      exact hgint.mono_set
        ((hsub i hi).trans Set.Ioc_subset_Icc_self)
    -- The disjointness of the subintervals (within `uIoc`).
    have hdisj : (↑(Finset.range n) : Set ℕ).PairwiseDisjoint
        (fun i => Set.uIoc (I i).1 (I i).2) := hE.2
    -- Measurability of each subinterval.
    have hmeas : ∀ i ∈ Finset.range n, MeasurableSet (Set.uIoc (I i).1 (I i).2) :=
      fun i _ => measurableSet_uIoc
    -- Bound each distance by the per-subinterval integral, then sum.
    calc ∑ i ∈ Finset.range n, dist ((f ∘ γ) (I i).1) ((f ∘ γ) (I i).2)
        ≤ ∑ i ∈ Finset.range n,
            ∫ t in Set.uIoc (I i).1 (I i).2, g t ∂(volume.restrict (Set.uIoc a c)) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          rw [Measure.restrict_restrict_of_subset (hsub i hi)]
          exact dist_le_setIntegral_fderiv_norm_mul_deriv hf hγac hfin (I i).1 (I i).2
            (hsub01 i hi) hgood
      _ = ∫ t in s (n, I), g t ∂(volume.restrict (Set.uIoc a c)) := by
          rw [hs]
          exact (integral_biUnion_finset (Finset.range n) hmeas (hdisj : Set.Pairwise _ _)
            hgint_i).symm

/-- **(Chain-rule clause.)** For a.e. `t ∈ [0,1]` with `deriv γ t ≠ 0`, the
composite `f ∘ γ` has derivative `(fderiv ℝ f (γ t)) (deriv γ t)` at `t`.

The single-point identity is `HasFDerivAt.comp_hasDerivAt`, which needs both
`HasFDerivAt f (fderiv ℝ f (γ t)) (γ t)` and `HasDerivAt γ (deriv γ t) t`. The
second factor comes from the absolute continuity of `γ` (`hγac`): an AC curve has
bounded variation on `[0,1]`, hence is differentiable a.e.
(`BoundedVariationOn.ae_differentiableAt_of_mem_uIcc`), so `HasDerivAt γ
(deriv γ t) t` holds a.e. The first factor comes from `hmeet`: the arc length of
the contact between `γ` and the degeneracy set
`N := {z | ¬(DifferentiableAt ℝ f z ∧ 0 < det (fderiv ℝ f z))}` is negligible,
which forces the parameter footprint `{t ∈ [0,1] | deriv γ t ≠ 0 ∧ γ t ∈ N}` to
be Lebesgue-null; off it, `deriv γ t ≠ 0` implies `DifferentiableAt ℝ f (γ t)`.
Combining the two a.e. facts gives the chain rule a.e. on `[0,1]`. -/
theorem chainRule_hasDerivAt_of_finite {f : ℂ → ℂ} {b : BeltramiCoeff}
    (_hf : IsQCAnalytic f b) {γ : ℝ → ℂ}
    (hγac : ∀ a c : ℝ, AbsolutelyContinuousOnInterval γ a c)
    (_hfin : arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ ≠ ∞)
    (hmeet : ¬ 1 ≤ arcLengthLineIntegral
      ({z | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)}.indicator
        (fun _ => ∞)) γ) :
    ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
      HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t := by
  classical
  -- `γ` is continuous: it is absolutely continuous, hence continuous, on every
  -- interval `uIcc (x-1) (x+1)`, which is a neighborhood of `x`.
  have hγcont : Continuous γ := by
    rw [continuous_iff_continuousAt]
    intro x
    have hcon : ContinuousOn γ (Set.uIcc (x - 1) (x + 1)) := (hγac (x - 1) (x + 1)).continuousOn
    have hmem : Set.uIcc (x - 1) (x + 1) ∈ nhds x := by
      rw [Set.uIcc_of_le (by linarith)]
      exact Icc_mem_nhds (by linarith) (by linarith)
    exact hcon.continuousAt hmem
  -- The degeneracy set `N` (where `f` is not differentiable with positive Jacobian).
  set N : Set ℂ := {z | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)} with hN
  have hNmeas : MeasurableSet N := by
    have hd : MeasurableSet {z : ℂ | DifferentiableAt ℝ f z} :=
      measurableSet_of_differentiableAt ℝ f
    have hdet : MeasurableSet {z : ℂ | 0 < (fderiv ℝ f z).det} :=
      measurableSet_lt measurable_const
        ((ContinuousLinearMap.continuous_det).measurable.comp (measurable_fderiv ℝ f))
    have : N = ({z : ℂ | DifferentiableAt ℝ f z} ∩ {z : ℂ | 0 < (fderiv ℝ f z).det})ᶜ := by
      ext z; simp [hN, Set.mem_compl_iff, not_and]
    rw [this]; exact (hd.inter hdet).compl
  -- The bad parameter set: where `deriv γ t ≠ 0` and `γ t` lands in the degeneracy set.
  set B : Set ℝ := {t | deriv γ t ≠ 0 ∧ γ t ∈ N} with hB
  have hBmeas : MeasurableSet B := by
    have hd : MeasurableSet {t : ℝ | deriv γ t ≠ 0} :=
      (measurableSet_singleton (0 : ℂ)).preimage (measurable_deriv γ) |>.compl
    have hpre : MeasurableSet {t : ℝ | γ t ∈ N} := hNmeas.preimage hγcont.measurable
    have : B = {t : ℝ | deriv γ t ≠ 0} ∩ {t : ℝ | γ t ∈ N} := by
      ext t; simp [hB, Set.mem_inter_iff]
    rw [this]; exact hd.inter hpre
  -- The `∞·𝟙_N`-line-integrand equals `∞` exactly on `B`, else `0`.
  have hintegrand : ∀ t, (N.indicator (fun _ => (∞ : ℝ≥0∞)) (γ t)) *
      (‖deriv γ t‖₊ : ℝ≥0∞) = B.indicator (fun _ => (∞ : ℝ≥0∞)) t := by
    intro t
    by_cases hd : deriv γ t = 0
    · have htB : t ∉ B := fun h => h.1 hd
      rw [Set.indicator_of_notMem htB]
      simp [hd]
    · by_cases hγN : γ t ∈ N
      · have htB : t ∈ B := ⟨hd, hγN⟩
        have hnz : (‖deriv γ t‖₊ : ℝ≥0∞) ≠ 0 := by
          simp only [ne_eq, ENNReal.coe_eq_zero, nnnorm_eq_zero]
          exact hd
        rw [Set.indicator_of_mem hγN, Set.indicator_of_mem htB, ENNReal.top_mul hnz]
      · have htB : t ∉ B := fun h => hγN h.2
        rw [Set.indicator_of_notMem hγN, Set.indicator_of_notMem htB, zero_mul]
  have hLI : arcLengthLineIntegral (N.indicator (fun _ => (∞ : ℝ≥0∞))) γ
      = (∞ : ℝ≥0∞) * volume (B ∩ Set.Icc (0 : ℝ) 1) := by
    unfold arcLengthLineIntegral
    rw [show (fun t => (N.indicator (fun _ => (∞ : ℝ≥0∞)) (γ t)) *
        (‖deriv γ t‖₊ : ℝ≥0∞)) = B.indicator (fun _ => (∞ : ℝ≥0∞)) from
      funext hintegrand]
    rw [lintegral_indicator hBmeas, setLIntegral_const,
      Measure.restrict_apply hBmeas, Set.inter_comm]
  -- From `hmeet`: the parameter footprint of `B` on `[0,1]` is Lebesgue-null.
  have hBnull : volume (B ∩ Set.Icc (0 : ℝ) 1) = 0 := by
    by_contra hpos
    apply hmeet
    rw [hLI, ENNReal.top_mul hpos]
    exact le_top
  -- Hence a.e.-`t` on `[0,1]`: `deriv γ t ≠ 0 → DifferentiableAt ℝ f (γ t)`.
  have hdifff : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      deriv γ t ≠ 0 → DifferentiableAt ℝ f (γ t) := by
    rw [ae_restrict_iff' measurableSet_Icc, ae_iff]
    apply measure_mono_null _ hBnull
    intro t ht
    simp only [Set.mem_setOf_eq, Classical.not_imp] at ht
    obtain ⟨hmem, hd, hndf⟩ := ht
    refine ⟨⟨hd, ?_⟩, hmem⟩
    -- `¬ DifferentiableAt ℝ f (γ t)` ⟹ `γ t ∈ N`.
    simp only [hN, Set.mem_setOf_eq, not_and]
    exact fun hdf => absurd hdf hndf
  -- A.e.-`t` on `[0,1]`: `γ` is differentiable (hence `HasDerivAt γ (deriv γ t) t`).
  have hdiffγ : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      DifferentiableAt ℝ γ t := by
    rw [ae_restrict_iff' measurableSet_Icc]
    have hbv : BoundedVariationOn γ (Set.uIcc (0 : ℝ) 1) := (hγac 0 1).boundedVariationOn
    filter_upwards [hbv.ae_differentiableAt_of_mem_uIcc] with t ht htmem
    exact ht (by rw [Set.uIcc_of_le (by norm_num)]; exact htmem)
  -- Combine the three a.e. facts and compose via `HasFDerivAt.comp_hasDerivAt`.
  filter_upwards [hdifff, hdiffγ] with t hdiffft hdiffγt hd0
  have hfd : HasFDerivAt f (fderiv ℝ f (γ t)) (γ t) := (hdiffft hd0).hasFDerivAt
  have hγd : HasDerivAt γ (deriv γ t) t := hdiffγt.hasDerivAt
  exact hfd.comp_hasDerivAt t hγd

/-- **(F3) Good curves obey the chain rule.** A curve `γ` whose gradient line
integral `∫₀¹ ‖fderiv ℝ f (γ t)‖ ‖γ' t‖ dt` is *finite* and which meets the
degeneracy set `N := {z | ¬(DifferentiableAt ℝ f z ∧ 0 < det (fderiv ℝ f z))}`
only on an arc-length-negligible set (`¬ 1 ≤ ∫₀¹ (∞·𝟙_N)(γ t)‖γ' t‖ dt`) satisfies
all three good clauses: `f ∘ γ` is absolutely continuous on every interval; the
Jacobian determinant `det (fderiv ℝ f (γ t))` is positive for a.e.-`t`; and the
chain rule `HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t))(deriv γ t)) t` holds for
a.e.-`t`.

**Domain of the a.e.-clauses.** The arc-length line integral lives on the
parameter interval `[0,1]`, and the hypotheses (`hfin`, `hmeet`) constrain `γ`
*only* there; nothing is known about `γ` outside `[0,1]`. Accordingly clauses 2
and 3 are stated for `∀ᵐ t ∂(volume.restrict (Set.Icc 0 1))` — exactly the
strength the length–area transfer consumes (its integrand
`ρ(γ t)‖deriv (f∘γ) t‖` is integrated over `[0,1]`, and the `deriv γ t = 0`
points contribute `0`). With the global `∀ᵐ t : ℝ` the clauses would be
genuinely unprovable, the parametrisation outside `[0,1]` being arbitrary.

**What is proven here vs isolated.** Clause 2 (the guarded determinant
positivity) is discharged in full: from `hmeet`, the contact set
`{t ∈ [0,1] | γ t ∈ N ∧ deriv γ t ≠ 0}` carries an `∞`-valued integrand, so it
must be Lebesgue-null (else the integral is `∞ ≥ 1`), giving `γ t ∉ N`, i.e.
`0 < det`, for a.e. such `t`. The two remaining clauses are the genuine
Fuglede/chain-rule content and are isolated as named helper hypotheses:
  * `clause 3` (the chain rule `HasDerivAt (f∘γ) ((Df)(γ t)·γ' t) t`) needs
    `DifferentiableAt ℝ γ t` (via `HasFDerivAt.comp_hasDerivAt`, since
    `deriv γ t` is the junk derivative unless `γ` is differentiable). The curve
    family carries no rectifiability/AC of `γ`, so this is *not* dischargeable
    from `hfin`/`hmeet` alone — see `chainRule_hasDerivAt_of_finite`.
  * `clause 1` (absolute continuity of `f∘γ`) is the genuine length–area
    estimate `‖f(γ t)−f(γ s)‖ ≤ ∫ₛᵗ ‖Df(γ)‖‖γ'‖`. Our ACL theory is for
    coordinate lines, not general curves, so this is isolated as
    `absolutelyContinuous_comp_of_finite_lineIntegral`. -/
theorem chainRule_good_of_finite {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) {γ : ℝ → ℂ} (hγcont : Continuous γ)
    (hγac : ∀ a c : ℝ, AbsolutelyContinuousOnInterval γ a c)
    (hfin : arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ ≠ ∞)
    (hmeet : ¬ 1 ≤ arcLengthLineIntegral
      ({z | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)}.indicator
        (fun _ => ∞)) γ) (hgood : GoodCurve f γ) :
    (∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
        AbsolutelyContinuousOnInterval (f ∘ γ) a c) ∧
      (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det) ∧
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
        HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t := by
  -- The degeneracy set and the operator-norm density.
  set N : Set ℂ := {z | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)} with hN
  -- `N` is measurable (same computation as in the modulus reduction).
  have hNmeas : MeasurableSet N := by
    have hd : MeasurableSet {z : ℂ | DifferentiableAt ℝ f z} :=
      measurableSet_of_differentiableAt ℝ f
    have hdet : MeasurableSet {z : ℂ | 0 < (fderiv ℝ f z).det} :=
      measurableSet_lt measurable_const
        ((ContinuousLinearMap.continuous_det).measurable.comp (measurable_fderiv ℝ f))
    have : N = ({z : ℂ | DifferentiableAt ℝ f z} ∩ {z : ℂ | 0 < (fderiv ℝ f z).det})ᶜ := by
      ext z; simp [hN, Set.mem_compl_iff, not_and]
    rw [this]; exact (hd.inter hdet).compl
  -- ===================================================================
  -- CLAUSE 2 (proven): the guarded determinant positivity on `[0,1]`.
  -- From `hmeet`, the contact set has a Lebesgue-null parameter footprint.
  -- ===================================================================
  -- The bad parameter set for clause 2, sitting inside the contact set.
  set B : Set ℝ := {t | deriv γ t ≠ 0 ∧ γ t ∈ N} with hB
  -- `B` is measurable: `γ` is continuous (hence measurable), `N` measurable,
  -- and `deriv γ` is always measurable.
  have hBmeas : MeasurableSet B := by
    have hd : MeasurableSet {t : ℝ | deriv γ t ≠ 0} :=
      (measurableSet_singleton (0 : ℂ)).preimage
        (measurable_deriv γ) |>.compl
    have hpre : MeasurableSet {t : ℝ | γ t ∈ N} :=
      hNmeas.preimage hγcont.measurable
    have : B = {t : ℝ | deriv γ t ≠ 0} ∩ {t : ℝ | γ t ∈ N} := by
      ext t; simp [hB, Set.mem_inter_iff]
    rw [this]; exact hd.inter hpre
  -- The `∞·𝟙_N`-line-integrand: equals `∞` exactly on `B`, else `0`.
  have hintegrand : ∀ t, (N.indicator (fun _ => (∞ : ℝ≥0∞)) (γ t)) *
      (‖deriv γ t‖₊ : ℝ≥0∞) = B.indicator (fun _ => (∞ : ℝ≥0∞)) t := by
    intro t
    by_cases hd : deriv γ t = 0
    · -- `‖0‖₊ = 0` kills the product; and `t ∉ B`.
      have htB : t ∉ B := fun h => h.1 hd
      rw [Set.indicator_of_notMem htB]
      simp [hd]
    · by_cases hγN : γ t ∈ N
      · have htB : t ∈ B := ⟨hd, hγN⟩
        have hnz : (‖deriv γ t‖₊ : ℝ≥0∞) ≠ 0 := by
          simp only [ne_eq, ENNReal.coe_eq_zero, nnnorm_eq_zero]
          exact hd
        rw [Set.indicator_of_mem hγN, Set.indicator_of_mem htB, ENNReal.top_mul hnz]
      · have htB : t ∉ B := fun h => hγN h.2
        rw [Set.indicator_of_notMem hγN, Set.indicator_of_notMem htB, zero_mul]
  -- The line integral of `∞·𝟙_N` equals `∞ * volume (B ∩ [0,1])`.
  have hLI : arcLengthLineIntegral (N.indicator (fun _ => (∞ : ℝ≥0∞))) γ
      = (∞ : ℝ≥0∞) * volume (B ∩ Set.Icc (0 : ℝ) 1) := by
    unfold arcLengthLineIntegral
    rw [show (fun t => (N.indicator (fun _ => (∞ : ℝ≥0∞)) (γ t)) *
        (‖deriv γ t‖₊ : ℝ≥0∞)) = B.indicator (fun _ => (∞ : ℝ≥0∞)) from
      funext hintegrand]
    rw [lintegral_indicator hBmeas, setLIntegral_const,
      Measure.restrict_apply hBmeas, Set.inter_comm]
  -- From `hmeet`: that integral is `< 1 < ∞`, so the measure must be `0`.
  have hBnull : volume (B ∩ Set.Icc (0 : ℝ) 1) = 0 := by
    by_contra hpos
    apply hmeet
    rw [hLI, ENNReal.top_mul hpos]
    exact le_top
  -- Hence `∀ᵐ t ∂(restrict [0,1])`, `deriv γ t ≠ 0 → γ t ∉ N`, i.e. `0 < det`.
  have hclause2 : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det := by
    rw [ae_restrict_iff' measurableSet_Icc]
    rw [ae_iff]
    -- The exceptional set is contained in `B`, intersected with `[0,1]`.
    apply measure_mono_null _ hBnull
    intro t ht
    simp only [Set.mem_setOf_eq, Classical.not_imp] at ht
    obtain ⟨hmem, hd, hdet⟩ := ht
    refine ⟨⟨hd, ?_⟩, hmem⟩
    -- `¬ 0 < det` ⟹ `γ t ∈ N` (since `N` includes the `¬ 0 < det` half).
    simp only [hN, Set.mem_setOf_eq, not_and, not_lt]
    exact fun _ => not_lt.mp hdet
  -- ===================================================================
  -- CLAUSES 1 and 3 (isolated): the genuine Fuglede / chain-rule content.
  -- ===================================================================
  refine ⟨absolutelyContinuous_comp_of_finite_lineIntegral hf hγac hfin hgood, hclause2, ?_⟩
  exact chainRule_hasDerivAt_of_finite hf hγac hfin hmeet

/-- **Fuglede: the non-good curves of a family have zero modulus.** Assembled from
the mollified-gradient `L²` energy decay (`mollified_fderiv_ball_energy_tendsto_zero`)
and the Fuglede line-integral sweep (`curveModulus_lineIntegral_not_tendsto_zero`) via
a ball exhaustion of the (continuous) curves. -/
theorem IsQCAnalytic.curveModulus_notGoodCurve_zero {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) (Γ : Set (ℝ → ℂ)) (hcont : ∀ γ ∈ Γ, Continuous γ) :
    curveModulus {γ ∈ Γ | ¬ GoodCurve f γ} = 0 := by
  classical
  -- ===================================================================
  -- Ball exhaustion: split the non-good family by where the curve lives.
  -- ===================================================================
  set E : Set (ℝ → ℂ) := {γ ∈ Γ | ¬ GoodCurve f γ} with hE
  set Em : ℕ → Set (ℝ → ℂ) := fun m => {γ ∈ Γ | ¬ GoodCurve f γ ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Metric.closedBall (0 : ℂ) m)} with hEm
  -- `E = ⋃ m, Em m`.
  have hEunion : E = ⋃ m, Em m := by
    apply Set.eq_of_subset_of_subset
    · rintro γ ⟨hγΓ, hγbad⟩
      -- `γ '' Icc 0 1` is compact, hence bounded, hence in some `closedBall 0 m`.
      have hcomp : IsCompact (γ '' Set.Icc 0 1) :=
        isCompact_Icc.image (hcont γ hγΓ)
      obtain ⟨r, hr⟩ := hcomp.isBounded.subset_closedBall (0 : ℂ)
      obtain ⟨m, hm⟩ := exists_nat_ge r
      refine Set.mem_iUnion.mpr ⟨m, hγΓ, hγbad, fun t ht => ?_⟩
      have : γ t ∈ Metric.closedBall (0 : ℂ) r := hr (Set.mem_image_of_mem γ ht)
      exact Metric.closedBall_subset_closedBall hm this
    · refine Set.iUnion_subset (fun m γ hγ => ?_)
      obtain ⟨hγΓ, hγbad, _⟩ := hγ
      exact ⟨hγΓ, hγbad⟩
  rw [hEunion]
  -- Reduce to: each `Em m` has zero modulus.
  refine curveModulus_iUnion_zero (fun m => ?_)
  -- ===================================================================
  -- Per-ball sweep.  Fix `m`; work on the ball of radius `R = m + 1`.
  -- ===================================================================
  set R : ℝ := (m : ℝ) + 1 with hR
  -- A canonical mollifier sequence with `rOut = 2/(n+2) → 0`.
  set φ₀ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ with hφ₀
  have hφ₀rout : Filter.Tendsto (fun n => (φ₀ n).rOut) Filter.atTop (nhds 0) := by
    have : (fun n : ℕ => (φ₀ n).rOut) = fun n : ℕ => (2 : ℝ) / (n + 2) := rfl
    rw [this]
    exact Filter.Tendsto.div_atTop tendsto_const_nhds
      (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  -- The mollified-differential difference density and its ball-energy.
  set D : ℕ → ℂ → ℝ≥0∞ := fun n z =>
    (‖fderiv ℝ (MeasureTheory.convolution ((φ₀ n).normed MeasureTheory.volume) f
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) z - fderiv ℝ f z‖₊ : ℝ≥0∞)
    with hD
  -- `D n` is measurable.
  have hDmeas : ∀ n, Measurable (D n) := by
    intro n
    have h1 : Measurable (fderiv ℝ (MeasureTheory.convolution
        ((φ₀ n).normed MeasureTheory.volume) f (ContinuousLinearMap.lsmul ℝ ℝ)
        MeasureTheory.volume)) := measurable_fderiv ℝ _
    have h2 : Measurable (fderiv ℝ f) := measurable_fderiv ℝ f
    exact ((h1.sub h2).nnnorm).coe_nnreal_ennreal
  set a : ℕ → ℝ≥0∞ := fun n => ∫⁻ z in Metric.ball (0 : ℂ) R, (D n z) ^ 2 with ha
  -- Pillar A: the ball-energy of the differential difference tends to `0`.
  have haTendsto : Filter.Tendsto a Filter.atTop (nhds 0) :=
    mollified_fderiv_ball_energy_tendsto_zero hf R φ₀ hφ₀rout
  -- ===================================================================
  -- Extract a subsequence `σ` whose root-energies are geometrically small.
  -- ===================================================================
  have hkey : ∀ (c : ℝ≥0∞), c ≠ 0 → ∀ N : ℕ, ∃ n, N < n ∧ a n ≤ c := by
    intro c hc N
    have hev : ∀ᶠ n in Filter.atTop, a n ≤ c :=
      (ENNReal.tendsto_nhds_zero.mp haTendsto) c (pos_iff_ne_zero.mpr hc)
    obtain ⟨n, hn, hnc⟩ := (hev.and (Filter.eventually_gt_atTop N)).exists
    exact ⟨n, hnc, hn⟩
  -- The geometric threshold (squared so its root dominates `(1/2)^k`).
  have hthresh : ∀ k : ℕ, ((ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) ^ 2) ≠ 0 := by
    intro k
    apply pow_ne_zero
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  choose g hg1 hg2 using hkey
  set σ : ℕ → ℕ := fun k => Nat.rec
    (g ((ENNReal.ofReal ((1 / 2 : ℝ) ^ 0)) ^ 2) (hthresh 0) 0)
    (fun k prev => g ((ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1))) ^ 2) (hthresh (k + 1)) prev) k
    with hσ
  have hσmono : StrictMono σ := by
    apply strictMono_nat_of_lt_succ
    intro k
    exact hg1 ((ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1))) ^ 2) (hthresh (k + 1)) (σ k)
  have hσbound : ∀ k, a (σ k) ≤ (ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) ^ 2 := by
    intro k
    cases k with
    | zero => exact hg2 _ _ 0
    | succ n => exact hg2 _ _ (σ n)
  -- ===================================================================
  -- The truncated densities `G k` and their summable root-energies.
  -- ===================================================================
  set G : ℕ → ℂ → ℝ≥0∞ := fun k =>
    (Metric.ball (0 : ℂ) R).indicator (fun z => D (σ k) z) with hG
  have hGmeas : ∀ k, Measurable (G k) := fun k =>
    (hDmeas (σ k)).indicator measurableSet_ball
  -- `∫⁻ (G k)² = a (σ k)`.
  have hGenergy : ∀ k, (∫⁻ z, (G k z) ^ 2) = a (σ k) := by
    intro k
    have h1 : (fun z => (G k z) ^ 2)
        = (Metric.ball (0 : ℂ) R).indicator (fun z => (D (σ k) z) ^ 2) := by
      funext z
      by_cases hz : z ∈ Metric.ball (0 : ℂ) R
      · simp only [hG, Set.indicator_of_mem hz]
      · simp only [hG, Set.indicator_of_notMem hz]; ring
    rw [h1, lintegral_indicator measurableSet_ball]
  -- Root-energy bound: `(∫⁻ (G k)²)^{1/2} ≤ ofReal ((1/2)^k)`.
  have hGroot : ∀ k, (∫⁻ z, (G k z) ^ 2) ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    intro k
    rw [hGenergy k]
    calc a (σ k) ^ ((1 : ℝ) / 2)
        ≤ ((ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) ^ 2) ^ ((1 : ℝ) / 2) := by
          gcongr; exact hσbound k
      _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
          rw [← ENNReal.rpow_natCast (ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) 2,
            ← ENNReal.rpow_mul]; norm_num
  -- The sum of root-energies is finite (dominated by `∑ (1/2)^k = 2`).
  have hsum : ∑' k, (∫⁻ z, (G k z) ^ 2) ^ ((1 : ℝ) / 2) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hGroot)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  -- ===================================================================
  -- Pillar B: the curves where the truncated line integrals fail to
  -- vanish form a zero-modulus family.
  -- ===================================================================
  have hEmcont : ∀ γ ∈ Em m, Continuous γ := fun γ hγ => hcont γ hγ.1
  have hBzero : curveModulus {γ ∈ Em m | ¬ Filter.Tendsto
      (fun k => arcLengthLineIntegral (G k) γ) Filter.atTop (nhds 0)} = 0 :=
    curveModulus_lineIntegral_not_tendsto_zero hGmeas hsum hEmcont
  -- ===================================================================
  -- Containment: every curve of `Em m` fails the truncated convergence.
  -- ===================================================================
  refine le_antisymm ?_ (zero_le _)
  rw [← hBzero]
  refine curveModulus_mono ?_
  rintro γ ⟨hγΓ, hγbad, hγball⟩
  refine ⟨⟨hγΓ, hγbad, hγball⟩, ?_⟩
  -- For curves inside the ball, the truncated line integral equals the full one.
  have hLIeq : ∀ k, arcLengthLineIntegral (G k) γ
      = arcLengthLineIntegral (fun z => D (σ k) z) γ := by
    intro k
    unfold arcLengthLineIntegral
    apply setLIntegral_congr_fun measurableSet_Icc
    intro t ht
    simp only [hG]
    have hin : γ t ∈ Metric.ball (0 : ℂ) R := by
      have hcb : γ t ∈ Metric.closedBall (0 : ℂ) m := hγball t ht
      exact Metric.closedBall_subset_ball (by rw [hR]; linarith) hcb
    rw [Set.indicator_of_mem hin]
  -- Suppose the truncated line integrals tended to `0`; then `γ` would be good.
  intro hTend
  apply hγbad
  have hTend' : Filter.Tendsto (fun k => arcLengthLineIntegral (fun z => D (σ k) z) γ)
      Filter.atTop (nhds 0) := by
    have : (fun k => arcLengthLineIntegral (G k) γ)
        = fun k => arcLengthLineIntegral (fun z => D (σ k) z) γ := by
      funext k; exact hLIeq k
    rw [← this]; exact hTend
  -- The witness `φ := fun k => φ₀ (σ k)`.
  refine ⟨fun k => φ₀ (σ k), ?_, ?_⟩
  · exact hφ₀rout.comp hσmono.tendsto_atTop
  · exact hTend'

/-- **Fuglede's theorem (quasiconformal case).** For a quasiconformal map `f`, the
curves `γ` of a family along which the chain rule for `f` fails — either `f ∘ γ` is
not absolutely continuous, or its derivative does not agree almost everywhere with
`(D f)(γ) · γ'` — form a subfamily of zero modulus. This is exactly the strength the
length–area density transfer needs: on the complementary (full-modulus) subfamily,
the arc-length integral of a transferred density is governed by the differential of
`f` along the curve. (The bare absolute-continuity statement is strictly weaker:
absolute continuity of `f ∘ γ` does not by itself give the chain-rule identity,
because `f`'s plane-a.e. differentiability need not hold at a.e. point of a fixed
curve.)

The proof assembles three modulus-zero exceptional families.  Writing
`G z := ‖fderiv ℝ f z‖₊` and `N := {z | ¬(DifferentiableAt ℝ f z ∧
0 < det (fderiv ℝ f z))}` (a Lebesgue-null set), the exceptional family `E` is
contained in `F1 ∪ F2`, where `F1` is the infinite-`G`-line-integral family
(`curveModulus_lineIntegral_top_zero`) and `F2` is the family meeting `N` with
positive arc length (`curveModulus_meetsNullSet_zero`, since `N` is null).  The
inclusion `E ⊆ F1 ∪ F2` is the contrapositive of `chainRule_good_of_finite`.
Monotonicity (`curveModulus_mono`) and subadditivity for null families
(`curveModulus_union_zero`) finish. -/
theorem IsQCAnalytic.chainRule_exceptional_modulus_zero {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) (Γ : Set (ℝ → ℂ)) (hcont : ∀ γ ∈ Γ, Continuous γ)
    (hac : ∀ γ ∈ Γ, ∀ a c : ℝ, AbsolutelyContinuousOnInterval γ a c) :
    curveModulus {γ ∈ Γ | ¬ ((∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
        AbsolutelyContinuousOnInterval (f ∘ γ) a c) ∧
      (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det) ∧
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
        HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t)} = 0 := by
  classical
  -- The operator-norm density `G` of the differential, and the degeneracy set `N`.
  set G : ℂ → ℝ≥0∞ := fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞) with hG
  set N : Set ℂ := {z | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)} with hN
  -- `N` is measurable.
  have hNmeas : MeasurableSet N := by
    have hd : MeasurableSet {z : ℂ | DifferentiableAt ℝ f z} :=
      measurableSet_of_differentiableAt ℝ f
    have hdet : MeasurableSet {z : ℂ | 0 < (fderiv ℝ f z).det} :=
      measurableSet_lt measurable_const
        ((ContinuousLinearMap.continuous_det).measurable.comp (measurable_fderiv ℝ f))
    rw [hN]
    have : {z : ℂ | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)}
        = ({z : ℂ | DifferentiableAt ℝ f z} ∩ {z : ℂ | 0 < (fderiv ℝ f z).det})ᶜ := by
      ext z; simp [Set.mem_compl_iff, not_and]
    rw [this]
    exact (hd.inter hdet).compl
  -- `N` is Lebesgue-null: a.e. `z` is differentiable with positive determinant.
  have hNnull : volume N = 0 := by
    rw [hN, ← ae_iff]
    filter_upwards [hf.1.2, IsQCAnalytic.ae_differentiableAt hf] with z hz hzd
    exact ⟨hzd, hz⟩
  -- The three exceptional families.
  set F1 : Set (ℝ → ℂ) := {γ ∈ Γ | arcLengthLineIntegral G γ = ∞} with hF1
  set F2 : Set (ℝ → ℂ) :=
    {γ ∈ Γ | 1 ≤ arcLengthLineIntegral (N.indicator (fun _ => ∞)) γ} with hF2
  set F3 : Set (ℝ → ℂ) := {γ ∈ Γ | ¬ GoodCurve f γ} with hF3
  -- All three have zero modulus.
  have hF1zero : curveModulus F1 = 0 := curveModulus_lineIntegral_top_zero hf Γ hcont
  have hF2zero : curveModulus F2 = 0 := curveModulus_meetsNullSet_zero hNmeas hNnull Γ
  have hF3zero : curveModulus F3 = 0 :=
    IsQCAnalytic.curveModulus_notGoodCurve_zero hf Γ hcont
  -- The union has zero modulus by subadditivity.
  have hUnionZero : curveModulus (F1 ∪ F2 ∪ F3) = 0 :=
    curveModulus_union_zero (curveModulus_union_zero hF1zero hF2zero) hF3zero
  -- The exceptional family is contained in `F1 ∪ F2 ∪ F3`.
  refine le_antisymm ?_ (zero_le _)
  rw [← hUnionZero]
  refine curveModulus_mono ?_
  rintro γ ⟨hγΓ, hbad⟩
  -- Contrapositive of `chainRule_good_of_finite`: a curve outside `F1 ∪ F2 ∪ F3` is
  -- finite-gradient, meets `N` negligibly, and is good.
  by_contra hnotin
  rw [Set.mem_union, Set.mem_union, not_or, not_or] at hnotin
  obtain ⟨⟨hnF1, hnF2⟩, hnF3⟩ := hnotin
  -- Outside `F1`: the gradient line integral is finite.
  have hfin : arcLengthLineIntegral G γ ≠ ∞ := by
    intro htop; exact hnF1 ⟨hγΓ, htop⟩
  -- Outside `F2`: the contact with `N` has negligible arc length.
  have hmeet : ¬ 1 ≤ arcLengthLineIntegral (N.indicator (fun _ => ∞)) γ := by
    intro hge; exact hnF2 ⟨hγΓ, hge⟩
  -- Outside `F3`: `γ` is a good curve.
  have hgood : GoodCurve f γ := by
    by_contra hng; exact hnF3 ⟨hγΓ, hng⟩
  -- Then all three good clauses hold, contradicting `hbad`.
  exact hbad (chainRule_good_of_finite hf (hcont γ hγΓ) (hac γ hγΓ) hfin hmeet hgood)

/-- **(Image-side exceptional sweep.)** For a quasiconformal `f` and a family `Γ` of
continuous, absolutely continuous curves, the image under `f` of the chain-rule
exceptional subfamily (curves where `f ∘ γ` fails absolute continuity, or positive
Jacobian a.e., or the chain rule) has zero modulus.

This is the image-side companion of `chainRule_exceptional_modulus_zero`. Unlike the
energy transfer for good curves, it cannot be obtained from the source-side modulus by
the dilatation bound (the chain rule, which the density transfer needs, is exactly what
fails on these curves). It is the genuine residual of `image_modulus_zero`, and its
crux is a planar Lusin-(N) property: the image `f '' N` of the degeneracy null set
`N = {z | ¬(DifferentiableAt ℝ f z ∧ 0 < det (fderiv ℝ f z))}` is itself null. -/
theorem IsQCAnalytic.image_chainRule_exceptional_modulus_zero {f : ℂ → ℂ}
    {b : BeltramiCoeff} (hf : IsQCAnalytic f b) (Γ : Set (ℝ → ℂ))
    (hcont : ∀ γ ∈ Γ, Continuous γ)
    (hac : ∀ γ ∈ Γ, ∀ a c : ℝ, AbsolutelyContinuousOnInterval γ a c) :
    curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) ''
      {γ ∈ Γ | ¬ ((∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
          AbsolutelyContinuousOnInterval (f ∘ γ) a c) ∧
        (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
            deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det) ∧
        ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
          HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t)}) = 0 := by
  sorry

/-- **Quasiconformal maps preserve zero modulus.** The image under a quasiconformal
map of a curve family of zero modulus again has zero modulus. The proof splits the
family into the chain-rule *good* curves, whose image modulus is bounded by the
length–area energy transfer with dilatation constant `K* = (1 + ‖μ‖∞)/(1 − ‖μ‖∞)`
(finite because `‖μ‖∞ < 1` is built into `BeltramiCoeff`), and the chain-rule
*exceptional* curves, whose image modulus vanishes by
`image_chainRule_exceptional_modulus_zero`. Since the source family has zero modulus,
the good-curve energy bound collapses to zero, and the two pieces assemble by
subadditivity. -/
theorem IsQCAnalytic.image_modulus_zero {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) {Γ' : Set (ℝ → ℂ)}
    (hcont : ∀ γ ∈ Γ', Continuous γ)
    (hac : ∀ γ ∈ Γ', ∀ a c : ℝ, AbsolutelyContinuousOnInterval γ a c)
    (h0 : curveModulus Γ' = 0) :
    curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γ') = 0 := by
  classical
  -- Notation.
  set hhom : IsHomeomorph f := hf.1.1 with hhom_def
  -- The almost-everywhere essential-sup bound on the Beltrami coefficient.
  have hμae : ∀ᵐ z : ℂ, ‖b.μ z‖ ≤ b.normInf := by
    filter_upwards [ae_le_eLpNormEssSup (f := b.μ) (μ := volume)] with z hz
    have hfin : eLpNormEssSup b.μ volume ≠ ⊤ := ne_top_of_lt b.bound
    have hz' : (‖b.μ z‖₊ : ℝ≥0∞) ≤ eLpNormEssSup b.μ volume := by
      simpa [enorm_eq_nnnorm] using hz
    have := (ENNReal.toReal_le_toReal (by simp) hfin).mpr hz'
    simpa [BeltramiCoeff.normInf, coe_nnnorm] using this
  -- ============================================================
  -- BLOCK A.  Almost-everywhere dilatation bound with the INTRINSIC constant
  --   K* := (1 + ‖μ‖∞) / (1 − ‖μ‖∞):
  --   ‖(Df z)⁻¹‖² · det (Df z) ≤ K*.
  -- ============================================================
  have hkbound : b.normInf < 1 := b.normInf_lt_one
  have hknn : (0 : ℝ) ≤ b.normInf := b.normInf_nonneg
  have h1mk : (0 : ℝ) < 1 - b.normInf := by linarith
  set K : ℝ := (1 + b.normInf) / (1 - b.normInf) with hKdef
  have hK1 : 1 ≤ K := by
    rw [hKdef, le_div_iff₀ h1mk]; linarith
  have hK0 : 0 ≤ K := by linarith
  have hdil : ∀ᵐ z : ℂ,
      ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 * (fderiv ℝ f z).det ≤ K := by
    filter_upwards [hf.1.2, hf.2.2, hμae] with z hdet hbel hμz
    set p : ℂ := dz f z with hp
    set q : ℂ := dzbar f z with hq
    set d : ℝ := (fderiv ℝ f z).det with hd
    have hdval : d = ‖p‖ ^ 2 - ‖q‖ ^ 2 := det_fderiv_eq_wirtinger f z
    have hinvval : ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ = (‖p‖ + ‖q‖) / d :=
      opNorm_inverse_eq_wirtinger f z hdet
    have hqeq : ‖q‖ = ‖b.μ z‖ * ‖p‖ := by rw [hq, ← hq, hbel, norm_mul]
    have hqp : ‖q‖ ≤ b.normInf * ‖p‖ := by
      rw [hqeq]; gcongr
    have hdpos : 0 < d := hdet
    have hppos : 0 < ‖p‖ := by nlinarith [norm_nonneg q, norm_nonneg p, hdval, hdpos]
    have hqnn : 0 ≤ ‖q‖ := norm_nonneg q
    have hpqlt : ‖q‖ < ‖p‖ := by nlinarith [hdval, hdpos, norm_nonneg p]
    have hpmq : 0 < ‖p‖ - ‖q‖ := by linarith
    have hfactor : ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 * d
        = (‖p‖ + ‖q‖) / (‖p‖ - ‖q‖) := by
      rw [hinvval, div_pow, hdval]
      have hsplit : ‖p‖ ^ 2 - ‖q‖ ^ 2 = (‖p‖ + ‖q‖) * (‖p‖ - ‖q‖) := by ring
      rw [hsplit]
      have hsum_ne : ‖p‖ + ‖q‖ ≠ 0 := by positivity
      have hpmq_ne : ‖p‖ - ‖q‖ ≠ 0 := ne_of_gt hpmq
      field_simp
    rw [hfactor]
    -- `(‖p‖+‖q‖)/(‖p‖-‖q‖) ≤ (1+k)/(1-k) = K*`.
    rw [hKdef, div_le_div_iff₀ hpmq h1mk]
    -- `(‖p‖+‖q‖)(1-k) ≤ (1+k)(‖p‖-‖q‖)`, i.e. `2‖q‖ ≤ 2k‖p‖`.
    nlinarith [hqp, hppos]
  -- ============================================================
  -- BLOCK B.  Global infrastructure + good/bad split + energy transfer.
  -- ============================================================
  set S : Set ℂ := {z : ℂ | DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det} with hSdef
  have hSmeas : MeasurableSet S := by
    apply MeasurableSet.inter (measurableSet_of_differentiableAt ℝ f)
    exact measurableSet_lt measurable_const
      ((ContinuousLinearMap.continuous_det).measurable.comp (measurable_fderiv ℝ f))
  have hSae : ∀ᵐ z : ℂ, z ∈ S := by
    filter_upwards [hf.1.2, IsQCAnalytic.ae_differentiableAt hf] with z hz hzd
    exact ⟨hzd, hz⟩
  have hScompl_null : volume (Sᶜ : Set ℂ) = 0 := by
    have : {z : ℂ | ¬ z ∈ S} = (Sᶜ : Set ℂ) := rfl
    rw [← this, ← ae_iff]
    filter_upwards [hSae] with z hz using hz
  set g : ℂ → ℂ := ⇑(hhom.homeomorph f).symm with hg_def
  have hgf : ∀ z, g (f z) = z := (hhom.homeomorph f).symm_apply_apply
  have hfg : ∀ w, f (g w) = w := (hhom.homeomorph f).apply_symm_apply
  have hg_cont : Continuous g := (hhom.homeomorph f).symm.continuous
  have hfderiv_S : ∀ z ∈ S, HasFDerivWithinAt f (fderiv ℝ f z) S z := fun z hz =>
    (hz.1.hasFDerivAt).hasFDerivWithinAt
  have hfinj_S : Set.InjOn f S := hhom.injective.injOn
  have hfSmeas : MeasurableSet (f '' S) :=
    measurable_image_of_fderivWithin hSmeas hfderiv_S hfinj_S
  -- The exceptional (bad) and good subfamilies of `Γ'`.  The `badProp` below is
  -- DEFEQ to the one in `image_chainRule_exceptional_modulus_zero`.
  set badProp : (ℝ → ℂ) → Prop := fun γ =>
    ¬ ((∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
          AbsolutelyContinuousOnInterval (f ∘ γ) a c) ∧
      (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det) ∧
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
        HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t) with hbadProp
  set Γ'bad : Set (ℝ → ℂ) := {γ ∈ Γ' | badProp γ} with hΓ'bad
  set Γ'good : Set (ℝ → ℂ) := Γ' \ Γ'bad with hΓ'good
  -- ============================================================
  -- KEY: for every density `ρ` admissible for `Γ'`,
  --   curveModulus ((f∘·)''Γ'good) ≤ ofReal K* * ∫⁻ ρ².
  -- ============================================================
  have key : ∀ ρ : ℂ → ℝ≥0∞, IsAdmissibleDensity ρ Γ' →
      curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γ'good)
        ≤ ENNReal.ofReal K * ∫⁻ z, (ρ z) ^ 2 := by
    intro ρ ⟨hρmeas, hρadm⟩
    set wt : ℂ → ℝ≥0∞ := fun z =>
      ENNReal.ofReal ((‖dz f z‖ + ‖dzbar f z‖) / (fderiv ℝ f z).det) with hwt_def
    have hwt_eq : ∀ z ∈ S, wt z =
        ENNReal.ofReal ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ := by
      intro z hz
      rw [hwt_def, opNorm_inverse_eq_wirtinger f z hz.2]
    set σ : ℂ → ℝ≥0∞ := fun w =>
      (f '' S).indicator (fun w => ρ (g w) * wt (g w)) w with hσ_def
    have hfderivmeas : Measurable (fderiv ℝ f) := measurable_fderiv ℝ f
    have hdzmeas : Measurable (fun z : ℂ => dz f z) := by
      have h1 : Measurable (fun z : ℂ => (fderiv ℝ f z) 1) :=
        measurable_fderiv_apply_const ℝ f 1
      have h2 : Measurable (fun z : ℂ => (fderiv ℝ f z) Complex.I) :=
        measurable_fderiv_apply_const ℝ f Complex.I
      simpa only [dz] using (measurable_const.mul ((h1.sub (measurable_const.mul h2))))
    have hdzbarmeas : Measurable (fun z : ℂ => dzbar f z) := by
      have h1 : Measurable (fun z : ℂ => (fderiv ℝ f z) 1) :=
        measurable_fderiv_apply_const ℝ f 1
      have h2 : Measurable (fun z : ℂ => (fderiv ℝ f z) Complex.I) :=
        measurable_fderiv_apply_const ℝ f Complex.I
      simpa only [dzbar] using (measurable_const.mul ((h1.add (measurable_const.mul h2))))
    have hdetmeas : Measurable (fun z : ℂ => (fderiv ℝ f z).det) :=
      ContinuousLinearMap.continuous_det.measurable.comp hfderivmeas
    have hwtmeas : Measurable wt := by
      refine ENNReal.measurable_ofReal.comp ?_
      exact ((hdzmeas.norm.add hdzbarmeas.norm).div hdetmeas)
    have hσmeas : Measurable σ := by
      refine (Measurable.indicator ?_ hfSmeas)
      exact (hρmeas.comp hg_cont.measurable).mul (hwtmeas.comp hg_cont.measurable)
    -- Energy bound: ∫⁻ σ² ≤ ofReal K* * ∫⁻ ρ².
    have henergy : ∫⁻ w, (σ w) ^ 2 ≤ ENNReal.ofReal K * ∫⁻ z, (ρ z) ^ 2 := by
      have hσsq_ind : (fun w => (σ w) ^ 2)
          = (f '' S).indicator (fun w => (ρ (g w) * wt (g w)) ^ 2) := by
        funext w
        simp only [hσ_def]
        by_cases hw : w ∈ f '' S
        · simp only [Set.indicator_of_mem hw]
        · simp only [Set.indicator_of_notMem hw]; ring
      rw [hσsq_ind, lintegral_indicator hfSmeas]
      have hcov := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
        (volume : Measure ℂ) hSmeas hfderiv_S hfinj_S
        (fun w => (ρ (g w) * wt (g w)) ^ 2)
      rw [hcov]
      have hmono : ∫⁻ z in S, ENNReal.ofReal |(fderiv ℝ f z).det| *
              (ρ (g (f z)) * wt (g (f z))) ^ 2
          ≤ ∫⁻ z in S, ENNReal.ofReal K * (ρ z) ^ 2 := by
        refine setLIntegral_mono_ae' hSmeas ?_
        filter_upwards [hdil] with z hzdil hzS
        rw [hgf z, hwt_eq z hzS]
        have hdetpos : 0 < (fderiv ℝ f z).det := hzS.2
        rw [abs_of_pos hdetpos, mul_pow, ← ENNReal.ofReal_pow (norm_nonneg _)]
        rw [show ENNReal.ofReal (fderiv ℝ f z).det *
              ((ρ z) ^ 2 * ENNReal.ofReal (‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2))
            = (ρ z) ^ 2 * (ENNReal.ofReal (fderiv ℝ f z).det *
                ENNReal.ofReal (‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2)) by ring]
        rw [← ENNReal.ofReal_mul hdetpos.le, mul_comm (ENNReal.ofReal K) ((ρ z) ^ 2)]
        gcongr
        rw [mul_comm]; exact hzdil
      calc ∫⁻ z in S, ENNReal.ofReal |(fderiv ℝ f z).det| *
              (ρ (g (f z)) * wt (g (f z))) ^ 2
          ≤ ∫⁻ z in S, ENNReal.ofReal K * (ρ z) ^ 2 := hmono
        _ = ENNReal.ofReal K * ∫⁻ z in S, (ρ z) ^ 2 := by
            rw [lintegral_const_mul _ (hρmeas.pow_const 2)]
        _ ≤ ENNReal.ofReal K * ∫⁻ z, (ρ z) ^ 2 :=
            mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
    -- `σ` is admissible for `(f∘·)''Γ'good`.
    have hσadm : IsAdmissibleDensity σ ((fun γ : ℝ → ℂ => f ∘ γ) '' Γ'good) := by
      refine ⟨hσmeas, ?_⟩
      rintro δ ⟨γ, hγgood, rfl⟩
      have hγΓ : γ ∈ Γ' := hγgood.1
      have hnotbad : ¬ badProp γ := by
        intro hbad; exact hγgood.2 ⟨hγΓ, hbad⟩
      rw [hbadProp] at hnotbad
      obtain ⟨hAC, hdetγ, hchainγ⟩ := not_not.mp hnotbad
      have hpoint : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞)
            ≤ σ ((f ∘ γ) t) * (‖deriv (f ∘ γ) t‖₊ : ℝ≥0∞) := by
        filter_upwards [hdetγ, hchainγ] with t hdett₀ hchaint₀
        rcases eq_or_ne (deriv γ t) 0 with hd0 | hd0
        · simp [hd0]
        have hdett : 0 < (fderiv ℝ f (γ t)).det := hdett₀ hd0
        have hchaint : HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t :=
          hchaint₀ hd0
        set A : ℂ →L[ℝ] ℂ := fderiv ℝ f (γ t) with hA
        have hdett' : 0 < (fderiv ℝ f (γ t)).det := hdett
        have hγtS : γ t ∈ S := by
          refine ⟨?_, hdett'⟩
          by_contra hnd
          rw [fderiv_zero_of_not_differentiableAt hnd] at hdett'
          simp [ContinuousLinearMap.det] at hdett'
        have hAinv : A.IsInvertible :=
          ⟨A.toContinuousLinearEquivOfDetNeZero hdett.ne',
            A.coe_toContinuousLinearEquivOfDetNeZero hdett.ne'⟩
        have hderiv : deriv (f ∘ γ) t = A (deriv γ t) := hchaint.deriv
        have hfγtS : f (γ t) ∈ f '' S := ⟨γ t, hγtS, rfl⟩
        have hσval : σ ((f ∘ γ) t) = ρ (γ t) * ENNReal.ofReal ‖A.inverse‖ := by
          simp only [Function.comp_apply, hσ_def]
          rw [Set.indicator_of_mem hfγtS, hgf, hwt_eq (γ t) hγtS]
        rw [hσval, hderiv]
        have hkey : (‖deriv γ t‖₊ : ℝ≥0∞)
            ≤ ENNReal.ofReal ‖A.inverse‖ * (‖A (deriv γ t)‖₊ : ℝ≥0∞) := by
          have hself : A.inverse (A (deriv γ t)) = deriv γ t :=
            ContinuousLinearMap.IsInvertible.inverse_apply_self hAinv (deriv γ t)
          have hop : ‖deriv γ t‖₊ ≤ ‖A.inverse‖₊ * ‖A (deriv γ t)‖₊ := by
            have hle : ‖A.inverse (A (deriv γ t))‖₊ ≤ ‖A.inverse‖₊ * ‖A (deriv γ t)‖₊ :=
              A.inverse.le_opNNNorm _
            rwa [hself] at hle
          have hcoe : ENNReal.ofReal ‖A.inverse‖ = (‖A.inverse‖₊ : ℝ≥0∞) := by
            rw [ofReal_norm_eq_enorm, enorm_eq_nnnorm]
          rw [hcoe, ← ENNReal.coe_mul]
          exact_mod_cast hop
        calc ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞)
            ≤ ρ (γ t) * (ENNReal.ofReal ‖A.inverse‖ * (‖A (deriv γ t)‖₊ : ℝ≥0∞)) := by
              gcongr
          _ = ρ (γ t) * ENNReal.ofReal ‖A.inverse‖ * (‖A (deriv γ t)‖₊ : ℝ≥0∞) := by ring
      have hint : arcLengthLineIntegral ρ γ ≤ arcLengthLineIntegral σ (f ∘ γ) := by
        unfold arcLengthLineIntegral
        exact lintegral_mono_ae hpoint
      exact le_trans (hρadm γ hγΓ) hint
    calc curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γ'good)
        ≤ ∫⁻ w, (σ w) ^ 2 := iInf₂_le σ hσadm
      _ ≤ ENNReal.ofReal K * ∫⁻ z, (ρ z) ^ 2 := henergy
  -- ============================================================
  -- BLOCK C.  Assemble to `0`.
  -- ============================================================
  -- The bad image has zero modulus by the chain-rule exceptional sweep.
  have hbadimg : curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γ'bad) = 0 :=
    IsQCAnalytic.image_chainRule_exceptional_modulus_zero hf Γ' hcont hac
  -- The good image has zero modulus: collapse the energy bound using `h0`.
  have hgoodimg : curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γ'good) = 0 := by
    refine le_antisymm ?_ (zero_le _)
    have hKne0 : ENNReal.ofReal K ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
    have hKnetop : ENNReal.ofReal K ≠ ⊤ := ENNReal.ofReal_ne_top
    have hbound : curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γ'good)
        ≤ ENNReal.ofReal K * curveModulus Γ' := by
      conv_rhs => rw [curveModulus, ENNReal.mul_iInf_of_ne hKne0 hKnetop]
      refine le_iInf fun ρ => ?_
      rw [ENNReal.mul_iInf_of_ne hKne0 hKnetop]
      refine le_iInf fun hρ => ?_
      exact key ρ hρ
    rw [h0, mul_zero] at hbound
    exact hbound
  -- The full image is the union of the two zero-modulus pieces.
  have himg_union : (fun γ : ℝ → ℂ => f ∘ γ) '' Γ'
      = (fun γ : ℝ → ℂ => f ∘ γ) '' Γ'good ∪ (fun γ : ℝ → ℂ => f ∘ γ) '' Γ'bad := by
    rw [← Set.image_union]
    congr 1
    rw [hΓ'good]
    ext γ
    constructor
    · intro hγ
      by_cases hb : γ ∈ Γ'bad
      · exact Or.inr hb
      · exact Or.inl ⟨hγ, hb⟩
    · rintro (⟨hγ, _⟩ | hb)
      · exact hγ
      · exact hb.1
  rw [himg_union]
  exact curveModulus_union_zero hgoodimg hbadimg

end RiemannDynamics

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Regularity.GeometricToACL
import RiemannDynamics.QC.LengthArea.CurveModulus

/-!
# Pointwise dilatation bound for geometric quasiconformality

A geometrically `K`-quasiconformal homeomorphism satisfies, almost everywhere, the pointwise
dilatation inequality `‖(Df)⁻¹‖² · det (Df) ≤ K` for the real differential `Df = fderiv ℝ f`.

This is the analytic payoff of the length–area regularity theory. From `IsQCGeometric` the map is
`W^{1,2}_loc` and almost-everywhere differentiable (`geometric_ae_differentiableAt`), and
`SensePreserving` gives a positive Jacobian almost everywhere (`SensePreserving.ae_det_pos`). The
length–area transport of the round-annulus/rectangle modulus bound pins the operator dilatation
`‖(Df)⁻¹‖² · det (Df)` — equivalently `(|∂f| + |∂̄f|) / (|∂f| − |∂̄f|)` via the Wirtinger identities
`det_fderiv_eq_wirtinger` and `opNorm_inverse_eq_wirtinger` — below `K`.

The conclusion is stated in exactly the form consumed by the length–area transport
`pushforwardGood_modulus_le`.

## Main statements

* `geometric_pointwise_dilatation` — the almost-everywhere bound `‖(Df)⁻¹‖² · det (Df) ≤ K`.
-/

open MeasureTheory Complex
open scoped ENNReal NNReal Topology

namespace RiemannDynamics

/-- The **rotated square** centred at `z` with half-side `ε > 0` and unit direction `e`
(`‖e‖ = 1`): the affine parametrization `q ↦ z + ε·e·((2 q.1 − 1) + (2 q.2 − 1) i)`. Its image is
the square of side `2 ε` centred at `z`, with sides parallel to `e` and `i·e`; the left side is the
image of `{0} × [0, 1]`, the right side the image of `{1} × [0, 1]`. -/
noncomputable def rotSquare (z : ℂ) (ε : ℝ) (e : ℂ) (hε : 0 < ε) (he : ‖e‖ = 1) :
    Quadrilateral where
  toFun q := z + (ε : ℂ) * e *
    (((2 * q.1 - 1 : ℝ) : ℂ) + ((2 * q.2 - 1 : ℝ) : ℂ) * Complex.I)
  continuous_toFun := by
    refine continuous_const.add (continuous_const.mul ?_)
    exact (Complex.continuous_ofReal.comp (by fun_prop)).add
      ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)
  injOn_unitSquare := by
    intro q _ q' _ hqq'
    simp only [add_right_inj] at hqq'
    have hfac : (ε : ℂ) * e ≠ 0 := by
      refine mul_ne_zero (by exact_mod_cast ne_of_gt hε) ?_
      rw [← norm_ne_zero_iff, he]; norm_num
    rw [mul_right_inj' hfac] at hqq'
    have hre := congrArg Complex.re hqq'
    have him := congrArg Complex.im hqq'
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, zero_add] at hre him
    exact Prod.ext (by linarith) (by linarith)

/-- **Modulus upper bound for the rotated square.** The connecting-family modulus of the rotated
square `rotSquare z ε e` is at most `1`: the constant density `1 / (2 ε)` on the square is
admissible (every connecting curve crosses the width `2 ε` between the two `e`-perpendicular sides)
with energy `area / (2 ε)² = 1`. -/
theorem rotSquare_modulus_le_one {z : ℂ} {ε : ℝ} {e : ℂ} (hε : 0 < ε) (he : ‖e‖ = 1) :
    (rotSquare z ε e hε he).modulus ≤ 1 := by
  sorry

/-- **Image-family modulus lower bound for the rotated square aligned to the minimal-stretch
direction.** If `f` is a homeomorphism differentiable at `z` with differential `A = fderiv ℝ f z`,
and the unit direction `e` is a minimal-stretch direction of `A` (`‖A e‖ = σ₂ = |∂f| − |∂̄f|` and
`‖A (i·e)‖ = σ₁ = |∂f| + |∂̄f|`), then for every `δ > 0` there is a half-side `ε > 0` at which the
image connecting family of `rotSquare z ε e` has modulus at least `σ₁ / σ₂ − δ`. The image is,
to first order, a `σ₂ × σ₁` rectangle; a per-fibre exit-point segment and Cauchy–Schwarz give the
length–area lower bound, whose leading term is `σ₁ / σ₂` and whose error is `o(1)` in `ε`. -/
theorem rotSquare_imageCurveFamily_modulus_ge {f : ℂ → ℂ} {z : ℂ} {e : ℂ}
    (hfh : IsHomeomorph f) (hd : HasFDerivAt f (fderiv ℝ f z) z) (he : ‖e‖ = 1)
    (hmin : ‖(fderiv ℝ f z) e‖ = ‖dz f z‖ - ‖dzbar f z‖)
    (hmax : ‖(fderiv ℝ f z) (Complex.I * e)‖ = ‖dz f z‖ + ‖dzbar f z‖)
    (hpos : 0 < ‖dz f z‖ - ‖dzbar f z‖) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, ∃ hε : 0 < ε,
      ENNReal.ofReal ((‖dz f z‖ + ‖dzbar f z‖) / (‖dz f z‖ - ‖dzbar f z‖) - δ)
        ≤ curveModulus ((rotSquare z ε e hε he).imageCurveFamily f) := by
  sorry

/-- **Minimal-stretch direction of a Wirtinger real-linear map.** For `A w = p·w + q·conj w` with
`‖q‖ < ‖p‖` and `q ≠ 0`, there is a unit direction `e` at which `A` shrinks maximally
(`‖A e‖ = ‖p‖ − ‖q‖`) and, perpendicularly, stretches maximally (`‖A (i·e)‖ = ‖p‖ + ‖q‖`). The
direction is a square root of `−(q/p)·(‖p‖/‖q‖)`, cancelling the `q·conj e` term against `p·e`. -/
theorem align_minStretch (p q : ℂ) (hqlt : ‖q‖ < ‖p‖) (hqne : q ≠ 0)
    (A : ℂ →L[ℝ] ℂ) (hArep : ∀ w : ℂ, A w = p * w + q * (starRingEnd ℂ) w) :
    ∃ e : ℂ, ‖e‖ = 1 ∧ ‖A e‖ = ‖p‖ - ‖q‖ ∧ ‖A (Complex.I * e)‖ = ‖p‖ + ‖q‖ := by
  have hppos : 0 < ‖p‖ := lt_of_le_of_lt (norm_nonneg q) hqlt
  have hpne : p ≠ 0 := by rw [← norm_ne_zero_iff]; positivity
  have hqpos : 0 < ‖q‖ := by rwa [norm_pos_iff]
  have hpRne : (‖p‖ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hppos
  have hqRne : (‖q‖ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hqpos
  set u : ℂ := -(q / p) * ((‖p‖ : ℂ) / (‖q‖ : ℂ)) with hu
  have hunorm : ‖u‖ = 1 := by
    rw [hu, norm_mul, norm_neg, norm_div, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hppos.le, Real.norm_of_nonneg hqpos.le]
    field_simp
  obtain ⟨e, he2⟩ := Complex.isSquare u
  have hene1 : ‖e‖ = 1 := by
    have h : ‖e‖ * ‖e‖ = 1 := by rw [← norm_mul, ← he2, hunorm]
    nlinarith [norm_nonneg e, h]
  have hene : e ≠ 0 := by rw [← norm_ne_zero_iff, hene1]; norm_num
  have hconje : (starRingEnd ℂ) e = e⁻¹ := by
    have hh : e * (starRingEnd ℂ) e = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hene1]; norm_num
    rw [inv_eq_one_div, eq_div_iff hene]; linear_combination hh
  have he2' : e * e = u := he2.symm
  have hrel : e * e * p * (‖q‖ : ℂ) = -(q * (‖p‖ : ℂ)) := by rw [he2', hu]; field_simp
  have hqconje : q * (starRingEnd ℂ) e = -(e * p * (‖q‖ : ℂ) / (‖p‖ : ℂ)) := by
    rw [hconje]
    have hcancel : q * e⁻¹ * (e * (‖p‖ : ℂ))
        = -(e * p * (‖q‖ : ℂ) / (‖p‖ : ℂ)) * (e * (‖p‖ : ℂ)) := by
      field_simp; linear_combination hrel
    exact mul_right_cancel₀ (mul_ne_zero hene hpRne) hcancel
  have hAe : A e = p * e * ((‖p‖ - ‖q‖ : ℝ) : ℂ) / (‖p‖ : ℂ) := by
    rw [hArep, hqconje]; push_cast; field_simp; ring
  have hnormAe : ‖A e‖ = ‖p‖ - ‖q‖ := by
    rw [hAe, norm_div, norm_mul, norm_mul, hene1, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ ‖p‖ - ‖q‖), Real.norm_of_nonneg hppos.le]
    field_simp
  have hAIe : A (Complex.I * e) = Complex.I * p * e * ((‖p‖ + ‖q‖ : ℝ) : ℂ) / (‖p‖ : ℂ) := by
    rw [hArep]
    have hcI : (starRingEnd ℂ) (Complex.I * e) = -Complex.I * (starRingEnd ℂ) e := by
      rw [map_mul, Complex.conj_I]
    rw [hcI, hconje]
    have hqe : q * (-Complex.I * e⁻¹) = -Complex.I * (q * e⁻¹) := by ring
    rw [hqe]
    have hqei : q * e⁻¹ = -(e * p * (‖q‖ : ℂ) / (‖p‖ : ℂ)) := by rw [← hconje]; exact hqconje
    rw [hqei]; push_cast; field_simp
  have hnormAIe : ‖A (Complex.I * e)‖ = ‖p‖ + ‖q‖ := by
    rw [hAIe, norm_div, norm_mul, norm_mul, norm_mul, hene1, Complex.norm_I,
      Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ‖p‖ + ‖q‖), Real.norm_of_nonneg hppos.le]
    field_simp
  exact ⟨e, hene1, hnormAe, hnormAIe⟩

/-- **The maximal-dilatation inequality at a point of positive Jacobian.** For a geometrically
`K`-quasiconformal homeomorphism `f` differentiable at `z` with positive Jacobian, the Wirtinger
singular values `σ₁ = |∂f| + |∂̄f|` and `σ₂ = |∂f| − |∂̄f|` satisfy `σ₁ ≤ K · σ₂`. This is the
geometric core of the pointwise dilatation bound: a rotated square microscopically aligned with the
minimal-stretch direction has image connecting family of modulus tending to `σ₁ / σ₂`, while the
`IsQCGeometric` modulus transport bounds that modulus by `K` times the square's own modulus `1`. -/
theorem geometric_dilatation_wirtinger {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    {z : ℂ} (hdiff : DifferentiableAt ℝ f z) (hdet : 0 < (fderiv ℝ f z).det) :
    ‖dz f z‖ + ‖dzbar f z‖ ≤ K * (‖dz f z‖ - ‖dzbar f z‖) := by
  have hK1 : (1 : ℝ) ≤ K := hf.1
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
  set A : ℂ →L[ℝ] ℂ := fderiv ℝ f z with hA
  set p : ℂ := dz f z with hp
  set q : ℂ := dzbar f z with hq
  -- Wirtinger representation of the real differential `A w = p w + q conj w`.
  have hArep : ∀ w : ℂ, A w = p * w + q * (starRingEnd ℂ) w := by
    intro w
    rw [hp, hq, dz, dzbar]
    have hLw : A w = (↑w.re : ℂ) * A 1 + (↑w.im : ℂ) * A Complex.I := by
      conv_lhs => rw [show w = w.re • (1 : ℂ) + w.im • Complex.I by
        rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
      rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    have hcw : (starRingEnd ℂ) w = (↑w.re : ℂ) - ↑w.im * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im w]
      simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
    have hw : w = (↑w.re : ℂ) + ↑w.im * Complex.I := (Complex.re_add_im w).symm
    rw [hLw, hcw]
    set sa : ℂ := (↑w.re : ℂ) with hsa
    set sb : ℂ := (↑w.im : ℂ) with hsb
    rw [hw]
    linear_combination (sb * A Complex.I) * Complex.I_mul_I
  have hdetw : A.det = ‖p‖ ^ 2 - ‖q‖ ^ 2 := by rw [hA, hp, hq]; exact det_fderiv_eq_wirtinger f z
  have hqlt : ‖q‖ < ‖p‖ := by
    rw [hA] at hdet; nlinarith [hdet, hdetw, norm_nonneg p, norm_nonneg q]
  have hσ2pos : 0 < ‖p‖ - ‖q‖ := by linarith
  have hd' : HasFDerivAt f A z := by rw [hA]; exact hdiff.hasFDerivAt
  rcases eq_or_ne q 0 with hq0 | hqne
  · -- `∂̄f = 0`: `σ₁ = σ₂ = ‖p‖`, so the bound is `1 ≤ K`.
    rw [hq0, norm_zero, add_zero, sub_zero]
    nlinarith [norm_nonneg p, hqlt, hK1]
  · -- Minimal-stretch alignment: a unit direction `e` with `‖A e‖ = σ₂`, `‖A(i e)‖ = σ₁`.
    obtain ⟨e, hene1, hnormAe, hnormAIe⟩ :
        ∃ e : ℂ, ‖e‖ = 1 ∧ ‖A e‖ = ‖p‖ - ‖q‖ ∧ ‖A (Complex.I * e)‖ = ‖p‖ + ‖q‖ := by
      exact align_minStretch p q hqlt hqne A hArep
    -- The Wirtinger dilatation `σ₁ / σ₂ ≤ K` from the microscopic square limit.
    have hratio : (‖p‖ + ‖q‖) / (‖p‖ - ‖q‖) ≤ K := by
      refine le_of_forall_lt_imp_le_of_dense (fun c hc => ?_)
      -- suffices to bound `σ₁/σ₂ - δ ≤ K` for all `δ > 0`; take `δ = σ₁/σ₂ - c`.
      set δ : ℝ := (‖p‖ + ‖q‖) / (‖p‖ - ‖q‖) - c with hδdef
      have hδpos : 0 < δ := by rw [hδdef]; linarith
      obtain ⟨ε, hε, hmodge⟩ := rotSquare_imageCurveFamily_modulus_ge (f := f) (z := z) (e := e)
        (hf.2.1.1) hd' hene1 hnormAe hnormAIe hσ2pos hδpos
      -- transport bound: `mod(imageFam) ≤ K · mod(square) ≤ K`.
      have htrans : curveModulus ((rotSquare z ε e hε hene1).imageCurveFamily f)
          ≤ ENNReal.ofReal K := by
        refine le_trans (hf.2.2 (rotSquare z ε e hε hene1)) ?_
        calc ENNReal.ofReal K * (rotSquare z ε e hε hene1).modulus
            ≤ ENNReal.ofReal K * 1 := by gcongr; exact rotSquare_modulus_le_one hε hene1
          _ = ENNReal.ofReal K := by rw [mul_one]
      have hchain : ENNReal.ofReal
          ((‖p‖ + ‖q‖) / (‖p‖ - ‖q‖) - δ) ≤ ENNReal.ofReal K :=
        le_trans hmodge htrans
      rw [ENNReal.ofReal_le_ofReal_iff hK0, hδdef] at hchain
      linarith [hchain]
    rw [div_le_iff₀ hσ2pos] at hratio
    exact hratio

/-- **Pointwise dilatation bound of a geometrically quasiconformal map.** For a geometrically
`K`-quasiconformal homeomorphism `f`, at almost every point the real differential `Df = fderiv ℝ f`
satisfies `‖(Df)⁻¹‖² · det (Df) ≤ K`. This is the almost-everywhere dilatation inequality in the
exact operator form the length–area transport `pushforwardGood_modulus_le` consumes; via the
Wirtinger identities it is `(|∂f| + |∂̄f|) / (|∂f| − |∂̄f|) ≤ K`, i.e. the pointwise maximal
dilatation is bounded by `K`. Where the Jacobian is non-positive the operator dilatation is
non-positive and the bound is automatic; where it is positive the map is differentiable and the
Wirtinger core `geometric_dilatation_wirtinger` supplies the bound. -/
theorem geometric_pointwise_dilatation {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∀ᵐ z : ℂ,
      ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 * (fderiv ℝ f z).det ≤ K := by
  have hK1 : (1 : ℝ) ≤ K := hf.1
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
  refine Filter.Eventually.of_forall (fun z => ?_)
  by_cases hdet : 0 < (fderiv ℝ f z).det
  · -- Positive Jacobian forces differentiability (else `fderiv = 0`, `det = 0`).
    have hdiff : DifferentiableAt ℝ f z := by
      by_contra hnd
      rw [fderiv_zero_of_not_differentiableAt hnd] at hdet
      simp [ContinuousLinearMap.det] at hdet
    set p : ℂ := dz f z with hp
    set q : ℂ := dzbar f z with hq
    have hdetw : (fderiv ℝ f z).det = ‖p‖ ^ 2 - ‖q‖ ^ 2 := by
      rw [hp, hq]; exact det_fderiv_eq_wirtinger f z
    have hqlt : ‖q‖ < ‖p‖ := by nlinarith [hdet, hdetw, norm_nonneg p, norm_nonneg q]
    have hσ2pos : 0 < ‖p‖ - ‖q‖ := by linarith
    have hopn : ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖
        = (‖p‖ + ‖q‖) / (fderiv ℝ f z).det := by
      rw [hp, hq]; exact opNorm_inverse_eq_wirtinger f z hdet
    have hcore := geometric_dilatation_wirtinger hf hdiff hdet
    rw [← hp, ← hq] at hcore
    -- `‖A⁻¹‖² · det = σ₁ / σ₂` and `σ₁ ≤ K σ₂ ⇒ σ₁/σ₂ ≤ K`.
    have hval : ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 * (fderiv ℝ f z).det
        = (‖p‖ + ‖q‖) / (‖p‖ - ‖q‖) := by
      rw [hopn, hdetw, div_pow,
        show (‖p‖ ^ 2 - ‖q‖ ^ 2) = (‖p‖ + ‖q‖) * (‖p‖ - ‖q‖) by ring]
      field_simp
    rw [hval, div_le_iff₀ hσ2pos]
    exact hcore
  · -- Non-positive Jacobian: the operator dilatation is non-positive.
    rw [not_lt] at hdet
    have h1 : (0 : ℝ) ≤ ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 := by positivity
    calc ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 * (fderiv ℝ f z).det
        ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 hdet
      _ ≤ K := hK0

end RiemannDynamics
